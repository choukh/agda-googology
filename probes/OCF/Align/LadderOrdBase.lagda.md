# 序数高度 (一): 结构 `HtB`

> **判决: HOLDS (只有声明与由字段导出的量).** 结论写在 [LadderOrd](LadderOrd.lagda.md). `HtB` 是 [LadderInfBase](LadderInfBase.lagda.md) 的 `HtS` 的弱化: `Ht` 只是一个字面上界之下的段, 三歧只在段内. 与 `HtS` 的差别:
>
> 1. `Rec`, `Rec-β` 不再是字段, 由 **秩** `rk : Ht → Ordᴵ`, `rk<` 导出 (`RecR`). 秩只要把 $<$ 映到字面路径, 不要求单射, 不要求保值.
> 2. `tr-assoc` 不再是字段, 由 $<$ 的命题性 `<-prop` 导出. 这也是 `Rq` 里同一个 $q$ 可以留着不放宽的原因.
> 3. `view-step` (链的下一项必须是上一项的闭包) 去掉, 换成 `view-ok`: 第 0 行的写法要告诉我们什么在它下面. 这是 $\omega^2$ 需要的 (`view-step` 在那里是假的).
> 4. `irr`, `no<` 也导出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdBase where

open import Agda.Primitive using (Level; Setω)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _≅ᴵ_; ≅ᴵ-refl; ≺ᴵ-irrefl; via)
open import OCF.Align.LadderInfBase public using (Tri; tlt; teq; tgt; View; base; clos; chain)

-- 第 0 行的写法附带的证据: 什么在这个高度下面
ViewOk : {H : Set} (_<_ : H → H → Set) (h₀ m : H) → View _<_ h₀ m → Set
ViewOk _<_ h₀ m base = ⊤
ViewOk _<_ h₀ m (clos {n = n} q) = ∀ {x} → x < m → (x ≡ n) ⊎ (x < n)
ViewOk _<_ h₀ m (chain F qs) = (∀ i → F i < F (suc i)) × (∀ {x} → x < m → Σ ℕ λ i → (x ≡ F i) ⊎ (x < F i))
```

## §1 由秩导出的递归

`Rec-β` 没有函数外延是证不出来的, 除非右边的函数字面就是 `Rec X F n`. 所以递归按秩的字面路径走, 秩的相等用 `e` 带着, 基本情形把 `e` 消掉.

```agda
module RecR {Ht : Set} (_<_ : Ht → Ht → Set) (rk : Ht → Ordᴵ) (rk< : ∀ {a b} → a < b → rk a <ᴵ rk b) where
  RecP : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ t {a} → a <ᴵ t → ∀ n → rk n ≡ a → X n
  RecP X F (suc a)   zero      n e = F n (λ {n′} q′ → RecP X F a (subst (rk n′ <ᴵ_) e (rk< q′)) n′ refl)
  RecP X F (suc b)   (suc r)   n e = RecP X F b r n e
  RecP X F (lim f s) (lim j r) n e = RecP X F (f j) r n e

  Rec : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ m {n} → n < m → X n
  Rec X F m {n} q = RecP X F (rk m) (rk< q) n refl

  RecP-β : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ t {a} (r : a <ᴵ t) n (e : rk n ≡ a) → RecP X F t r n e ≡ F n (Rec X F n)
  RecP-β X F (suc a)   zero      n refl = refl
  RecP-β X F (suc b)   (suc r)   n e    = RecP-β X F b r n e
  RecP-β X F (lim f s) (lim j r) n e    = RecP-β X F (f j) r n e

  Rec-β : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ m {n} (q : n < m) → Rec X F m q ≡ F n (Rec X F n)
  Rec-β X F m {n} q = RecP-β X F (rk m) (rk< q) n refl
```

## §2 结构

```agda
record HtB : Setω where
  infix 4 _<ᴸ_
  field
    Ht     : Set
    _<ᴸ_   : Ht → Ht → Set
    h₀     : Ht
    -- 序: 传递, 命题, h₀ 在最下
    tr<    : ∀ {m c d} → m <ᴸ c → c <ᴸ d → m <ᴸ d
    <-prop : ∀ {a b} (x y : a <ᴸ b) → x ≡ y
    bot    : ∀ i → (h₀ ≡ i) ⊎ (h₀ <ᴸ i)
    -- 三歧: 只在这个段内
    tri    : ∀ a b → Tri _<ᴸ_ a b
    -- 秩: 把 < 映到字面路径
    rk     : Ht → Ordᴵ
    rk<    : ∀ {a b} → a <ᴸ b → rk a <ᴵ rk b
    -- 第 0 行的写法
    view    : ∀ m → View _<ᴸ_ h₀ m
    view-ok : ∀ m → ViewOk _<ᴸ_ h₀ m (view m)

  -- 以下都导出
  irr : ∀ {m} → m <ᴸ m → ⊥
  irr {m} q = ≺ᴵ-irrefl (via (≅ᴵ-refl (rk m)) (rk< q))

  no< : ∀ {i} → i <ᴸ h₀ → ⊥
  no< {i} q with bot i
  ... | inj₁ refl = irr q
  ... | inj₂ r = irr (tr< q r)

  tr-assoc : ∀ {a b c d} (x : a <ᴸ b) (y : b <ᴸ c) (z : c <ᴸ d) → tr< (tr< x y) z ≡ tr< x (tr< y z)
  tr-assoc x y z = <-prop _ _

  open RecR _<ᴸ_ rk rk< public using (Rec; Rec-β)
```
