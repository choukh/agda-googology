# 高度抽象: 字面上把 `Ordᴵ` 作高度

> 结论写在 [LadderInf](LadderInf.lagda.md). **判决: 字面的实例不存在 (编译过的否定), 只否定下面这个结构原样搬到 $(\mathrm{Ord}^I, <^I, 0)$.** 不否定带界比较的变体, 也不否定 "高度是序数" 这个想法.
>
> | 字段 | $(\mathrm{Ord}^I,<^I,0)$ 上 | 定理 |
> | --- | --- | --- |
> | `tr<`, `irr`, `no<` | 成立 | `trᴼ`, `irrᴼ`, `noᴼ` |
> | `Rec`, `Rec-β` | 成立 (就是 `Us` 的递归) | `recᴼ`, `recᴼ-β` |
> | `tr-assoc` | 成立 | `assocᴼ` |
> | `tri` | **假** | `no-triᴼ` ($\omega$ 与 $\omega'=[1,2,3,\dots]$ 不可比, 即 `¬tri`) |
> | `bot` | **假** | `no-botᴼ` (常值 $0$ 的极限) |
> | `view` | **没有** | `no-viewᴼ` (同一个例子: 第 0 行三种写法都要低于它的元素) |
> | `view-step` | 依赖 `view`, 对 `suc ↦ clos zero` 这个选法是假的 | 判断, 见 [LadderInf](LadderInf.lagda.md) |
>
> `bot` 与 `view` 的失败是 $\mathrm{Ord}^I$ 的退化极限造成的, 不是壁垒; `tri` 的失败才是. 判断见结论文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfOrd where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level
open import OCF.Align.LadderInfBase

trᴼ : ∀ {a b c} → a <ᴵ b → b <ᴵ c → a <ᴵ c
trᴼ = <ᴵ-trans

irrᴼ : ∀ {a} → a <ᴵ a → ⊥
irrᴼ {a} q = ≺ᴵ-irrefl (via (≅ᴵ-refl a) q)

noᴼ : ∀ {i} → i <ᴵ zero → ⊥
noᴼ ()

recᴼ : ∀ {ℓ : Level} (X : Ordᴵ → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴵ m → X n) → X m) → ∀ m {n} → n <ᴵ m → X n
recᴼ X F (suc m)   zero      = F m (recᴼ X F m)
recᴼ X F (suc m)   (suc q)   = recᴼ X F m q
recᴼ X F (lim f s) (lim i q) = recᴼ X F (f i) q

recᴼ-β : ∀ {ℓ : Level} (X : Ordᴵ → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴵ m → X n) → X m) → ∀ m {n} (q : n <ᴵ m) → recᴼ X F m q ≡ F n (recᴼ X F n)
recᴼ-β X F (suc m)   zero      = refl
recᴼ-β X F (suc m)   (suc q)   = recᴼ-β X F m q
recᴼ-β X F (lim f s) (lim i q) = recᴼ-β X F (f i) q

assocᴼ : ∀ {a b c d} (x : a <ᴵ b) (y : b <ᴵ c) (z : c <ᴵ d) → trᴼ (trᴼ x y) z ≡ trᴼ x (trᴼ y z)
assocᴼ x y zero      = refl
assocᴼ x y (suc z)   = cong suc (assocᴼ x y z)
assocᴼ x y (lim n z) = cong (lim n) (assocᴼ x y z)

-- 字段 tri 是假的
ωᴼ : Ordᴵ
ωᴼ = lim natᴵ natᴵ-step

ω′ᴼ : Ordᴵ
ω′ᴼ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

head : Ordᴵ → Ordᴵ
head (lim f s) = f 0
head a = a

nl : ∀ m {f s} → lim f s <ᴵ natᴵ m → ⊥
nl zero ()
nl (suc zero) (suc ())
nl (suc (suc m)) (suc q) = nl (suc m) q

no-triᴼ : (∀ a b → Tri _<ᴵ_ a b) → ⊥
no-triᴼ t with t ωᴼ ω′ᴼ
... | tlt (lim n q) = nl (suc n) q
... | tgt (lim n q) = nl n q
... | teq e with cong head e
...   | ()

-- 退化的极限: 下面什么都没有
𝟎ω : Ordᴵ
𝟎ω = lim (λ _ → zero) (λ _ → z⊑)

none : ∀ {a} → a <ᴵ 𝟎ω → ⊥
none (lim n ())

no-botᴼ : (∀ i → (zero ≡ i) ⊎ (zero <ᴵ i)) → ⊥
no-botᴼ b with b 𝟎ω
... | inj₁ ()
... | inj₂ q = none q

no-viewᴼ : (∀ m → View _<ᴵ_ zero m) → ⊥
no-viewᴼ v with v 𝟎ω
... | clos q = none q
... | chain F qs = none (qs 0)
```
