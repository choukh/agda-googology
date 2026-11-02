# 奇异下标的定时检验: 判决的精确规格、WLPO 的边界与新判决 `D♯` (不含记号)

> 底座, 结论在 [InaccSingular](InaccSingular.lagda.md). 本文件的导入链不含 `OCF.Align.EBO`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingularBase where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-cancelʳ-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.InaccTreeBase hiding (eq; _+_)
open import OCF.Align.InaccStrikeBase using (Funext; St; strip; toLvS; module Ext)
open import OCF.Align.InaccStrikeOracle using (natL; natT′)
open import OCF.Align.InaccModulusBase
```

`WLPO` 与 `Stage2` 的定义逐字相同; 这里重述一次, 因为 `Stage2` 的导入链含记号.

```agda
WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)
```

## §1 判决的精确规格

`Right V`: `pen` 的路径字面命中, `rise` 确实没有路径. 正确的判决就是字面前驱关系 `Nd` 的判定过程, 外加见证 (`right→dec`). 这个规格只提树. `Nd-limᴼ` 是 `limᴼ` 目标上的全部内容: `j` 是 `k`, 或在 `k` 之下, 或落在**某个字面的** `g x` 之下.

```agda
Right : ∀ {j i} → Verdict j i → Set
Right {j} {i} (pen r b) = at i r ≡ j
Right {j} {i} rise      = ¬ Nd j i

right→dec : ∀ {j i} (V : Verdict j i) → Right V → Dec (Nd j i)
right→dec (pen r b) e = yes (r , e)
right→dec rise      n = no n

Nd-limᴼ : ∀ {j k} {g : Ordᴸ k → Lv} → Nd j (limᴼ k g) → (k ≡ j) ⊎ (Nd j k ⊎ Σ (Ordᴸ k) λ x → Nd j (g x))
Nd-limᴼ (inj₁ (inj₁ _) , e) = inj₁ e
Nd-limᴼ (inj₁ (inj₂ r) , e) = inj₂ (inj₁ (r , e))
Nd-limᴼ (inj₂ (x , r) , e)  = inj₂ (inj₂ (x , r , e))
```

## §2 对整个 `Reg` 正确的判决推出 WLPO

`Stage2` 的 `dec→WLPO` 用的是任意树. 这里更强: 族 `σ s` 的每一棵都**规整**. `σ s` 在第一个 `true` 之前逐字是 `[0,1,2,…]`, 之后整体加一 (跳过一个数). 走步条件不怕跳: `n` 在 `n+2` 的 1-走步上. 于是 `σ s` 与 `ω` 字面相等当且仅当 `s` 全假. 所以**规整性是逐棵的性质, 它不足以给出判决; 类必须是有向的**. 这把 InaccModulus 的 `Reg-ω`, `Reg-ω⁺` 这对例子变成了定理.

```agda
bump : (ℕ → Bool) → ℕ → ℕ
bump s zero    = 0
bump s (suc m) with s m
... | true  = 1
... | false = bump s m

σseq : (ℕ → Bool) → ℕ → Lv
σseq s m = natL (bump s m + m)

σ : (ℕ → Bool) → Lv
σ s = lim (σseq s)

ωL : Lv
ωL = lim natL

Reg-nat : ∀ n → Reg (natL n)
Reg-nat zero    = tt
Reg-nat (suc n) = Reg-nat n

W-nat-suc : ∀ n → W (natL n) (natL (suc n))
W-nat-suc n = ws0

bump≤ : ∀ s m → (bump s m ≡ 0) ⊎ (bump s m ≡ 1)
bump≤ s zero = inj₁ refl
bump≤ s (suc m) with s m
... | true  = inj₂ refl
... | false = bump≤ s m

bump-up : ∀ s m → bump s m ≡ 1 → bump s (suc m) ≡ 1
bump-up s m e with s m
... | true  = refl
... | false = e

n+s : ∀ a m → a + suc m ≡ suc (a + m)
n+s zero    m = refl
n+s (suc a) m = cong suc (n+s a m)

σ-step : ∀ s m → W (σseq s m) (σseq s (suc m))
σ-step s m with s m | bump≤ s m
... | true  | inj₁ e rewrite e = ws ws0
... | true  | inj₂ e rewrite e = ws0
... | false | inj₁ e rewrite e = ws0
... | false | inj₂ e rewrite e = subst (λ z → W (natL (suc m)) (natL z)) refl ws0

Reg-σ : ∀ s → Reg (σ s)
Reg-σ s = σ-step s , (λ m → Reg-nat (bump s m + m))

-- `σ s` 字面等于 ω 当且仅当 `s` 全假
bump-false : ∀ s → (∀ n → s n ≡ false) → ∀ m → bump s m ≡ 0
bump-false s a zero = refl
bump-false s a (suc m) with s m | a m
... | false | refl = bump-false s a m

natL-inj : ∀ a b → natL a ≡ natL b → a ≡ b
natL-inj zero    zero    e    = refl
natL-inj (suc a) (suc b) e with natL a | natL-inj a b (suc-inj′ e)
  where
    suc-inj′ : ∀ {x y : Lv} → Lv.suc x ≡ Lv.suc y → x ≡ y
    suc-inj′ refl = refl
... | _ | refl = refl

σ≡ω : Funext → ∀ s → (∀ n → s n ≡ false) → σ s ≡ ωL
σ≡ω fe s a = cong lim (fe (λ m → cong (λ z → natL (z + m)) (bump-false s a m)))

lim-inj′ : ∀ {f g : ℕ → Lv} → Lv.lim f ≡ Lv.lim g → ∀ n → f n ≡ g n
lim-inj′ refl n = refl

bump-true : ∀ s n → s n ≡ true → bump s (suc n) ≡ 1
bump-true s n t with s n | t
... | true | refl = refl

σ≡ω→false : ∀ s → σ s ≡ ωL → ∀ n → s n ≡ false
σ≡ω→false s e n = go (s n) refl
  where
    k : bump s (suc n) ≡ 0
    k = +-cancelʳ-≡ (suc n) (bump s (suc n)) 0 (natL-inj _ _ (lim-inj′ e (suc n)))
    go : ∀ b → s n ≡ b → b ≡ false
    go false _ = refl
    go true  q with () ← trans (sym (bump-true s n q)) k

at-nat : ∀ n (r : Pre (natL n)) → Σ ℕ λ m → at (natL n) r ≡ natL m
at-nat (suc n) (inj₁ _) = n , refl
at-nat (suc n) (inj₂ r) = at-nat n r

Nd-σ→false : ∀ s → Nd (σ s) (suc ωL) → ∀ n → s n ≡ false
Nd-σ→false s (inj₁ _ , e) = σ≡ω→false s (sym e)
Nd-σ→false s (inj₂ (m , r) , e) with at-nat m r
... | k , q = ⊥-elim (lim≠nat k (trans (sym e) q))
  where
    lim≠nat : ∀ k → σ s ≡ natL k → ⊥
    lim≠nat zero    ()
    lim≠nat (suc k) ()

-- **定理.** 判决若在全部规整树上满足 `Right`, 则 WLPO
allReg→WLPO : Funext → (D : Oracle) → (∀ j i → Reg j → Reg i → Right (D j i)) → WLPO
allReg→WLPO fe D ok s with right→dec (D (σ s) (suc ωL)) (ok _ _ (Reg-σ s) (Reg-nat-ω))
  where
    Reg-nat-ω : Reg (suc ωL)
    Reg-nat-ω = (λ n → ws0) , Reg-nat
... | yes n = inj₁ (Nd-σ→false s n)
... | no ¬n = inj₂ (λ a → ¬n (inj₁ tt , sym (σ≡ω fe s a)))
```

## §3 有向的规整族里没有禁忌

反过来, 在公共规整上界之内, `Dᵐ` 满足 `Right`, 是定理且不带前提 (除了 `Funext`). 所以 **"判决的正确性 ⟹ WLPO" 不可能在可数段的有向规整族上成立**: 不是没找到, 而是 `Dᵐ` 本身就是反例. §2 的否定用到的正是非有向: `σ s` 与 `ω` 没有公共规整上界 (若有, `tri` 就判定了 WLPO).

```agda
Reg-Nd : ∀ c {x} → Reg c → Nd x c → Reg x
Reg-Nd zero _ (() , _)
Reg-Nd (suc c) r (inj₁ _ , refl) = r
Reg-Nd (suc c) r (inj₂ s , e)    = Reg-Nd c r (s , e)
Reg-Nd (lim h) (_ , rg) ((n , s) , e) = Reg-Nd (h n) (rg n) (s , e)
Reg-Nd (limᴼ _ _) () _

module Dir (fe : Funext) where
  open OnFam famReg
  open CastR fe

  Dᵐ-right : ∀ c {j i} → Reg c → Nd j c → Nd i c → Right (Dᵐ j i)
  Dᵐ-right c {j} {i} rc nj ni with Reg-Nd c rc nj | Reg-Nd c rc ni | tri c rc nj ni
  ... | rj | ri | inj₁ refl =
    subst Right (sym (Dᵐ-eq j rj)) (irr j rj)
  ... | rj | ri | inj₂ (inj₁ n) with Dᵐ j i | Dᵐ-lt {j} {i} rj ri n
  ...   | V | record { rr = r ; bb = b ; vq = refl ; lb = l ; sb = _ } = l
  Dᵐ-right c {j} {i} rc nj ni | rj | ri | inj₂ (inj₂ n) =
    subst Right (sym (Dᵐ-gt {j} {i} rj ri n)) (λ m → irr j rj (Nd-trans n m))

  -- 推论: 有向规整族内 `Nd` 可判定
  dir-dec : ∀ c {j i} → Reg c → Nd j c → Nd i c → Dec (Nd j i)
  dir-dec c rc nj ni = right→dec _ (Dᵐ-right c rc nj ni)
```
