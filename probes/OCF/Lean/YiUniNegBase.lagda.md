# YiUni 否定的部件：由 α 定的极限层号 `Tα α` 里有没有层号 1 的槽位

**非验收文件。判决：编译定理，无前提。** 第 0 层的合法树 `lim (fα α)`：各项是 1，遇到 `α` 的真值后是 2。读回 `Tα α` 有层号 1 的槽位当且仅当 `α` 有真值 (`found→at`, `keep→found`)；
所以一个以 `Tα α` 为目标、以 1 为结点层号的派发若在能保留处保留，就判定了 `α` (`decide`)。只是部件；否定在 [YiUniNegCmp](YiUniNegCmp.lagda.md)、[YiUniNegStep](YiUniNegStep.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniNegBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; ⌜_⌝; lev; Way; keep; fold)
open import OCF.Lean.YiUniIf using (At; IsKeep)
```

## 1 LPO 与探针树

`hit α n`：`α` 在 `n` 之前有真值。`hit α 0` 定义性地是 `false`，所以 `fα α 0` 定义性地是 1 (第 [YiUniNegStep](YiUniNegStep.lagda.md) 篇要用)。

```agda
Found : (ℕ → Bool) → Set
Found α = Σ ℕ λ n → α n ≡ true

LPO : Set
LPO = ∀ α → Found α ⊎ (Found α → ⊥)

hit : (ℕ → Bool) → ℕ → Bool
hit α zero = false
hit α (suc n) = α n ∨ hit α n

one two : R
one = G.suc G.zero
two = G.suc one

pick : Bool → R
pick true = two
pick false = one

fα : (ℕ → Bool) → ℕ → R
fα α n = pick (hit α n)

pick-step : ∀ a b → Cp zero (pick b) (pick (a ∨ b))
pick-step true true = inj₁ refl
pick-step true false = inj₂ (inj₁ refl)
pick-step false b = inj₁ refl

pick-lgl : ∀ b → Lgl zero (pick b)
pick-lgl true = tt
pick-lgl false = tt

lim-lgl : ∀ α → Lgl zero (G.lim (fα α))
lim-lgl α = (λ n → pick-step (α n) (hit α n)) , (λ n → pick-lgl (hit α n))

Tα : (ℕ → Bool) → LF
Tα α = ⌜ G.lim (fα α) ⌝
```

## 2 层号 1 的槽位

```agda
or-l : ∀ a b → a ≡ true → (a ∨ b) ≡ true
or-l true b refl = refl

hit-found : ∀ α n → hit α n ≡ true → Found α
hit-found α zero ()
hit-found α (suc n) e with α n in q
... | true = n , q
... | false = hit-found α n e

pick-at : ∀ b → b ≡ true → Σ (Pre ⌜ pick b ⌝) λ s → lev ⌜ pick b ⌝ s ≡ suc zero
pick-at true refl = inj₁ tt , refl

at-pick : ∀ b (s : Pre ⌜ pick b ⌝) → lev ⌜ pick b ⌝ s ≡ suc zero → b ≡ true
at-pick true s e = refl
at-pick false (inj₁ tt) ()
at-pick false (inj₂ ()) e

found→at : ∀ α → Found α → At (Tα α) (suc zero)
found→at α (n , e) with pick-at (hit α (suc n)) (or-l (α n) (hit α n) e)
... | s , p = (suc n , s) , p

keep→found : ∀ α (s : Pre (Tα α)) → lev (Tα α) s ≡ suc zero → Found α
keep→found α (n , s) e = hit-found α n (at-pick (hit α n) s e)

decide : ∀ α (w : Way (Tα α) (suc zero)) → (Found α → IsKeep w) → Found α ⊎ (Found α → ⊥)
decide α (keep s e) c = inj₁ (keep→found α s e)
decide α fold c = inj₂ c
```
