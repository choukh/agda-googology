# YiUni：接口的两条单调由合法性的保持逼出

**非验收文件。判决：编译定理，无前提。** 在接口 [YiUniIf](YiUniIf.lagda.md) 里只用 `Ψ-lgl` 与 `top-rowᶜ`：`top` 在 Ω 结点层号上折叠时，相邻链点的观察是第一位置 (`chain-up`，即 `top-up` 在链点上的实例)；
保留在槽位 `s` 时，分支族是 `Br` (`keep-br`，即 `Kb-br` 在这个派发上的实例)。所以这两条律不是为翻译加的，删掉它们也被 `Ψ-lgl` 要求。不否定律可以写得更弱。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniForced where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Br; ΩT; nodeAt; self)
open import OCF.Lean.YiNextFold using (p₀)
open import OCF.Lean.YiNextTop using (V₂)
open import OCF.Lean.YiUniIf using (Uni)
open import OCF.Lean.YiUniTw2 using (Tw2)
```

## 1 `nodeAt` 的合法性反推分支

与 `YiNextBase.nodeAt-lgl` 反向。

```agda
LgB⁻ : ∀ {M k} → Bld M k → Set
LgB⁻ {M} {k} B = ∀ r g → Lgl M (B r g) → Br (Lo k r) M g

nodeAt-br : ∀ {M} m p (B : Bld M m) → LgB⁻ B → ∀ g → Lgl M (nodeAt m p B g) → Br (layer (lev m p)) M g
nodeAt-br (suc k) (inj₁ _) B b = b (inj₁ tt)
nodeAt-br (suc k) (inj₂ p) B b = nodeAt-br k p _ (λ r → b (inj₂ r))
nodeAt-br (lim f) (n , p) B b = nodeAt-br (f n) p _ (λ r → b (n , r))
nodeAt-br (lc j g) (η , l , p) B b = nodeAt-br (g η) p _ (λ r → b (η , l , r))
```

## 2 两条

```agda
module _ (U : Uni) where
  open Uni U

  top-lgl : ∀ m {k g} (V : Bd (lc k g)) x → Lgl m (ΩT m k (ωw m V x) (Kb m V x)
    (λ n → Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top))
  top-lgl m V x = subst (Lgl m) (top-rowᶜ m V x) (Ψ-lgl m V x G.top tt)

  chain-up : ∀ m {k g} (V : Bd (lc k g)) x → ωw m V x ≡ fold → ∀ n →
    Cp m (Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top)
         (Ψ m (bC V (cpt V (suc n)) (cpt-lgl V (suc n))) (obd m V x (cpt V (suc n)) (cpt-lgl V (suc n))) G.top)
  chain-up m {k} V x w n =
    proj₁ (subst (λ w′ → Lgl m (ΩT m k w′ (Kb m V x) _)) w (top-lgl m V x)) n

  keep-br : ∀ m {k g} (V : Bd (lc k g)) x (s : Pre m) (e : lev m s ≡ k) → ωw m V x ≡ keep s e →
    Br (layer k) m (Kb m V x)
  keep-br m V x s refl w =
    nodeAt-br m s G.lc (λ r g l → l) (Kb m V x)
      (subst (λ w′ → Lgl m (ΩT m (lev m s) w′ (Kb m V x) _)) w (top-lgl m V x))
```

## 3 前提的实例

`tw 2` 实例上：折到第 0 层时 `top` 折叠，折到 `tw 2` 自己 (派发 `self`) 时保留在 `p₀`；两条都实际用到。

```agda
chain-up₂ : ∀ n → _
chain-up₂ = chain-up Tw2 zero V₂ (λ _ → fold) refl

keep-br₂ : Br (layer zero) (tw 2) (Uni.Kb Tw2 (tw 2) V₂ (self (tw 2)))
keep-br₂ = keep-br Tw2 (tw 2) V₂ (self (tw 2)) p₀ refl refl
```
