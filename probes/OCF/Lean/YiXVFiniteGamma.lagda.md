# YiXVFiniteGamma
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteGamma where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (γ; Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as Fold
import OCF.Lean.YiXVFiniteFoldOmega as O

module At (k : ℕ) where
  Γ : ℕ → I.T k
  Γ = γ k
  ψ-good : ∀ {X} → A.Gd k X → A.Gd k (Ψ k X)
  ψ-good {X} gx = Q.Ops.good (Fold.ops k) k L.zero (λ q → L.suc q) X gx
  ψ-mono : ∀ {X Y} → A.Le k X Y → A.Le k (Ψ k X) (Ψ k Y)
  ψ-mono {X} {Y} t = Q.Ops.mono (Fold.ops k) k L.zero L.zero (λ q → L.suc q) (λ q → L.suc q) X Y t
  good : ∀ n → A.Gd k (Γ n)
  good zero = proj₁ (B.Ω-model k F.zero)
  good (suc n) = ψ-good (good n)
  inv-Ω : A.Le k (L.suc (O.Ω k)) (Ψ k (O.Ω k))
  inv-Ω = B.trans k F.zero {X = L.suc (O.Ω k)} {Y = O.Ω k L.+ O.Ω k} {Z = Ψ k (O.Ω k)}
    (Add.plus k {X = O.Ω k} {X′ = O.Ω k} {Y = L.suc L.zero} {Y′ = O.Ω k}
      (B.rfl k F.zero {X = O.Ω k} (good 0)) (proj₂ (B.Ω-model k F.zero)))
    (O.two k k L.zero (λ q → L.suc q))
  inv : ∀ n → A.Le k (L.suc (Γ n)) (Γ (suc n))
  inv zero = inv-Ω
  inv (suc n) = B.trans k F.zero {X = L.suc (Γ (suc n))} {Y = Ψ k (L.suc (Γ n))} {Z = Γ (suc (suc n))}
    (It.strict k L.zero (λ q → L.suc q) (Γ n) (good (suc n))) (ψ-mono (inv n))
  next : ∀ n → A.Le k (Γ n) (Γ (suc n))
  next n = B.trans k F.zero {X = Γ n} {Y = L.suc (Γ n)} {Z = Γ (suc n)}
    (B.w≤ k F.zero {X = Γ n} {Y = Γ n} (B.rfl k F.zero {X = Γ n} (good n))) (inv n)
  step : ∀ {X} n → A.Le k X (Γ n) → A.Le k (X L.+ Ψ k X) (Γ (suc (suc n)))
  step {X} n t = B.trans k F.zero {X = X L.+ Ψ k X} {Y = Ψ k (L.suc (Γ n))} {Z = Γ (suc (suc n))}
    (B.lr k F.zero {X = X L.+ Ψ k X} {a = _}
      (Add.plus-good k {X = X} {Y = Ψ k X} (B.left k F.zero {X = X} {Y = Γ n} t)
        (ψ-good (B.left k F.zero {X = X} {Y = Γ n} t)))
      (It.good k (Γ (suc n)) (good (suc n))) 2
      (Add.plus k {X = X} {X′ = Γ (suc n)} {Y = Ψ k X} {Y′ = Γ (suc n)}
        (B.trans k F.zero {X = X} {Y = Γ n} {Z = Γ (suc n)} t (next n)) (ψ-mono t))) (ψ-mono (inv n))

actual : ∀ k → A.Le k (O.Ω k L.+ Ψ k (O.Ω k)) (γ k 2)
actual k = At.step k 0 (B.rfl k F.zero {X = O.Ω k} (At.good k 0))
```
