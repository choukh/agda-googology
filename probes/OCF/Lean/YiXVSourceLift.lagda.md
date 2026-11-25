# YiXVSourceLift
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceLift where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCanonicalInputs as C
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceGroundLift as Ground
import OCF.Lean.YiXVSourceNodeLift as Node
import OCF.Lean.YiXVSourceNext as Next

module Stage (n k : ℕ)
  (low : ∀ (p : P.Path (suc n) k) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
    A.Gd (suc n) X → U.U (suc n) x (Ψ (suc n) X) → A.Gd k Y → U.U k y Y →
    U.U (suc n) (O.Up (J.nat k) (P.src p) x nx y) (Ψ (suc n) (L.add X (P.σ p) Y))) where

  lift : ∀ (p : P.Path (suc n) (suc k)) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
    A.Gd (suc n) X → U.U (suc n) x (Ψ (suc n) X) → A.Gd (suc k) Y → U.U (suc k) y Y →
    U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx y) (Ψ (suc n) (L.add X (P.σ p) Y))
  lift p {X = X} nx gx hx gy U.Layer.uz = UB.weakU (suc n) hx
    (Gamma.At.ψ-mono (suc n) (Right.right (suc n) (suc k) (B.rfl (suc n) F.zero {X = X} gx) (P.σ p)
      (L.Ω (L.natᴵ (suc k))) (proj₁ (B.Ω-model (suc k) F.zero))))
  lift p {X = X} nx gx hx (A.Layer.gs {X = Y} gy) (U.Layer.us {x = y} hy) =
    Next.next (suc n) (O.Up-nz (J.nat (suc k)) (P.src p) _ nx y)
      (Gamma.At.ψ-good (suc n) (Add.good (suc n) (suc k) {X = X} gx (P.σ p) Y gy)) (lift p nx gx hx gy hy)
  lift p {X = X} nx gx hx gy (U.Layer.uw {X = Y} {Y = Y′} hy t@(A.Layer.pack gy₀ gy′ _)) = UB.weakU (suc n)
    (lift p nx gx hx gy₀ hy)
    (Gamma.At.ψ-mono (suc n) (Add.mono (suc n) (suc k) {X = X} {X′ = X} (B.rfl (suc n) F.zero {X = X} gx) (P.σ p) Y Y′ t))
  lift p nx gx hx gy (U.Layer.ul h) = UB.limU (suc n) (λ j → lift p nx gx hx gy (h j))
  lift p {x} {X} nx gx hx (A.Layer.gn law gb) (U.Layer.un i {g} {f} h) =
    Node.Node.Run.result p i x nx X g f IH
    where
    module D = A.Layer k (A.GoFam k) (A.LeFam k)
    IH : ∀ a V Y → A.Gd (I.rank k i) V → A.Gd (I.rank k i) Y →
      A.Le (I.rank k i) (L.Ω (L.natᴵ (I.rank k i))) Y → U.UR k i a V → A.Le (I.rank k i) (L.suc V) Y →
      U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx (g (J.inB k i a)))
        (Ψ (suc n) (L.add X (P.σ p) (f (L.into (L.<→◃ (J.q k i)) Y))))
    IH a V Y gv gy o ha t = lift p nx gx hx
      (gb (L.into (L.<→◃ (J.q k i)) Y) (C.At.good-in k (I.rank k i) (J.q k i) Y gy) (C.At.floor-in k (I.rank k i) (J.q k i) Y o))
      (h a V Y gv gy o ha t)
  lift p {X = X} nx gx hx gy (U.Layer.uu {x = y} {y = z} {X = Y} {Y = Z} gy₀ hy gz hz) =
    UB.weakU (suc n)
      (low (P.down p) (O.Up-nz (J.nat (suc k)) (P.src p) _ nx y)
        (Add.good (suc n) (suc k) {X = X} gx (P.σ p) Y gy₀)
        (lift p nx gx hx gy₀ hy) gz hz)
      (Gamma.At.ψ-mono (suc n) (Compose.compose (suc n) (suc k) k X (P.σ p) Y (λ q → L.suc q) Z gx gy₀ gz))

lift : ∀ n k (p : P.Path (suc n) k) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
  A.Gd (suc n) X → U.U (suc n) x (Ψ (suc n) X) → A.Gd k Y → U.U k y Y →
  U.U (suc n) (O.Up (J.nat k) (P.src p) x nx y) (Ψ (suc n) (L.add X (P.σ p) Y))
lift n zero p nx gx hx gy hy = Ground.bound (suc n) (P.src p) nx gx hx (P.σ p) hy
lift n (suc k) p nx gx hx gy hy = M.lift p nx gx hx gy hy
  where module M = Stage n k (lift n k)

actual : ∀ n → U.U (suc n)
  (O.Upc (J.nat (suc n)) _ (O.Ωt (J.nat (suc n))) (O.Ωt-nz (J.nat (suc n))) (O.Ωt (J.nat n)))
  (Ψ (suc n) (L.add (L.Ω (L.natᴵ (suc n))) (λ q → L.suc q) (L.Ω (L.natᴵ n) L.+ L.Ω (L.natᴵ n))))
actual n = lift n n (P.down P.top) (O.Ωt-nz (J.nat (suc n))) (proj₁ (B.Ω-model (suc n) F.zero))
  (UB.weakU (suc n) (UB.ΩU (suc n)) (Omega.two (suc n) (suc n) L.zero (λ q → L.suc q)))
  (Add.plus-good n {X = L.Ω (L.natᴵ n)} {Y = L.Ω (L.natᴵ n)} (proj₁ (B.Ω-model n F.zero)) (proj₁ (B.Ω-model n F.zero))) (UB.ΩU n)
```
