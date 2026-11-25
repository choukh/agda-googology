# YiXVSourceAffineLift
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineLift where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCanonicalInputs as In
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceNext as Next
import OCF.Lean.YiXVSourceAffineGround as Ground
import OCF.Lean.YiXVSourceAffineNode as Node

module Frame (n H : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ (suc n) L.<ᴵ ambient)
  (ρ : L.Simᴵ (L.natᴵ H) ambient) (ε : L.Simᴵ (L.natᴵ (suc n)) (L.natᴵ H)) where
  module C = Ground.Frame n H pc ρ
  σ : ∀ {k} → P.Path (suc n) k → L.Simᴵ (L.natᴵ k) (L.natᴵ H)
  σ p q = ε (P.σ p q)
  module Stage (k : ℕ)
    (low : ∀ (p : P.Path (suc n) k) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
      A.Gd H X → U.U (suc n) x (C.φ X) → A.Gd k Y → U.U k y Y →
      U.U (suc n) (O.Up (J.nat k) (P.src p) x nx y) (C.φ (L.add X (σ p) Y))) where
    module D = U.Layer k (U.UR k)
    module R = A.Layer k (A.GoFam k) (A.LeFam k)
    lift : ∀ (p : P.Path (suc n) (suc k)) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
      A.Gd H X → U.U (suc n) x (C.φ X) → R.Gd Y → D.U y Y →
      U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx y) (C.φ (L.add X (σ p) Y))
    lift p {X = X} nx gx hx gy D.uz = UB.weakU (suc n) hx
      (C.mono (Right.right H (suc k) (B.rfl H F.zero {X = X} gx) (σ p)
        (L.Ω (L.natᴵ (suc k))) (proj₁ (B.Ω-model (suc k) F.zero))))
    lift p {X = X} nx gx hx (R.gs {X = Y} gy) (D.us {x = y} hy) =
      Next.next (suc n) (O.Up-nz (J.nat (suc k)) (P.src p) _ nx y)
        (C.good (Add.good H (suc k) {X = X} gx (σ p) Y gy)) (lift p nx gx hx gy hy)
    lift p {X = X} nx gx hx gy (D.uw {X = Y} {Y = Y′} hy t) = UB.weakU (suc n)
      (lift p nx gx hx (R.left t) hy)
      (C.mono (Add.mono H (suc k) {X = X} {X′ = X} (B.rfl H F.zero {X = X} gx) (σ p) Y Y′ t))
    lift p nx gx hx gy (D.ul h) = UB.limU (suc n) (λ j → lift p nx gx hx gy (h j))
    lift p {x} {X} nx gx hx (R.gn law gb) (D.un i {g} {f} h) = Node.Node.Run.result H pc ρ ε p i x nx X g f IH
      where
      IH : ∀ a V Y → A.Gd (I.rank k i) V → A.Gd (I.rank k i) Y →
        A.Le (I.rank k i) (L.Ω (L.natᴵ (I.rank k i))) Y → U.UR k i a V → A.Le (I.rank k i) (L.suc V) Y →
        U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx (g (J.inB k i a)))
          (C.φ (L.add X (σ p) (f (L.into (L.<→◃ (J.q k i)) Y))))
      IH a V Y gv gy o ha t = lift p nx gx hx
        (gb (L.into (L.<→◃ (J.q k i)) Y) (In.At.good-in k (I.rank k i) (J.q k i) Y gy) (In.At.floor-in k (I.rank k i) (J.q k i) Y o))
        (h a V Y gv gy o ha t)
    lift p {X = X} nx gx hx gy (D.uu {x = y} {y = z} {X = Y} {Y = Z} gy₀ hy gZ hz) = UB.weakU (suc n)
      (low (P.down p) (O.Up-nz (J.nat (suc k)) (P.src p) _ nx y)
        (Add.good H (suc k) {X = X} gx (σ p) Y gy₀) (lift p nx gx hx gy₀ hy) gZ hz)
      (C.mono (Compose.compose H (suc k) k X (σ p) Y (λ q → L.suc q) Z gx gy₀ gZ))

  lift : ∀ k (p : P.Path (suc n) k) {x X y Y} (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
    A.Gd H X → U.U (suc n) x (C.φ X) → A.Gd k Y → U.U k y Y →
    U.U (suc n) (O.Up (J.nat k) (P.src p) x nx y) (C.φ (L.add X (σ p) Y))
  lift zero p nx gx hx gy hy = C.bound (P.src p) nx gx hx (σ p) hy
  lift (suc k) p nx gx hx gy hy = M.lift p nx gx hx gy hy
    where module M = Stage k (lift k)

module Actual (n : ℕ) = Frame n (suc (suc n)) L.zero (λ q → q) (λ q → L.suc q)
actual : ∀ n → U.U (suc n)
  (O.Upc (J.nat (suc n)) _ (O.Ωt (J.nat (suc n))) (O.Ωt-nz (J.nat (suc n))) (O.Ωt (J.nat n)))
  (L.ψ L.zero (λ q → q) (L.add (L.Ω (L.natᴵ (suc (suc n)))) (λ q → L.suc (L.suc q))
    (L.Ω (L.natᴵ n) L.+ L.Ω (L.natᴵ n))))
actual n = Actual.lift n n (P.down P.top) (O.Ωt-nz (J.nat (suc n))) (proj₁ (B.Ω-model (suc (suc n)) F.zero))
  (UB.weakU (suc n) (UB.ΩU (suc n)) (Omega.two (suc n) (suc (suc n)) L.zero (λ q → q)))
  (Add.plus-good n {X = L.Ω (L.natᴵ n)} {Y = L.Ω (L.natᴵ n)} (proj₁ (B.Ω-model n F.zero)) (proj₁ (B.Ω-model n F.zero))) (UB.ΩU n)
```
