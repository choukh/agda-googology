# YiXVSourceGroundLift
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceGroundLift where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼l)
open import OCF.Align.YiLvValBase using (Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceNext as Next

exact : ∀ n {x X} (d : O.Dn (J.nat n) S.zero) (nx : J.nat n S.⊢ S.zero ◃ x) →
  A.Gd n X → U.U n x (Ψ n X) → (σ : L.Simᴵ L.zero (L.natᴵ n)) (z : J.Tr zero) →
  U.U n (O.Up S.zero d x nx z) (Ψ n (L.add X σ (read z)))
exact n d nx gx hx σ S.zero = hx
exact n {X = X} d nx gx hx σ (S.suc z) = Next.next n (O.Up-nz S.zero d _ nx z)
  (Gamma.At.ψ-good n (Add.good n 0 {X = X} gx σ (read z) tt)) (exact n d nx gx hx σ z)
exact n {X = X} d nx gx hx σ (S.lim f a) = UB.limU n (λ k → UB.weakU n (exact n d nx gx hx σ (f k))
  (Gamma.At.ψ-mono n (Add.mono n 0 {X = X} {X′ = X} (B.rfl n F.zero {X = X} gx) σ (read (f k)) (read (S.lim f a))
    (≼l k (≼-refl (read (f k)))))))
exact n d nx gx hx σ (S.Ω () f)
exact n d nx gx hx σ (S.up x () z e)

bound : ∀ n {x X z Y} (d : O.Dn (J.nat n) S.zero) (nx : J.nat n S.⊢ S.zero ◃ x) →
  A.Gd n X → U.U n x (Ψ n X) → (σ : L.Simᴵ L.zero (L.natᴵ n)) → U.U 0 z Y →
  U.U n (O.Up S.zero d x nx z) (Ψ n (L.add X σ Y))
bound n {X = X} {z} {Y} d nx gx hx σ h = UB.weakU n (exact n d nx gx hx σ z)
  (Gamma.At.ψ-mono n (Add.mono n 0 {X = X} {X′ = X} (B.rfl n F.zero {X = X} gx) σ (read z) Y h))

actual : U.U 1 (O.Up S.zero (O.down O.stop tt) (O.Ωt (J.nat 1)) (O.Ωt-nz (J.nat 1)) (O.Ωt S.zero))
  (Ψ 1 (L.add (L.Ω (L.natᴵ 1)) (λ q → L.suc q) (L.suc L.zero)))
actual = bound 1 (O.down O.stop tt) (O.Ωt-nz (J.nat 1)) A.actual₁
  (UB.weakU 1 (UB.ΩU 1) (Omega.two 1 1 L.zero (λ q → L.suc q))) (λ q → L.suc q) (≼-refl (L.suc L.zero))
```
