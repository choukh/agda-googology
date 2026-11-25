# YiXVSourceAffineGround
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineGround where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼l)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as Fold
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceNext as Next

module Frame (n H : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ (suc n) L.<ᴵ ambient) (ρ : L.Simᴵ (L.natᴵ H) ambient) where
  φ : I.T H → I.T (suc n)
  φ = L.ψ pc ρ
  good : ∀ {X} → A.Gd H X → A.Gd (suc n) (φ X)
  good {X} gx = Q.Ops.good (Fold.ops H) (suc n) pc ρ X gx
  mono : ∀ {X Y} → A.Le H X Y → A.Le (suc n) (φ X) (φ Y)
  mono {X} {Y} t = Q.Ops.mono (Fold.ops H) (suc n) pc pc ρ ρ X Y t
  exact : ∀ {x X} (d : O.Dn (J.nat (suc n)) S.zero) (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
    A.Gd H X → U.U (suc n) x (φ X) → (σ : L.Simᴵ L.zero (L.natᴵ H)) (z : J.Tr zero) →
    U.U (suc n) (O.Up S.zero d x nx z) (φ (L.add X σ (read z)))
  exact d nx gx hx σ S.zero = hx
  exact {X = X} d nx gx hx σ (S.suc z) = Next.next (suc n) (O.Up-nz S.zero d _ nx z)
    (good (Add.good H 0 {X = X} gx σ (read z) tt)) (exact d nx gx hx σ z)
  exact {X = X} d nx gx hx σ (S.lim f a) = UB.limU (suc n) (λ k → UB.weakU (suc n) (exact d nx gx hx σ (f k))
    (mono (Add.mono H 0 {X = X} {X′ = X} (B.rfl H F.zero {X = X} gx) σ (read (f k)) (read (S.lim f a)) (≼l k (≼-refl (read (f k)))))))
  exact d nx gx hx σ (S.Ω () f)
  exact d nx gx hx σ (S.up x () z e)
  bound : ∀ {x X z Y} (d : O.Dn (J.nat (suc n)) S.zero) (nx : J.nat (suc n) S.⊢ S.zero ◃ x) →
    A.Gd H X → U.U (suc n) x (φ X) → (σ : L.Simᴵ L.zero (L.natᴵ H)) → U.U 0 z Y →
    U.U (suc n) (O.Up S.zero d x nx z) (φ (L.add X σ Y))
  bound {X = X} {z} {Y} d nx gx hx σ h = UB.weakU (suc n) (exact d nx gx hx σ z)
    (mono (Add.mono H 0 {X = X} {X′ = X} (B.rfl H F.zero {X = X} gx) σ (read z) Y h))

module Model = Frame 1 3 L.zero (λ q → q)
actual : U.U 2 (O.Up S.zero (O.down (O.down O.stop tt) tt) (O.Ωt (J.nat 2)) (O.Ωt-nz (J.nat 2)) (O.Ωt S.zero))
  (L.ψ L.zero (λ q → q) (L.add (L.Ω (L.natᴵ 3)) (λ q → L.suc (L.suc (L.suc q))) (L.suc L.zero)))
actual = Model.bound (O.down (O.down O.stop tt) tt) (O.Ωt-nz (J.nat 2)) A.actual₃
  (UB.weakU 2 (UB.ΩU 2) (Omega.two 2 3 L.zero (λ q → q))) (λ q → L.suc (L.suc (L.suc q))) (≼-refl (L.suc L.zero))
```
