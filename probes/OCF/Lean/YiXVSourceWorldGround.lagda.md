# YiXVSourceWorldGround
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldGround where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (fold₀≼; folds₀≼)
open import OCF.Lean.YiXVAffine using (pw-add)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; 1≼ψ⁰)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVZeroRead as Z

module World (H : ℕ) (X : I.T H) (gx : A.Gd H X) (σ : L.Simᴵ L.zero (L.natᴵ H)) (SrcB : Fold.Base S.zero)
  (b : read (Fold.b⊥ SrcB) ≼ L.ψ⁰ X) (s : read (Fold.bs SrcB S.zero P.self) ≼ L.ψ⁰ X) where
  β = Fold.bs SrcB S.zero P.self
  nβ = Fold.ns SrcB S.zero P.self
  Both : S.Tr S.zero → I.T 0 → Set
  Both x Y =
    (read (Fold.ψ⊥ S.zero tt tt SrcB x) ≼ L.ψ⁰ (L.add X σ Y)) ×
    (read (Fold.ψs S.zero tt tt SrcB S.zero P.self β nβ x) ≼ L.ψ⁰ (L.add X σ Y))
  upper : ∀ {x Y} → U.U 0 x Y → Both x Y
  upper {x} {Y} h =
    ≼-trans (fold₀≼ SrcB b x) (≼-trans (pw-add σ X (read x)) tail) ,
    ≼-trans (folds₀≼ SrcB β nβ s x) (≼-trans (pw-add σ X (read x)) tail)
    where
    tail = Z.mono H (Add.mono H 0 {X = X} {X′ = X} (B.rfl H F.zero {X = X} gx) σ (read x) Y h)

module Model = World 1 (L.Ω (L.natᴵ 1)) A.actual₁ (λ q → L.suc q) (Fold.B₀ S.zero)
  (1≼ψ⁰ (L.Ω (L.natᴵ 1))) (1≼ψ⁰ (L.Ω (L.natᴵ 1)))
actual : Model.Both (S.suc S.zero) (L.suc L.zero)
actual = Model.upper (≼-refl (L.suc L.zero))
```
