# 连同出口证据返回的低层保持
> 验收文件（读记号），条件定理：`Leaf`、`Lift`、`LowKeepᴱ` 推出主线终点的 EBO 序数值下界。
> `LowKeepᴱ` 将零层出口证据与推导放在同一结论；三条全域律仍未实填，不声称无条件达到 EBO。
> 来源：`YiGIEnd.Assembly`；零层的基础关系片段调用 `YiTBFam.Qu`、`YiHCCheck.of⁰/ex-of⁰`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXEnd where
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; Bdᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open Laws gradedᵍ domsᵍ using (Leaf; Lift; LowKeep; Gb; Wl; Gx)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

Exᵍ : ∀ j {s x} → GR.R j s x → Set
Exᵍ B.zero m = H.Exᴴ m
Exᵍ (B.nd s h) m = ⊤

LowKeepᴱ : Set
LowKeepᴱ = ∀ {ℓ j} (b : Bsᵍ ℓ) (w : j P.≤ ℓ) (β : O.Tr⁺ j) (t₀ : E.T)
  → Gb ℓ b → Wl w → Bdᵍ b w β t₀
  → ∀ {a x} → Gx ℓ x → GR.R ℓ a x
  → Σ (GR.R j (E.ψ [] (t₀ ++ a) ∷ []) (proj₁ (ψᵍ ℓ b j w β x))) (Exᵍ j)

forgetᴱ : LowKeepᴱ → LowKeep
forgetᴱ f b w β t₀ gb wl bd gx m = proj₁ (f b w β t₀ gb wl bd gx m)

module End (lf : Leaf) (li : Lift) (f : LowKeepᴱ) where
  module A = GE.Assembly lf li (forgetᴱ f)

  exits : A.ExitCondition
  exits n = proj₂ (f (Keel⁻.b₀ keelᴱ n) (Keel⁻.w₀ keelᴱ n)
    (Keel⁻.β₀ keelᴱ n) (Keel⁻.K₀ keelᴱ n) (Keel⁻.gb keelᴱ n)
    (Keel⁻.wl keelᴱ n) (Keel⁻.bd keelᴱ n) (Keel⁻.gx keelᴱ n) (A.T.keelᴿ n))

  eboᴱ : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  eboᴱ = GE.eboᵍ lf li (forgetᴱ f) exits

eboᴱ : Leaf → Lift → LowKeepᴱ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
eboᴱ = End.eboᴱ

low-zeroᴱ : (b : Bsᵍ B.zero) (β : O.Tr⁺ B.zero) (t₀ : E.T)
  → K.M⁰ (E.ψ [] t₀ ∷ []) (proj₁ β)
  → ∀ {a x} → K.M⁰ a x
  → Σ (GR.R B.zero (E.ψ [] (t₀ ++ a) ∷ [])
      (proj₁ (ψᵍ B.zero b B.zero P.self β x))) H.Exᴴ
low-zeroᴱ (o , r , b) β t₀ mb m = HC.of⁰ q , HC.ex-of⁰ q
  where
  q = TF.Qu {t = t₀} o r b P.self β mb m

startᴱ : Σ (GR.R B.zero (E.EBOψ 0)
  (proj₁ (ψᵍ B.zero (tt , tt , F.B₀ B.zero)
    B.zero P.self (O.Ωt B.zero) (proj₁ (O.Ωt B.zero))))) H.Exᴴ
startᴱ = low-zeroᴱ (tt , tt , F.B₀ B.zero) (O.Ωt B.zero) []
  (K.m1 {t = E.natT 1} refl K.mz) (K.m1 {t = E.natT 1} refl K.mz)
```
