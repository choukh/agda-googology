# 修正步进到原 LowKeep 的显式条件版
验收文件；`steps′→lowKeep⁺` 比原目标多出具名 `RootSupply`，该假设的域逐字保留原 `LowAt` 的参数。
`supported-low` 只消费指定上下文中的 `Support`；没有把供给塞进原 `Bdᵍ`。
`RootSupply (fn 1)` 被编译否定，故条件版不作强度成果；最小实际折叠另有不使用 `Leaf` 的实例。
入口：`RootSupply`、`supported-low`、`steps′→lowKeep⁺`、`no-root-one`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUReduce where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; Bdᵍ; Wlᵍ; wz)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiLKIface using (LowAt)
open import OCF.Lean.YiLKSlot using (start-from-leaf)
open import OCF.Lean.YiSUIface using (StepU′)
open import OCF.Lean.YiSUSupport
open import OCF.Lean.YiSUFold
open import OCF.Lean.YiSUBridge using (no-prefix-one; bd)
open import OCF.Lean.YiSUNeg using (ℓ; o; t)
open import OCF.Lean.YiGICheck using (leaf-fin)
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

RootSupply : L → Set
RootSupply ℓ = ∀ {j} (b : Bsᵍ ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (t : E.T)
  → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ → Wlᵍ w → Bdᵍ b w β t
  → ∀ {a x} → x ≡ proj₁ (Ωt ℓ) → GR.R ℓ a x
  → Support ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) t

supported-low : ∀ ℓ → Rows ℓ → RootSupply ℓ → LowAt ℓ
supported-low ℓ rows supply b@(o , r , B) .(z≤ ℓ) β t rb wz bd gx m =
  fold ℓ rows o r B (proj₂ bd) t (supply b (z≤ ℓ) β t rb wz bd gx m) β (proj₁ bd) m

rows-from-leaf : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU′ ℓ) → ∀ ℓ → Rows ℓ
rows-from-leaf lf st zero = tt
rows-from-leaf lf st (nd s h) =
  (start-from-leaf lf (nd s h) , st (nd s h)) , λ c → rows-from-leaf lf st (h c)

steps′→lowKeep⁺ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU′ ℓ)
  → (∀ ℓ → RootSupply ℓ) → Laws.LowKeep gradedᵍ domsᵍ
steps′→lowKeep⁺ lf st supply {ℓ} = supported-low ℓ (rows-from-leaf lf st ℓ) (supply ℓ)

no-root-one : RootSupply ℓ → ⊥
no-root-one supply = no-prefix-one (proj₁
  (supply (o , MT.rbᶻ ℓ , B₀ ℓ) (z≤ ℓ) (next⁺ (Ωt zero)) t refl wz bd refl (leaf-fin 1)))
```
