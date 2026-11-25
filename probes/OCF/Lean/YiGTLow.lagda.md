# 补前缀条件下的实际 LowKeep 形状
验收文件（读记号）；沿原 Wl 的标准零路径，IndexTree 给一般保持，额外显式携带 PrefixU。
LowAt′ 比原 LowAt 多这个前提；原 Bdᵍ 不供给它，不把结论标成原 LowKeep。
不调用 Leaf，也不组装 EBO 条件终点；零层和最小层的实例见 YiGTInst。
入口：`low-at′`、`low-when-prefix`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTLow where
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGIInst using (Bdᵍ; Wlᵍ; wz)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiGTIndex using (index-zero)
open import OCF.Lean.YiGTDirect using (IndexTree; direct; LayerIndex; layer-at)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E

LowAt′ : L → Set
LowAt′ ℓ = ∀ {j} (b : Bsᵍ ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (t : E.T)
  → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ → Wlᵍ w → Bdᵍ b w β t
  → PrefixU (proj₂ (proj₂ b)) t
  → ∀ {a x} → x ≡ proj₁ (Ωt ℓ) → GR.R ℓ a x
  → GR.R j (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b j w β x))

low-at′ : ∀ ℓ → IndexTree ℓ → LowAt′ ℓ
low-at′ ℓ it (o , r , B) .(z≤ ℓ) β t rb wz (mb , gb) pref gx m =
  direct ℓ it o r B gb t pref zero (z≤ ℓ) [] (index-zero ℓ o r) β mb m

low-when-prefix : ∀ ℓ (it : IndexTree ℓ) (b : Bsᵍ ℓ) (β : Tr⁺ zero) (t : E.T)
  → Bdᵍ b (z≤ ℓ) β t → PrefixU (proj₂ (proj₂ b)) t
  → ∀ {a x} → GR.R ℓ a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b zero (z≤ ℓ) β x))
low-when-prefix ℓ it (o , r , B) β t (mb , gb) pref m =
  direct ℓ it o r B gb t pref zero (z≤ ℓ) [] (index-zero ℓ o r) β mb m

low-layer-prefix : ∀ ℓ (b : Bsᵍ ℓ) → LayerIndex ℓ (proj₁ b) (proj₁ (proj₂ b))
  → (β : Tr⁺ zero) (t : E.T) → Bdᵍ b (z≤ ℓ) β t → PrefixU (proj₂ (proj₂ b)) t
  → ∀ {a x} → GR.R ℓ a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b zero (z≤ ℓ) β x))
low-layer-prefix ℓ (o , r , B) li β t (mb , gb) pref m =
  layer-at ℓ o r li B gb t pref zero (z≤ ℓ) [] (index-zero ℓ o r) β mb m
```
