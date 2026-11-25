# 空格退路的保留量与尚未证明的局部值比较
验收文件，读记号依赖只用于 readRW 与值序；不改树、折叠或表。
fallback-prefix 证明退路保留此前折叠的值；Retains 是有路径时比较臂不高于退路的值命题，未实填。
来源：值下界复用 YiKVRel.+⊴、◃→≼；Retains 按 YiTBRow 的第二臂逐字写，不当作已知定理。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOValue where
open import Data.Nat using (zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiKVRel using (readRW; _⊴_; ⊴r; ⊴◃; +⊴; ◃→≼)
open import OCF.Align.Value using (_≼_; ≼-refl)

⊴→≼ : ∀ {x y : Tr zero} → x ⊴ y → readRW x ≼ readRW y
⊴→≼ {x = x} ⊴r = ≼-refl (readRW x)
⊴→≼ (⊴◃ d) = ◃→≼ d

module Row (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h))
  (r : TB.Rb (nd (sΩ k) h)) (b : Base (nd (sΩ k) h))
  (c′ : Tr k) (v : zero ≤ h c′) (β : Tr⁺ zero)
  (x : Tr (nd (sΩ k) h)) (y : Tr (h zero)) (e : h zero ⊢ zero ◃ y) where
  before : Tr⁺ zero
  before = TB.ψ (nd (sΩ k) h) o r b zero (inc c′ v) β x
  cb : Base (h c′)
  cb i u = TB.ψ (nd (sΩ k) h) o r b i (inc c′ u) (b i (inc c′ u)) x
  right : h zero ≤ h c′ → Tr⁺ zero
  right u = TB.ψ (h c′) (proj₂ o c′) (proj₂ r c′) cb zero v before
    (proj₁ (emb (h c′) (proj₂ o c′) u (y , e)))
  fallback : Tr⁺ zero
  fallback = before ⊞ TB.ψ₀ʳ (h zero) (proj₂ o zero) (proj₂ r zero) y
  fallback-prefix : readRW (proj₁ before) ≼ readRW (proj₁ fallback)
  fallback-prefix = ⊴→≼ (+⊴ (proj₁ before)
    (ι zero (proj₁ (TB.ψ₀ʳ (h zero) (proj₂ o zero) (proj₂ r zero) y))))
  Retains : Set
  Retains = (u : h zero ≤ h c′) → readRW (proj₁ (right u)) ≼ readRW (proj₁ fallback)
```
