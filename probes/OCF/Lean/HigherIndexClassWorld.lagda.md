# 高层分量可入证书在实际扩界下保持

Position 明确读取低世界，但不因此固定世界。下面对所有含 Ω 的
分量高度证明：低世界增长时证书和 rank 路径都能搬运；并实例化真实
累加扩界 β↦β⊞leg e。这里不要求裸指标可判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexClassWorld where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.HigherIndexClassIf

position↑ : ∀ {w v} → _≤w_ U w v → ∀ c κ → Position w c κ → Position v c κ
position↑ q hz κ p = tt
position↑ q (hs c) (inj₁ κ) p = position↑ q c κ p
position↑ q (hs c) (inj₂ _) p = tt
position↑ q (hl f) (n , κ) p = position↑ q (f n) κ p
position↑ q (hΩ (inj₁ ()) g) κ p
position↑ q (hΩ (inj₂ _) g) (inj₁ _ , κ) p = tt
position↑ (q , b) (hΩ (inj₂ _) g) (inj₂ e , κ) (bd , p) =
  ⊲ᴮ-tr bd b , position↑ (q , b) (g e) κ p

class↑ : ∀ {w v c A} → _≤w_ U w v → Class w c A → Class v c A
class↑ q (base κ to fr a b) = base κ to fr a b
class↑ q (rank i p to fr a b) = rank i (⊲ᴮ↑ q p) to fr a b

grow : Cd → Cd → Wd U
grow β e = tt , β ⊞ leg e
growth : ∀ β e → _≤w_ U (tt , β) (grow β e)
growth β e = tt , ⊞-fst β (leg e)
legal-growth : ∀ β → LgB β → ∀ e → LgW U (grow β e)
legal-growth β lβ e = tt , Lg-⊞ β (leg e) lβ (Lg-leg e)

actual-position : ∀ β e c κ → Position (tt , β) c κ → Position (grow β e) c κ
actual-position β e = position↑ (growth β e)
actual-class : ∀ β e {c A} → Class (tt , β) c A → Class (grow β e) c A
actual-class β e = class↑ (growth β e)
```

legal-growth 对任意 raw e 都有实例，不限制成有限指标。定理只保证
扩大世界后保留已有可入/分类证据；不自动给先前不可入的所有分量证书，
也不声称不同世界的 decide 返回同一计算分支。总折叠及其值仍须另证。
