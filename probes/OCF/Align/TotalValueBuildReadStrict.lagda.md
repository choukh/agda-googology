# 严格新坐标读回后仍可作累计嵌入的源或目标

这里只忘掉实际 Ordᴵ 的步进证。没有把值不等式反射成位置；层号的
往返仅有逐构造同形，不要求任意合法证明相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildReadStrict where
open import Data.Product using (proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Align.TotalValueBuildStrict using (SV; svz; svs; svl)
open import OCF.Align.TotalValueBuildStrictBase using (St; stz; sts; stl)
open import OCF.Align.TotalValueEmbeddingValue using (read-strict)
open import OCF.Align.ValueJudgeBase using (≼-trans; s≼s; ⊑→≼)
import OCF.Free.TotalOrbitBuild as A

read-strictness : ∀ {a} → SV a → St (A.read a)
read-strictness svz = stz
read-strictness (svs d) = sts (read-strictness d)
read-strictness (svl d st) = stl (λ n → read-strictness (d n))
  (λ n → ≼-trans
    (s≼s (⊑→≼ _ (A.read-mono (proj₂ (proj₂ (st n))))))
    (read-strict (proj₁ (proj₂ (st n)))))

read-level : ∀ a (h : HS (A.read a)) → toLevel (A.read a) h ≅ᴵ a
read-level zero h = z≅
read-level (suc a) h = s≅ (read-level a (hs⁻ h))
read-level (lim f st) h = l≅ (λ n → read-level (f n) (hl₁ h n))
```
