# 原mid保持两层坐标膨胀证书

最低Ω的坐标恢复只经纯Cd归纳及Native0值合成。中Ω所有实际回灌
坐标先递归获得Seed0，再进入Seed1分支；没有调用任意raw中槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedMiddle where
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel)
open import OCF.Lean.TwoSlotValueRun using (middle; middle-positive)
open import OCF.Align.BoundedWorldValueTwoSlot
open import OCF.Align.BoundedWorldSeedIf
open import OCF.Align.BoundedWorldSeedClosure
open import OCF.Align.BoundedWorldSeedCompose using (trans0)
import OCF.Lean.Fold1Fold as F

recover-pure : ∀ b (c : Cd) → Value hz (up c) (mid b (up (up c)))
recover-pure b hz = vz
recover-pure b (hs c) = vli 1 (add-rel (recover-pure b c) (middle-positive b (up (up c))))
recover-pure b (hl f) = vl (λ n → vli n (recover-pure b (f n)))

preserve : ∀ {b a} → Seed0 b → Seed1 a → Seed0 (mid b a)
preserve {a = hz} sb sa = vs vz , (vz , Data.Unit.tt)
  where import Data.Unit
preserve {a = hs a} sb (aa , sa) = middle aa (self0 sb) , mul0 (preserve sb sa)
preserve {a = hl f} sb (aa , sa) = middle aa (self0 sb) , (λ n → preserve sb (sa n))
preserve {a = hΩ (inj₁ (inj₁ ())) g} sb sa
preserve {b} {a = hΩ (inj₁ (inj₂ _)) g} sb (aa , inf , sa) =
  middle aa (self0 sb) ,
  (λ c → trans0 (recover-pure b c) (middle (inf c) (self0 sb))) ,
  (λ c → preserve sb (sa c))
preserve {b} {a = hΩ (inj₂ _) g} sb (aa , inf , sa) = middle aa (self0 sb) , sums
  where
  module C = F.Col _⊞_ _⊞_ b b (λ _ e → e)
    (λ b′ e → mid b′ (g e)) (λ b′ e → mid b′ (g e))
  coordinates : ∀ n → Seed0 (C.ce n)
  outputs : ∀ n → Seed0 (C.oo n)
  coordinates zero = sb
  coordinates (suc n) = add0 (coordinates n) (outputs n)
  outputs zero = preserve sb (sa b sb)
  outputs (suc n) = preserve (coordinates (suc n)) (sa (C.ce (suc n)) (coordinates (suc n)))
  sums : ∀ n → Seed0 (C.oO n)
  sums zero = outputs zero
  sums (suc n) = add0 (sums n) (outputs (suc n))

instance-middle : MiddlePreservation
instance-middle = record { preserve = preserve }
```

preserve作用于原mid，输出仍为原Col全部部分和的极限。此处没有证明
low因该证书而复合化，也没有完成跨Uniform的值覆盖。
