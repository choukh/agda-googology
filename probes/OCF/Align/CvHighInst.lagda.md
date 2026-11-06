# 折叠产出的读坐标节点: 分支对坐标的值单调

> 不含记号. 入口 [CvHigh](CvHigh.lagda.md). `CvFoldInst.Kn` (折叠在目标第 1 层上走 $\Omega_\Omega$ 回灌闭包第 0 层那一格产出的 `ni`) 的分支, 对坐标的第 0 层值单调: $\mathrm{toA}\,z\le\mathrm{toA}\,z'$ 则 $0+u(z)\preccurlyeq 0+u(z')$ (`Kn-mono`). 值相等的坐标给值相等的分支 (`Kn-cong`). 这比 `Cv` 强: `Cv` 只比 $z$ 与它的规范形.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvHighInst where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ss; ⊲-tr)
import OCF.Align.CumReadCF as C
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (D; D̂; n0; n1; ni; cnt)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.BrwMidZero using (toA)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S)
open import OCF.Align.CvFoldInst using (StepV; StepA; Kn)
import OCF.Align.CvHighCong as H
import OCF.Align.CvFoldRun as R

-- Kn 的分支
br : ∀ {W} → D one W → ∀ {W′} → W ⊲ W′ → Lg W′ → D azero W′ → D one W′
br (ni (ss C.self) u) p l z = u p l z
br _ p l z = n0

Kn-mono : ∀ (w : D̂ one) (Y : F.St one) {W′} (p : one ⊲ W′) (l : Lg W′) (z z′ : D azero W′) →
          proj₁ (toA z) ≤ proj₁ (toA z′) → S C.self l bz (br (Kn w Y) p l z) ≼ S C.self l bz (br (Kn w Y) p l z′)
Kn-mono w Y {W′} p l z z′ le =
  StepV l t′ (Y₂ F.⊕ F.Run ac′ z C.self l ll′ A′ n0 Y₂) (Y₂ F.⊕ F.Run ac′ z′ C.self l ll′ A′ n0 Y₂) z≼ (H.cong0 l t′ ac′ ll′ A′ ha z z′ le C.self C.self n0 n0 Y₂ Y₂ (≼-refl _))
  where
  kW : azero ⊲ one
  kW = ⊲-tr C.self (C.suc C.self)
  p″ = ⊲-tr C.self p
  t′ = ⊲-tr C.self p
  ac′ = F.accCn azero
  ll′ = ⊲-tr kW p″
  A′ : F.Ig (cnt azero) W′
  A′ = F.Ig↾ p″ (F.Ai F.accTop C.self (λ _ _ _ → n1) (C.suc C.self) kW tt StepA w)
  Y₂ = F.cv p″ l Y
  ha : R.HA l t′ ac′ ll′ A′
  ha w w′ Z Z′ r = StepV l t′ Z Z′ r r

Kn-cong : ∀ (w : D̂ one) (Y : F.St one) {W′} (p : one ⊲ W′) (l : Lg W′) (z z′ : D azero W′) →
          proj₁ (toA z) ≤ proj₁ (toA z′) → proj₁ (toA z′) ≤ proj₁ (toA z) →
          S C.self l bz (br (Kn w Y) p l z) ≈ S C.self l bz (br (Kn w Y) p l z′)
Kn-cong w Y p l z z′ le le′ = Kn-mono w Y p l z z′ le , Kn-mono w Y p l z′ z le′
```
