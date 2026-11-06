# 沿 View 递归 (五): 高度树 `H`, 无条件

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 高度树的 View `viewᴴ` ([BrwViewHt](BrwViewHt.lagda.md)) 是恒等, 部分是字面的直接子树. 度量取对象自己, 关系取 `H` 的直接子树 `SubH` (对 `H` 结构归纳良基). $\Omega$-极限的部分只在合法坐标上 (`LgC = Lg`), 直接子树关系取遍一切坐标, 更宽, 所以没有影响.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfHt where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; LgH)
open import OCF.Align.BrwViewDef using (BrwView)
open import OCF.Align.BrwViewHt using (Sigᴴ; viewᴴ)
open import OCF.Align.BrwWfDef

data SubH : H → H → Set where
  sh-s : ∀ {h} → SubH h (hs h)
  sh-l : ∀ {f} n → SubH (f n) (hl f)
  sh-Ω : ∀ {g} (c : A) → SubH (g c) (hΩ g)

SubH-wf : WellFounded SubH
SubH-wf hz = acc (λ ())
SubH-wf (hs h) = acc (λ { sh-s → SubH-wf h })
SubH-wf (hl f) = acc (λ { (sh-l n) → SubH-wf (f n) })
SubH-wf (hΩ g) = acc (λ { (sh-Ω c) → SubH-wf (g c) })

Obᴴ : Set
Obᴴ = Obj Sigᴴ (λ _ → H) (λ h → h) LgH

voᴴ : Obᴴ → H
voᴴ (_ , h , _) = h

_◁ᴴ_ : Obᴴ → Obᴴ → Set
_◁ᴴ_ = _◁_ Sigᴴ (λ _ → H) (λ h → h) LgH viewᴴ

decᴴ : ∀ {o o′} → o′ ◁ᴴ o → SubH (voᴴ o′) (voᴴ o)
decᴴ {_ , hz , _} ()
decᴴ {_ , hs h , _} p-s = sh-s
decᴴ {_ , hl f , _} (p-l n) = sh-l n
decᴴ {_ , hΩ g , _} (p-Ω c lc) = sh-Ω c

wfᴴ : WellFounded _◁ᴴ_
wfᴴ = measure _◁ᴴ_ SubH voᴴ SubH-wf decᴴ

viewᴴᵂ : BrwViewᵂ Sigᴴ (λ _ → H) (λ h → h) LgH
viewᴴᵂ = record { bv = viewᴴ ; wf = wfᴴ }
```
