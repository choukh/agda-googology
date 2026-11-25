# 最小表实例: EVEnd

参数化（工程）的最小表实例；验收文件。来源 `YiVTEVEnd`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinEVEnd where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; inb; ink; Ev; Rt; Ev-tw; Rt-tw; Ev-Λ; Rt-Λ)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read; plus≽)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (OKB; ok-B₀; ok-dL)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁; ez; es; E-next)
import OCF.Lean.YiPMLSBtbo
open OCF.Lean.YiPMLSBtbo.F OCF.Lean.YiPMTable.tbᶠ using (btbo-tw1)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (ok-dW)
import OCF.Lean.YiPMEBShape
open OCF.Lean.YiPMEBShape.F OCF.Lean.YiPMTable.tbᶠ using (dB; Fn; br; br≼; ok-dB)
import OCF.Lean.YiPMEBBtbo
open OCF.Lean.YiPMEBBtbo.F OCF.Lean.YiPMTable.tbᶠ using (btbo-dB1; Start)
open import OCF.Lean.YiPMMinHi using (module HiΩ)
open import Data.Unit using (tt)
import OCF.Lean.YiDropRow as DR
import OCF.Lean.YiPMEVReach
open OCF.Lean.YiPMEVReach.F OCF.Lean.YiPMTable.tbᶠ
import OCF.Lean.YiPMMEAnchor
open OCF.Lean.YiPMMEAnchor.F OCF.Lean.YiPMTable.tbᶠ using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA; btbo≺A)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanTree using (hc-tower)
import OCF.Lean.YiPMEXRow
open OCF.Lean.YiPMEXRow.F OCF.Lean.YiPMTable.tbᶠ using (labR)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼-trans; ≅→≼)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiPMMinTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)

h₂ : Tr (tw 1) → LF
h₂ c = tw 1 ⊕ ↑ (tw 1) c

Br0 : Base (tw 1)
Br0 = dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2) zero zero

ε′ : Ev (tw 1)
ε′ = proj₂ (proj₂ (Ev-tw 2) zero)

ρ′ : Rt (tw 1)
ρ′ = proj₂ (Rt-tw 2) zero

ok0 : OKB (tw 1) Br0
ok0 = ok-dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2) (ok-dB 2) zero zero

-- 改: 删去 hi0 (它靠回退行的输出形状); 带表时改证孩子 c₁ 的底的 `Hi` (下面的 hi1).

c₁ : Tr zero
c₁ = c1Ω zero h₁ ε′ ρ′ Br0

c₁-form : c₁ ≡ next (bs Br0 zero (ink self)) (ns Br0 zero (ink self))
c₁-form = refl

B₁ : Base (h₁ c₁)
B₁ = dW zero h₁ ε′ ρ′ Br0 c₁ zero

-- 改 (新写): 第 0 层分量经孩子 c₁ 的一切路径, 是层号 `tw 1` 上以 B′ 为底的 Ω 树的折叠, 用 `YiVTHi.hiΩ`.
B′ : Base (tw 1)
B′ = dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dL tw Ev-Λ Rt-Λ (B₀ Λ) 2 (cumΩ tw 0)) zero zero

okB′ : OKB (tw 1) B′
okB′ = ok-dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dL tw Ev-Λ Rt-Λ (B₀ Λ) 2 (cumΩ tw 0)) (ok-dL tw Ev-Λ Rt-Λ (B₀ Λ) (ok-B₀ Λ) 2 (cumΩ tw 0)) zero zero

stB′ : Start B′
stB′ = E-next (es ez)

hi1 : Hi (h₁ c₁) B₁
hi1 = btbo-dB1 , λ w → HiΩ.hiΩ B′ okB′ stB′ c₁ tt w _ _

path₂ : two ⇐ h₁ c₁
-- 改: 带表时底的第 0 层分量 (链的起点) 是另一棵树, c₁ 的层号走到层号 2 的孩子编号随之不同
path₂ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l 1 ⇐r)))

low2 : Lo (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
low2 = reach path₂ (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1

tA≼br2 : (h : HC tA) → R2.Rt h ≼ read (br 2)
tA≼br2 h = ≼-trans (low2 h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

tA≼EBO : (h : HC tA) → R2.Rt h ≼ read EBOᶜ
tA≼EBO h = ≼-trans (tA≼br2 h) (br≼ 2)

tA≼EBOᴿ : (h : HC tA) → R2.Rt h ≼ readRW EBOᶻ
tA≼EBOᴿ h = up≼ EBOᶻ-R (tA≼EBO h)

btbo≼row₂ : D.BTBOᴵ ≼ R2.Rt (hc-tower 2)
btbo≼row₂ = ≅→≼ (L.≅-sym (Lab-uniq (labR (hc-tower 2)) BTBO-label))

btbo≺EBOᴿ : L.suc D.BTBOᴵ ≼ readRW EBOᶻ
btbo≺EBOᴿ = ≼-trans (s≼s btbo≼row₂) (≼-trans (btbo≺A (hc-tower 2) hA) (tA≼EBOᴿ hA))
```
