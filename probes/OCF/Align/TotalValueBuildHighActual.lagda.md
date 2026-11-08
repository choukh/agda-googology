# 冻结的完整高闭项已有 BTBO 下界

只取原 HBω² 端行的两个真实链分量（各是第1输出），再消费完整
base 闭包下界。不是把高输入改成低输入，也不是新建另一个闭项。
参照 NC.BTBOᴵ 已由 OrdLabZLabel.BTBO-label 验为 ψ₀(Ω_Ω)。本篇
只给此下界，尚非原 EmbVV 的 ψ₀(Ω_{Ω·ω²}) 下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildHighActual where
open import Data.Nat using (ℕ; zero)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Align.LadderOrdBase using (chain)
open import OCF.Align.LadderOrdPos using (HB; end; low; blk)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdTree (HB ω²ᶜ)
open import OCF.Align.ValLabLadder (HB ω²ᶜ) using (e₀; ev₀)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueBuildHighChain (HB ω²ᶜ) as C
import OCF.Align.TotalValueBuildBaseActual (HB ω²ᶜ) as B
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept

outer : ℕ → Ht
outer n = low (blk n end)
outer-path : ∀ n → outer n <ᴸ end
outer-path n = tt
outer-view : view end ≡ chain outer outer-path
outer-view = refl

inner : ℕ → Ht
inner n = low (blk 0 (low (blk n end)))
inner-path : ∀ n → inner n <ᴸ outer 0
inner-path n = tt
inner-view : view (outer 0) ≡ chain inner inner-path
inner-view = refl

base-lower : N.BTBOᴵ ≼ C.value (inner 0)
base-lower = B.whole ok₀ e₀ ev₀ zero

raw-lower : N.BTBOᴵ ≼ C.value end
raw-lower = ≼-trans base-lower
  (≼-trans (C.component (outer 0) inner inner-path inner-view 0)
    (C.component end outer outer-path outer-view 0))

closed-lower : N.BTBOᴵ ≼ Accept.read (proj₁ Final.closed)
closed-lower = ≼-trans raw-lower Accept.original-lower
```
