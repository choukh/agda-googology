# 最高实际 Final 的尾层前提已实填

最高源也是原 Q，故新运行的 SV 来自全构造生成性，不再是待填前提。
下面仅把外部 y 的值界转换为最终完成后的界。它还没有给最高源
选择并证明一个具名 y；不能把条件结论读成最高 Final 已验收上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailHighFinal where
open import Data.Product using (proj₁)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdTree (HB ω²ᶜ)
open import OCF.Align.ValLabLadder (HB ω²ᶜ) using (e₀; ev₀)
open import OCF.Align.TotalValueBuildStrict using (SV)
open import OCF.Align.TotalValueBuildStrictBase using (St)
open import OCF.Align.TotalValueTailHighExternal using (external-upper)
open import OCF.Align.TotalValueTailHighGenerated (HB ω²ᶜ) using (output-sv)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalOrbitSource as Source
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Read

native : Ordᴵ
native = R.run (Source.High.raw end zero)
high-sv : SV native
high-sv = output-sv ok₀ e₀ (Ω̇ end zero) ev₀ zero

final-upper : ∀ (y : Ordᶜ zero) (hy : HS y) → St y →
  A.read native ≼ y → Read.read (proj₁ Final.closed) ≼ ψ⁰ (Ω (toLevel y hy))
final-upper y hy sy h = external-upper native high-sv y hy sy h
```

实际源仍为完整 HBω² 端行，并未投影已算好的旧 V，未换候选。
外部参照规则已有完整 rowB/BTBO 的实填实例（HighBaseFinal）；
这里对最高源只消掉 SV 生成性缺口。剩余主任务是控制高行全部非零
参数回灌，证明 A.read native≼一个独立旧参照，不是源本身。
