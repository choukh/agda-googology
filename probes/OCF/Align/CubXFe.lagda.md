# Cubical 验证实验 (一): 函数外延对标准库的 `_≡_`, 填上条件定理的前提

> **验证实验, 作者 2026-11-05 准许, 不进成品, 不改规则.** 本篇是 `--cubical --safe` 模块 (库文件另加 `--cubical-compatible --guardedness --hidden-argument-puns`), 不开 K (立方类型论本身不含 K). 不改任何已有文件, 只导入它们. 无公设, 无洞, 无停机或正性编译指示. 不含记号.
>
> 问题: ψ₀Λ 一侧几条路的障碍写成了以 `Funext` (或由它推出的 `UIPᴴ`) 为前提的条件定理. 在立方类型论里函数外延是定理. 若把它填进去, 哪些条件定理变成无条件的?
>
> **结果 (都是编译过的定理, 在 `--cubical` 下).**
>
> 1. `fe : Funext`: 与 [AdmWUip](AdmWUip.lagda.md) 的 `Funext` 逐字同型 (对 `Agda.Builtin.Equality` 的 `_≡_`, 也就是标准库的 `_≡_`). 证明来自 cubical 库 `Cubical.Data.Equality.Conversion.funExt`: 把逐点的 `≡` 用 `eqToPath` 译成路径, 拼成函数之间的路径, 再用 `pathToEq` 译回 `≡`.
> 2. 由它直接得到: `uipᴴ : UIPᴴ` (`fe→uip`), `dirA` (`dirA-cond`), `uipᴸ : UIPᴸ` (`fe→uipᴸ`), `lemma1 : Lemma1` (`fe→lemma1`), `loopRefl : LoopRefl` (`uip→loop`), `raise1₀` (`fe→raise1₀`), `fix₀ω` (`fe→fix₀ω`), `cohω`, `cmpω` ([UipFbClosed](UipFbClosed.lagda.md) 以 `UIPᴴ` 为模块参数的两条), `loopFix : LoopFix` (`HB S₀` 上环沿任意族的搬运平凡, 直接由 `uipᴴ`).
> 3. 否定一侧以 `FE₀` (`ℕ → HB S₀` 上的外延) 或 `FE₁` 为前提的定理也变成无条件的: `raiseA→WLPO`, `raiseGω→WLPO`, `decAtω→WLPO` ([ColimWNeg](ColimWNeg.lagda.md)), `iso-ω→WLPO`, `slotFam→WLPO`, `pres→WLPO` ([NegFamSec](NegFamSec.lagda.md)), `raiseA′→WLPO` ([NegColimADom](NegColimADom.lagda.md)), `up-ω`. 这些是 "某某推出 WLPO" 的形状, 无条件化以后是更强的否定 (在立方类型论里), 不是新的构造.
>
> **读法 (判断).** 这些都是立方类型论的定理, 不是 `--safe --without-K` (仓库主线的选项) 的定理. 主线模块是 `--cubical-compatible` 的, 所以它们能被 `--cubical` 模块导入并在立方的意义下解释; 反过来, 本篇的结论不能导回主线模块 (`--cubical` 是传染的: 导入本篇的模块也要 `--cubical`). 一般 `S` 上的 UIP (`HB S` 是集合) 见 [CubXSet](CubXSet.lagda.md). 一般 `S` 上不成立的反例见 [CubXSetNeg](CubXSetNeg.lagda.md). 经 `funExt` 搬过的合法性证据还算不算得动 (计算检验) 见 [CubXComp](CubXComp.lagda.md).

```agda
{-# OPTIONS --cubical --safe --lossy-unification #-}
module OCF.Align.CubXFe where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Cubical.Data.Equality.Conversion using (funExt)

open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWUip using (Funext; fe→uip)
open import OCF.Align.AdmWCoh using (UIPᴴ; dirA-cond; raise₀ᴮ)
open import OCF.Align.LocUipIf using (UIPᴸ; Lemma1; LoopRefl)
open import OCF.Align.LocUipHed using (fe→uipᴸ; fe→lemma1; uip→loop)
open import OCF.Align.LocUipNegLoop using (LoopFix)
open import OCF.Align.NegColimALoop using (fe→raise1₀; fe→fix₀ω; X₀; LoopFix₀At)
open import OCF.Align.ColimAIf using (module Adm)
open import OCF.Align.ColimWIf using (ω₀)
import OCF.Align.UipFbClosed as U
open import OCF.Align.ColimWIf using (RaiseA; RaiseG; DecAt; x₀; finH)
import OCF.Align.ColimWNeg as CW
import OCF.Align.NegFamSec as NF
import OCF.Align.NegColimADom as ND
open Slot
open RaiseIf
```

## §1 函数外延

`fe` 的类型就是 `AdmWUip.Funext` 的定义体. 下面写两遍: 一遍用名字 `Funext`, 一遍逐字写出类型, 让检查器确认二者同型.

```agda
fe : Funext
fe = funExt

fe-literal : ∀ {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g
fe-literal = fe
```

## §2 构造一侧: 填上 `Funext` / `UIPᴴ`

```agda
uipᴴ : UIPᴴ
uipᴴ = fe→uip fe

dirA : Σ RaiseB (RaiseCoh Coh≡) × CmpKᶜ Coh≡
dirA = dirA-cond uipᴴ

uipᴸ : UIPᴸ
uipᴸ = fe→uipᴸ fe

lemma1 : Lemma1
lemma1 = fe→lemma1 fe

loopRefl : LoopRefl
loopRefl = uip→loop uipᴴ

raise1₀ : Adm.RaiseA1 X₀ azero
raise1₀ = fe→raise1₀ fe

fix₀ω : LoopFix₀At {X = X₀} {w = azero} ω₀
fix₀ω = fe→fix₀ω fe

cohω : ∀ n → Coh≡ (U.wω , U.Cω.V n)
cohω = U.cohω uipᴴ

cmpω = U.cmpω uipᴴ
```

`LoopFix` 只说 `HB S₀` 上的环 (仓库里由 `LocUipNegLoop` 定义): 有 `UIPᴴ` 时环就是 `refl`, 搬运平凡.

```agda
loopFix : LoopFix
loopFix {x} lx ℓ δ = h ℓ (uipᴴ ℓ refl)
  where
  h : (ℓ′ : x ≡ x) → ℓ′ ≡ refl → subst (λ z → HB (G₀ z)) ℓ′ δ ≡ δ
  h .refl refl = refl
```

## §3 否定一侧: 填上 `FE₀`, `FE₁`

`FE₀`, `FE₁` ([ColimWNeg](ColimWNeg.lagda.md)) 是 `ℕ → HB S₀`, `ℕ → HB S₁` 上的函数外延, 是 `Funext` 的特例. 填上以后, "某某推出 WLPO" 成为立方类型论里无条件的定理. 类型由检查器从原定理推出 (不重抄陈述, 免得抄错); 每条的原陈述见右边注释里的原名.

```agda
fe₀ : CW.FE₀
fe₀ f g = fe

fe₁ : CW.FE₁
fe₁ f g = fe

raiseA→WLPO : (∀ α → RaiseA x₀ (CW.wα α)) → CW.WLPO
raiseA→WLPO = CW.raiseA→WLPO fe₀

raiseGω→WLPO : RaiseG (up ω₀) → CW.WLPO
raiseGω→WLPO = CW.raiseGω→WLPO fe₀

decAtω→WLPO : DecAt (up ω₀) → CW.WLPO
decAtω→WLPO = CW.decAtω→WLPO fe₀

up-ω : up ω₀ ≡ hl finH
up-ω = CW.up-ω fe₁

iso-ω→WLPO : NF.Isolated ω₀ → CW.WLPO
iso-ω→WLPO = NF.iso-ω→WLPO fe₀

slotFam→WLPO = NF.slotFam→WLPO fe₀    -- ∀ R → (∀ α → SlotFam (wα α , VF R α)) → WLPO
pres→WLPO = NF.pres→WLPO fe₀          -- ∀ R → PresFam R → WLPO
raiseA′→WLPO = ND.raiseA′→WLPO fe₀    -- (∀ α → Adm.RaiseA′ (Xα α) wω) → WLPO
```

**读法 (判断).** 第 3 组在主线里是条件定理 "有外延时, 某个律族推出 WLPO". 立方类型论有外延而不证 WLPO (它与 `¬WLPO` 的模型相容是元定理, 纸面, 本篇不编译), 所以在立方的意义下这些律族不能一致地满足. 这不改变主线里它们的地位: 主线不开 `--cubical`, 那里它们仍是条件定理.
