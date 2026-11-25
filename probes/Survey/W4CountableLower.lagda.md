# W4 在可数层号上的一次性下界与 BTBO

第四层，无条件。W4 的折叠在只含后继与严格 ℕ 极限的层号上，不低于参照系统 Level 在镜像码上的折叠（`lower`），对这类层号一次成立，不按站。由它得到已发表的 BTBO 闭项不高于 `EBOᶜ`（`btbo-lower`），以及参照的 ψ₀(Ω_n)、ψ₀(Ω_ω) 不高于 `EBOᶜ`（`finite-lower`、`omega-lower`）。只是下界；不涉及任何 Ω 形层号，Y 是否达到 EBO 不由此判定。模块原件是留档附件，先用 `scripts/w4klower/materialize.py` 抄成实验目录再编译。[纸面与进度](W4-可数层号定理-纸面.md) · [审计](W4-EBO-独立审计-Fable52.md) · 回报：[镜像](Reports-2026-11-24/M0-镜像与判定一致.md)、[乘幂](Reports-2026-11-24/M1-Level侧乘幂.md)、[折叠保持](Reports-2026-11-24/M3-折叠保持与顶层下界.md)、[迭代子保持](Reports-2026-11-24/M4-迭代子保持.md)、[装配](Reports-2026-11-24/M5-接到BTBO下界.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4CountableLower where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁)
open import W4Block
open import W4Ops using (Tr⁺; Ωt)
open import W4Path using (Ok)
open import W4Fold using (Base; ψ; EBOᶜ; twᶜ)
open import WVOne using (read; 𝟏)
import OCF.Align.Level as LV
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; ⊑→≼)
open import OCF.Align.BTBOValMain using (nat⊑L₁)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.NoCumsum as NC
open import KMir using (IsS; IsS→IsN; code)
open import KLowIface using (Cov)
import KLow
import KBtbo
import KJLevel
import KJEbo
```

`IsS m`：层号 m 只由零、后继、严格的 ℕ 极限生成。`code m`：m 的镜像码。`Cov S`：状态的每个条目按 W4 的步进序不低于该层的标准 Ω 树。

```agda
lower : (m : L) (st : IsS m) (o : Ok m) (S : Base m) → Cov S
      → (β : Tr⁺ zero) → 𝟏 ≼ read (proj₁ β) → (w : zero ≤ m)
      → LV.ψ⁰ (LV.Ω (code m (IsS→IsN m st) o)) ≼ read (proj₁ (ψ m o S zero w β (proj₁ (Ωt m))))
lower = KLow.lowerW

tw1-lower : NC.BTBOᴵ ≼ read (twᶜ 1)
tw1-lower = KBtbo.tw1-lower

ebo-lower : NC.BTBOᴵ ≼ read EBOᶜ
ebo-lower = KBtbo.ebo-lower

btbo-lower : tr₀ Ord-Ord.BTBO ≼ read EBOᶜ
btbo-lower = KBtbo.btbo-lower
```

参照链的第 2 项已经不低于参照的 ψ₀(Ω_ω)（Level 一侧的已有引理），所以首页曾列为开放的两条在这一口径下成立。

```agda
omega-lower : LV.ψ⁰ (LV.Ω LV.ωᴵ) ≼ read EBOᶜ
omega-lower = ≼-trans (⊑→≼ (LV.ψ⁰ (LV.Ω LV.ωᴵ)) (LV.Ψ⁰-mono (LV.l⊑ nat⊑L₁)))
  (≼-trans (≼l 1 (≼-refl (NC.γ 2))) ebo-lower)

finite-lower : (n : ℕ) → LV.ψ⁰ (LV.Ω (LV.natᴵ n)) ≼ read EBOᶜ
finite-lower n = ≼-trans (≼l n (≼-refl (LV.ψ⁰ (LV.Ω (LV.natᴵ n))))) omega-lower
```

越过 BTBO 的第一步（2026-11-25）。`KJLevel.JS.J` 是参照系统里从 `suc BTBOᴵ` 起步的链 x, ψ⁰(Ω_x), … 的极限。它不高于 `EBOᶜ`，所以 `EBOᶜ` 严格高于 `BTBOᴵ`。从 `BTBOᴵ` 本身起步的链停在原地（`BTBOᴵ` 是 z ↦ ψ⁰(Ω_z) 的不动点），不给出新内容。

```agda
above-btbo : LV.suc NC.BTBOᴵ ≼ read EBOᶜ
above-btbo = KJEbo.sBTBO-EBO

next-closure : KJLevel.JS.J ≼ read EBOᶜ
next-closure = KJEbo.JS-EBO

fixed-at-btbo : KJLevel.JB.J ≼ NC.BTBOᴵ
fixed-at-btbo = KJLevel.JB≼
```

机制：塔第 2 项的真实运行里，孩子 zero（层号就是 `tw 1`）的那个运行，状态在第 0 层的条目带着塔第 1 项从头折的值作尾巴（回退行，`KJEbo.entry-shape`），链从它之上起步。用到的仍只是没有 Ω 形结点的层号上的 `lower`。`JS.J` 按记号的位置是估计：α ↦ ψ₀(Ω_α) 的第二个不动点，约 ψ₀(Ω_Ω·2)，未证。[回报](Reports-2026-11-25/KJ-越过BTBO的第一步.md)

范围。`NC.BTBOᴵ` 的标签 ψ₀(Ω_Ω) 外层是定理、内层是估计（[NoCumsum](../OCF/Align/NoCumsum.lagda.md) §4），所以 `btbo-lower` 读作 "不低于已发表的 BTBO 闭项"。装配里 "链点的规范化层号嵌进折叠值的字面前驱" 只对只含 `inu` 的到零路径证了，目标用到的都是这种。树、折叠、合法性证书没有改。 Ω 形层号上折叠的输出依赖层号证书里的下标路径（[审计](W4-EBO-独立审计-Fable52.md) §9.1）；本文的定理不受影响：`btbo-lower` 对的是 `Ok-Λ`，`lower` 只涉及没有 Ω 形结点的层号。
