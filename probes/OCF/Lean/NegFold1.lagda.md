# 改 "在上" 的折法, 否定一路 (入口)

> 不含记号. 与构造一路 Fold1 配对, 共用接口 [Fold1If](Fold1If.lagda.md) (定稿 2026-11-06 08:07). 作者本轮 (原话) "摆脱: 改 '在上' 的折法". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有), 没有条件定理. 只新建 `NegFold1*` 文件, 不改别的文件.
>
> **接口定稿之前 (不依赖契约).**
>
> 1. [NegFold1Sup](NegFold1Sup.lagda.md): **sup 层没有前驱** (`no-pred`, `sup-two`, `sup-not-one`): 层号 $\lim f$ 相邻项字面严格时, 对它之下的任一层 $j$, 都有一个种类至少高出 $j$ 两层, 所以 "降一层到 $j$" (`OneStep`) 对一切 $j$ 不成立. 对照: 后继层与常列极限层都有前驱 (`succ-one`, `const-one`). **复合式在 sup 层与分量不相容** (`CompIncoh.no-coh`): 只要第 $1$, $2$ 层的分量把 $0$ 折成 $1$ 与 $\omega$, sup 层上任何函数都不能与分量经 $\iota$ 双向值相容 ($\iota_k\,0$ 字面是 $0$).
> 2. [NegFold1Fab3](NegFold1Fab3.lagda.md): 上一条的实例, Fab3Typed 的 `fold` (`fab3-no-coh`, `fab3-no-coh≡`).
>
> **接口定稿之后 (对契约).**
>
> 3. [NegFold1If](NegFold1If.lagda.md): **值的两条律是三个子句的推论** (`Φ-≤-free`, `Φ-l11-free`; 一般形 `Clauses.F-≤` 对一切满足零, 后继, ℕ-极限三条等式的函数); 无 $\Omega$ 的输入上输出与层, 目标, 界, 实例无关 (`Φ-indep`, 直接折); **值单调不能用不带界的 `≤ᵛ` 推广到 $\Omega$-输入** (`no-val-ext`, 由 `up≤top` 与膨胀 `infl`); 合法 `Lg` 不全 (`Lg-not-total`).
> 4. [NegFold1Blind](NegFold1Blind.lagda.md): **接口的一个实例 `Ibl` 把 $\Omega_1$ 折成 $1$** (`Ibl-Ω₁`, `refl`): 不坍缩, 只取最小坐标的分支; 输入世界的界全取 $0$. 接口的十二个字段全满足; 接口不说强度. 同时说明 3 的 "对一切实例" 不空真.
>
> **对构造一路的实例的检查** (构造一路 08:26 版: `Fold1Base`, `Fold1Fold`, `Fold1`; 只读导入).
>
> 5. [NegFold1X](NegFold1X.lagda.md): **坍缩子句的部分和使折叠在 $\Omega$-输入上不是值的函数** (`col-acc`: 合法的 $A=\Omega_1\{\_\mapsto1\}$ 折出 $\lim(\omega,\omega\boxplus\omega,\dots)$, $1$ 折出 $\omega$, $\Phi A\not\le\Phi1$; `col-not-val`: 对任何含自反与带界 $\Omega$-左规则的关系). 闭项 `TΩ1` 的基本列第 $1$ 项字面是 $1\boxplus\omega$ (`gl-TΩ1`, 值同 $\omega$, `gl-val`). 接口定理对实例 `Fold1.I` 实例化; `Ibl` 与 `I` 满足同一接口而在 $\Omega_1$ 上折出不同的树 (`blind-pair`); 接口参数 $b$ 在 `I` 里不起作用 (`X-b-irr`).
>
> **判决 (只对写明的形状).**
>
> - **sup 层**: "每次只降一层" 从字面严格的 sup 层出发不可能 (`sup-not-one`); 复合式与 sup 层的双向值相容不可能 (`no-coh`, `fab3-no-coh`). 构造一路没有走复合, 改为直接折; 这两条对它的设计是信息, 不否定它.
> - **构造一路的设计 (直接折, 链只作坐标)**: 证书 (`Φ-mono`, `Φ-lg`) 是构造一路的定理, 本路复编通过, 闭项有标准 `LgB`; `NoAccStuck` 的两段折法问题在它的设计里不出现 (它的 `route-ok`, `out-lg`). 本路找到的问题: (i) 值的律只在无 $\Omega$ 的输入上, 那里是三个子句的推论 (盲); (ii) 用不带界的 `≤ᵛ` 推广到 $\Omega$-输入不可能 (`no-val-ext`, 对一切实例); (iii) 用带界的 $\Omega$-左规则, 实例的折叠也不保值序, 根在坍缩输出的部分和 (`col-not-val`). 所以 "折叠是值的函数" 在 $\Omega$-输入上**未达到**; "不累加或累加不产生毛刺" **未达到** (坍缩处仍累加, 毛刺在值上 (iii) 与在闭项基本列上 (`gl-TΩ1`) 都有实例). 路线本身**没有被否定**: 没有定理说别的坍缩写法 (例如去掉部分和而证跨世界的单调) 不可能.
> - **读法 (判断)**: 层号只有可数层号, 闭项 `TΩΩ` 读 ψ₀(Ω_Ω), 低于 `TU2` 的 ψ₀(Ω_{Ω·2}); "重现 `TU2` 一类闭项" 按读法未达到, 没有值的定理.
>
> **只否定什么 (汇总).** 只否定: 从字面严格的 sup 层降一层; 复合式在 sup 层与分量双向值相容; 值单调用不带界 `≤ᵛ` 推广到 $\Omega$-输入 (一切实例); 构造一路的实例对含带界 $\Omega$-左规则的关系保值序; "接口的律推出强度". **不否定**: 构造一路的证书与闭项的合法; 直接折这一设计; 去掉坍缩部分和的版本; 带界值关系下别的折叠. 本路没有关闭任何路线.
>
> **对纲领与目标.** 纲领 1–4 不受影响 (都是对布劳威尔树与具体实例的陈述, 无公理, 不读记号). 目标 "让树自足" 的判据 "有树侧的合法性标准": `no-val-ext` 是 "比较要有字面公共上界" (纲领 3 的影子, `EBOHandbook` §3.1) 在值关系上的又一例: 值的律在 $\Omega$-输入上要说话, 值关系必须带界; `col-not-val` 说明带界之后, 坍缩输出的部分和就是值上的毛刺. 构造一路证书读输入合法 (`Lg-not-total` 说这是逼出的). 翻译账: 本路没有新增来自记号的字段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1 where

open import OCF.Lean.NegFold1Base public using (≤ᵛ-refl; ≤ᵛ-trans; mul≤)
open import OCF.Lean.NegFold1Sup public using (StrictL; no-pred; sup-two; sup-not-one; succ-one; const-one; ω-not-one; module CompIncoh)
open import OCF.Lean.NegFold1Fab3 public using (fab3-no-coh; fab3-no-coh≡)
open import OCF.Lean.NegFold1If public using (module Clauses; module Det; module Infl; Φ-≤-free; Φ-l11-free; no-val-ext; Lg-not-total; Φ-indep)
open import OCF.Lean.NegFold1Blind public using (Ibl; Ibl-Ω₁; Ibl-Ω₂)
open import OCF.Lean.NegFold1X public using (col-acc; col-not-val; Rfree-not-val; gl-TΩ1; gl-ne; gl-val; X-no-val-ext; X-Lg-not-total; X-≤-free; blind-pair; X-b-irr)
```

## 结论 (按档)

- **[定理]** 见各篇 "结论". 主要: `no-pred`, `sup-two`, `sup-not-one`, `succ-one`, `const-one`, `CompIncoh.no-coh`; `fab3-no-coh`; `Clauses.F-≤`, `Φ-≤-free`, `Φ-l11-free`, `Det.Sm-F`, `Φ-indep`, `Infl.no-val-Ω`, `no-val-ext`, `Lg-not-total`; `Ibl`, `Ibl-Ω₁`; `col-acc`, `col-not-val`, `gl-TΩ1`, `gl-val`, `blind-pair`, `X-b-irr`.
- **[有限测试]** 无 (`gl-TΩ1`, `Ibl-Ω₁` 是 `refl` 定理, 不是测试).
- **[判断]** 读法 (`TΩΩ` 读 ψ₀(Ω_Ω), 低于 `TU2`); 闭项输入里没有常值分支结点; 去掉坍缩部分和需要跨世界的单调; sup 层 "一步坍缩多层" 的非形式说法; 接口要说强度需约束 `Win` 并加带界的 $\Omega$-值律 (建议).
