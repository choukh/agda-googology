# 带类型折叠到 sup 层: 否定一路 (入口)

> 不含记号. 与构造一路 `TySup` 配对 (构造一路从 [Fab3Typed](Fab3Typed.lagda.md) 出发, 把带类型折叠推广到 sup 层与一次封闭 `SL`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在标 "条件" 的定理里作前提.
>
> **接口定稿之前的部分 (不依赖 `TySupIf`).**
>
> 1. [NegTySupLg](NegTySupLg.lagda.md): `Lg*` 与 `LgB` 一般不可互推 (`lg*⇏lgB`, `lgB⇏lg*`, 反例); 有最小合法世界且合法性互推时两者互推 (`Coin`); `Coin` 对 `S⊥`, `step`, 逐分量的 `sup` 一步保持; 所以 Fab3Typed 的塔与一切 `Lv x` 上两者互推, `Ψ-mono`, `Ψ-lg` 在塔上用 `LgB` 陈述证得出 (`Ψ-monoᴮ`, `Ψ-lgᴮ`).
> 2. [NegTySupDiag](NegTySupDiag.lagda.md): `sup I G` 里带结点的输出不能跨分量作第一位置 (`no-cross`); 逐站独立坍缩、各站保留结点时 ℕ-对角不合法 (`indep-illegal`, `sw-illegal`); 带类型折叠各站的顶折一层再放回各自分量, 对角不合法 (`typed-indep-illegal`).
> 3. [NegTySupSel](NegTySupSel.lagda.md): sup 层的留/坍缩: 裸下标上的点律推出分离子 (`pt-sep`; 有外延时 WLPO, `pt→WLPO`, 条件), 一族目标的严格律推出 LPO (`lt→LPO`); 公共上界之下两种律都有构造 (`bpt`, `blt`).
>
> **接口定稿之后的部分** (接口 [TySupIf](TySupIf.lagda.md), "接口定稿 2026-11-05 21:37"; 构造一路的 [TySupFold](TySupFold.lagda.md), [TySupC](TySupC.lagda.md), [TySup](TySup.lagda.md) 只读导入).
>
> 4. [NegTySupIf](NegTySupIf.lagda.md): 接口的 `dec` 与层号之间没有律. 塔的实例 `towerIf` (决定正确, `ok-tower`; 回灌恒等, `feed-tower`); 对**一切**实例, 把 `dec` 换成 "一律同层, 常值回灌" 仍是实例 (`constOf`), 在塔上它不正确 (`¬ok-const`), 从不留种类 (`noKeep-const`); 无种类的平凡实例 `trivIf`. 判据 `Ok`/`Correct` 是建议增补的律.
> 5. [NegTySupMono](NegTySupMono.lagda.md): 累加的折叠不单调 (`NotMono.Φ-not-mono`, 对一切实例: $1\lhd\lim(0,1,1,\dots)$ 而 $\Phi 1
ot\lhd\Phi(\lim\dots)$); 塔的实例里留下的 $\Omega_1$-结点不满足 `LgB` 但满足 `Sh` (`kept-not-LgB`, `sh⇏lgB`).
> 6. [NegTySupC](NegTySupC.lagda.md): 对构造一路实例 `ICd` 的检查. 正面: `dec` 正确 (`ok-ICd`). 否定: 中间层留下的结点不满足 `LgB` (`kept-not-LgB-ICd`, `sh⇏lgB-ICd`); $\omega$ 层的地板是逐分量独立的对角, 不满足 `LgB` (`¬LgB-topω`); 证书对错误的 `dec` 同样成立, 闭项不同 (`blind-TC`).
>
> **只否定什么 (汇总).** 见各篇文件头. 没有一条否定闭项 `Tn n`, `Tω`, `TΩΩ` 的 `LgB` 证书, 也没有一条关于值 (读法) 的结论. 本路没有关闭任何路线. 未做: 不累加的折叠的单调 (构造一路接手清单第 3 条; 本路只否定了累加版本).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySup where

import OCF.Align.NegTySupLg
import OCF.Align.NegTySupDiag
import OCF.Align.NegTySupSel
import OCF.Align.NegTySupIf
import OCF.Align.NegTySupMono
import OCF.Align.NegTySupC
```
