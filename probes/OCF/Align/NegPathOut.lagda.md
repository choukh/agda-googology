# 路径记在折叠输出上: 否定一路 (入口)

> 不含记号. 与构造一路 `PathOut` 配对 (作者本轮选定 "①(b): 路径记在折叠输出上"; 构造一路从带类型折叠 `TySup*`, `Fab3Typed` 出发, 把折叠输出改成 "带路径的高度", 让 lΩ 层号上的留/坍缩决定可做). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在标 "条件" 的定理里作前提.
>
> **接口定稿之前的部分 (不依赖接口).**
>
> 1. [NegPathOutWorld](NegPathOutWorld.lagda.md): Fab4LOm §5 的三条判断写成定理. 链坐标越过界 (`escape`, `fab3-escape`); "在世界里" 谓词三种读法: 一切分支同界不成立 (`inWA-out`), 界下分支管不到链分支 (`inWB-chain-out`), 分支换任意更大合法界推出字面并 (`no-grow`); 只对链坐标换界是构造 (`inWC-D`); 带界的节点有最大分支, 无界的没有 (`bd-max`, `unbd-no-max`).
> 2. [NegPathOutCmp](NegPathOutCmp.lagda.md): lΩ 层号的坐标, 有合法公共上界则层号字面可比 (`cmp-bound`, 构造); 首项不同的有限项极限 (如 $\lim\mathrm{od}$, $\lim\mathrm{ev}$) 字面不可比 (`incomp-lim`), 无公共上界 (`no-join-lim`); 精确决定蕴含字面可比 (`exact→cmp`), 所以这些坐标对上**没有**精确决定 (`no-exact-lim`); **Fab4LOm `exact→Sep` 的前提在 $X_1$ 上不可满足** (`fab4-premise-false`); 正确报告第四种结果 "不可比" 推出分离子 (`cmpdec→Sep′`), 有外延时 WLPO (`cmpdec→WLPO`, 条件).
> 3. [NegPathOutPath](NegPathOutPath.lagda.md): 路径不是命题, $\Sigma$ 存路径的输出带拷贝 (`paths-not-prop`, `copies`); 精确决定的标签与路径无关 (`exact-tag`); 到自选界的路径等于裸下标 (`own→⊥`); 链内后来的界盖住先前的界与目标 (`chain-common`, 构造); 不同起始界的链坐标无公共上界 (`cross-chain-nojoin`).
>
> 4. [NegPathOutLg](NegPathOutLg.lagda.md): 合法的 $\Omega_1$-结点把低坐标的种类带进每个高分支 (`spread`); "种类都在界之上" 的谓词在非零界下没有合法分支满足 (`no-AbV-branch`, 实例 `Dᶜ` 合法). 这是对构造一路 23:16 版证据方向 ("在界之上") 写的; 构造一路 23:21 改成 "在界之下", 这一条不再打到实例, 留作边界.
>
> **接口定稿之后的部分** (接口 [PathOutIf](PathOutIf.lagda.md), "接口定稿 2026-11-05 23:16"; 构造一路的 [PathOutFold](PathOutFold.lagda.md), [PathOutX1](PathOutX1.lagda.md), [PathOut](PathOut.lagda.md) 只读导入).
>
> 5. [NegPathOutIf](NegPathOutIf.lagda.md): 对一切实例, `correct` 加 `dec` 的证据推出字面三歧 (`Tri.ev-tg→tri`), 不三歧的一对没有同时带证据的合法世界 (`Tri.no-world`; 前提实例 `¬tri-od-ev`); 盲: `shift` 换成常值仍是实例 (`constShiftOf`), 证据恒空也是实例 (`voidIf`).
> 6. [NegPathOutInst](NegPathOutInst.lagda.md): 对实例 `IX₁` 与闭项 `TX₁`. 合法、分支提到自己坐标的 $\Omega_1$-结点不满足 `PH` (`ph-lg-own`, 实例 `¬PH-Dᶜ`); 闭项的输入 `topX₁` 满足 `PH` 但不合法 (`¬LgB-topX₁`); 合法且满足 `PH` 的地板存在 (`top′`: `Lg-top′`, `PH-top′`); 正面 `tri-IX₁`, 前提实例 `no-world-IX₁`; 盲: 常值 `shift` 的同一闭项也有 `LgB` 证书 (`LgB-TX₁c`).
>
> **只否定什么 (汇总).** 见各篇文件头. 没有一条否定 `TX₁` 的 `LgB` 证书或 `correct₁`; 没有值的定理. 本路没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOut where

import OCF.Align.NegPathOutWorld
import OCF.Align.NegPathOutCmp
import OCF.Align.NegPathOutPath
import OCF.Align.NegPathOutLg
import OCF.Align.NegPathOutIf
import OCF.Align.NegPathOutInst
```
