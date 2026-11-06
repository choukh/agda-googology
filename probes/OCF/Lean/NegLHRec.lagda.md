# 底对 LH 递归: 否定一路 (入口)

> 不含记号. 与构造一路 `LHRec` 配对 (作者本轮选定 "RecB → 底对 LH 递归"). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有). 本路没有关闭任何路线.
>
> 1. [NegLHRecPre](NegLHRecPre.lagda.md) (接口之前, 只导入 `CRwBase`, `NegRecBPre`): `no-wfree-cmp`, `sep-worlds` (第 $k\geq1$ 层分量下标的比较必须在同一个世界里带公共上界); `layer-up`, `layer-reset`, `old-world-strict` (世界的一层 (低层世界, 界) 按 `step` 的世界序移动; 低层世界缩小丢证据); `no-plain-fb` (回灌不合法化则不合法); `Λ-naive-illegal`, `copy-diag-illegal`, `Λ-acc-legal` (对角到 $\Lambda$: 各项在各自分量里不合法, 累加合法).
> 2. [NegLHRecIf](NegLHRecIf.lagda.md) (接口 `LHRecIf`, 08:06 定稿): 盲 `stayL`, `stay-no-cover`, `kripkeC`, `kripkeC-const`; 边界 `naive-adm↓-fails` (`I₁` 原样抬到第 1 层不满足 `adm↓`), 正面 `Kr.inst` (Kripke 式可入, 对一切合法化族是实例); `fb-must-legalize`, `no-plain-sh` (新界是 $e+1$ 时回灌必须合法化).
> 3. [NegLHRecInst](NegLHRecInst.lagda.md) (构造一路 `LHRecLeg`, `LHRecLay`, `LHRecFl`, `LHRec` 只读导入, 08:20 到 08:30 版): 实例 `J₁` 进入后界是 $e+1$ (`nb-J₁`), 回灌合法 (`J₁-legal-fb`) 且依赖坐标 (`J₁-sh-dep`); $\Lambda$ 地板 `flΛ-shape`, 不累加不合法 (`Λ-naive-flL`); 构造一路 §4 的两难写成定理: (a) **`dilemma-a`** (`sup` 的合法世界里分量世界不相容, 跨分量搬运丢第一位置; 正面 `compat-transport`), `no-kind-emb`, `flL-blind`; (b) **`shared-keep-fails`** (按指标层共享界时, 留下指标结点带回灌不保路径, `ΦX↓M-fails` 在 `LHRec` 对象上的版本); 合法化 `leg-not-id` (改基本列), `leg-node`, `fl-coord-node`. **构造一路没有折叠, 没有 `Cd` 上的闭项, 没有 FGH** (读文件). 两难不是穷尽 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLHRec where

import OCF.Lean.NegLHRecPre
import OCF.Lean.NegLHRecIf
import OCF.Lean.NegLHRecInst
```
