# CRw 上底做成递归: 否定一路 (入口)

> 不含记号. 与构造一路 `RecB` 配对 (作者本轮选定 "CRw 上底做成递归"). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有). 本路没有关闭任何路线.
>
> 1. [NegRecBPre](NegRecBPre.lagda.md) (接口之前, 只导入 `CRwBase`): `wdep-top`, `wdep-low`, `zero-low` (第 k≥1 层第一位置依赖世界, 低层世界不能重置); `bound-wdep` (第 1 层坐标对的合法公共上界存在与否依赖低层世界); `sup-diag-illegal` (各站在 sup 各自分量里写, 对角不合法; 累加对角合法 `Lg-Σᴬ`); `Lg-ΩA` (任一坐标层 U 上新种类结点的 θ 累加合法化, 正面); `no-retract` (CRwBase 版).
> 2. [NegRecBIf](NegRecBIf.lagda.md) (接口 `RecBIf`, 01:53 定稿): 盲 `constShB`, `stayB`, `trivB`; 初始世界不定 `W₀-free`, `w2B`, `wωB`; `W₀≢0`; 读类型: 每层世界都是 `Cd`.
>
> 3. [NegRecBInst](NegRecBInst.lagda.md) (构造一路 `RecBFold`, `RecBPath`, `RecB` 只读导入): 一个定义覆盖一切 n (`Sb-step`, `dcI-suc`, 但底的下标是 ℕ 不是 `LH`); 形状 `root-keep` (n≥1 留指标结点), `root-collapse₀`; 证书标准 `LgB` (`cert-std`), 中间层不合法 (`kept-not-LgB₁`), 折叠不保第一位置 (`ΦS-acc`, `ΦX-acc`); 决定 `ok-dcxR`, `ok-dcI₀`, `dcI-suc-not-local`; **`ΦX↓M-fails`**: 指标分量在下层结构里也移动世界 (`liftM`) 时 `PH-ΦX↓` 的结论不成立 (反例 `out-fails`, 前提 `in-M`, `nd-M`, `fl-Q₀`, `ok-Q₀`).
>
> **未查.** `TD 0` 与 `TD 1` 没有能分开它们的有限测试 (`RecBCmp` 深度 4, 5 结点数相同); 读法没有定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegRecB where

import OCF.Lean.NegRecBPre
import OCF.Lean.NegRecBIf
import OCF.Lean.NegRecBInst
```
