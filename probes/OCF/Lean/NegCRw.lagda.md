# C 线重写成一个折叠: 否定一路 (入口)

> 不含记号. 与构造一路 `CRw` 配对 (作者本轮选定 "摆脱+压缩: C 线重写成一个折叠"; 构造一路把 `TySup*`, `PathOut*`, `X1Up*` 三段重写成一个对层号递归的带类型折叠, 放在 `OCF/Lean/CRw*`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 本路没有用函数外延, 没有条件定理.
>
> **接口定稿之前的部分 (不依赖接口).**
>
> 1. [NegCRwAcc](NegCRwAcc.lagda.md): 形状证书与 ℕ-极限子句的两难. 部分和子句的折叠不保第一位置 (`AccNM.acc-not-mono`, 只看三个值; 实例 `Φ-acc`, `Ψ-acc`, `ΦU-acc` 覆盖 C 线三段折叠, 其中 `Ψ-acc` 是新的); 形状证书加余锥性推出像是一条链 (`shape-cocone→chain`, `pt-shape→chain`); Fab3Typed 的逐点 `Ψ` 没有形状证书 (`fab3-no-shape`).
> 2. [NegCRwWorld](NegCRwWorld.lagda.md): 统一路径的代价. 用 X1Up 的搭法从底 `S⊥` 搭出的可数层号上, 统一的路径处处成立 (`Uni.ph-free-cnt`, 盲区); $X_1$ 的底上不平凡 (`base-not-free`); 第 0 层值的第一位置与世界无关 (`wfree-S⊥`), 第 1 层的依赖世界 (`wdep₁`).
>
> **接口定稿之后的部分** (接口 [CRwIf](CRwIf.lagda.md), "接口定稿 2026-11-06 00:49"; 构造一路的 `CRwBase`, `CRwFold`, `CRwPath`, `CRw` 只读导入).
>
> 3. [NegCRwIf](NegCRwIf.lagda.md): 接口的盲区. 对一切实例: 回灌换成与坐标无关仍是实例 (`constShOf`); 进入后世界不动仍是实例 (`stayOf`); 平凡实例 `trivIf`; 律唯一强制的是合法世界里有可入的坐标 (`adm-nonempty`).
> 4. [NegCRwInst](NegCRwInst.lagda.md): 对折叠与实例 `I₁` 的检查. 正面: 两个决定都正确 (`ok-dcl`, `ok-dcx`, 对一切 `I`; 底种类一行是 $\top$, 盲). 否定: 重写后的 `Φ` 不保第一位置, 同底与跨底都是 (`Φ-acc-sm`, `Φ-acc-cx`, 对一切 `I`); 合法输入经同底折叠到 $\Omega_1$ 层后留下的 $\Omega_1$ 结点不满足 `LgB` (`kept-not-LgB-X`, 对一切 `I`; 这正是闭项 `TU` 的中间一步 `inU` 用的折叠). 边界: 在 `stayOf I₁` 里 $\Omega_1$ 层的地板不带路径 (`stay-no-PH`), 闭项公式写不出来, 接口的律不保证闭项可写; 补的律 $e+1\lhd\mathrm{nxt}_0$ 在 `I₁` 上成立 (`cover-I₁`). 盲: 在 `constShOf I₁` 里同一闭项公式 `TX′` 也有 `LgB` 证书, 且 `TX′ ≢ TX` (`blind-TX`, `TX-differ`).
>
> **前提实例 (汇总).** 部分和的反例输入 $\lim(0,1,1,\dots)$ 合法 (`Lg-fI`), $1\lhd$ 它 (`one⊲fI`); `kept-not-LgB-X` 的输入合法 (`Lg-inΩ`), 世界合法 (`lg-wX`); `wdep₁` 两个世界都合法; `stay-no-PH` 的可入坐标 $3$; `fab3-no-shape` 的世界 `(tt , hz)`; `base-not-free` 的世界 $1$ 合法. 没有前提矛盾的定理.
>
> **只否定什么 (汇总).** 只否定: (a) 部分和子句的折叠 (C 线三段与 CRw 的 `Φ`) 保字面第一位置; (b) 逐点子句且像不是链的折叠有对一切输入的形状证书; (c) CRw 的同底折叠的中间输出满足 `LgB`; (d) 接口 `CRwIf` 的律保证闭项可写, 或保证回灌依赖坐标; (e) 第 1 层值的第一位置与世界无关. **不否定**: CRw 的 `Sh-Φ`, `PH-ΦX`, 闭项 `TX`, `TU m`, `TU2` 与它们的 `LgB` 证书 (都对); 决定的正确 (正面定理); 读法; 不累加且证书读输入合法的折叠 (未写, 未否定); 带世界塔的 `lΩ k g` ($k\geq1$) 设计. 本路没有关闭任何路线.
>
> **未查 (主审要求收尾时如实写).** (i) `TU2` 是否与 `X1Up.TU2` 逐项一致: 构造一路的 `CRwCmp` 只比了深度 4 的结点数; 本路的形状指纹 (深度 4, 5) 测试在 6G 内跑了 10 分钟以上未完成, 已停止, **未查**. (ii) 行数复核: 脚本 `Survey/scripts/negcrw/audit_crw.py` 已写 (分出 X1Up 第 3 层里 "决定正确" 与 "地板合法" 两项, CRw 不再证), 要 `--html` 编译 `CRwCmp` 后运行, **未跑**. (iii) "层号单调" (闭项随层号字面递增) 的否定: 只有纸面分析 (判断: 直接折与经第 $i$ 层的复合折各是一条同值上确界的链, 字面不包含), 没有定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegCRw where

import OCF.Lean.NegCRwAcc
import OCF.Lean.NegCRwWorld
import OCF.Lean.NegCRwIf
import OCF.Lean.NegCRwInst
```
