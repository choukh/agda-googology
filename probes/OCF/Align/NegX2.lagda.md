# X₂ 与往 `tw n`: 否定一路 (入口)

> 不含记号. 与构造一路 `X2` 配对 (作者本轮选定 "C 线继续攻: X₂ / 往 Λ"; 构造一路从 [X1Up](X1Up.lagda.md) 出发, 把可数折叠推广到带底种类, 再写 $X_2=$ `lΩ lz (λ c → ls (ofU c))` 的实例). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在标 "条件" 的定理里作前提.
>
> **接口定稿之前的部分 (不依赖接口).**
>
> 1. [NegX2Bd](NegX2Bd.lagda.md): 不合法的坐标在任何合法世界里没有合法的公共上界 (`no-bd`, `no-lg-bound`, `ev→lgB`, 对一切种类结构). $X_2$ 的 `lΩ` 坐标层是第 0 层, 形状合法就是合法 (`cnt-ok`): 这一条**不在 $X_2$ 出现**. 坐标层是第 1 层 (`lΩ (ls lz) g`, 共尾度 $\Omega_2$) 时, 折叠在第 1 层的输出 $o_1$ 没有界 (`no-bd-o₁`, `no-ev-o₁`); 但第 1 层的合法化 `leg₁` 是构造 (`Lg-leg₁`), 所以那里要多一个合法化子句, 不是墙.
> 2. [NegX2Lv](NegX2Lv.lagda.md): $X_2$ 里 $X_1$ 的拷贝对可数目标无精确决定 (`no-exact-base-X₂`, 对一切分支 $c$); 叠层新种类来自不同 `lΩ` 坐标时无精确决定 (`no-exact-new-X₂`), 且没有固定的可数界盖住一切坐标 (`no-fixed-m`): `X1UpFold.decU` 的公共上界 (折叠所在的层号 $m$) 在 $X_2$ 里不存在, 要 `lΩ` 坐标上的世界. 叠层结构 `LS` 与 `Lv ∘ ofU`: 有外延时相等 (`LS≡LU`, 条件 `FE₁`); 不用外延的搬运是构造 (`toU`, `toS`, `kU`, `kS`, 种类往返 `kS-kU`, `kU-kS`); 闭的 $\omega$ 上 `refl` 已经不通过 (测试, 元层).
>
> **接口定稿之后的部分** (接口 [X2If](X2If.lagda.md), 2026-11-06 00:16 定稿; 构造一路的 [X2Fold](X2Fold.lagda.md), [X2Inst](X2Inst.lagda.md) 只读导入).
>
> 3. [NegX2If](NegX2If.lagda.md): 盲, 对一切实例. 读入一律换常值仍是实例 (`constOf`, `const-cls`, `const-cv`); 只要底有一个无条件有证据的种类, 一切种类都可以分成它的低种类视图 (`AllLo.allLoOf`, `all-lo`; 前提实例 `free-κΩ`): 接口没有 "分类正确" 律; 证据恒空也是实例 (`voidOf`).
> 4. [NegX2Mono](NegX2Mono.lagda.md): `Ψ₂` 不单调 (`NotMono₂.Ψ₂-not-mono`, 对一切实例).
> 5. [NegX2Inst](NegX2Inst.lagda.md): 对实例 `I₂` 与闭项 `TX2`. 正面: 分类正确 (`cls-ok`), 高种类一律在上正确 (`up-not-below`), 种类真被折到 (`TX2-root`, `up-step`, refl), 证书是标准 `LgB`. 盲: 读入常值的实例上同一闭项也有 `LgB` 证书 (`LgB-TX2c`). 边界: 叠层下标超过世界的合法输入不带路径 (`no-PH₂-high`); $X_2$ 地板接在任一叠层结点前面不带路径 (`no-up-after-floor`, 由 `¬CB-⊞`); $X_2$ 的 $\Omega_1$ 结点 (地板式分支) 换不到任何固定叠层 (`κΩ₂-not-cv`).
>
> **只否定什么 (汇总).** 见各篇文件头. 没有一条否定构造一路的 `Ψ₂`, `Sh-Ψ₂`, `PH₂-top`, 闭项 `TX2` 与 `LgB-TX2`; 没有值的定理. 本路没有关闭任何路线.
>
> **对纲领与目标 (判断, 依据上面的定理).** 纲领 1, 2: `TX2` 是布劳威尔树上的合法项, 证书靠形状. 树侧判据: 实例的分类与种类按结构读出的读回层一致 (`cls-ok`), 这一条是树侧可陈述的律, 接口还没有 (3). 读法: `TX2` 的外层是把前一个输出当叠层高度的同层链, 与 `TU2` 的对角同一机制, 读 ψ₀(Ω_{Ω·2}); **判断: 不高于 `TU2`** (同 `TXL` 与 `TΩΩ`). 越过它要 $X_2\oplus m$, 上层输出的形状落在 `Ψ₂` 的定义域外 (5 的边界, 判断: 上层折叠未写). 往 `tw n`: 新的坐标层要新的合法化子句 (1), 对层号递归的一般定义未写 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2 where

import OCF.Align.NegX2Bd
import OCF.Align.NegX2Lv
import OCF.Align.NegX2If
import OCF.Align.NegX2Mono
import OCF.Align.NegX2Inst
```
