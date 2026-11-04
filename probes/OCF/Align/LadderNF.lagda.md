# 阶梯去记号: 记号无关的闭包定理

> **判决 (编译过的定理, 无条件, `--safe`).** 塔上的树 `Tᵠ m α` (取自标签阶梯, 代码逐字) 对**一切** $m$, 一切 $\alpha:$ `Ordᴵ`, 有不读记号的证书:
>
> `GᴺTᵠ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᵠ m α ev z))`
>
> | 目标 (读法来自验收) | 记号无关的证书 | 标签 (克隆世界, [LadderNFAccept](LadderNFAccept.lagda.md)) |
> | --- | --- | --- |
> | $\psi_0(\Omega_{\Omega\cdot2})$ 决定性锚点 | `GᴺTΩ·2` | `anchor-Ω₂`, 与旧树 `agree-P` |
> | $\psi_0(\Omega_{\Omega\cdot2+1})$ | `GᴺTΩ·2+1` | `label-Ω·+1 1` |
> | $\psi_0(\Omega_{\Omega\cdot3})$ | `GᴺTΩ·3` | `label-Ω·3` |
> | $\psi_0(\Omega_{\Omega\cdot(m+1)+\theta})$, 一切 $m$ | `GᴺTᵠ m α`, 一切 $\alpha$ | `label-cert m`, $\theta<\psi_0(\Omega_{\Omega\cdot(m+2)})$ |
> | $\psi_0(\Omega_{\Omega\cdot\omega})$ | **条件**: `GᴺTω-if`, 逐项 `GᴺTωn`; 缺跨高度的单调 | `Tω-lab` (单调读记号, 不算) |
>
> **最高的无条件目标: $\psi_0(\Omega_{\Omega\cdot(m+1)+\alpha})$, 一切 $m$, $\alpha$.** 停在 $\psi_0(\Omega_{\Omega\cdot\omega})$ 的跨高度单调.
>
> **第一个障碍 (判断, 纸面, 没有编译成否定).** $T_n\sqsubseteq T_{n+1}$ 比较两个世界: $\bar\psi_n(x)$ 与 $\bar\psi_{n+1}(\iota_\downarrow x)$. `⊑ᵀ` 只比较同一个 `Cx m`. 要的是一个跨塔的模拟: `top` 与 `pD top`, `pψ r C` 与 `pD (pΨ zero … C′)` 同值; 其中 `omk r z x` 左边读 $x$, 右边读 $z$, 所以要记下 $x=\iota\,r\,z$ 这个不变量, 而 `Rq` 没有传递性, 这个模拟要在值上做. 这是工程量, 不是壁垒: 标签世界里单调是真的 (`Tω-mono-lab`). 没有试.
>
> **否定结果: 无新增.** 支配没有失败. 下面的设计约束是**纸面的**, 没有编译成否定: 把 `VisQT` 放在最外层对任意 $\alpha$ 是假的 (取 $b=\lim$ 链, $\psi_0(\dot\Omega_b)=b$, 不动点), 所以等级 `g₀` (最外层只要 `Ctxᶜ`) 与节点等级 `g₂` 必须分开.
>
> **闭包定理的形状.** `T̄`, `Psi`, `PsiH`, `Iota`, `Add`, `Tr`, `ID`, `TL` 全是对证书 `Gq` 的结构递归, 没有对 $m$, $\theta$, $c$ 的归纳, 没有分阶段的支配论证. `Ω̇G′` 对 $(m,k)$ 递归, 那是 `Ω̇` 定义本身的结构; 每一行用的还是同一组规则.
>
> **检查 (都在本文件以外跑, 结果如下).**
>
> - 导入闭包: `importclosure.py OCF.Align.LadderNFMain`: 禁用表命中 0; 闭包内没有 `ScafLadderZ*`, 只有 `OCF.Align.LadderNF*`, `OCF.Free.{Aux,Base,Eq,Floor,Force,Level,Prefix,Tree}`, `OCF.BTBO`.
> - 定义级切片: `depslice.py`: `GᴺTᵠ` 到达 949 块, 记号 0, 词命中 0; `Ω̇G` 795 块, 记号 0. 正对照 `TΩᵠ-label`: 1718 块, 记号 92, 词命中 364.
> - 切片是语法级的; 闭包是编译器保证的, 但不说明定义没有受记号启发.
>
> **文法形状账 (如实说).** 下面这些是**从记号读来的**, 所以这不是"树自足", 只是"证书记号无关":
>
> | 形状 | 来源 |
> | --- | --- |
> | `Q m`: $\Omega\cdot m$ 的块, 高度由 `n <ᴸ m` 分开 | 记号的层号语法 |
> | `Ω̇ (suc m) zero`: 第一支在 $\eta=1$, 其余 $\eta$ 走 `ι↓ (Ω̇ m η)` | 记号的 $\Omega_{\Omega\cdot(m+2)}$ 的基本列 |
> | `Ψ` 的存在与三个分支 (`tlt`, `teq`, `tgt`) | 标签证明里读出来的 |
> | `omk r z x`, $x=\iota\,r\,z$ | 协调者提示, 记号里的 $\Omega_a$ 紧地板 |
> | `Ω̇ m (suc α)` 的输入, `ql` 的基本列 | 与 `Ord` 相同, 非记号特有 |
>
> **证书侧的新东西 (不读记号, 但设计受过失败的尝试引导).**
>
> - **等级 `Gr`.** `g₀`: 字面世界, 最外层, 类只要 `Ctxᶜ`. `g₂`: 节点世界, 输出要过 `ι↓`, 类要 `VisQ`, `hq` 要层号 $\sqsupseteq c$. `g₁`: `omk` 的第二格, 只在 `Nd` 上下文求值. `NdG`: 封闭性按等级要求, `g₂` 要对一切上下文, 这是 `ID` 过 `ι↓` 的前提.
> - **`VisQ k C`.** $C$ 的一切下移 $E$ 下, $\dot\Omega_b$ 的层号 $\succeq b+1$. 这是"$\psi_0(\dots\dot\Omega_b\dots)\succ b$"的栈形陈述, 由 `Sft` 归纳定义. 支配由它担保: 闭包目标的界 `bd⊑`, 链的地板.
> - **`Brq`.** 高度 $n$ 的闭包守卫, 与根层 `Brᵀ` 同形. 增长 `growT` 要 `Ω↓≺` (节点的严格增长, `ClimbΩ`, `Climb↓`), 比较 $b$ 与 $\eta$ 的公共上界是输出的层号, 这是壁垒允许的形式.
> - **`InvD`.** 下移经 `pD` 不出 `pD` 的链, 所以读数归结到根上的 `Brq`.
>
> **与世界的关系 (判断).** 证明里 $n<^L m$ 只经 `Hi`, `tri`, `upd-lt` 用到, ℕ 的高度没有别的用处. ℕ 到 $\psi_1(1)+\Omega$ 不够 (`noTimes`). 换成 `Ordᴵ` 上的层号语法 (`GuardTight*`, `LvGuardTree`) 时, `Gq`, `VisQ`, `Brq` 的形状不必改, 但这没有编译.
>
> **没有做到的.** (1) 跨高度单调. (2) 标签贴在克隆世界的证书上, 没有贴在主线的项上, 跨世界的联系是脚本比较 (树的代码逐字相同) 与有限测试 (`fgh-Ω·2`), 不是定理. (3) `Tω` 的闭项与 FGH 没有写.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNF where

open import OCF.Align.LadderNFMain public using (GᴺTᵠ; GᴺT; GᴺTΩ; GᴺTΩ·2; GᴺTΩ·2+1; GᴺTΩ·3; GᴺTωn; GᴺTω-if; Gᴺof)
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [LadderNFTree](LadderNFTree.lagda.md) | 树, 代码取自 `ScafLadderQ` |
| [LadderNFRel](LadderNFRel.lagda.md) | 互模拟 `Rq` |
| [LadderNFCx](LadderNFCx.lagda.md) | 观测上下文 `Cx` |
| [LadderNFRules](LadderNFRules.lagda.md), [Rules2](LadderNFRules2.lagda.md), [Rules3](LadderNFRules3.lagda.md) | 前序 `⊑ᵀ` 的规则 |
| [LadderNFStrict](LadderNFStrict.lagda.md), [Strict2](LadderNFStrict2.lagda.md), [Strict3](LadderNFStrict3.lagda.md) | 下移 `sh`, `𝟏q`, 严格增长, 节点攀登 `Ω↓≺` |
| [LadderNFMono](LadderNFMono.lagda.md) | $\dot\Omega$ 对层号单调 `Ωm`, `Ωm↓`, `Up≤` |
| [LadderNFClass](LadderNFClass.lagda.md), [ClassF](LadderNFClassF.lagda.md) | 值层的 `Good`, `Vis` |
| [LadderNFGood](LadderNFGood.lagda.md), [Vis](LadderNFVis.lagda.md), [Read](LadderNFRead.lagda.md) | 证书 `Gq`, 等级, `VisQ`, 读数 |
| [LadderNFIota](LadderNFIota.lagda.md), [Tr](LadderNFTr.lagda.md), [Add](LadderNFAdd.lagda.md), [Psi](LadderNFPsi.lagda.md), [PsiH](LadderNFPsiH.lagda.md), [Eval](LadderNFEval.lagda.md), [Tail](LadderNFTail.lagda.md) | 闭包定理的各行 |
| [LadderNFRoot](LadderNFRoot.lagda.md), [Omega](LadderNFOmega.lagda.md) | 根层与塔上的 `Ω̇G` |
| [LadderNFMain](LadderNFMain.lagda.md) | 主定理 |
| [LadderNFAccept](LadderNFAccept.lagda.md) | 验收, 标签 |
| `LadderNFW*` | 证书的机械克隆, 落在标签阶梯的树上, 只供验收 |
