# 统一形 (五): 评估

> 本文只有结论, 证据在各文件. 区分三档: **已编译** (仓库内, `--safe`), **草稿已编译** (临时目录, 不在仓库, 因为要改已有文件), **判断**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Assess where

open import OCF.Align.Uniform5Top using (TΩ·2-label)
open import OCF.Align.Uniform5Wall using (¬tri)
open import OCF.Align.Uniform5NF using (¬Acc-T; nf-below)
open import OCF.Align.Uniform5SynPsi using (TQ)
```

## §1 $\psi_0(\Omega_{\Omega\cdot2})$ (已编译)

`TΩ·2-label`, `TΩ-label` 无条件. 上一位的预言对了一半: `Idx`, `pickMax`, `Lab-oc` 都没有改, 也没有新的调用方式. 没预言到的有两处, 都在互模拟: `Rᵒ` 必须跨层 (`<ᴵ-dec` 的代表元依赖证明, ℕ 上的 `≡-irrelevant` 没有 `Ordᴵ` 版), 以及 `trO` 两侧的搬运引理. `lΩ`/`rΩ` 的 $\Omega_{\Omega+k}$ 字段可以删掉, 因为它现在是定理.

## §2 标准形 (草稿已编译)

**裁决: 现在不移植 `OTFS_thm`, 就地推广 `Sb`.** 证据:

1. `StandardOmega` 的 `Sb` 加一个构造子 `sΩ² : Ctbl c → Sb (Ω₁ ∷ Ω₁ ∷ c)`, 补丁约 100 行 (奇异叶 `sing²` 在 9 个 `with` 处各一行, 加 `singΩ²`, `singG²`, `swapΩ²`, `swapΩ₂`, `1<plug`). `NF₁-fsn`, `cofin₁`, `fsT-mono₁` 全部通过. 没有用到新的自界引理.
2. 下游 70 个模块不改一行地重新通过, 只有三处例外: `SystemOmega` 的 `dsp` (没有调用者, 删) 与 `Sb-suc`/`leafSb` (各一行); `¬NF-Ω·2` 本来就是在陈述旧边界. 重新检查的闭包是从 `Uniform5Eval` 与 `Uniform4Label` 出发的 75 个模块. `Uniform5Label` 不在其中: 它的 `key`/`NF-Ω` 在新世界要加前提 $\theta<\psi_0(\Omega_{\Omega\cdot2})$, 否则为假 (`sΩ²` 分支).
3. 新世界里 $\psi_0(\Omega_{\Omega\cdot2})$ 的标签就是普通的 `cloOd 0`, 不要 `clo†`.

代价: 这些补丁改已有文件, 所以不在仓库; 克隆则要 70 个模块. **是否就地改 `StandardOmega`, 或者把它参数化, 要作者决定.** `NF₁` 在 77 个模块的依赖闭包里出现在 55 个模块的类型中 (18986 行代码), 但绝大多数只是传递.

**移植什么时候才是必需的 (判断).** `Sb` 的语法一旦含 $\psi_1(\cdot)$ (路径第 5 站), 奇异叶就不再是字面的 $\Omega_{\Omega\cdot k}$, `sing` 必须对下标递归, 指南 §5.2 的陷阱 1 ("界要相对于 $c$") 才会进来. 我没有试过这一步. 在那之前 `Sb` 每个阶段约 100 行.

## §3 下一堵墙 (已编译)

1. **`Syn`=$(m,\alpha)$ 可以写, 不用记号.** `Q`, `ψᵒ`, `TQ`; 切片从 `TQ`, `ψᵒ`, `ψ̄`, `Ω̇` 出发, 376 个定义, 没有一个落在 `EBO`/`Correspond`/`StandardOmega`/`SystemOmega`/`Standard`/`Bachmann`/`Closure`.
2. **需要比较而字面子项关系不够的第一处:** `Uniform5Wall` 的 $W$: 目标 $\Omega+1$, 节点 $\Omega+\gamma_n$. `¬tri` 说定义时比较不可能. **环境给公共上界:** 回答调度者的问题: 在这一段答案是肯定的, 地板 `fk τ` 与 `ac` 给 $\tau,k<\ell$, `<ᴵ-dec` 就够, 用不到 `Reg` (`Ordᴵ` 的 `lim` 已带步进证据). 代价是 `oev`.
3. **`Syn` 合法吗.** 不读记号的意义上合法: 切片是干净的. 但语法的形状 ($\Omega\cdot(m+1)+\alpha$, 字典序, 闭包第一支在 $1$) 是看记号写的, 树侧没有逼出它. 这是把记号的一段抄到了树侧.
4. **`Syn` 的边界.** $\psi_0(\Omega_{\Omega_\Omega})[1]$ 的路径第 5 站要 $\theta\mapsto\psi_1(\Omega_\theta)$ 对 $\theta$ 一致, $\theta=2$ 已是 $\psi_1$ 的迭代. 所以 `Syn` 必须含 $\psi_1$. 而 `¬Acc-T` 说语法序不良基, `Q σ` 要对 $\sigma$ 递归就要把标准形与 `Acc` 带进树的定义. 这个 `Acc` 就是指南说的未解决的 EBO 构造性良基性的相对版本. **这是第一个我不知道怎么过的地方, 没有否定定理.**

**标签的第一个具体障碍.** 仓库内: `¬NF-t₁[1]`. 草稿世界里 `NF₁` 已含 $\psi_0(\Omega_{\Omega\cdot2+1})$, 但 `Ld` 对 `Q` 没写. 预计的两个义务 (判断, 未试): `fk τ` 这个地板的 `Occ`: $\tau$ 是 $\Omega+\tau$ 的尾巴, 不是任何节点的下标, 现行 `Occ` 不含它, 要加一个构造子并补 `domᴸ`; `oev` 的互模拟要跨 $\ell$ 一致. 所以 $[n]$, $n\ge1$ 的标签都没有; $[0]$ 有 (`tΩΩ0-label`).

## §4 总评 (判断)

**一条对角线到 $\psi_0(\Lambda)$: 这个设计走不到, 每阶段要输入.** 阶段输入是 `Syn` 的语法, 比较, `Ω̇` 的子句, `Sb` 的补丁, `Ld`/`R` 的新行. $\Omega\cdot k+\alpha$, $\Omega\cdot\beta+\alpha$, $\Omega^n$ 看来都是这个模式, 我只写了第一个. 到 $\psi_1(\Omega_\theta)$ 输入变成 `Acc`.

**与 `Lv` 对照.** "`Lv` 的折叠加 Uniform3 的地板, 判决限制在可判定的范围" 这个描述仍然对. Uniform5 比它多的只有: 可判定的范围从 $\Omega+\alpha$ 扩到 $\Omega\cdot(m+1)+\alpha$, 办法是把判决推迟到求值 (`oev`). `Lv` 的判决 `D` 问题没有被绕开, 只是推后了. **建议不合并树, 但把两者的关系写清楚:** Uniform4/5 是 `Lv` 的判决取 "`Syn` 比较加 `<ᴵ-dec`" 的实例; 标签定理只在这个实例上有. 继续 `Syn` 阶梯可以多拿几个阶段, 但不要把它当通向 $\psi_0(\Lambda)$ 的路.

**树侧逼出的:** 地板, `trO`, 跨层 `Rᵒ`, `oev` (由 `¬tri`). **读记号的:** 层号语法, `cmpᵀ` 对应的字典序, 标签类的全部字段. `NF₁` 的边界 (`nf-below`) 与 `Ordᴵ` 层号的边界重合, 这一点不是设计出来的, 是算出来的.
