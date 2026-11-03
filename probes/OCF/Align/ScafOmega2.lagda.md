# 脚手架: 站点 $\psi_0(\psi_\Omega(\psi_{\omega+1}(\Omega_\Omega)))$ 的好输入族 (判决: 站点无条件, 往上没有到达)

> 底座 [ScafOmega2Family](ScafOmega2Family.lagda.md), [ScafOmega2Node](ScafOmega2Node.lagda.md), [ScafOmega2GL](ScafOmega2GL.lagda.md) 不用记号的定义 (切片见文末). 记号只在 [ScafOmega2Site](ScafOmega2Site.lagda.md), [ScafOmega2Accept](ScafOmega2Accept.lagda.md). 接 [LvIR](LvIR.lagda.md), [LvStrat](LvStrat.lagda.md), [LvKey](LvKey.lagda.md), [EBOTop](EBOTop.lagda.md).
>
> **判决. 站点的标签是无条件定理, 证书不读记号, 没有新的树. 好输入族是下界族 $\{\eta:\mathsf{Ord}^\mathsf I\mid\tau+1\sqsubseteq^\mathsf I\eta\}$, 它没有公共上界. 这条路往上的目标一个也没有到达: $\psi_0(\Omega_{\Omega\cdot2+1})$ 以上的标签都没有, $\psi_0(\Omega_{\Omega_2})$, $x_3$ 也没有. 本文没有写新树, 也没有试它们 (见 "第一个障碍").**
>
> **中心问题的回答.**
>
> - **族与界是什么.** $\psi_\tau(\Omega_\Omega)$ 在世界 $\ell$ 里求值成字面闭包 `ŝ c t₀ g` (`Node.node`, `refl`), 定义域受支配: $g:\prod_\eta\,c\sqsubseteq^\mathsf I\eta\to\cdots$. $c$ 是 `Bd`, 模前序恰好是 $\tau+1$ (`τ+1⊑c`, `c⊑τ+1`, `fam→`, `fam←`). 比较用的公共上界逐分支现造: $\mathrm{Mlev}(\mathrm{Fc},\eta+1)$, 步进证据就是 $e:c\sqsubseteq^\mathsf I\eta$ (`cloA` 的定义, `cmpW`). $\tau=\omega+1$ 时 $c\cong\omega+2$.
> - **记号的标准形给什么界, 不要输出先有.** `Bnd₁ [] a` (`site-bnd`, `one<arg`): $a$ 里可见的 $\zeta$ 满足 $\zeta<a$, 这是**对输入**的条件. 目标 $\omega+1=\psi_0(1)+1$ 的可见参数是 1. 由 $1<a$ 到 "第 0 个链点 $\psi_0(a[1])$ 大于目标" 用的是记号的单调性, 这一步在这里只有有限检查 (`above₀`, `above₁`, `refl`).
> - **树语言的陈述 (不读记号).** `readT` ([UniformNF5Eval](UniformNF5Eval.lagda.md)): 第 $\tau$ 层的树 $t\sqsupseteq\Omega_\tau$, 经任何观测读到第 0 层, 它的证书 $G$ 的层号 $\sqsupseteq\tau+1$. 前提是 $G$, 不是一个预先给定的上界. `first-above` 是它在站点的实例.
> - **旧标签怎样躲开 `self-bound`.** 第 0 层没有地板. `self-bound` 的前提是 "链都低于 $L_0$", 这里没有这样的 $L_0$. 树是 $(\eta,e)$ 的总函数, 先于链定义, 只要 $c$; 证书在定义之后给 `dy`. 所以 [LvIRPos](LvIRPos.lagda.md) 的循环 "成员证据提上界, 上界要链点" 不出现: 成员证据提的是下界, 下界不要链点. **不要归纳-递归.**
> - **`no-read`.** 这条否定仍然成立, 也不被绕过: `G` 不含全假的 $y_s$ (`G-excl`). 但 [LvIR](LvIR.lagda.md) 的判断 "好输入要是有公共上界的族" 不对: `G-unbounded` 说这个族没有公共上界, `G-y-in` 说它含反例族里的成员. 判决不比较 (`G-rise`, `G-suc`, `Node.rise`), 证据就是答案.
> - **`LevelK` 的地板 (`A`, `<-decᴬ L`) 覆盖它吗: 不覆盖.** 地板有字面上界 (`bounded`), `G` 向上封闭, 没有 (`G-unbounded`). `self-bound`, `¬X∈A₀` 说地板装不下链点.
> - **`Ordᴵ` 分支覆盖它吗: 单独不够, 要加守卫.** `Ordᴵ` 整个含反例族 (`yᴵ`, `no-read-ᴵ`), 分支换成 `Ordᴵ` 不解决任何事. 解决问题的是定义域的守卫 $c\sqsubseteq^\mathsf I\eta$. 这不是 `UniformLv` 的新东西: `ŝ` 在 [Prefix](Prefix.lagda.md) 就有, 从 Uniform3 起一直在用.
> - **`LvKeyStep` 的 `GL` 逃得掉吗: 单独逃不掉.** `y∈GL`, `no-read-GL`: `Ordᴵ` 整个嵌进 `GL`. `Gᴸ-rise`, `Gᴸ-excl`: 守卫在 `GL` 上起同样的作用, 这只对 `LvKeyBase` 的路径搬运写了, `Step` 的局部版本没有写. `lc` 现在没有守卫 (读定义).
>
> **编译过的定理 (无条件).**
>
> 1. `site-label`, `site₀-label` ($\theta=1$ 的 `TΩ-label` 沿路径, `Lab-walk`): $\psi_0(\psi_\Omega(\psi_{\omega+1}(\Omega_\Omega)))$, 与更小的 $\psi_0(\Omega_\Omega+\psi_\omega(\Omega_\Omega))$. 后者已经是非自然数目标, 分支是全部 $v$, 在 $\psi_0(\Omega_\Omega\cdot2)$ 之内 (`site₀-walk`).
> 2. `site-labelᴺ`, `site₀-labelᴺ`: 同一个标签落在证书不读记号的树上 (`GᴺΩ̇ 1`, `forceᴺ-≅`). **所以这个站点到第 2 步也已经是 "无记号证书 + 标签验收".**
> 3. `Node.good`, `good-ω⁺`, `first-above`: $\psi_\tau(\Omega_\Omega)$ 的 `Good` 对一切 $\tau$, 不读记号. `Node.rise`: 第 $a+1$ 枝上升, 不比较. `through`: 穿过 $\psi_\Omega$, $\psi_0$ 后界还是 $c$, 第 0 层节点是 `ĉᴸ c`.
> 4. `G-*`, `cmpW` ([ScafOmega2Family](ScafOmega2Family.lagda.md)). `y∈GL`, `no-read-GL`, `Gᴸ-*` ([ScafOmega2GL](ScafOmega2GL.lagda.md)).
> 5. 次序 (`reach₅`–`reach₉`, `reach₁`, `refl`): $\psi_0(\Omega_{\Omega_2})\to$ 第 5 站 $\to\psi_0(\Omega_{\psi_1(\Omega)})\to\psi_0(\Omega_{\psi_1(1)})\to\psi_0(\Omega_{\Omega\cdot3})\to\psi_0(\Omega_{\Omega\cdot2+1})$. 所以任务的目标次序里 $\psi_0(\Omega_{\psi_1(\Omega)})$ 不比第 5 站难, 第 4 站最难, 而都要先过 $\psi_0(\Omega_{\Omega\cdot2+1})$. $\psi_0(\Omega_{\psi_1(0)})=\psi_0(\Omega_\Omega)$ 平凡 (`_ : ψ₁ᵗ [] ≡ Ω₁ᵗ`), 不算目标.
>
> **编译过的否定.** `no-read-ᴵ`, `no-read-GL`: 无条件的判决是 WLPO. `G-unbounded`: 族没有上界. `¬G-tri`: 族内没有三歧, 所以 `G` 不是 `Ordᴰ` 的精确初始段的形状 (对照 [Barrier](../Barrier.lagda.md) 是判断). 站点从不比较两个分支: `cmpW` 只比分支与目标.
>
> **对 [EBOTop](EBOTop.lagda.md) 与 [LvIR](LvIR.lagda.md) 的修正.** 它们说 "$\psi_0(\Omega_{\Omega_2})$ 的 `HS` 要好输入是有公共上界的族". `reach-hard` 没有错, 但站点在 $\psi_0(\Omega_{\Omega+1})$ 之内 (`reach₁`), 那里的标签早就是定理. 非自然数目标不是这条路线的新障碍, 它只在裸层号 `Lv` 与判决 `S` 的路线上是障碍: 那里 `hard` 的分支是全部 $v$, 没有守卫. 判断: 裸层号路线要接这个结果, 折叠的输出要有带守卫的闭包, 也就是把 `Ordᴸ` 换成 `Ordˢ` 那样的树; 这没有写.
>
> **有限测试 ([ScafOmega2Accept](ScafOmega2Accept.lagda.md), `refl`).** 直接写出站点形状的树 `Sτ`: `head-c` (第 0 层节点的界就是 `Node.c`), `agree-site`, `deep` (种类, 深 5, 7), 对照 `ctl`. [ScafOmega2Site](ScafOmega2Site.lagda.md): `fs0`, `fs1`, `above₀`, `above₁`, `below-one`. **`Sτ` 就是 `site-label` 走到的那棵树, 这一句没有编译**: 走路径经过证书, 我没有归约它, 证据只有 `node`, `through` 的形状与这里的有限检查.
>
> **移除台账 (第 2 步的输入).**
>
> | 东西 | 从哪里来 | 站点上的状态 | 树侧的形式 (判断: 伪装的树侧陈述) |
> |---|---|---|---|
> | `gc` 的 `l₀`, `lE` | `Lab` | **已移除**: `Goodᴺ` 的 `ys` 不带标签 | $\cong$ 到下一个链点 |
> | `gc` 的 `d₀`, `dE` ($c\sqsubseteq$ 链点) | 标签路线: `pickMax`, `Idx`, `cmpᵀ` | **已移除**: `bd⊑`, `readT`, `Dem` | `readT` |
> | `mo₀`, `mo` | `mono-lab`, `Lab-oc`, `fs-mono₁` | **已移除**: `⊑ᵒ`, `Ωm`, `Vm` | 观测单调 |
> | `NF₁`, `Bnd₁` | 标准形 | 只在验收. 树侧对应 `Dem`, `dt`, `dg`, `Brᵀ` | "地板元低于链", 就是 [LvStrat](LvStrat.lagda.md) 判断的边条件 |
> | `cmpᵀ` | 记号比较 | 只在验收. 定义里是 `<ᴵ-dec` | 字面上界之下的结构递归 |
> | 文法 | 这个站点没有 `Syn`. `O c φ` 的层号形状 $\Omega+\alpha$, `Ω̇` 的三个子句, 第一支 `oclo t g` 的 $\eta=1$ 是看记号定的 | **未移除**: 形状读过记号 | 到 $\Omega\cdot2$ 为止的结构, 没有树侧判据 |
>
> 关系 (判断). `WFᴬ` ([LevelK](LevelK.lagda.md)): 层号合法性, 不带下界, 在目标 0 不传 (`¬mono-0`); 这里的 `dy` 是它缺的那一半. `Good` ([InaccTheta](InaccTheta.lagda.md)): 与 `Good₊` 同形, 差在第 0 层的好输入是 `Aℓ` (上界) 而这里是守卫 (下界). `Family` ([EBOTop](EBOTop.lagda.md)): 只提 $\psi_0(\Omega_{L_n})$, $n\le1$ 的两项与这里的 `T̄` 同类; $n\ge2$ 这里没有说任何话.
>
> **读了记号的.** 路径 `path₁`, `path₀`, `path₀₁` 与项 `site`, `site₀` 来自 `fsn`; $\tau+1$ 这个界是从 `Bd` 算的, 不是读的; "第 0 个链点在目标之上" 是 `above₀`, `above₁` 的记号比较, 树侧由 `readT` 给. **这个结论没有由树带路**: 我是看 `cloA` 的定义与记号的基本列对出来的, 而 `cloA` 的形状当初也是看记号定的.
>
> **第一个障碍.**
>
> 1. **层号要走出 `Ordᴵ`.** 守卫是 $\tau+1\sqsubseteq^\mathsf I\eta$, 两边都在 `Ordᴵ`. $\psi_0(\Omega_{\Omega_2})$ 的链点是 $\psi_1(\Omega_{u})$ (`s₄`, `reach₅`), 分支的 $u$ 是第 1 层的值, 不在 `Ordᴵ`. `O c φ` 的 $c$ 是 `Ordᴵ`, `Ordᴵ` 没有共尾元 (`no-topᴵ`), 所以这个站点的树写不出 $\Omega_{\Omega_2}$. 要的是: `GL` 那样的层号 (`no-read-GL` 说它还要守卫), 目标 1 的折叠回读 ($\hat F$), 以及 $\hat F$ 的 `WF` (`good-feed`). 这些都没有, 这里也没有写. 这是判断, 没有编译的否定.
> 2. **过 $\Omega\cdot2$ 的界.** `noW`, `noCert₂` 对 `UniformLv` 的树成立, 而每个目标都要先过 $\psi_0(\Omega_{\Omega\cdot2+1})$ (`reach₉`). 这归 `ScafLadder*` 处理, 我没有重复.
> 3. **标签.** `¬NF-t₁`: 这些项不在 `NF₁`. 标签定理要标准形的扩充, 这与树无关.
>
> 所以我没有试 $\psi_0(\Omega_{\psi_1(\Omega_\Omega)})$, $\psi_0(\Omega_{\Omega_2})$, $x_3$ 的标签, 也没有用模块参数写它们的条件形式: 那样的参数就是结论本身, 不提供信息. 没有两个设计败在同一点这回事, 因为往上一个设计也没有写.
>
> **壁垒 (判断, 没有形式对比).** 这里没有新的树, 用的是已有的 `Ordᴵ`, `Ordˢ`. `Ordᴵ` 有 `<ᴵ-dec`, 没有共尾元 (`no-topᴵ`), 不是壁垒的形状. `ŝ` 不是可数层的 $\hat\Omega$ 构造子 (`loop` 挡的那个): 它有分支函数, 定义域受支配, 第 0 层要证书才计值 ([Prefix](Prefix.lagda.md)). 全局三歧没有用到 (`¬G-tri`).
>
> **审计 (`depslice.py`, 语法级).** `Family:G-excl`, `Family:no-read-ᴵ`, `Family:cmpW`, `Node:good-ω⁺`, `Node:first-above`, `Node:through`, `GL:no-read-GL`, `GL:Gᴸ-excl` 到达的记号定义都是 0 (`good-ω⁺` 到达 681 个定义块). 正对照 `Site:site-label`, `Site:site-labelᴺ` 都是 241. 切片看不见 Agda 求解的隐式参数; 模块层面的导入不干净, `Node` 经 `Uniform3Base` 的导入链含 `OCF.Align.EBO`.
>
> 全文 `--safe --without-K` (`Family`) 或加 `--lossy-unification` (其余), 无公设、无洞、无停机或正性编译指示. 没有模块参数作假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafOmega2 where

open import OCF.Align.ScafOmega2Family using (yᴵ; no-read-ᴵ; G; G-rise; G-suc; G-up; G-excl; G-y-in; G-unbounded; cmpW; ¬G-tri)
open import OCF.Align.ScafOmega2Node using (module Node; first-above; good-ω⁺; through)
open import OCF.Align.ScafOmega2GL using (em; WF-em; y∈GL; no-read-GL; Gᴸ-rise; Gᴸ-excl)
open import OCF.Align.ScafOmega2Site using (site; site₀; site-label; site₀-label; site-labelᴺ; site₀-labelᴺ; nf-site; site-bnd; one<arg; reach₁; reach₅; reach₉)
open import OCF.Align.ScafOmega2Accept using (head-c; agree-site; deep; ctl)
```
