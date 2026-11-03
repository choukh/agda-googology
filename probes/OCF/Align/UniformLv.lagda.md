# 层号上的数据树: 分支带证据, 判决读证据 (判决: PARTIAL)

> 接 [InaccFloor](InaccFloor.lagda.md), [InaccTheta](InaccTheta.lagda.md), [Uniform5Syn](Uniform5Syn.lagda.md). 底座 [UniformLvBase](UniformLvBase.lagda.md), [UniformLvTree](UniformLvTree.lagda.md), [UniformLvTheta](UniformLvTheta.lagda.md), [UniformLvNeg](UniformLvNeg.lagda.md), 测试工具 [UniformLvWalk](UniformLvWalk.lagda.md) 都不用记号的定义 (切片见文末). 记号只在验收节 [UniformLvAccept](UniformLvAccept.lagda.md).
>
> **判决: PARTIAL. 定义一侧的树写出来了, 没有 `S`, 没有 `Syn` 的项文法, 种类检验过了 $W$ 与 `Zero.dev` 的位置, 也过了 $\Omega\cdot\omega+\Omega\cdot2$. 证书一侧: 新树上没有任何 `Goodᴺ`, 决定性目标一个也没有证. 第一个设计 (一个 $\ell$ 装下全部地板) 被编译的否定 `noAll` 打掉了; 第二个设计 (地板按高度分开) 要一个高度标签, 这是逐层输入.**
>
> **比较的答案从哪来 (任务 1 的问题).** 不是单从 "字面界含链点 $x$". [Uniform5Syn](Uniform5Syn.lagda.md) 的 `fk τ`, `ac` 是这个答案, 而它不对: 同一个 $\ell$ 同时要装两类东西, 比较要的上界, 与闭包为了造新世界而要求链点支配的东西. 所以答案分三件:
>
> 1. 比较本身: `<-dec` (`UniformLvBase` §4), 对层号结构递归, 输入是层号的 `WF` 证书与两条路径的字面证据 `Adm`, 输出的路径带**对一切世界**的可容许性转移. 从不测试原始树, 没有全局判决函数.
> 2. 证据的来源: `lcl h g` 的分支在 `Ordᴵ` 上, 每个分支 $\eta$ 由闭包绑定, 地板 `tk h η` 说 $\eta<w\,h$. 目标的证据是目标自带的地板 $\chi$.
> 3. 世界是一族 $w:\mathbb N\to$ `Ordᴵ`, 按高度分开: 第 $h$ 层的闭包只收第 $h$ 层的地板 (`prj h π`), 只改第 $h$ 层的世界 (`cloᵗ`). 高度不同的参数从不比较, 所以不需要公共上界.
>
> **编译过的定理.**
>
> - `<-dec`, `≈-move`, `shL`, `shR`: 有证据就三歧, 输出的路径带转移. `≈` 是部分等价, `o≈` 是关系式的, `L ≈ L` 是合法性的一部分.
> - `WF-⊞`, `WF-times`, `WFΩ`, `WFΩ·ω`: $L+a$, $L\cdot\Omega$, $\Omega\cdot m$, $\Omega\cdot\omega$ 的证书. 单调对一切 $\eta$ 成立, 比 [InaccFloorBase](InaccFloorBase.lagda.md) 的世界版强.
> - `Fold.ψᵒ`, `Fold.ψ̄`, `Ω̇`, `T₀`: 对任何带证书的层号 $L$ 一个定义. 没有对阶段的归纳. 证书是折叠的参数, 不存进树.
> - `F : Ordᴵ → LI`, `Lv₅`: $\theta\mapsto\psi_1(\Omega_\theta)$ 对一切 $\theta$, 没有判决参数: 目标 1 看头, 链的目标与节点都是 $\theta$ 的字面前驱, 比较是 `<ᴵ-dec`. 这是 [InaccTheta](InaccTheta.lagda.md) 的判断 "分支带证据, 判决读证据" 的一个实例, 它不撞 `no-uniform`, 因为分支不是原始树. **只有定义, 没有 `WF`.**
>
> **编译过的否定.**
>
> - `noAll`: `Uniform5Syn` 的 `ι↓` 把地板 `flo K` 加到闭包上, 界就不低于 $K$ (`Bd-K`), 而 `Goodᴺ` 的 `gc` 要界不高于第 0 个链点 (`clo⊑`), 第 0 个链点与 $K$ 无关 (`F-≈`). 所以 `Clo K` 不能对一切 $K$ 都有 `Goodᴺ`. **这不是旧结论的推论, 是对 `Q` 路线的修正**: `Q` 的 `firstBad` 只走闭包的第 0 个孩子, 种类检验看不见它. 对比: `GᴺΩ̇ η` 对一切 $\eta$ 成立, 那棵树的闭包没有这项地板.
> - `base⊑zero`: `⊑` 只看路径, 看不见原子 `base`. 所以 `P̂⊑` 不能照搬到 `LI`, 这是 `Lv₅` 的 `WF` 的第一个技术障碍.
>
> **对 `TQ 1 zero` 本身 (判断, 未编译).** $\psi_0(\Omega_{\Omega\cdot2})$ 的 `Q` 树: 第 0 个链点 $\eta_0$ 处的分支走到底是闭包, 地板 `flo η₀`, 所以 `Goodᴺ` 推出 $\eta_0\sqsubseteq$ `lvG` $(\psi_0(\Omega_1))$. 这在数值上是假的, 但我只编译了 "对一切 $K$" 的形式, 没有编译这一个实例: 它还要 $\psi_0(\Omega_1)\prec\eta_0$ 的严格性. 所以写 "`TQ` 没有证书" 是判断.
>
> **有限测试 (验收节, 都是 `refl`).**
>
> | 目标 | 层号 | 比较器, 深度, 宽度 | 结果 |
> | --- | --- | --- | --- |
> | $\psi_0(\Omega_{\Omega\cdot2})$ | `Ω· 2` | 精确, 14, 2 | 一致 |
> | $\psi_0(\Omega_{\Omega\cdot2+1})$ | `suc (Ω· 2)` | 精确, 16, 2; 12, 3 | 一致 |
> | $\psi_0(\Omega_{\Omega\cdot3})$ | `Ω· 3` | 精确, 14, 2 | 一致 |
> | $\psi_0(\Omega_{\psi_1(1)})$ | `Ω·ω` | 精确, 12, 3 | 一致 |
> | $\psi_1(1)+1$, $+\Omega$, $+\Omega\cdot2$ | 同上加 `suc`, `times` | 精确, 10, 2 | 一致 |
> | $W$ | `Xw`, 直接由折叠写出 | 精确, 24, 1; 12, 2; 近似, 10, 2 | 一致 |
> | `Zero.dev` 的路径 | 同上 | 近似, 走到底再 4, 2 | 一致 |
> | $W$ 型分支, $\eta=1,2,3,\omega$ | 目标 $\Omega+1$, 节点 $\Omega+\eta$ | 精确, 8, 2 | 一致 |
> | $\psi_0(\Omega_{\psi_1(\Omega_\theta)})$, $\theta=1,2,3,\omega$ | `F θ`, 证书是变量 | 精确, 20, 2 | 一致, 证书未被问到 |
> | 第 5 站 | `Lv₅`, 证书是变量 | 精确, 20, 2; 10, 3 | 一致, 证书未被问到 |
> | 第 5 站走到 $\psi_0(\Omega_{\Omega\cdot2+1})$ | 同上 | 项相等; 精确, 2, 2 | 一致; 深度 3 处问证书 (探针) |
>
> "精确": 闭包只走第 0 个孩子, 不用链点. "近似": 第 $\ge1$ 个孩子用 `apx⁺`. 比种类之外, 还查 `ŝ` 必须对应 $\Omega$-共尾的尾巴 (`headBad`), 否则种类相同也可能走错位置; 第一版只比种类时确实漏掉过错位. `ctl₁`, `ctl₂`, `ctl₃` 是对照: 换分支值或换层号, 比较器报告不一致.
>
> **这些测试说不了什么.** 第一, 变量证书的两行只覆盖不需要比较的部分, 证书一被问到就走不下去. 第二, 从 $\psi_0(\Omega_{\Omega\cdot2+1})$ 沿 `p₂` 真正走到 $W$ 要穿过链点的内部, 近似 `apx⁺` 有部分和的噪声 (探针: 走到 $W$ 时闭包头随近似深度变化), 所以我没有把这条路径算作结果; $W$ 是直接用折叠写出的. 第三, 种类一致不是值相等, 也不说明闭包的界对: 这正是 `noAll` 的教训, `Q` 的树种类也全对.
>
> **第一个具体障碍, 两处.**
>
> - **定义一侧: 高度标签.** `lcl h g` 的 $h$ 是输入. 在 $\Omega\cdot m$ 上由 `ht` 算出, 在 $\Omega\cdot\omega$ 上每条路径只见有限个高度, 所以到这里够用. 第一个不够的地方是 $\psi_1(1)+\Omega$ (`times Ω·ω`): 它的分支里含一切 $\Omega\cdot n$, 而 `ht (lim f)` 只取 `ht (f 1)`, 外层与内层的 $\Omega\cdot2$ 同高度, 那就回到 `noAll` 的形状 (判断: 这个实例的否定没有编译; `prj-self` 只说同高度的项进界). 换一种逐层的编号能走得更远, 但 `Lv₅` 的分支里高度随 $\theta$ 无界, 外层没有自然数可用 (判断). 所以自然数标签不是一个定义. 一个不带编号的写法是拿层号自己作标签: 第 $M$ 层的世界, 查表时用外层世界比较层号. 这只是纸面设想, 我没有写, 不知道它是否良定. **我没有往 `Syn` 退: 这里报告, 不修.**
> - **证书一侧: 同高度的支配.** 目标的地板 `tk h τ` 落在同高度的闭包上时, 界真的要抬高, `gclo` 的 `dt`, `dg` 要链点支配 $\tau$. `Fl` 的地板平凡, 旧定理没有这个义务. 记号的标准形条件保证它成立, 但我没有树侧的证明. 这需要链点严格增长的不变量, `TopClo` 特意绕开了它 (判断, 未试).
>
> **任务 3: 证书.** 新树上的 `Goodᴺ` 一个也没有: 锚点 $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega\cdot2+1})$, $\psi_0(\Omega_{\Omega\cdot3})$, $\psi_0(\Omega_{\Omega\cdot\omega})$, $\psi_0(\Omega_{\psi_1(1)})$, $\psi_0(\Omega_{\psi_1(\Omega_\Omega)})$ 都没有. 没有移植 `UniformNF5*` (约 4300 行). 看行数, 其中直接碰层号结构的只有约 300 到 400 行, 但要改的不止这些: `Run` 换成 `Runᵗ`, 上下文的 `top` 换世界族, `gclo` 带高度, `pψ` 带目标地板与证书, 加 `oev` 的一行, 再加上面的支配义务. [InaccTheta](InaccTheta.lagda.md) 的 `Cert` 是 `PF S` 的树的层号证书, 不是 `F` 的, 也不能直接用: 它的世界是固定的 $\ell$, 这里的 `WF` 要对一切世界转移 (`tlt` 的路径要作树节点).
>
> **任务 4: 判据.**
>
> - 每阶段输入: 折叠, `Ω̇`, `F` 没有; 高度标签有. 层号的证书 (`WF`) 是定理, 不是输入, 但只到 $\Omega\cdot\omega$ 与它之上的 `times`.
> - 闭包定理对阶段无归纳: 无从回答, 新树上没有闭包定理. 定义本身没有对阶段的归纳.
> - 一个定义走到 $\psi_0(\Lambda)$: 没有依据, 不作断言. 已知缺口: 高度标签; `LI` 的分支只在第 0 层 (`no-Ω₂` 说参数层 $\ge1$ 的 `limᴼ` 作下标在那个设计里推出 WLPO, 第 4 站 $\psi_0(\Omega_{\Omega_2})$ 就要它); `F` 只有目标 1.
> - 还读了记号的: 定义没有读; 比较器, 路径 `p₁`, `p₂`, 项 $W$ 在验收节. 高度标签 $\Omega\cdot m\mapsto m$ 的形状是看塔的结构写的, 不算读记号的定义, 但也不算让树自足: 没有树侧的判据告诉我们标签该怎么取, 只有 `noAll` 说不取不行.
>
> **树侧逼出, 与读记号.** 树侧逼出: 高度分开 (由 `noAll`); 对一切世界的转移 (由节点要作树节点); `o≈` 关系式与 `L ≈ L` (由 `RΩ̇` 要跨 $\cong^\mathsf I$); 第一支 `fst` 不要 $1<\ell$ (由闭包的第 0 点). 读记号的: 任务给的路径与要比较的项; `lcl` 的第一支在 $\eta=1$ 沿用 `oclo`, 它的形状当初是看记号定的.
>
> **审计 (`depslice.py`, 语法级).** `UniformLvTree:T₀`, `UniformLvTheta:F`, `UniformLvBase:<-dec`, `UniformLvNeg:noAll` 到达的记号定义都是 0; 正对照 `UniformLvAccept:tBη` 是 48. 模块层面的导入不干净: `UniformLvTree` 经 `Uniform3Base` 的导入链含 `OCF.Align.EBO`, 用到的只是 `Flr`, `Ev`, `bound` 等不含记号的定义.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLv where

open import OCF.Align.UniformLvBase using (LI; WF; <-dec; WFΩ; WFΩ·ω; base⊑zero)
open import OCF.Align.UniformLvTree using (O; module Fold; Ω̇; T₀)
open import OCF.Align.UniformLvTheta using (F; Lv₅)
open import OCF.Align.UniformLvNeg using (noAll; clo⊑; Bd-K; prj-blind; prj-self)
```
