# 键即节点: 没有标签的一个定义 (判决: PARTIAL)

> 接 [UniformLv](UniformLv.lagda.md), [LvCert](LvCert.lagda.md), [EBOTop](EBOTop.lagda.md). 底座 [LvKeyBase](LvKeyBase.lagda.md), [LvKeyTree](LvKeyTree.lagda.md), [LvKeyTheta](LvKeyTheta.lagda.md), 陈述 [LvKeyClo](LvKeyClo.lagda.md), [LvKeyReach](LvKeyReach.lagda.md), 否定 [LvKeyNeg](LvKeyNeg.lagda.md), 上一层 [LvKeyStep](LvKeyStep.lagda.md), 都不用记号的定义. 记号只在 [LvKeyAccept](LvKeyAccept.lagda.md).
>
> **判决: PARTIAL. 高度标签这个逐层输入消掉了, 这部分是定理. 但这只解决了不同节点之间的问题; [LvCert](LvCert.lagda.md) 的反驳落在同一个节点上, 这个设计逃不掉 (第 3 步是这里的定理, 第 4 步是判断). 两个设计败在同一点, 按任务的规定停在这里, 没有写第三个. 种类检验全部通过, 但它们不看界, 不算证据.**
>
> **世界的接口 (`LvKeyTree` 开头).** `w = wd ℓ₀ Ε`. `at Ε y ℓ` 是关系: 尊重 `≈`, 唯一, 界非零. 表 `Ε ▸ κ , X` 在 $y\approx\kappa$ 处是 $X$, $y\not\approx\kappa$ 处沿用旧表: **写下它不判定任何东西.** 判定只发生在闭包挑地板时 (`Sel.selF`), 由 `kdec` 读 `Evt` 里的字面证据. 与 [LvCertWorld](LvCertWorld.lagda.md) 的 `Worlds` 不同处: `prj` 要世界与证据, 所以 `Worlds` 不能字面实例化; `noSameᵏ` 是 `Core.noSame` 的对应.
>
> **任务 1: 断点 (编译).**
>
> - `noTimes`: `times Ω·ω` 上不能对一切 $K$ 有证书. 外层标签 1 (`tag-out`), 内层 $\Omega\cdot2$ 标签 1 (`tag-in`). 第 0 点与 $K$ 无关 (`free`, 用 [LvCertRel](LvCertRel.lagda.md) 的掩码互模拟). 判断 "第一次断在 $\psi_1(1)+\Omega$" 坐实, 只是 `Clo K` 是用树的运算造的, 不是从 `T₀` 走到的.
> - `noNest h cf`: 任何标签 $h$, 任何证书: 嵌套同标签就没有证书. 所以**标签必须把嵌套的节点分开.**
> - `noTag`: 尊重 $\cong^\mathsf I$ (由 `≈` 强制, `resp-of`) 且分开 $\prec^\mathsf I$ 的 $t:\mathsf{Ord}^\mathsf I\to\mathbb N$ 推出 WLPO. 所以**任何带判定相等的键都不行**, 不只是编号选得不好: $\theta\mapsto$ 节点的键必须读证据. 证明只用 $\mathbb N$ 的判定相等, 对其他判定相等的类型同样写得出 (判断).
>
> **任务 2: 设计 (编译).** `LI` 没有标签. 键是节点在顶层 $c$ 里的位置 `Cp (lcl g) c`, 由 `Ω̇ᵖ` 沿下降算出, 没有编号要选. `kdec`: 两个键, 同一张表里的证据, `WF c` $\Rightarrow$ 相同或不同. 对 $c$ 结构递归, 比较分支用 `bel-dec` (`<ᴵ-dec`), 搬运用新义务 `⊑ᴷ`; 节点与其下的节点不同是 `irr`. 对照壁垒: 输入是字面证据, 不是原始层号, 所以不撞 `¬tri`, `dec-A→WLPO`, `no-uniform`; `noTag` 正是说这个证据省不掉. `noAll` 的情形: `free` ($K$ 是变量, `refl`) 说不同节点的地板不进界. 同节点的进界: `same-in`, `sel-in`.
>
> **任务 3: 种类检验 (有限测试, 比较器与 [UniformLvAccept](UniformLvAccept.lagda.md) 是同一套).**
>
> | 目标 | 层号 | 比较器, 深度, 宽度 | 结果 |
> | --- | --- | --- | --- |
> | $\psi_0(\Omega_{\Omega\cdot2})$, $\Omega\cdot2+1$, $\Omega\cdot3$ | 字面 `WF` | 精确, 14 到 16, 2; 12, 3 | 一致 |
> | $\psi_0(\Omega_{\psi_1(1)})$, $+1$, $+\Omega$, $+\Omega\cdot2$ | 字面 `WF` | 精确, 12, 3; 10, 2 | 一致 |
> | $\psi_1(1)+\Omega$, $+\Omega\cdot2$, 第 $\ge1$ 个孩子 | 字面 `WF` | 近似, 6, 2 | 一致 (`c-ω2⁺`, `c-ω3⁺`, 跑真的 `selF`) |
> | $W$, `Zero.dev` 的路径 | 字面 `WF` | 精确, 24, 1; 12, 2; 近似, 10, 2; 走到底再 4, 2 | 一致 |
> | 分支值 $\eta=1,2,3,\omega$ | 字面 `WF` | 精确, 8, 2 | 一致; 3 条对照报告不一致 |
> | $\theta=1,2,3,\omega$, 第 5 站 | **证书是变量** | 精确, 20, 2; 10, 3 | 一致, 证书未被问到 |
>
> 这些测试说不了什么: 精确比较器只走闭包的第 0 个孩子; 变量证书的行不碰比较; 全都不看界. **[LvCert](LvCert.lagda.md) 的 `noCert₂` 说旧树种类全对而没有证书, 这里的种类一致同样不说明有证书.** 第 5 站没有实际的 `WF` (`F` 的 `WF` 没有写). `p₂` 走到 $W$ 没有做, `apx⁺` 的噪声没有修.
>
> **第一个障碍: `noW` 的形状.** 按协调者的要求先测这个.
>
> 1. 第 3 步是定理: `noSameᵏ`: 对任何位置, 任何世界, 地板项键 $\approx\kappa$ 时 `Goodᴺ` 推出第 0 点的层号 $\succ K$. `pick-in` 里 `kdec` 不可能答 "不同".
> 2. 两个键是字面同一个位置: `same-P₂`, `ι (db τ P₂)` 的项键 `P₂` 就是 $W=\dot\Omega_D$ 的闭包的键. 换键逃不掉. [LvCert](LvCert.lagda.md) 对这一点的判断, 在这里成立.
> 3. 有限测试 ([LvKeyReach](LvKeyReach.lagda.md)): 沿 `noW` 的路径, 字面 $\tau=2$ 时确实走到 $W$ 的闭包 (`c-W₂`). 界的数值没有算: `toN` 强制 `Bd` 跑了 10 分钟没有结束, 这个测试删了.
> 4. 第 4 步 (第 0 点与 $\tau$ 无关, 层号 $\sqsubseteq\tau$) **没有移植**: [LvCertRel](LvCertRel.lagda.md) 是对旧树写的, 新树的 `Rel` 要处理 `selF` 跨世界的一致. 所以 "这棵树的 `T₀` 没有 `Goodᴺ`" 是判断, 不是定理. 我认为它成立.
>
> **这说明键与紧地板是正交的两件事 (判断).** 键解决: 地板不属于这个节点, 却进了界. `noW` 的问题: 地板属于这个节点, 但数值是穿过的分支 $\tau$ 而不是目标的 $a$. 修后者的方向见 [LvCert](LvCert.lagda.md) 的 `at a`, `oup`. 那个修法要 `g` 不是黑箱; `noTag` 与 `noTimes` 说的事不因此消失, 键还是要的.
>
> **任务 4: 参数层 $\ge1$ (编译, 只有层号一侧).**
>
> - `no-↑`: 在 `LI` 现有的 `⊑` (转移对一切表) 下, $\Omega+3\sqsubseteq\Omega\cdot2$ **是假的**. 所以 `lcl` 不能直接取 $x\mapsto x$. `times` 能取是因为 `L ⊞ η` 的路径搬动不产生新分支.
> - `Step : Sys → Sys`: 下一层. 分支的定义域是 `GL` (层号 + `WF` + 自反), 比较局部于世界 (`Pre`), 由上一层的 `tri` 回答 (`tri′`). `Ωnext`, `WF-Ωnext`, `self-Ωnext` 对**任何** `Sys` 成立, 所以 $\Omega_2$ (`Cf₂`), $\Omega_3$ (`Cf₃`) 是同一个定义的实例. `c₁`, `c₂` 是跨分支比较的有限测试.
> - 与 `no-Ω₂`, `no-all-branch` 的关系: 那里 `limᴼ` 的分支是原始树, 好谓词要对全部分支负责. 这里分支的**类型**就是好的, 与 `Ordᴵ` 的 `lim` 自带步进同形, 所以量词只跑好输入. 代价是比较局部于世界. 这不矛盾: 原始的 $E\,a$ 族要进 `GL` 就要给 `WF`, 比较要给字面路径, 不能一致地给出.
> - **没有做:** $\psi_0(\Omega_{\Omega_2})$ 的树与种类检验. `kdec` 没有写到 `Step`. 还差的是: (a) 局部的转移意味着节点的可容许性不能对一切世界, 所以地板要在运行时增长 (判断, `oev` 返回 $\Sigma\rho$); (b) 值类型要带分支在 `GL` 上的闭包, 链点由目标 1 的折叠回读 ($\hat F:L\mapsto\psi_1(\Omega_L)$), 它要 `WF` 对 $\hat F$ 封闭, 这正是 [EBOTop](EBOTop.lagda.md) 的 `good-feed`; (c) `noW` 的问题在这里同样存在 (判断).
> - **覆盖塔吗.** `Step` 覆盖自然数层. $\Omega_{\Omega_\eta}$ 要对 $\eta\in\mathsf{Ord}^\mathsf I$ 递归, 极限处要余极限, 没有写; 再往上下标是层号本身 (判断: 那是 [LvIRBase](LvIRBase.lagda.md) 一路的归纳-递归). `Step` 是接口上的证明模式, 我不声称它是最终定义.
>
> **任务 5: 判据.**
>
> - 每阶段输入: 折叠, `Ω̇ᵖ`, `F`, `Lv₅`, `Ωnext` 都没有. 高度标签没有了.
> - 还有的: 层号的 `Cf` (`WF` 与自反). 对 `Ω·m`, `Ω·ω`, `times`, `Ωnext` 是定理, `F` 没有. 新增义务 `⊑ᴷ`, 对 `⊞` 是免费的 (`monoK⊞`).
> - 能否对角化到 $\psi_0(\Lambda)$: 没有依据. 这棵树过不了 $\Omega\cdot2$ 的证书 (判断), `Step` 只到自然数层.
> - 还读了记号的: 定义没有读. 比较器, 目标, $W$ 在验收节. `lcl` 第一支的形状沿用旧树, 当初是看记号定的. **树侧逼出:** 键要读证据 (`noTag`); 节点搬运 (`kdec` 的 `lim`, `lcl` 分支); 世界用关系 (更新不能判定); 比较局部于世界 (`no-↑`). 位置作键是我的设计, 不是逼出的.
>
> **编译过的否定一览.** `noTimes`, `noNest`, `noTag`, `no-↑`. **编译过的定理一览.** `kdec`, `irr`, `<-dec`, `at-uq`, `at-resp`, `WF-⊞`, `WF-times`, `WFΩ·ω`, `T₀`, `free`, `same-in`, `pick-in`, `sel-in`, `noSameᵏ`, `Step`, `WF-Ωnext`.
>
> **审计 (`depslice.py`, 语法级).** `LvKeyTree:T₀`, `LvKeyBase:kdec`, `LvKeyTheta:F`, `LvKeyNeg:noTag`, `noNest`, `noTimes`, `LvKeyClo:free`, `noSameᵏ`, `LvKeyStep:Step`, `Cf₃`, `no-↑` 到达的记号定义都是 0; 正对照 `LvKeyAccept:c-tω2`, `c-W` 是 48. 模块层面的导入不干净: `Uniform3Base` 的导入链含 `OCF.Align.EBO`; `LvKeyNeg` 导入旧树与 [LvCertRel](LvCertRel.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKey where

open import OCF.Align.LvKeyBase using (LI; kdec; WF; irr)
open import OCF.Align.LvKeyTree using (T₀; module Over)
open import OCF.Align.LvKeyTheta using (F; Lv₅)
open import OCF.Align.LvKeyNeg using (noTimes; noNest; noTag)
open import OCF.Align.LvKeyClo using (free; same-in; module KS; same-P₂)
open import OCF.Align.LvKeyStep using (Sys; Step; S₀; Cf₂; Cf₃; no-↑)
open import OCF.Align.LvKeyReach using (c-W₂)
```
