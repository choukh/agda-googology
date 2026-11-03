# 字面上界代替 `Syn`: 用树产生的层号作下标, 比较来自环境 (判决: PARTIAL)

> 接 [Uniform5Assess](Uniform5Assess.lagda.md), [InaccSingular](InaccSingular.lagda.md). 底座 [InaccFloorBase](InaccFloorBase.lagda.md), [InaccFloorTree](InaccFloorTree.lagda.md), [InaccFloorIter](InaccFloorIter.lagda.md), [InaccFloorLink](InaccFloorLink.lagda.md), [InaccFloorNeg](InaccFloorNeg.lagda.md) 不含记号, 导入链里没有 `OCF.Align.EBO`. 记号只在验收节 [InaccFloorAccept](InaccFloorAccept.lagda.md).
>
> **判决: PARTIAL. 不能替换 `Syn` 阶梯, 但 `Syn` 的两条理由有一条不成立.** "$\psi_1$ 的输出作下标必须把 `Acc` 带进定义" 是错的说法: 下标比较的证书是对树的结构递归, 在 $\theta=1,2$ 已编译. 另一条成立: 比较要证据, 证据不能从原始的树读出, 而链点的证据就是 `Goodᴺ`/`force`. 这个设计没有绕开它. 第 5 站本身 (对一切 $\theta$ 的 $\psi_1(\Omega_\theta)$) 的证书**没有**证出来; 数据树没有写; 标签没有.
>
> **已编译的事实.**
>
> 1. **`<ᴵ-dec` 为什么成立 (`Rel`).** 对公共上界 $c$ 结构递归. 两条路径在 `suc` 上剥; 在 `lim` 上用步进证据把一条搬到另一条的分支里. 它从不搜索, 用到的只有 $c$ 的字面结构. `<-decᴬ` 把这件事对可容许集 `A` 参数化: 只要路径碰到的分支在 `A` 里, 且 `A` 内有向, 比较就是定理, 输出的路径也可容许. `≈` 是不带互搬的 `≅`, 用它可容许性才保持.
> 2. **可容许集的三种取法.** 全体原始树: 假 (`¬WF-L₁`). 全体规整树: 也假 (`¬WF-Reg`), 所以 `Reg` 不是分支的证据, 它只在一个公共上界之内才够 (`dir-dec`). `ℓ` 的字面前驱 (世界 $\ell$, `Aℓ`): 成立. 这就是地板: `fk τ`, `ac` 说的正是 "在 $\ell$ 的字面前驱里".
> 3. **世界 $\ell$ 里的层号函数, 都不是语法.** `WF-+`: $L\mapsto L+a$. `WF-times`: $L\mapsto L\cdot\Omega$. `WFΩ·ω`. `cmpΩ` 是 Uniform5 的 `ψ≡` 的层号版, 字面界 $\Omega\cdot m+\ell$. `WFP̂`: $x\mapsto\psi_1(x)$ 保持证书, 对 $x$ 结构递归, 不用 `Acc`. `WF-Ψ₁Ω₂`: $\psi_1(\Omega_2)$ 有证书, 这是 Uniform5Wall §5 指出的 "$\theta=2$ 已是 $\psi_1$ 的迭代". 它只是自函数的 `iter`, 不要语法里含 $\psi_1$. `cmp-Ψ₁Ω₂`: 它之下的比较是定理.
> 4. **这些层号就是树的层号 (`link`, `link-F₂`).** `toLv (ψⁿ 1 x) ≈ P̂ (toLv x)`, 对任何 `S`. `toLv (F (natL 2)) ≈ Ψ₁Ω₂`. (`times` 只对 $L=0$ 与 `toLv (Ω 1)` 连上; $\Omega\cdot m$, $m\ge2$ 没有写这个连接.)
> 5. **带来源的折叠 (`PF`): 没有 `Syn`, 没有总判决.** `F θ` $=\psi_1(\Omega_\theta)$ 对**一切**原始 $\theta$ 是总函数. 判决不从 $(j,i)$ 反读: 有限目标看头 (`finD`, 对原始的 $j$ 都对); 目标是树层的字面前驱时比路径 (`lit`); 树层在目标之下时永远穿透 (`bel`). (判断, 未逐点核对: InaccSingular 的三类读数 `sub-*`, `rel-*`, `hid-*` 在目标是字面前驱时都变成路径比较, 不用读.) 只有两条路径落在同一个 `lim`/`limᴼ` 的不同分支上才问参数 `S`.
> 6. **验收 (`AllS`, 变量 `S` 的 `refl`, 所以这段路径上 `S` 没有被问到; 只比种类, 宽度与深度有限).** 起点, 第 4, 5 站, $\psi_0(\Omega_{\psi_1(1)})$, $\psi_0(\Omega_{\Omega\cdot3})$, $\psi_0(\Omega_{\Omega\cdot2+1})$ 都逐点一致 (深 3 宽 2), 中间各站由 `walkB` 走过, 再往 $W$ 走 20 步也是 (深 2 宽 2). 一致族 $\theta=2,3,\omega$, 以及下标自身是 $\psi_1$ 输出的 $\psi_0(\Omega_{\psi_1(\Omega_{\psi_1(\Omega_\Omega)})})$ 也一致. 走过闭包的 $n\ge1$ 孩子不要证书, 这一点比 Uniform5 的符号树强 (`firstBad` 走不到 $W$).
> 7. **`S` 不是摆设 (`Zero.dev`).** `S = rise` 走到 $W$ 仍对 (`reachW`, `atW`), 在 $W[0]$ 之下深度 10 处错.
> 8. **证据读不出来 (`dec-A→WLPO`).** 判定 "$x$ 在 $\omega+1$ 的字面前驱的像里" 推出 WLPO (以 `Funext` 为参数). 所以 `S` 不能先测 $x\in A$ 再用 `<-decᴬ`. 证据要由树带着.
>
> **第一个具体障碍, 两侧各一个.**
>
> - **定义一侧.** 路径 `take 30 (p₁ ++ p₂) ++ [1]` (探针: 对变量 `S` 不归约, 这不是编译的否定). 第 30 步的项是 $\psi_0(\psi_{\Omega\cdot2}(\Omega_{\Omega\cdot2}+\Omega_{\Omega+\psi_0(1)})[2])$, 手算: 它的第 1 个孩子的目标是 $\Omega+$有限, 节点是 $\Omega+x$, $x$ 是链点, 与 $W$ 同类, 早 10 步 (`S` 收到的那一对没有打印). $x$ 是折叠的输出, 要 $x\in A$ 就要 `force`, 就要 `Goodᴺ`.
> - **证书一侧.** $\theta=3$ (`¬WF-L₂`). `F (natL 3)` 的树有定义, 验收通过, 但输入的节点参数层是 1, `Aℓ` 在那里空, `P̂` 与 `WFP̂` 不覆盖. 第 5 站的层号 $\limᴼ\,0\,(x\mapsto\psi_1(\Omega_x))$ 的证书要对世界里的全部 $\theta$ 成立, 所以第 5 站的字面界现在**不是定理**.
>
> **任务 3 的回答.** 三个子句要折叠里没有的证据.
>
> | 子句 | 要什么 | 能否推迟 | 现状 |
> | --- | --- | --- | --- |
> | `suc`, `lim` 的输出作层号 | 步进 (`⊑ᴬ`) | 能, 它是闭层号的命题, 可作参数 | `WFP̂` 证到 $\theta=1,2$ |
> | `rise` 的链点作分支 | $x\in A$ | 不能在折叠里测 (`dec-A→WLPO`); 要把分支换成 `Ordᴵ` (`oclo`) 并在 `ĉ` 处 `force` | 没写; 这就是 `Goodᴸ` |
> | `pen` 的全称输入作分支 | $y\in A$ | 同上 | 没写 |
>
> **是否退回 `Goodᴸ`.** 两半的答案不同. 层号的证书是 `Good` 式的遗传谓词加闭包定理, 但只对结构递归, 不要 `Acc`, 也不要语法. 链点的证据就是 `Goodᴺ`, 这部分完全退回. 地板能给字面界: 折叠里每对比较都是最外层层号 $c$ 的两条路径 (`Mode`, `lit`), 所以公共上界始终是 $c$ 本身, 这一点不用证书 (判断: `lt` 模式把它写明了, 但 `sib` 丢掉了路径, 全程带路径的版本没有写). 缺的是 $c$ 的证书.
>
> **数据树没有写. 这是判断, 不是定理.** 假设里的 "数据树 `O` 加 `Lv`" 我只验证了层号一半. 要写它, 闭包分支必须在 `Ordᴵ` 上 (否则 `Aℓ` 的证据没有来源), 而 `toLv` 要的 `limᴼ` 分支在原始树上, 所以层号类型要换成分支在 `Ordᴵ` 上的中间类型 (本文的证明逐字可搬, 因为 `Aℓ` 已经只看 `em a`). `oev` 必须绑定 $\ell$: `Adm` 的证据只在这个 $\ell$ 成立, 所以 `oΩ` 的 "对一切 $\ell$" 的证据字段要收紧. 值层的 `cloA` 要的环境更新 (`Top`) 与 `oi` 的分层也要重写. 估计 400 行以上. 这些都不解决上面两个障碍, 所以没有继续.
>
> **一条对角线到 $\psi_0(\Lambda)$: 没有依据, 不作断言.** 层号的形成规则到这里是 3 个定理而不是逐阶段的语法, 这是好消息. 但 `WFP̂` 只有目标 1. 一般目标要 $P_j$, 输入带参数层 $\ge1$ 的节点, 这要第 $k$ 层的地板: 第 $k$ 层的字面上界本身是一个有证书的层号 (判断, 未编译).
>
> **过 $\psi_0(\Omega_{\psi_1(\Omega_\Omega)})$ 还剩什么.**
>
> 1. **本文的路 (推荐先试的一步).** 证 `F θ` 对一切 $\theta$ 有证书, 它是 `Uniform` 的 `HS` 定理在目标 1 上的版本. 先看 $\theta=3$: 只有一条链, 不需要第 1 层的 `dir`, 可以用 "分支对好输入单调" 代替 `Aℓ`. 这一步决定层号一半的命运.
> 2. **接受记号引导.** 用 `Syn` 加 EBO → OT_I 嵌入的 `Acc`, 作为看记号写的定义. 本文的新信息是: `Acc` 不是被 $\psi_1$ 逼出来的 (至少在 $\theta=1,2$), 所以这是选择, 不是必需.
> 3. **`Syn` 阶梯继续到 $\Omega\cdot\omega$ 为止.** `WF-times`, `WF-+`, `WFΩ·ω` 说这一段的层号比较在 `Lv` 上也是定理. `Q` 的标签路线不受影响.
>
> **来源.** 树侧逼出: `Rel` 与 `A` (由 `¬WF-L₁`, `noBT`), `≈` (由 `Adm` 不沿 `≅` 保持), `Mode` (由折叠的结构), `W₀` (由停机检查: `at y s` 不是子项). 读记号的: 任务给的路径 $p_1,p_2$ 与要比较的项; `times`, `⊞` 的取舍参考了 Uniform5 的 $(m,\alpha)$, 但 `P̂` 是由 `link` 确认的树折叠, 不是看记号写的. 判决 `S` 的语义规格来自 `<-decᴬ`, 不来自 `cmpᵀ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloor where

open import OCF.Align.InaccFloorBase using (module Rel; module World; module WorldN; Ω·_; Ω·ω; times; _≈_)
open import OCF.Align.InaccFloorTree using (Sib; module PF; finD; lit; Mode)
open import OCF.Align.InaccFloorIter using (P̂; Ψ₁Ω₁; Ψ₁Ω₂; module Iter)
open import OCF.Align.InaccFloorLink using (link; link-F₂)
open import OCF.Align.InaccFloorNeg using (¬WF-Reg; dec-A→WLPO; ¬WF-L₂)
```
