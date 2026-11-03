# 判决的规格: `CV` 能不能当树侧的正确性判据 (判决: PARTIAL)

> 接 [InaccTheta](InaccTheta.lagda.md). 底座 [VerdictSpecBase](VerdictSpecBase.lagda.md), [VerdictSpecTwo](VerdictSpecTwo.lagda.md), [VerdictSpecUniq](VerdictSpecUniq.lagda.md), [VerdictSpecEvid](VerdictSpecEvid.lagda.md), [VerdictSpecReject](VerdictSpecReject.lagda.md), [VerdictSpecFrame](VerdictSpecFrame.lagda.md), [VerdictSpecFloor](VerdictSpecFloor.lagda.md). 记号只在验收节 [VerdictSpecAccept](VerdictSpecAccept.lagda.md).
>
> **判决: PARTIAL. 对判决本身, 这是规格: 种类与树 (模 `Eq`) 都由正确性决定, 判决能由证书算出来. 对树, 它不是规格: `CV` 不提折叠, 所以错的折叠拒绝不了 (`wrong-fold`), 帧塔要靠折叠方程才拒绝, 旧地板是合法性的问题, `CV` 看不到. 字面的 `CV` 要放宽成 `CVx` 才能用, 定义域要限制在有好上界的层号对.**
>
> **编译过的定理.**
>
> 1. **唯一性.**
>    - 种类: `cv-kind`, `cv-kind≈`: 两个正确的判决种类相同, 对 $\approx^\mathsf{B}$-相关的层号对也成立.
>    - 树: `ψ≃` ([VerdictSpecTwo](VerdictSpecTwo.lagda.md)): 两个不同的 `S`, `S′`, 两个模式都 `OK`, 输入 `Eq`, 则输出 `Eq`. 关系是 `Eq`, 不是 $\equiv$: 路径不唯一 (`two-paths`, `paths≢`).
>    - 大数: 第 0 层的 `Eq` 给出 `FGH` 逐点相等 (`FGH≃`). 目标 0 要补一个前提 `CZ`: 第 0 层节点的链点在 `B₀` 里 (`ψ≃₀`, `T≃`, `Station5≃`).
>    - 非空: `two-correct`: `S₁ ≠ S₂`, 都正确, 都被问到, 树 `Eq`. 目标 0 且 `S` 真被问到的实例**没有**: 那要世界含链点, 也就是 `S` 对一个增长的世界正确. 目标 0 的实例只有 `T-nat`, 那里 `S` 没被问到. 所以 `Station5≃` 现在是条件定理.
> 2. **拒绝 `S = rise`, 不看记号.** `reject-rise`: $\Omega\cdot2$ 上目标 $\Omega+1$ 的模式不 `OK`, 因为目标里有字面的路径到 $\Omega$. `accept-S₁`: 只改这一对就 `OK`. `tree-S₀≠S₁`: 这一对真的改变树, 就在 `Zero.dev` 的路径上. 这一对就是 `S` 第一次被问到的 $(\Omega,\Omega+1)$. [InaccFloor](InaccFloor.lagda.md) 手算的是 "节点 $\Omega+x$, $x$ 是链点"; 实际第一次的 $x$ 是 1, 节点就是字面的 $\Omega$.
> 3. **证据给出判决.** `decide`: (`c`, `WFᴬ c`, `P0 c`, 两条可容许路径) $\mapsto$ 判决与它的 `CVx`. 它就是 `<-decᴬ`, 不测试. `first-is-S₁`, `second-is-S₁`: 在真实的第一对上, 算出来的就是手给的 `S₁`, `refl`. 上升的正确性不要 `WF`, 只要 `all-ac` (对一切层号的良基).
> 4. **放宽是必须的, 且不改唯一性.** `CVx` 允许搬运是 `coe⁺` (不要证据的总函数); `TL⁺`, `TR⁺` 说它在 $\approx^\mathsf{B}$ 时尊重 `Eq`. 字面的 `CV` 是特例 (`CV→CVx`, `LvG→x`).
>
> **编译过的否定.**
>
> - **`wrong-fold`, 关键的一条.** `PW` 把上升的链丢掉, 判决是同一个函数, `OK` 根本不提折叠, 所以它 "正确". 它与 `PF` 不 `Eq`, 对任何 `S`, `S′`, `B₀`. 这是判据单独拒绝不了的错树.
> - **`frame-rejected`.** 帧塔与 `PF` 在 $[1,0,0,1,0,0,0]$ 上头不同, 对一切 `S`: 这段计算不问 `S`, 拒绝它的是折叠方程. 帧塔的错不在判决.
> - **`floor-high`, `reject-floor`.** 旧地板: 第 2 份副本的闭包的证书要第 0 个链点的层号高于地板 $L$. 这是合法性 (`Goodᴺ`). `reject-floor` 以 "链点层号 $\prec L$" 为**前提**; 对真实的 $L_1$ 这个前提只由 [OmegaSqA](OmegaSqA.lagda.md) 的标签证过 (`Z≺L`). **所以旧地板的拒绝是条件的, 没有完全摆脱记号.** 判断: 旧树的比较都由 `<ᴵ-dec` 算出, 所以 `CV` 拒绝不了它, 这一点没有编译.
> - **`no-cv`.** 字面的 `CV` 有空的层号对: 两个 `limᴼ 0` 在 `B₀` 上相同, 外面不同, 没有判决正确. **`cv-total→ext`**: 字面的 `CV` 处处有解推出函数外延性的实例.
> - **`trap₁`, `trap₂`, `trap-tree₁`, `trap-tree₂`.** $\omega$ 与 $\omega'=[1,2,\dots]$ 互相 $\sqsubseteq^\mathsf{A}$ (`ω⊑ω′`, `ω′⊑ω`), 但 `CVx` 对 $(\omega,\omega'+1)$ 强制上升, 对 $(\omega',\omega'+1)$ 强制穿透, 树的种类不同. **`CVx` 比的是写法, 不是值.** `no-bound`: 这两个层号没有公共的好上界, 所以 `WF` 把这种对排除了. 判据要带定义域.
> - **`no-uniformˣ`.** 放宽之后一个拿原始层号对的 `S` 对一切 `Ordᴵ` 层号仍不能正确, 还是 WLPO. 证据不是字面性的产物.
> - **`reject-LvT`.** 同一个 `S = rise` 下 $\Omega\cdot2$ 整个层号不好.
>
> **有限测试 (只在验收节, 只比种类).**
>
> - `S₁` 在 `Zero.dev` 的路径上一致 (`dev-fixed`, 深 10 宽 2), 第 30 步 (深 5 宽 3), $W$ (深 6 宽 3), $W[1]$, $W[2]$ (深 7 宽 2). `Asked` 说 `Zero.dev` 的路径与 $W[1]$ 的这个范围里 `S` 只被问到两种形状; 脚本探针把它们读成 $(\Omega,\Omega+1)$, $(\Omega,\Omega)$, 这两对上 `S₁` 的正确性是定理. $x>1$ 的真实比较在这些宽度里没有出现, 只由下面的压力测试间接覆盖.
> - `Sₕ` (有限深度比较, **逐对的正确性没有证明**) 在十个下标对 $\psi_0(\psi_{\Omega+u}(\Omega_{\Omega+v}))$ 上一致 (深 6 宽 2).
> - `PF` 在帧塔与旧地板出错的项上一致 (`spec-frame`, `spec-floor`). `PW` 与 EBO 不符 (`wrong-is-wrong`), `PF` 相符 (`right-is-right`): `wrong-fold` 的正对照.
> - **没有找到判决正确而与记号不一致的树.** 任务 3 的答案是: 范围内没有反例, 这不是定理. 唯一找到的 "判决正确而树不一致" 是 `trap`, 它与值不一致, 不是与记号不一致 (记号里没有 $\omega'$), 而且没有好上界.
>
> **任务 4: 什么证据钉住判决.** 公共上界 $c$, 它的 `WFᴬ`, 两条可容许路径, 外加 `P0 c` (只有穿透的搬运要). `decide` 是最好的形式: 点态的函数. **折叠一级的函数没有写**: 折叠里的节点路径是原始的, 可容许性不能测 (`dec-A→WLPO`), `pen` 的分支要对原始的输入给值. 判断: 这要分支带证据, 也就是 [UniformLv](UniformLv.lagda.md) 的设计, 那边的 `lit` 就是这里的 `decide` 在 `Ordᴵ` 上的版本; 我没有把两者接起来.
>
> **边界.**
>
> - `toLv≃` 只到第 1 层: 第 $\ge2$ 层的节点层只 $\approx^\mathsf{B}$-相关, 而 `o≈` 要参数层字面相同. 所以嵌套下标上唯一性的传递也只到第 1 层的输出 (够第 5 站). 这一条是对定义的观察, 否定没有编译.
> - `bc` 带 `P0`: 参数层 $\ge1$ 的 `limᴼ` (如 $\Omega_{\Omega_2}$) 上 `coe` 的尊重没有证, 那里只认字面的穿透. 与 `no-Ω₂` 是同一个地方.
> - `CVx` 只认 `bl`, `bc` 两种搬运. 这是选择: 否则任意的 `b` 都算正确, 判据就管不住树. "尊重 `Eq` 的任意 `b`" 这种写法会让 `CV` 依赖 `Eq`, 而 `Eq` 经 `ND` 依赖 `CV`, 是循环的 (判断, 没有试编译).
>
> **树侧逼出的, 与读记号的.**
>
> - 树侧逼出: `CVx` 的 $\approx$ (`no-cv`); `coe⁺` 第 0 层是恒等 (要 `Bs` 不带条件地保持); `P0` (`coe` 的子句); 定义域要好上界 (`trap`, `no-bound`); `CZ` (目标 0 没有 `Zt`); `all-ac`.
> - 不是这里逼出的: **折叠方程本身.** $\psi(0)=\Omega$, 后继, 极限, 穿透, 上升的链, 来自 BTBO 与 `PF` 的定义. 这里只把它们当作规格的另一半, 没有从树侧导出. 判断: [OCFSpecRule](OCFSpecRule.lagda.md) 说每一行都是闭包规格的定理, 这可能是方程的树外来源; 没有接起来.
> - 读记号的: 路径 $p_1,p_2$ (抄成自然数列表, 陈述不读记号); `S₁` 要答对的那一对是跑探针发现的, 但它的正确性是 `CVx` 的定理, 不靠记号; `reject-floor` 的前提.
>
> **下一步该问谁.** 判决这一半够了, 可以当 `UniformLv` 的判据: 判决由证据算出, `CVx` 由构造成立. 树这一半缺一个 "折叠方程" 的正式陈述 (任何满足方程且判决正确的族都 `Eq` 于 `PF`), 以及 `reject-floor` 前提的树侧证明 (要把链点沿路径比较, 估计几百行, 判断). 这个选择应当交给作者.
>
> **审计 (`depslice.py`, 语法级).** `ψ≃`, `T≃`, `Station5≃`, `decide`, `no-uniformˣ`, `trap-tree₁`, `first-is-S₁`, `reject-rise`, `tree-S₀≠S₁`, `wrong-fold`, `two-correct`, `frame-rejected`, `reject-floor` 到达的记号定义都是 0; 正对照 `VerdictSpecAccept:spec-frame`, `VerdictSpecAccept:ck` 都是 48. 模块层面: `Base`, `Two`, `Uniq`, `Evid`, `Reject` 的导入闭包里没有 `OCF.Align.EBO`; `Frame`, `Floor` 有, 因为旧树的文件经过 `Prefix` 导入它, 这两个文件的文本不读记号.
>
> 全文 `--safe --without-K` (底座加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.VerdictSpec where

open import OCF.Align.VerdictSpecBase using (module Eqx; coe⁺)
open import OCF.Align.VerdictSpecTwo using (module Two)
open import OCF.Align.VerdictSpecUniq using (module Kinds; module Paths; module Uniq; module CZS; module Target₀; module Sanity)
open import OCF.Align.VerdictSpecReject using (module Reject; module Accept₁; accept-S₁; module TwoCorrect; tree-S₀≠S₁; module Wrong)
open import OCF.Align.VerdictSpecFrame using (module Spec)
open import OCF.Align.VerdictSpecFloor using (module Leaf)
open import OCF.Align.VerdictSpecEvid using (module NoCV; module LitExt; module Ev; module Trap; module TrapTree; module Real; module NegX)
```
