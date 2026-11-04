# 跨树的桥: 把 `T₀` 的证书推过闭包 (判决: BLOCKED)

> 文件: [GuardBridgeTree](GuardBridgeTree.lagda.md) (改一行的折叠 `T₀′`), [GuardBridgeZ](GuardBridgeZ.lagda.md) (`≲ᶻ`, `Good-≲`), [GuardBridgeNeg](GuardBridgeNeg.lagda.md) (否定), [GuardBridgeAccept](GuardBridgeAccept.lagda.md) (有限测试, 只有它读记号). 接 [GuardTight](GuardTight.lagda.md), [GuardTightCert](GuardTightCert.lagda.md).
>
> **判决: BLOCKED. 上一轮判断的桥 ("证书要 $c_0\sqsubseteq$ 对面的界") 走不通, 连 $\psi_0(\Omega_{\Omega+1})$ 都走不通. 这棵树上没有新的证书: $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega+\eta})$, $\psi_0(\Omega_{\Omega\cdot2})$ 都没有. 两个设计败在同一点 (闭包的界 $\sqsubseteq$ 对面的界), 按约定停下. 没有证明 `T₀` 没有 `Goodᴺ`: 否定只杀写明的桥.**
>
> **编译过的定理 (无条件, 无模块参数作假设).**
>
> | 定理 | 文件 | 陈述 |
> |---|---|---|
> | `Good-≲` | [Z](GuardBridgeZ.lagda.md) | `x ≲ᶻ y → (G′ : Goodᴺ y) → Σ (Goodᴺ x) λ G → forceᴺ x G ≅ forceᴺ y G′`. 对面的证书搬过来只要界 $c\sqsubseteq c'$, 分支在同一个 $\eta$ 上. `Goodᴺ-c` 的递归版本 |
> | `T₀-too-high` | [Neg](GuardBridgeNeg.lagda.md) | `T₀ (suc c₁) ≲ᶻ toZ (ψ̄ (Ω̇ 1) …) → ⊥`. 这里界 2, 对面界 1 |
> | `floor-gap` | [Neg](GuardBridgeNeg.lagda.md) | `Bd (bound (fk ω ⊔ fk 0) …) ⊑ᴵ Bd (bound (fb ω ⊔ fk 0) …) → ⊥`. 表的路线的地板对对面的地板, $L=\omega$ |
> | `no-join` | [Neg](GuardBridgeNeg.lagda.md) | $L=\lim 2n$, $\eta=\lim(2n+1)$: `L⊑η`, 但 `Σ X, L <ᴵ X × η <ᴵ X → ⊥` |
>
> **第一个障碍 (`T₀-too-high`): `owk` 这一行.** `ψ E T st (owk w x)` 收窄了输入, 没有收窄输出. 一个闭包过两遍折叠 (第 2 项: $\psi_{\Omega_\Omega}(\psi_{\Omega_\Omega}(\ldots))$), 第二遍保留它时, 它的上下文是整个 $\rho$, 含它不依赖的外层帧, 计值时读成地板. 这一点是判断, 由测试支持: `T₀′` 只改这一行, 同一条路径的界变回 1, 深度 10, 宽度 3 与塔一致. **上一轮的 `agree` 宽度是 2, 走不到第 2 项, 所以没有看到.**
>
> **第二个障碍 (`floor-gap`, `lim-u`, `lim-f`, `lim-q`), 这是真正的卡点: 表要字面的证据.** 帧的分支值是极限 $L$ 时, 表的证据是 `pr L <ᴵ ℓ`, `pr L = L`, 所以地板是 `fk L`, 界 $L+1$. 对面 (与塔) 的地板是 `flo L = fb L`, 证据只是 `Simᴵ L ℓ`, 界 $L$. 差这一步. `floor-gap` 是这个差别的定理; 这样的闭包确实在树里是有限测试 (`lim-u`, `lim-f`, 路径 `p₁`): 判断, 帧 $\omega$ 由 $W\oplus(\cdot+1)$ 的 `rep` 留在左边, 右边的闭包读到它. 这条路径写成 `≲ᶻ` 的否定时合一耗尽了 6 GB 堆, 所以对 `T₀′` 的 `≲ᶻ` 不成立是测试, 不是定理. `no-join` 说明不能简单地把界降到 $L$: 分支 $\eta$ 上只有 $L\sqsubseteq\eta$, 而 $L,\eta$ 可以没有字面公共上界, 新表的世界造不出来. 这与 [Barrier](../Barrier.lagda.md) 的后果同形: 有字面公共上界就可比.
>
> **于是 `≲ᶻ` 到 `OCF.Free` 不成立 (`T₀` 是定理, `T₀′` 是测试). 到塔 ([LadderNFTree](LadderNFTree.lagda.md)) 也一样 (`lim-q`, 测试): 塔的这个界也是 $\omega$.** 上一轮 "再往上桥到 `LadderNFTree`" 的判断受同样影响.
>
> **有限测试 ([Accept](GuardBridgeAccept.lagda.md), 全部 `refl`, 不是证明).**
>
> | 测试 | 比较, 深度, 宽度 | 结果 |
> |---|---|---|
> | `t-q`, `t-f` | `T₀` 对塔, 对对面, 10, 3 | 第一个差别: 路径 `pth₀`, 2 对 1 |
> | `t-q₂` | `T₀` 对塔, 10, 2 | 一致 (对照: 窄的宽度看不到) |
> | `u-q` | `T₀′` 对塔, 10, 3 | 一致 |
> | `u-kind` | `T₀′` 对 EBO, `dfZ` 12, 2 | 种类一致 |
> | `lim-u`, `lim-f`, `lim-q` | 路径 `p₁` 的界 | $\omega+1$; 对面 $\omega$; 塔 $\omega$ |
>
> 更高处没有结果: `T₀′` 对塔, $\Omega+2$ 与 $\Omega\cdot2$, 深度 9, 宽度 3, 都超过 9 分钟超时, 不算一致也不算不一致.
>
> **判断 (没有编译).**
>
> 1. `T₀`, `T₀′` 有没有 `Goodᴺ`: **未知.** 要 $L+1\sqsubseteq$ 链, 即 $L\prec$ 第一支的层号. 对面只给 $L\sqsubseteq$ (`Dem` 对 `fb`). $L\sqsubseteq Y\prec X$ 推不出 $L\prec X$: `⊑ᴵ` 是内涵的, 要 Bachmann 型的性质才行, 这里没有.
> 2. 下一步的设计 (没有写, 没有测): **帧只留弱证据 `Simᴵ a ℓ`, 地板用 `flo a`, 比较时先规范化节点的路径.** 紧的 `Tc` 下节点的路径规范化之后, 分支值总是后继 (`rec-exact`, `mark-exact`), `pr (b+1) = b` 从 `Simᴵ (b+1) ℓ` 就有字面的证据, 而 `a ⊲ L` 的 `⊲ˢ` 本来就只要 `Simᴵ L ℓ`. 所以 `bra`/`bra` 这一行比较规范化后的后继值, 不读字面的 $L$. 这样界与对面一致, `no-join` 不挡它. 要重写 `Evd`, `cmpN`, `cmpK`, `keepP`, `pick` 的 `bra` 行, 判断约 300 行定义; 然后才轮到桥本身.
> 3. 桥本身的形状 (纸面, 用过的结论: 地板只来自目标路径与帧, 关系要分低层 `Ordˢ` 与高层 `O α φ` 两个, `Inv`: 无证据的帧的键在目标里; `rep` 左右结合不同要一条结合律): 判断约 1500 行, 不是 500 行.
>
> **逐阶段的输入.** `T₀′`: 与 `T₀` 相同 (树没有, `Tc` 按闭包形状). 证书: 没有. **读了记号的 (如实).** 定义 `T₀′` 与 `Good-≲`, 否定都不读记号. `owk` 这一行的改法是看 [ScafLadderQ](ScafLadderQ.lagda.md) 与 `OCF.Free.Tree` 同一行定的, 塔是树, 但塔的形状来自记号; 差别是用塔与 `OCF.Free` 找到的, 不是树侧判据给的.
>
> **壁垒.** `no-join` 是在壁垒之内的现象. 没有全局三歧, 没有全分支比较. 上面的下一步设计也只比较字面上界之下的值 (判断).
>
> **审计.** 切片 (语法级): `T₀′`, `Good-≲`, `T₀-too-high`, `floor-gap`, `no-join` 到达的记号块都是 0; 正对照 `GuardBridgeAccept:u-kind` 读到 `EBO`. `importclosure.py` (编译器保证): `GuardBridgeTree`, `GuardBridgeZ`, `GuardBridgeNeg` 闭包干净. `GuardBridgeAccept` 读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardBridge where

open import OCF.Align.GuardBridgeTree using (T′; T₀′; module Fold′)
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; Good-≲)
open import OCF.Align.GuardBridgeNeg using (T₀-too-high; floor-gap; no-join)
```
