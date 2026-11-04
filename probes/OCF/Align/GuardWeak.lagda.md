# 弱证据的树: 帧只留 `Simᴵ`, 比较前规范化 (判决: PARTIAL)

> 文件: [GuardWeakTree](GuardWeakTree.lagda.md) (折叠), [GuardWeakRd](GuardWeakRd.lagda.md) (读法), [GuardWeakNorm](GuardWeakNorm.lagda.md) (规范化的定理, 否定), [GuardWeakRel](GuardWeakRel.lagda.md), [GuardWeakHi](GuardWeakHi.lagda.md) (桥的前两层, 不完整), [GuardWeakAccept](GuardWeakAccept.lagda.md) (有限测试, 只有它读记号与塔). 接 [GuardBridge](GuardBridge.lagda.md).
>
> **判决: PARTIAL. 树: [GuardBridge](GuardBridge.lagda.md) 提议的设计写出来了, 对塔的看界测试到下面的范围都一致, 包括上一轮的路径 `p₁`. 证书: 没有新的. $\psi_0(\Omega_{\Omega+1})$ 没有 `Goodᴺ`. 走到了一个具体的卡点, 有编译的否定 (`cover-false`), 见下. 没有证明这棵树没有 `Goodᴺ`.**
>
> **树的改动 (定义, 不含记号).** `Evd` 只留 `Belʷ` ($\mathrm{Sim}(a,\ell)$). 帧的地板 `flo a`. `cmpN`, `cmpK` 比较规范路径 (`nfR`, `nfK`). `prOf`: 规范分支的字面证据由支配它的帧的弱证据给. 输出的地板是路径自己的帧, 用 `ocv` 盖回. `pick` 分两半.
>
> **设计以外测试逼出来的两处 (读法, [GuardWeakRd](GuardWeakRd.lagda.md)):**
>
> 1. `xL` 要带 `Lk`. 否则模 $\approx$ 搬过的极限节点不下降, 帧留在 $\omega+1$, `p₁` 的界还是 $\omega+1$ (不是地板的写法, 是 `rxL` 把 `xL` 降成了 `xC`). [GuardRead](GuardRead.lagda.md) "第一个障碍" 第 3 条说 "没有测到差别", 这里测到了.
> 2. 节点 0 答第一支 (`zpos`), 不带帧. 否则 $\psi_1(1)$ 上路径 `L2 F L2 W1 L0 L0 L2` 这里 $\omega$, 塔 1.
>
> **编译过的定理 (无条件, 无模块参数作假设).**
>
> | 定理 | 文件 | 陈述 |
> |---|---|---|
> | `fn-rec`, `fn-rx` | [Rd](GuardWeakRd.lagda.md) | `Reader` 里: `NL k → FN (rx η e P)`: 后继与闭包节点只答 `xF`, `xN`, 一切 $\eta$ |
> | `rdV`, `rdΩ₁` | [Rd](GuardWeakRd.lagda.md) | 读位置的回答: `rdF`, 或 `rdB (suc b) …` 带 `Nw (G b) rep` |
> | `Tc-of`, `Tc-F`, `Tc-Lv₅` | [Rd](GuardWeakRd.lagda.md) | 与 [GuardReadRd](GuardReadRd.lagda.md) 同陈述, 对新读法 |
> | `nv` | [Norm](GuardWeakNorm.lagda.md) | `(r₁ : k < c₁) → k ≈ ⌜ j ⌝ → NV (suc r₁) j (nfR (suc r₁))`: 规范路径是 `suc (fst self)` ($j\cong0$), 或 `suc (bra (b+1) e self)`, $b\cong j$. 一切 $\eta$, 含极限 |
> | `belR-suc` | [Norm](GuardWeakNorm.lagda.md) | 帧有证据时, 后继分支的 `belR` 答 `just`. 只用弱证据 |
> | `no-guard` | [Norm](GuardWeakNorm.lagda.md) | $1\sqsubseteq\lim f\Rightarrow 1\sqsubseteq f\,n$ 假 |
> | `stays`, `¬ω2⊑ω`, `cover-false` | [Norm](GuardWeakNorm.lagda.md) | 节点 $\lceil\omega\rceil$ 在分支 $\omega\cdot2$ 里: 规范位置的第一个分支值还是 $\omega\cdot2$. 所以 "规范位置的分支 $\sqsubseteq$ 节点的层" 对一切位置是假的 |
> | `Rz`, `R-⊕`, `R-trO`, `R-tr⁻O`, `R-trˢ`, `R-tr⁻ˢ`, `R-ι`, `RΩ̇` | [Rel](GuardWeakRel.lagda.md) | [GuardTightCertRel](GuardTightCertRel.lagda.md) 的互模拟加上求过值的闭包 (`rŝ`, `rĉ`, `rĉŝ`), 界 $\sqsubseteq$ |
> | `fromRsP`, `fromRs`, `ι-Rc`, `RΩ̇₀`, `R⊕`, `≃as`, `rep≃`, `Tᴿ`, `rep-Rc` | [Hi](GuardWeakHi.lagda.md) | 闭包所在的层与 `FT.O` 的关系. `R⊕`, `rep-Rc` 要参数 `CvL` (函数的前提, 不是公设) |
>
> `Tc-F`, `Tc-Lv₅` 对新读法有定义与定理, 但这棵树在第 5 站上没有对塔的测试 (塔到不了), 也没有跑.
>
> **有限测试 ([Accept](GuardWeakAccept.lagda.md) 里的全部 `refl`; 比较器 `mis`, `chk`, 看界, 读数 `vE` 与字面形状无关).**
>
> | 目标 | 比较 | 结果 |
> |---|---|---|
> | $\psi_0(\Omega_{\Omega+1})$, 路径 `p₁` | `lim-w`, `lim-q`, `lim-old` | 这里 $\omega$, 塔 $\omega$, `T₀′` $\omega+1$ |
> | $\psi_0(\Omega_\Omega)$ | `mis 9 3 2` | 一致 |
> | $\psi_0(\Omega_{\Omega+1})$ | `mis 8 3 2` | 一致 |
> | $\psi_0(\Omega_{\Omega+2})$ | `mis 7 3 2` | 一致 |
> | $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega\cdot2+1})$, $\psi_0(\Omega_{\Omega\cdot3})$ | `mis 4 3 2` | 一致 |
> | $\psi_1(1)$ | `mis 5 3 2` | 一致 |
> | $\Omega+1$, $\Omega\cdot2$, $\Omega\cdot2+1$, $\Omega\cdot3$, $\psi_1(1)$ | `chk`, 随机路径, 长度 10, 39 条, 步子含 $\omega+j$, $\omega^2+j$ | 一致 |
> | 对照 | `ctl₁`, `ctl₂` | 比较器看得见不同的目标 |
>
> **没有写进文件的运行 (同一比较器, 在 scratch 目录, 编译器 `refl`):** `mis 10 3 2`: $\Omega_\Omega$ 46 秒, $\Omega+1$ 311 秒, 一致. `mis 8 3 1`: $\Omega+2$ 一致. `mis 5 3 2`: $\Omega\cdot2$, $\Omega\cdot2+1$, $\Omega\cdot3$ 约 6 分钟, 一致. `mis 6 3 2`: $\psi_1(1)$ 一致. **没有结果 (超时, 不算一致也不算不一致):** `mis 9 3 2` 的 $\Omega+2$, $\Omega\cdot2$, $\Omega\cdot2+1$; `mis 8 3 2` 的 $\Omega\cdot3$, $\psi_1(1)$; `mis 7 3 2`, `mis 8 3 1` 的 $\Omega\cdot2$, $\Omega\cdot2+1$; `mis 7 3 1` 的 $\Omega\cdot3$, $\psi_1(1)$; `mis 6 3 2` 的 $\Omega\cdot2$, $\Omega\cdot2+1$; 随机路径一条 (`u3`, 200 秒). **$\Omega\cdot2$ 以上穷尽只到深度 5, 这很浅; 深的部分只有随机路径.** 第二批随机路径 (scratch, 长度 14, 40 条, $\Omega+2$, $\Omega\cdot2$, $\Omega\cdot2+1$, $\Omega\cdot3$, $\psi_1(1)$ 各 8 条): 34 条一致, 6 条超时 240 秒 ($\Omega\cdot2+1$ 2 条, $\Omega\cdot3$ 4 条), 0 条不一致. `vE` 对 $\ge\omega^2$ 的界读数粗, 所以 `V` 探针对那样的界比不细.
>
> **证书: 为什么停在这里.** 选了桥 ($\Omega+1$ 对 [OCF.Free.Tree](../Free/Tree.lagda.md), 搬 `GᴺΩ̇`), 因为 `Gq` 整套搬过来约 8000 行. 写完的: 低层的互模拟 ([Rel](GuardWeakRel.lagda.md)), 闭包层的关系 `Rc`, 嵌入, $\dot\Omega$, 加法, `rep` 的结合律 ([Hi](GuardWeakHi.lagda.md)), 规范路径的形状 (`nv`). 没有写的: `R-ψ`, `R-ψᵒ` (折叠对 `ψ̄`, `ψᵒ`), 界的比较.
>
> **第一个障碍: 地板的盖住关系.** `Good-≲` 要 $c\sqsubseteq c'$. 这要 "左边闭包地板上每个帧的值 $\sqsubseteq$ 右边的地板" (`CvL`). 右边的地板在 `tl (up zero x)` 收窄到 `flo k′` (`owk`), 左边对应的收窄是 `ι` 的 `omk` 行 (`ocv`, 到规范位置的帧). 所以要一条定理: **规范位置的帧 $\sqsubseteq k'$.** 这是界一致的内容本身, 不是工程细节. 后继节点: `nv` 给了 ($b\cong j$). **极限节点: 假 (`cover-false`).** 原因是 `no-guard`: 分支 $\lim f$ 上的极限节点 $f\,n$ 不能成为分支, 字面的 $1\sqsubseteq f\,n$ 没有, 所以帧留在 $\lim f$. 判断 (没有编译): 这是过渡的, 极限层的 $\dot\Omega$ 只有 `ol`, 下一个 `omk` 又下降, 其间没有内容, 所以测试一致 (`V` 探针). 所以不变量要写成 "`os` 与闭包处" 的, 不能写成 "`rup` 处" 的, 而 `Rs` 的 `rmk (self n)` 要记下它是 $\dot\Omega$ 的像. 判断: 再要约 200 行改 `Rs`, 约 500 行写 `R-ψ`, `R-ψᵒ`, 才到 $\psi_0(\Omega_{\Omega+1})$; 没有写. 到 $\psi_0(\Omega_{\Omega\cdot2})$ 还要 `FT.ι` 的复合 ($\iota_r\circ\iota_q$ 对 $\iota_{r\circ q}$, 纸面, 用路径列表), 到 $\Omega\cdot2+1$ 要换到塔.
>
> **"形状不必改" 这个判断 ([LadderNF](LadderNF.lagda.md)): 没有被检验, 没有被证伪.** 没有搬 `Gq`. 但上面的障碍同样会出现在 `Gq` 的搬运里 (判断): `VisQ` 与 `Brq` 读的是界, 塔的 $\chi$ 的第 $n$ 格是 `flo k`, 这里是规范位置的帧, 两者只在 `os` 与闭包处才一致.
>
> **判断 (没有编译).** 1. `no-join` 确实不挡这个设计: 比较的两边都是规范位置的后继值, 它们的前驱是字面的 (`belR-suc`, `nv`). 2. `Tc` 的这两处修改不按阶段. 3. 第 5 站上没有测, 不知道树是否正确.
>
> **逐阶段的输入.** 树: 没有. `Tc`: 第 1 层的 `Rs` 项一个定理 (`Tc-of`), `Tc-F`, `Tc-Lv₅` 与 [GuardRead](GuardRead.lagda.md) 相同. 证书: 没有.
>
> **读了记号的 (如实).** 定义不读记号. 形状: 设计来自 [GuardBridge](GuardBridge.lagda.md) 的提议. 读法的两处修改是看对**塔**的差别定的 (塔的形状来自记号: `flo`, `up zero`, `up (self n)`). `Fold′` 的 `owk` 一行同上一轮. 树侧逼出的: `no-guard`, `cover-false`, `prOf` 的两种情形, `seed` (极限帧的种子要 $1\sqsubseteq K$).
>
> **壁垒.** 比较只读字面上界之下的值 (`bd` 仍是 `<ᴵ-dec`). `Simᴵ` 不进比较. 判断: 帧的值是极限时不比较, 所以 `no-join`, `no-lim-cmp` 不被触犯; 没有形式对比.
>
> **审计.** `importclosure.py` (编译器保证): `GuardWeak` (含 Tree, Rd, Norm, Rel, Hi) 闭包干净, 退出码 0; `GuardWeakAccept` 退出码 1 (读记号, 例外). `depslice.py` (语法级, 到达块数/记号块): `GuardWeakTree:T₀ʷ` 319/0, `GuardWeakNorm:nv` 362/0, `cover-false` 349/0, `GuardWeakHi:rep-Rc` 445/0, `ι-Rc` 430/0, `GuardWeakRd:Tc-Lv₅` 310/0, `GuardWeakRel:Rz` 118/0. 正对照 `GuardWeakAccept:k-11` 637/48.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无 trustMe. 模块参数: `FoldW` 的参数是层号与证书; `Reader`, `OfF`, 同 [GuardReadRd](GuardReadRd.lagda.md), 是读法的输入, 实例闭合. 没有条件定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeak where

open import OCF.Align.GuardWeakTree using (T₀ʷ; Tʷ; module FoldW; prOf)
open import OCF.Align.GuardWeakRd using (Tc-of; Tc-F; Tc-Lv₅; rdΩ₁; module Reader)
open import OCF.Align.GuardWeakNorm using (nv; belR-suc; no-guard; stays; cover-false)
open import OCF.Align.GuardWeakRel using (Rs; Rz)
open import OCF.Align.GuardWeakHi using (Rc; ι-Rc; RΩ̇₀; R⊕; rep-Rc)
```
