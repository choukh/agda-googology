# 一棵树: 带守卫的层号 + 紧的落地 (判决: PARTIAL)

> 底座 [GuardTightLv](GuardTightLv.lagda.md), [GuardTightTab](GuardTightTab.lagda.md), [GuardTightUni](GuardTightUni.lagda.md), [GuardTightFeed](GuardTightFeed.lagda.md), [GuardTightNext](GuardTightNext.lagda.md) (由 `LvGuard*` 脚本生成, 差别写在各文件开头), [GuardTightCum](GuardTightCum.lagda.md) (从 [Level](Level.lagda.md) 切出). 新东西 [GuardTightBase](GuardTightBase.lagda.md) (读位置, 规范化), [GuardTightTree](GuardTightTree.lagda.md) (树), [GuardTightRd](GuardTightRd.lagda.md) (读位置的实例), [GuardTightBound](GuardTightBound.lagda.md) (界的定理), [GuardTightNeg](GuardTightNeg.lagda.md), [GuardTightUp](GuardTightUp.lagda.md), [GuardTightCertRel](GuardTightCertRel.lagda.md), [GuardTightCert](GuardTightCert.lagda.md). 都不用记号的定义, **导入闭包只含 `OCF.Free.*`, `OCF.BTBO`, stdlib 与这一组文件.** 记号只在验收 [GuardTightAccept](GuardTightAccept.lagda.md). 接 [LvGuard](LvGuard.lagda.md), [ScafLadder](ScafLadder.lagda.md), [LvCert](LvCert.lagda.md), [LvKey](LvKey.lagda.md), [EBOTop](EBOTop.lagda.md).
>
> **判决: PARTIAL. 两个修法进了一棵树, 没有高度, 没有逐层输入 (`T₀`). 界的问题对 $a+\eta$ 型闭包是定理, 对一切 $\tau$, 一切 $b$ (`tail-ub`, `tail-lb`, `tail-free`, `mark-tail`). 这棵树上第一条证书: `Good-Ω₁ : Goodᴺ (T₀ Ω₁ …)`, 即 $\psi_0(\Omega_\Omega)$, 无条件, 不读记号 ([GuardTightCert](GuardTightCert.lagda.md)). $\psi_0(\Omega_{\Omega\cdot2+1})$ 没有证书, 连 $\psi_0(\Omega_{\Omega+1})$ 也没有: 现在的桥只走闭包以下. `good-feed` 没有证, 所以 $\psi_0(\Omega_{\Omega_2})$ 只有条件定义 (`Diag.TΩ₂`). 折叠不能实例化到 `𝔻ₙ`: 这是编译过的否定 (`no-WFˢ-Ω⁺`), 不是工程量. 没有编译过的否定挡住 $\mathbb N$ 层以内的证书, 所以不是 FAILS. 没有两个设计败在同一点: 第一版 (字面的分支值, 链带全部帧) 被推理和有限测试改掉了, 没有败在证书上.**
>
> **任务 1: 一棵树 (编译).**
>
> | 东西 | 哪里 | 与 [LvGuardTree](LvGuardTree.lagda.md), [ScafLadderQ](ScafLadderQ.lagda.md) 的关系 |
> |---|---|---|
> | 读位置 `Rdr`, `Tc`, 规范化 `nfC`, `nfS`, `nfT` | [Base](GuardTightBase.lagda.md) | 替代高度坐标. 对层号结构递归. `Tc` 是折叠的参数, 与 `WFˢ` 同档. 恒等读法 `Tc-id` 总有, 回到旧的界 |
> | 证据是 `pr a <ᴵ ℓ`, `pr (b+1)=b` | [Lv](GuardTightLv.lagda.md) | 分支 $b+1$ 的证据是 $b<\ell$, 就是地板 `fk b`. $b+1$ 一般不是 $\ell$ 的字面子项. 比较只给非严格答案 (`bd`), `WFˢ` 的上升改成非严格, 读回给的本来就是这个 |
> | `ocv`, `omk`, 走位置的 `ι` | [Tree](GuardTightTree.lagda.md) | `omk` 同 `ScafLadderQ`. 读到记号: 位置规范化, $z$ 直接嵌到规范的位置, 帧换成规范位置的帧. `Cov` 取代那里的 `qwk`/`upd-map` |
> | `riseΩ` 的 `nfT` | [Tree](GuardTightTree.lagda.md) §9 | 链的目标用规范路径. 取代目标坐标 $t$ |
> | `keepP`, `trim` | [Tree](GuardTightTree.lagda.md) §5″ | **取代高度分块 (`lo n ζ`).** 链只带在节点的层里有位置的帧. 由表里的证据比较闭包位置与节点路径 |
>
> **`Str`/`Cont` 要不要: 落地规则代替不了, 但也不必是这个形状.**
>
> - `no-min` ([Neg](GuardTightNeg.lagda.md), 编译): 若每个 `WFˢ` 闭包都有最小的读位置, 则 WLPO. 所以落地规则不能省掉证据, `Tc` 只能作层号证书的一部分.
> - 字面的闭包不要 `Str`/`Cont`: `Tail` ([Rd](GuardTightRd.lagda.md)) 只读 $G(\eta+1)$, $G(\lim f)$ 的头一步. 守卫也不判定: `guard₁`, `guardL` 用 $0$ 与 $b$ 的字面公共上界 $\eta$ (`<ᴵ-dec`). 实例 `RdΩ₁`, `RdAdd`, `RdIter`: $\Omega_1$, $a+\Omega_1$, $\Omega_1\cdot n$, 于是 $\psi_1(1)$, $\psi_1(1)+\Omega$.
> - **$F\theta=\psi_1(\Omega_\theta)$, `Lv₅` 的分支不是字面的 ($F(\eta+1)=\lim_n(F\eta)\cdot n$). 这两个现在用 `Tc-id`, 界不紧.** 紧的读法要比较 $F\eta$ 与位置, 判断: 就是 [LvGuard](LvGuard.lagda.md) 提议的 `Str` (`cmpF`) 与 `Cont`, 没有写. 所以第 5 站上 `c-bra*` 的那一半**还在** (判断, 没有测).
>
> **界的定理 ([Bound](GuardTightBound.lagda.md), 编译, 无条件, 模块参数都是层号与证书, 不是假设).**
>
> - 每一个位置: `land-tp`, `land-t0`, `head-goC`: 落成字面的 `oŝ c₀`. `cOf-ub`, `cOf-lb₁`, `cOf-lb₂`: 模前序 $c_0=\sup(c_2,\{K+1\})$. `floors`: 地板只有三类来源, 同键的活帧 (及其节点路径), 目标路径上同键的分支, 闭包自己路径上同键的分支.
> - $a+\eta$: `rdA-exact`, `nf-tail`: 目标 $a+b$ 不管穿过哪个分支 $\tau$ (含极限, 含极限的项还是极限), 规范化后都是 `bra (b+1) … zero`. `tail-ub`, `tail-lb`: 界模前序就是 $b+1$. `tail-free`: 两个世界, 两条路径, 界互相 $\sqsubseteq$. `tail-head`: 头是字面的. `ι-mark`, `mark-tail`: 分支 $\tau$ 里层 $a+(b+1)$ 的位置, 帧的分支值是 $b+1$, 地板是 `fk b`, 与 `flo (suc b) = fk b` 一致.
> - **没有证的:** "最小" 只对 `TailThm` 的闭包. $\lim$ 层自己的位置 (`omk (st-lim …)`) 在 $f\,n$ 还是极限时不下降 (`rC`), 下一步的 `omk` 再读. 判断: 这是这个定义与 `flo (lim f) = fb (lim f)` 的差. 比较极限分支值 (`pr (lim f) <ᴵ ℓ` 是字面的) 比 `fb` 强, 没有测到差别.
>
> **任务 3: 有限测试 ([Accept](GuardTightAccept.lagda.md), 全部 `refl`).**
>
> | 目标 | 比较器, 深度, 宽度 | 结果 |
> |---|---|---|
> | $\psi_0(\Omega_\Omega)$, $\Omega+1$, $\Omega\cdot2$, $+1$, $\Omega\cdot3$ | `dfZ`, 10–12, 2 | 一致, 对照 `ctl₄` |
> | $\psi_1(1)$, $\psi_1(1)+1$, $\psi_1(1)+\Omega$ (过 `noTimes`) | `dfZ`, 10, 2 | 一致, 对照 `ctl₇` |
> | $\psi_0(\Omega_{\psi_1(\Omega)})$, 第 5 站 (`Tc-id`) | `dfZ`, 10, 2 | 一致, 对照 `ctl₅`, `ctl₆` |
> | $W$ | `dfZ`, 24, 1; 12, 2 | 一致 |
> | $\psi_0(\Omega_{\Omega_2})$ 的前两项, 第三项 $u_2$ 的层号与树 | `dfZ` 6, 2; `dfL` 6, 2; `dfZ` 6, 2 | 一致, 对照 `ctlΩ₂`, `ctl-u₂`. **证书是变量, 只说这个深度没问到它** |
> | **界:** `c-bra*` 对 `t-bra*`, $\Omega\cdot2$, $\tau=2,3,5$ | `cO` | 恒等读法 $\tau$, 紧的读法 1 |
> | **界, 过 `noTimes`:** `t-brω2`, `t-brω4`, `c-brω4`, $\psi_1(1)+\Omega$ | `cO` | 紧的 1, 恒等 5 |
> | **界, 对塔:** `qa-1`, `qa-11`, `qa-2`, `qa-21`, `qa-3`, `qa-ω` | `agree`, 9–12, 2 | **逐闭包比界 (`toN`) 与种类, 与 [LadderNFTree](LadderNFTree.lagda.md) (= `ScafLadderQ`) 一致.** 对照 `qa-ctl`, `qa-ctl₂` |
>
> `agree` 是这一轮最有用的测试: 它看界, 走 $\eta=c_0+k$. 没有 `trim` 的版本在它下面不一致 ($\Omega+2$, 路径 `1, 1, 301, 0, 1, 0`, 这里 2, 塔 1), 这就是 `keepP` 的来历. **这些测试不说明有证书.** 第一个孩子走得到的地方不多; $\Omega\cdot2+1$ 的树一致到这个深度, 不是 $\cong^{\mathsf z}$ 的定理.
>
> **任务 2: 更高的定义域 ([Up](GuardTightUp.lagda.md)).**
>
> - **`no-WFˢ-Ω⁺` (编译): $\Omega_2$ 作为 `𝔻₁` 上的层号没有 `WFˢ`.** `Fold` 的比较要搬运带对一切表的转移, 上升 $x\mapsto x$ 没有. 所以 `𝔻ₙ` 上的 `Fold` 这样写不出来. 判断: 要 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `cmpW` 那样的局部比较 (分支 $x$ 自己是局部上界), 表随分支增长, 与第 1 层的待计值链. 没有写.
> - `rbO`, `F⁺` (编译, 定义). `Diag.TΩ₂` (编译, **条件**): $\psi_0(\Omega_{\Omega_2})=\sup_n\psi_0(\Omega_{u_n})$, $u_{n+1}=\psi_1(\Omega_{u_n})$. 这是 EBO 的基本列 (`c-Ω₂`, `c-u₂`, `c-a2`). 只用 `Dom₀` 上的树. 条件 `GoodFeed` 就是 `good-feed`, **没有证**. $u_0$ 是闭项; $u_1$ 的读回版本 `Lv₅` 的证书是定理 ([Uni](GuardTightUni.lagda.md)), 但它不是 `feedL u₀`, 两者的 $\approx$ 没有写; $u_2$ 起没有证书.
> - **$\Omega_{\Omega_\eta}$: 没有.** 判断: 对 `Ordᴵ` 递归, 后继是 `NextDom`, 极限要余极限, 而跨层的 $\approx$ 要沿 `f n ⊑ f (n+1)` 搬运层号, `s` 不是字面的. 仿 `Ord₊`/`U` 对 `◃` 递归写得出下标 (判断, 没有试). **每阶段的新层就在这里回来: `𝔻ₙ` 的每一层是一个新的定义域, 比较的 `Fold` 还不在其上.** `Diag` 那一层只在 $\Omega_2$ 上写了; $\Omega_3$ 的链点是 $\psi_2$, 要 `𝔻₁` 上的折叠.
>
> **任务 4: 证书: 第一条做到了, 第二条没有.**
>
> - **`Good-Ω₁` (编译, 无条件, [GuardTightCert](GuardTightCert.lagda.md), [GuardTightCertRel](GuardTightCertRel.lagda.md)):** 跨树互模拟 `Rs`: 闭包以下的 `O` 对 `Ordˢ`. `R-⊕`, `R-trO`, `R-trˢ`, `R-ι`, `RΩ̇`, `R-ψ` 对一切 $\eta$, 世界任意. 证书由 [OCF.Free.Main](../Free/Main.lagda.md) 的 `GᴺΩ̇ zero` 搬来 (`Goodᴺ-c`): 下界只要 $c_2\sqsubseteq$ `Bd`, 不要 $\cong$. 比较的答案只读语义 (`cb-sem`, `cu-sem`, `clash`), 不算 `⊴`. 表与世界不必对应: 两边比较同一对节点, 答案由 `clash` 对齐.
> - **这个证明逼出的定义改动:** `repᵒ` 改成右结合 (与 `iter` 同形, `agree` 不变); `cu` 带证据; `trim` 使链的地板为空 (`trim-emp`), 否则节点的 $\xi$ 没有证据, `cmpN` 可能答 `cj`.
> - **第一个障碍: 闭包以上.** 桥要过 `ocl`. 判断: 对 [OCF.Free.Tree](../Free/Tree.lagda.md) 的 `O` 再写一层 (`ψᵒ`, `ψ̄`, `cloA`), 约 500 行, 得 $\psi_0(\Omega_{\Omega+\eta})$ 与 $\psi_0(\Omega_{\Omega\cdot2})$; 证书要 $c_0\sqsubseteq$ 对面的界, 由 `floors` 与 "帧被对面的地板覆盖" 给. 再往上桥到 [LadderNFTree](LadderNFTree.lagda.md), $\Omega\cdot2+1$ 的证书要 `LadderNF*` 完成 (还在写, 我用 `LadderNFTree` 作 `agree` 的对照, 没有用它的证明). 判断: 高度对位置的语义引理加关系, 约 1500 行. **这些都没有写.** 也可以在这棵树上重走 `UniformNF5*` (约 4000 行).
>
> **否定的状态.** `noW`, `noCert₂` ([LvCertNeg](LvCertNeg.lagda.md)) 是对旧树的定理; 这里 `tail-free` 直接否定了它的第 3 步的前提 (界读到穿过的 $\tau$), 对 $a+\eta$ 的闭包. 第 4 步 (第 0 点与 $\tau$ 无关) 仍在, 现在是好事. `no-min`, `no-WFˢ-Ω⁺` 是这里的. `no-bra-cmp`, `noTag`, `¬tri` 没有变: `<ᴵ-dec` 只在字面上界之下.
>
> **逐阶段的输入.** 树 (`T₀`, `Fold`, `Ω̇`, `ι`, `nfC`, `keepP`): 没有. 层号的 `Cfˢ`: 没有 (`GuardTightUni`, 对 `Ordᴵ` 下标). **`Tc`: 有, 按闭包的形状, 不按阶段: `Tail` 一个定义, 每种形状要一个视图 (3 个).** `F`, `Lv₅` 没有紧的 `Tc`. `GoodFeed`: 条件. `𝔻ₙ`: 见上.
>
> **读了记号的 (如实).** 定义没有读 (切片 0, 导入闭包干净). 形状: $\Omega\cdot m$ 的落地规则, `omk`, "地板必须真实出现" 来自 `ScafLadder`, 那里是看记号定的. `trim` 是我看 `agree` 对塔的不一致后定的, 塔是树, 不是记号. **树侧逼出的:** `pr` (字面子项在极限上断掉); `no-min`; `no-WFˢ-Ω⁺`; 守卫由公共上界回答. **这不算由树带路:** `Tc` 的规格 "最小" 是看目标 $a$ 定的, 没有树侧判据说为什么要它, 只有 `noW` 说不要它不行.
>
> **壁垒.** `pr`, `bd` 只给字面上界之下的比较. 没有全局三歧, 没有 `Ordᴰ` 的初始段. `no-min`, `no-WFˢ-Ω⁺` 都是在说没有更强的东西. 判断, 没有形式对比.
>
> **审计.** `importclosure.py` (编译器保证): `GuardTightLv`, `Tab`, `Base`, `Tree`, `Cum`, `Uni`, `Feed`, `Next`, `Rd`, `Bound`, `Neg`, `Up`, `CertRel`, `Cert` 闭包干净. `GuardTightAccept` 读记号. 全文 `--safe --without-K` (加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示. 模块参数: `Lv`, `Up`, `Uni`, `Tab` 的 `𝔻` 是定义域; `Fold`, `Emb`, `Land`, `TailThm`, `Bd₁`, `MarkThm` 的参数是层号与它的证书; **`Diag` 的 `G` 是假设**; `DiagT`, `U₂` 的变量证书是测试装置, 只在验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTight where

open import OCF.Align.GuardTightBase using (Rdr; Tc; Tc-id; nfC; nfS; nfT; Cov)
open import OCF.Align.GuardTightTree using (O; T₀; Ω̇; module Emb; module Fold)
open import OCF.Align.GuardTightRd using (module Tail; module RdΩ₁; module RdAdd; module RdIter)
open import OCF.Align.GuardTightBound using (module Land; module TailThm; module EmbThm; module MarkThm)
open import OCF.Align.GuardTightNeg using (no-min)
open import OCF.Align.GuardTightUp using (rbO; F⁺; GoodFeed; module Diag; no-WFˢ-Ω⁺)
open import OCF.Align.GuardTightCert using (Good-Ω₁; R-ψ; Goodᴺ-c)
```
