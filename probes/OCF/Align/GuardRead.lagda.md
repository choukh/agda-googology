# 统一的读位置: 切口 (判决: HOLDS)

> 新文件 [GuardReadCut](GuardReadCut.lagda.md) (切口 `Sp`, 读法 `read`), [GuardReadRs](GuardReadRs.lagda.md) (带切口的项 `Rs`), [GuardReadRd](GuardReadRd.lagda.md) (统一读法 `Reader`, `Tc-of`, `Tc-F`, `Tc-Lv₅`), [GuardReadBound](GuardReadBound.lagda.md) (界的定理), [GuardReadNeg](GuardReadNeg.lagda.md) (否定), [GuardReadCert](GuardReadCert.lagda.md) (`Good-Ω₁` 换读法), [GuardReadAccept](GuardReadAccept.lagda.md) (有限测试, 记号与塔只在这里). 接 [GuardTight](GuardTight.lagda.md), [LvGuard](LvGuard.lagda.md), [LvCertNeg](LvCertNeg.lagda.md).
>
> **判决: HOLDS, 就下面这个问题: $F\,\theta$ (一切 $\theta$) 与 $\mathrm{Lv}_5$ 有紧的 `Tc`, 无条件, 一个定义, 不按阶段, 不按闭包形状; `tail-ub`, `tail-lb`, `tail-free` 型定理对它们编译.** 不是说证书到了第 5 站: 证书还是只有 `Good-Ω₁`. `tail-free` 的全称版有一处变弱, 见 "变弱".
>
> **这个想法.** $G\,b$ 是 $G(b+1)$ 的**切口**: $G(b+1)$ 的每个位置要么落在 $G\,b$ 里, 要么在 $G\,b$ 之上, 由结构给出 (`Sp`). 这比提议的 `Str` (`cmpF`, 比较 $F\eta$ 与位置) 弱也强: 不比较 (比较写不出, `no-cut`), 但带证据 (`s-suc`, `s-lc` 带 $a\sqsubseteq$ 节点), 所以回答不是空的. 读法只问切口, 由 $\eta$ 的结构下降. `Cont` 就是 $f(\lim h)\cong\lim(f\circ h)$.
>
> **任务 1: 紧的 `Tc` (编译, 无条件).**
>
> | 定理 | 陈述 | 哪里 |
> |---|---|---|
> | `Tc-F` | `∀ θ → Tc (F θ)` | [Rd](GuardReadRd.lagda.md) |
> | `Tc-Lv₅` | `Tc Lv₅` | [Rd](GuardReadRd.lagda.md) |
> | `Tc-of` | `Rs x → Good x → Tc (rb₁ x)`, $x$ 在第 1 层 | [Rd](GuardReadRd.lagda.md) |
> | `Tc-Ω₁`, `Tc-add`, `Tc-iter` | 字面的闭包是实例, 不要 `Tail` 的视图 | [Rd](GuardReadRd.lagda.md) |
> | `Rs-Ω`, `Rs-add`, `Rs-iter`, `Rs-ψ`, `Rs-ψ¹`, `Rs-tr`, `Rs-tr⁻` | `Rs` 对读回的项封闭, 与 `Good-*` 同形 | [Rs](GuardReadRs.lagda.md) |
> | `sp-bot` | $a\sqsubseteq c$, $a$ 是 $c$ 的切口 ⟹ $a$ 是 $c+x$ 的切口, 一切 $x$ | [Cut](GuardReadCut.lagda.md) |
> | `sp-iter`, `sp-Ωψ` | $a$ 是 $c\cdot n$ 的切口; $\Omega_j$ 是 $\psi_j(y)$ 的切口 | [Cut](GuardReadCut.lagda.md) |
> | `Sp-ψ¹`, `Sp-ψ`, `Sp-add`, `Sp-tr`, `Sp-tr⁻` | 折叠, 加法, 搬运保持切口 | [Cut](GuardReadCut.lagda.md) |
> | `sp-F` | $b$ 不是字面 0 时 $F\,b$ 是 $F(b+1)$ 的切口, 一切 $b$ | [Rd](GuardReadRd.lagda.md) |
>
> **任务 2: 界的定理 (编译, 无条件; 模块参数是读法的输入与层号的证书, 实例闭合).**
>
> | 定理 | 陈述 | 对应 |
> |---|---|---|
> | `tgt-of` | 后继节点只有两种回答: 第一支, 或分支 $b+1$ 且 $G\,b\trianglelefteq k'$ | `rdA-exact` |
> | `lc-of` | 闭包节点同上, $G\,b\trianglelefteq$ 节点 | `mark-tail` |
> | `tight-min`, `tight-min′`, `min-Lv₅` | $G\,b\trianglelefteq k$, $G\,x\trianglelefteq G\,b$ ⟹ $k$ 不在 $G\,x$ 之下: **这个分支最小**. 由良基 (`irr`), 不判定 | "最小" 第一次是定理 |
> | `tight-nf`, `tight-of`, `tight-Lv₅`, `tight-F₁` | 目标 `suc (bra τ e r)` 规范化之后是 `suc (fst …)` 或 `suc (bra (b+1) ea …)`, $G\,b\trianglelefteq$ 目标, **一切 $\tau$ 含极限, 一切路径 $r$** | `nf-tail` |
> | `bra-ub`, `bra-lb` | 目标 `suc (bra (b+1) ea r)`, $r$ 任意: 界模前序是 $b+1$ | `tail-ub`, `tail-lb` |
> | `fst-ub`, `fst-lb` | 目标 `suc (fst r)`: 界模前序是下界 $c$ | 新 |
> | `bound-of`, `bound-Lv₅`, `bound-F₁` | 合起来: 对一切 $\tau$, 路径, 世界, 规范化后的界是 1, 或 $b+1$ 且 $F\,b\trianglelefteq$ 目标 | **`c-bra*` 那一半的否定, 第 5 站上** |
> | `bra-free` | 同一个 $b$: 两个世界, 两条路径, 界互相 $\sqsubseteq$ | `tail-free` |
> | `ans-≅`, `free-Lv₅`, `free-bound` | $b,b'$ 有字面公共上界时, 同一个目标的两个回答 $b\cong b'$, 界互相 $\sqsubseteq$ | `tail-free` 的跨分支部分 |
> | `no-occ-b`, `no-occ-f` | 分支里没有 $\approx$ 闭包自己的闭包. 取代 "路径内部没有 `bra`" | 新 |
> | `Good-Ω₁` ([Cert](GuardReadCert.lagda.md)) | 换成统一读法, 证明一行不改 | 新 |
>
> **变弱.** `tail-free` 对 $a+\eta$ 是跨世界的: $b$ 是目标的字面子项, 两边相同. 这里 `free-Lv₅` 要 $b,b'$ 有字面的公共上界, 这是同一个世界给的 (路径上分支 $b+1$ 的证据是 $b<\ell$, 同键同一个 $\ell$). 没有上界时只有 "$b'+1\not\sqsubseteq b$" 两边 (`tight-min`). 判断: 全称版要比较两个无关的下标, 这条路上不应期待; 折叠里比较的都在一个世界. 没有编译否定.
>
> **任务 3: 否定, 只否定想法 ([Neg](GuardReadNeg.lagda.md), 编译).**
>
> | 定理 | 陈述 | 否定的想法 |
> |---|---|---|
> | `no-cut` | 若 `A ⊴ B` 总给 `Cu` (都有 `WFˢ`, 自反), 则 LPO | 切口由 `⊴` 算出, 即 `Str` 作判定 |
> | `no-fp-move` | 闭合的 $A\trianglelefteq B$, $A$ 是极限, $B$ 里没有 $A$ 的第一位置 | "比较第一位置": `⊴` 不搬它, 带上这个搬运 `⊴-lim-l` 就假 |
> | `no-F₀-first` | $F\,0\prec^f F\,1$ 假 | "比较第一路径" (`cmpF`) 的输入 |
> | `no-lim-cmp` | $A$ 与 $\lim h$ 总可比则 LPO | 极限节点也要回答; 所以 `cUn` |
>
> `no-min` 仍然成立, 不矛盾: `Rs` 的闭包带结构证据, 下界是字面的 1. `Rs` 不覆盖一切 `WFˢ` 闭包. `no-cut` 是 `⊴` 层的, 不是闭包层的 (没有写成带守卫的闭包族).
>
> **任务 4: 有限测试 ([Accept](GuardReadAccept.lagda.md), 全部 `refl`). 这些不是证书, 不是证明.**
>
> | 东西 | 比较 | 结果 |
> |---|---|---|
> | $\Omega$, $\Omega+1$, $\Omega\cdot2$, $+1$, $\Omega\cdot3$, $\psi_1(1)$ (`ua-*`) | 统一读法对**塔**, `agree`, 比界, 9–12, 2 | 一致, 对照 `ua-ctl` |
> | 同上, $\psi_1(1)+\Omega$, $\psi_0(\Omega_{\psi_1(\Omega)})$, **第 5 站** (`d-*`) | 对记号, `dfZ`, 只看种类, 10–12, 2 | 一致, 对照 `d-ctl₁`, `d-ctl₂` |
> | `t5-2`, `t5-2′`: 目标 $F\,1$; `t5-3` 到 `t5-7`: 目标 $F\,2$ (`t5-k`: 确实是, 结构比到 12 层, 极限比前 3 项, 闭包只比第一支, 对照 `t5-k₁`) | `Tgt`, $\tau=2,4$; $3,4,5,7$ | **恒等读法 $\tau$, 紧的读法 2; 3** |
> | `t5-ω`, `t5-ω′`: $\tau=\omega$ | 同上 | 紧的读法 3 |
> | `tH-3`, `tH-4`, `tH-6`: $\psi_1(\Omega)$, 目标 $H\,2$ (`tH-k`) | `Tgt`, $\tau=3,4,6$ | **恒等 $\tau$, 紧的 3** |
> | `tH-f`: 目标在第一支 | `Tgt` | 恒等 5, 紧的 1 |
> | `tC-3`, `tC-4`, `tC-6`: $F\,2$ 里的闭包, 分支 $\psi_1(\psi_1(\tau))$ (`tC-k`) | `Tgt`, $\tau=3,4,6$ | **恒等 $\tau$, 紧的 3** |
> | `pos-H2`, `pos-H2′`, `pos-H3`: 极限节点的位置 | `braOf` | 分支 2, 2, 3 |
> | `b-1`, `b-2`, `b-2′`, `b-id`, `b-ω`: 字面的闭包 | `Tgt` | 紧的 1, 2, 2; 恒等 7; 1 |
> | `u-W`, `u-W₂`: $W$ | `dfZ`, 24, 1; 12, 2 | 一致 |
>
> **没有塔对照的地方:** `t5-*`, `tH-*`, `tC-*`, `pos-*`, `u-W`. [LadderNFTree](LadderNFTree.lagda.md) 只到 $\psi_1(1)$ 附近. 这些只说 "不随 $\tau$ 变", 与 "目标确实是那个分支", 界的数值没有独立的对照. `dfZ` 不看界.
>
> **判断 (没有编译).**
>
> - 这解决了 `noW`, `noCert₂` 第 3 步的前提 (界读到穿过的 $\tau$) 在第 5 站上的那一半. 否定本身是对旧树的定理, 没有在这棵树上重新陈述.
> - `Rs` 可以看作层号的一条树侧合法性标准, 与 `Good`, `WFˢ` 同档: 闭包的分支序列正规 (`Cont`), 且每一步是切口 (`Str`). 这条标准不看记号也能写下. 但它是对 `Ordᶜ` 项写的, 不是对 `LG` 写的 (见第一个障碍), 所以只说 "朝这个方向", 不说树自足.
> - 为什么切口成立而比较不成立: 切口只问 "这个位置是不是在 $a$ 这份拷贝里", 答案在项的结构上; 比较问的是值.
>
> **第一个障碍: 高层下标与证书.**
>
> 1. **`Tc` 只在 `Dom₀`, `Rs` 只在 `Ordᶜ`.** $\psi_0(\Omega_{\Omega_2})$ 的条件 `GoodFeed` 要 `tcF : ∀ u → Tc (feedL u)`, 这里 `feedL` 经 `F⁺`, `rbO`, 从 `O` 读回, 不是 `Ordᶜ` 的项, 所以 `Tc-of` 用不上. 要在 [GuardTightTree](GuardTightTree.lagda.md) 的 `O` 上重写 `Sp`, `Rs` (判断: 形状相同, `oĉ`, `oŝ` 对 `limᵢ`, 约 600 行; 没有写). 本轮**没有**推进 `good-feed`.
> 2. **证书.** `Good-Ω₁` 换读法一行不改, 但闭包以上的桥 (`ocl`) 没有写, 与 [GuardTight](GuardTight.lagda.md) 同.
> 3. **极限节点 `s-mv` 不下降.** `cuMv` 对 0, 极限节点不答. 目前只有 `s-cg` ($\cong$) 能搬极限节点. `tgt-of`, `lc-of` 不受影响; `omk` 的极限层可能比必要的高一些 (判断, 没有测到差别; `pos-*` 只测了 `s-cg` 这条路).
>
> **读法是否按阶段定制: 否.** `Reader` 一个定义; `Tc-of` 一个定理, 对第 1 层一切 `Rs` 的好项; 第 $n$ 站没有输入. `Tail` 的 3 个视图不要了. **有一条不在 `Tc-of` 里:** `sp-F`, 因为 $\mathrm{Lv}_5$ 的下标是 `Ordᴵ`, 不是 `limᵢ` 的项; 它对一切 $b$ 一个定义. 又, `Reader` 第 0 步不问切口 ($G\,1$ 就是第一支). 这是定义, 不是阶段.
>
> **哪些形状受记号影响 (如实).** 定义没有读记号 (导入闭包, 切片). `Str`, `Cont` 的名字来自 [LvGuard](LvGuard.lagda.md) 的提议, 而 "要最小的分支" 的规格来自 [LvCertNeg](LvCertNeg.lagda.md) 与目标 $a$ 的讨论 (`GuardTight` 已说明). **这一轮树侧逼出的:** 比较写不出 (`no-cut`, `no-fp-move`, `no-F₀-first`) 所以改成切口; `s-lim` 不带证据 (`no-lim-cmp`); `s-mv` 只搬后继与闭包 (`⊴` 就这么多); "最小" 成为定理 (`tight-min`). 设计中看了 $F(b+1)$ 的链, 那是 `ψ¹` 的定义, 不是记号. `agree` 用塔查错, 这一轮没有因此改定义. 第 0 步读成第一支, 是定义相等 $t_1=G\,1$ 给的, `agree` 事后确认.
>
> **壁垒.** 只有字面上界之下的比较 (`guard₁`, `guardL`, `ans-≅`); 切口不比较. `no-cut`, `no-lim-cmp` 说明更强的东西是 LPO. 判断, 没有形式对比.
>
> **审计.** `importclosure.py` (编译器保证): `GuardReadCut`, `Rs`, `Rd`, `Bound`, `Neg`, `Cert`, 本文件闭包干净, 退出码 0. `GuardReadAccept` 读记号与塔, 退出码 1. `depslice.py` (语法级): `Cut:read`, `Cut:sp-Ωψ`, `Rs:Rs-ψ¹`, `Rd:Tc-F`, `Rd:Tc-Lv₅`, `Rd:Tc-of`, `Bound:bound-Lv₅`, `Bound:tight-of`, `Neg:no-cut`, `Cert:Good-Ω₁` 到达的记号块都是 0 (到达 193 到 1145 块); 正对照 `Accept:d-f5`, `d-f1` 是 48. 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示, 无 trustMe. 模块参数: `Reader`, `OfF`, `Spec`, `TightT`, `Full`, `BdU`, `NoOcc` 的参数是读法的输入或层号的证书, 实例闭合, 不是假设. 没有条件定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardRead where

open import OCF.Align.GuardReadCut using (Sp; read; Cu; sp-bot; sp-iter; sp-Ωψ; Sp-ψ¹; Sp-ψ; Sp-add; Sp-tr; Sp-tr⁻)
open import OCF.Align.GuardReadRs using (Rs; Rs-Ω; Rs-add; Rs-iter; Rs-ψ; Rs-ψ¹; Rs-tr; Rs-tr⁻; Rs-em)
open import OCF.Align.GuardReadRd using (module Reader; Tc-of; Tc-F; Tc-Lv₅; Tc-Ω₁; Tc-add; Tc-iter; sp-F)
open import OCF.Align.GuardReadBound using (tight-min; tight-min′; min-Lv₅; module Spec; module TightT; module Full; module BdU; module NoOcc; tight-of; tight-Lv₅; tight-F₁; bound-Lv₅; bound-F₁; ans-≅; free-Lv₅; free-bound; nf-rdB; nf-rdF)
open import OCF.Align.GuardReadNeg using (no-cut; no-fp-move; no-F₀-first; no-lim-cmp)
open import OCF.Align.GuardReadCert using (Good-Ω₁)
```
