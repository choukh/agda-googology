# `T₀ʷ` 上第一条新证书: $\psi_0(\Omega_{\Omega+1})$ (判决: PARTIAL)

> 文件: [GuardCertRel](GuardCertRel.lagda.md) (互模拟), [GuardCertNf](GuardCertNf.lagda.md) (规范位置的帧), [GuardCertHi](GuardCertHi.lagda.md) (闭包所在的层), [GuardCertFold](GuardCertFold.lagda.md) (折叠), [GuardCertMain](GuardCertMain.lagda.md) (证书), [GuardCertHt](GuardCertHt.lagda.md) (`HtS` 字段清单), [GuardCertAccept](GuardCertAccept.lagda.md) (验收, 只有它读记号). 接 [GuardWeak](GuardWeak.lagda.md).
>
> **判决: PARTIAL. 目标序列的第一个做到了: `Good-Ω+1 : Goodᴺ (T₀ʷ (c₁+1) …)`, 无条件, 无模块参数作假设, 导入闭包干净, 标签 $\psi_0(\Omega_{\Omega+1})$ 是定理 (`label-Ω+1`, 验收节). $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega\cdot2+1})$, $\psi_0(\Omega_{\psi_1(1)+\Omega})$ 没有做. 没有否定它们.**
>
> **选的路: A (桥, `Good-≲`, 对面是 [OCF.Free.Tree](../Free/Tree.lagda.md)).** 理由: $\Omega+1$ 这个小目标上, 桥是 `Rs`, `Rc` 两层互模拟加两条折叠的归纳: 新写约 1000 行 ([Nf](GuardCertNf.lagda.md) 280, [Fold](GuardCertFold.lagda.md) 580, [Main](GuardCertMain.lagda.md) 70), 另 950 行由 [GuardWeakRel](GuardWeakRel.lagda.md), [GuardWeakHi](GuardWeakHi.lagda.md) 改写. 路 B 要搬 `Gq`, `VisQ`, `Brq`, `Gr`, 约 8000 行, 没有试.
>
> **上一轮卡点的解法.** 上一轮说 "规范位置的帧 $\sqsubseteq$ 节点的层" 在极限节点上假 (`cover-false`), 判断不变量应写在 `os` 与闭包处, `rmk (self n)` 要记下它是 $\dot\Omega$ 的像. **这个判断对.** 形式:
>
> 1. `rs` 带 `FlrLe π B`: `os` 的输入地板上的帧 $\sqsubseteq B$ ([Rel](GuardCertRel.lagda.md)). `Rc` 的 `cs`, `ccl` 带 `CvL π φ` ([Hi](GuardCertHi.lagda.md)).
> 2. 模式 `Md`: `rmk (self n)` 的 $z$ 与 $x$ 是 `gd` 的: `rs` 只在 $B$ 是 0 时出现. `cover-false` 的位置 (`lim 0 self`) 只在这里出现, 到不了 `rs` (`Hr gd`). 不记字面的 $\dot\Omega$, 因为要过 `≈` 的搬运.
> 3. `rmk zero` 的位置带 `InvS`: 以 `suc self` 结尾 (`EndS`), 或层有闭包且帧 $\sqsubseteq k$. **`fr-lim`: 极限节点, 位置以 `suc self` 结尾: 第一支或帧 $\cong k$.** `cover-false` 不碰这一条: 它的位置不以 `suc self` 结尾. 后继节点就是 `nv` 的论证 (`fr-suc`), 节点 0 是第一支 (`fr-zero`).
> 4. 比较不计算: 右边的界由 `CvL` 给 $\sqsubseteq$ (`good-sel`, `ubd`). 目标在 $\lceil i\rceil$ 的折叠, 输出地板是空的, 所以 `rep-rel` 的 `FlrLe` 平凡.
> 5. 输出地板有帧时 (`R-ψᵒ`): `FV ρ π` (输出的帧被输入的帧支配, 只看值) 把 `cs` 的 `CvL π φ` 搬到 `ρ`, 就是 `rep-Rc` 要的.
>
> **编译过的定理 (无条件, 无模块参数作假设).**
>
> | 定理 | 文件 | 陈述 |
> |---|---|---|
> | **`Good-Ω+1`** | [Main](GuardCertMain.lagda.md) | `Goodᴺ (T₀ʷ cT (wf₁ , s≈ sf₁) tcʷ)`, $c_T=c_1+1$, $c_1$ 是 $\Omega$ 的层号 |
> | `≲-Ω+1` | [Main](GuardCertMain.lagda.md) | `T₀ʷ … ≲ᶻ toZ (ψ̄ (Ω̇ 1) ev₀ zero)`: 这棵树的界不高于对面 |
> | `value-Ω+1` | [Main](GuardCertMain.lagda.md) | 计值 $\cong$ 对面的计值 |
> | `R-ψ` | [Fold](GuardCertFold.lagda.md) | `Rc post x y` 推出 `Rs i fr (ψ E T st x) (ψ̄ y ev p)`; 状态 `Full`, 输出地板空, 目标 `Tgt T i` |
> | `R-ψᵒ` | [Fold](GuardCertFold.lagda.md) | `Rc post x y` 推出 `Rc pre (ψ E Tz st x) (ψᵒ zero y)`; 条件 `FV ρ π`, `AbF st` 是归纳不变量 |
> | `fr-zero`, `fr-suc`, `fr-lim`, `fr-end`, `fr-le` | [Nf](GuardCertNf.lagda.md) | 读位置的回答的帧值的上界 |
> | `hp-c₁`, `hp-cT`, `hp-free` | [Nf](GuardCertNf.lagda.md), [Rel](GuardCertRel.lagda.md) | `HPf`: `R-ι` 要的读法性质, 实例 |
> | `R-⊕`, `R-trO`, `R-ι`, `RΩ̇`, `Rz` | [Rel](GuardCertRel.lagda.md) | 带 `FlrLe` 与模式的互模拟 |
> | `fromRs`, `ι-Rc`, `RΩ̇₀`, `R⊕`, `rep-Rc` | [Hi](GuardCertHi.lagda.md) | 闭包所在的层 |
> | `tr<ᴸ`, `assocᴸ`, `irrᴸ`, `no<ᴸ`, `recᴸ`, `recᴸ-β`, `no-triᴸ`, `no-botᴸ`, `no-viewᴸ`, `keep-Ω+2` | [Ht](GuardCertHt.lagda.md) | 见下面的清单 |
> | `label-Ω+1`, `fgh-agree`, `same-u11` | [Accept](GuardCertAccept.lagda.md) | 标签 $\psi_0(\Omega_{\Omega+1})$; FGH 逐点相等; 这棵树就是上一轮测试的 `u11` (`refl`) |
>
> **定理不空.** `Good-Ω+1` 没有前提. 树是闭项, 不是退化的: `label-Ω+1` 给出它的值就是 $\psi_0(\Omega_{\Omega+1})$, `s₁` 是极限.
>
> **条件.** 没有条件定理. 模块参数 (`RecSpec`, `EmbR`, `NJM`, `SelM`, `RiseM`, `CloM`, `Top`) 都是证明的中间层, 实例闭合.
>
> **`Pinch`.** 有了证书, `pinch` 说 $\Omega+1$ 上这棵树的闭包不会是 `Pinch` 形状. 没有试去否定; 这回答了 [TreeJudge2](TreeJudge2.lagda.md) 的表里 `T₀ʷ` 那一行 "没有证": 有.
>
> **有限测试 (不是证明).** 上一轮的对塔测试不变. 新跑的, 对 [OCF.Free.Tree](../Free/Tree.lagda.md): `mis 10 3 2` ($\Omega+1$, 305 秒) 一致, 现在是定理的推论. 在 scratch 里, 不在文件里. 路径 `L 1, ω·2, L 1, L 1, L 0, L 1, F, L 0, L 2, L 0, L 2, L 0, L 1` 上三棵树的界都是 $\omega$ (这是 `cover-false` 的邻居, 读法在 `suc self` 那步落到 $\omega$). **没有结果 (超时, 不算一致也不算不一致):** 对 [OCF.Free.Tree](../Free/Tree.lagda.md), $\Omega+2$ 的 `mis 7 3 1` 与 $\Omega\cdot2$ 的 `mis 5 3 1` 同一次运行, 1400 秒超时. 所以 `≲` 在 $\Omega+2$, $\Omega\cdot2$ 上对 `OCF.Free` 是否成立, 这一轮没有证据; 上一轮对塔的测试在这两个目标上一致.
>
> **`HtS` 字段清单 (高度 = `LG`, 序 = `_<_`, 底 = `zero`). 定理在 [Ht](GuardCertHt.lagda.md); 只否定这个字面的实例.**
>
> | 字段 | 状况 | 依据 |
> |---|---|---|
> | `tr<`, `tr-assoc` | 成立 | `tr<ᴸ`, `assocᴸ` |
> | `irr`, `no<` | 成立 | `irrᴸ`, `no<ᴸ` |
> | `Rec`, `Rec-β` | 成立 | `recᴸ`, `recᴸ-β` |
> | `tri` | 假 | `no-triᴸ`. 弱化: `cmpN` ([GuardWeakTree](GuardWeakTree.lagda.md)) 是带字面公共上界的比较, 答 `cu`, `cb`, 没有证据答 `cj`; 规范位置上不答 `cj` (`nj-c`, 定理, 第 1 层). 全局的比较被 `no-bra-cmp`, `no-lim-cmp` 挡住 |
> | `bot` | 假 | `no-botᴸ`, 常值 0 的极限. 判断: 退化情形, 去掉退化极限就成立, 不是壁垒 |
> | `view` | 假 | `no-viewᴸ`, 同一个例子. 判断: 另外 $\mathrm{lc}\,c\,t\,g$ 这个节点既不是 `clos` 的自然形状也不是 `chain`, `T₀ʷ` 的折叠用 `Tc` 与闭包的第一支代替这一行, 要 `view` 就得把闭包写成新的一种情形 |
> | `view-step` | 依赖 `view`, 没有写 | |
>
> **`Good-Ω+1` 不用 `HtS`.** 对面的证书 `GᴺΩ̇` 是 `OCF.Free` 的, 比 `HtS` 早. 判断: 高度只在路 B 要; 路 A 只要右边的树, 不要 `Gq`.
>
> **第一个障碍 (判断, 没有编译的否定).** 到 $\Omega+\theta$ 与 $\Omega\cdot2$: `Rc` 只有两层 ($c_1$, $c_1+1$). 要改的:
>
> 1. **`Rc` 按层 $a$ 索引, 加 `FT.oΩ` 那一行** (节点 $c_1+a'$). 现在 `ci` 的节点是 $\lceil j\rceil$, 前提里 `Emp ξ` 由 `trim-emp` 给. `keep-Ω+2` ([Ht](GuardCertHt.lagda.md)): 节点 $c_1$ 上 `trim` 保留帧, `Emp ξ` 不再成立, 前提要换成 `CvL ξ ξ̂`.
> 2. **`Rc` 沿 `≈` 搬运** (`R-trO` 的 `Rc` 版, 含 `ccl`): 极限层的路径比较经 `⊴p`, 节点只模 `≈`. $c_1+n$ 上不要.
> 3. `kdec`, `nv` 对一般的 `P_θ`: 现在是定义上算出来的, 极限层要带 `with` 的引理.
> 4. $\Omega\cdot2$: `FoldW` 的 $c$ 是外层闭包, `fr-suc`, `fr-lim` 对 $G=c_1+\eta$, `FT.ι` 的复合. 估计: 到 $\psi_0(\Omega_{\Omega\cdot2})$ 再 2000 行以上 (判断).
> 5. **$\Omega\cdot2+1$ 起 `OCF.Free` 没有树了**, 要把右边换成 [LadderInfTree](LadderInfTree.lagda.md) (`Q m k φ χ`, 带 `Sub`). **第三条路 (判断, 没有试): 直接桥到 `LadderInfTree` 对 `HtS` 的实例.** 右边的证书 `GᴺTᵠ` 对一切 `HtS` 成立, 实例 `HS₂` 已过 `noTimes`. 这样不用搬 `Gq`, 也不用先走 `OCF.Free`. 代价在 `Rc` 要对 `χ`, `qΩ↓`, `qcl` 三样写 (这里没有), 判断约 3000 行. 上一轮说 "到不了塔之上" 指的是对 `OCF.Free` 的桥, 对 `LadderInfTree` 的桥没有这个限制 (判断).
>
> **判断 (没有编译).** 1. `no-join` 不挡: 比较的两边都是后继值 (`nv`, `belR-suc`), `bd` 读字面的前驱. 2. 这条证书不按阶段定制? **按了**: `Tgt`, `Sf`, `P = suc self`, `R-ψᵒ` 的目标都写死在 $c_1+1$. 这是第一个实例, 不是闭包定理. 上面 1-4 是把它变成闭包定理要做的事. 3. 不算 "树自足": 这是搬证书, 判据还是 "有 `≲` 到一棵已有证书的树".
>
> **逐阶段的输入.** 树: 没有 (`T₀ʷ` 不变). `Tc`: 第 1 层的 `Rs` 项 (`Tc-Ω₁`). 证书: 无. 阶段的定制见上面判断 2.
>
> **读了记号的 (如实).** 定义与证书不读记号. 形状: `T₀ʷ` 的形状来自对塔的测试 ([GuardWeak](GuardWeak.lagda.md)). 这里新增的不变量 (`FlrLe`, `Md`, `InvS`) 是桥逼出来的, 对面是 `OCF.Free`, 它的形状来自记号 ([Uniform4Base](Uniform4Base.lagda.md)). 标签只在 [Accept](GuardCertAccept.lagda.md).
>
> **壁垒.** 比较只读字面上界之下的值 (`bd`). `FlrLe`, `CvL` 是 $\sqsubseteq$ 的命题, 不进比较, 只进证书. 判断: 不触犯 `no-bra-cmp`, `no-lim-cmp`, `¬tri`; 没有形式对比.
>
> **审计.** `importclosure.py` (编译器保证): `GuardCertMain`, `GuardCertFold`, `GuardCertHi`, `GuardCertNf`, `GuardCertRel`, `GuardCertHt` 干净, 退出码 0; `GuardCertAccept` 退出码 1 (读记号, 例外). `depslice.py` (语法级, 到达块数/记号块/词命中): `GuardCertMain:Good-Ω+1` 1425/0/0, `≲-Ω+1` 916/0/0, `GuardCertFold:R-ψ` 818/0/0, `R-ψᵒ` 793/0/0, `GuardCertNf:hp-cT` 430/0/0, `GuardCertRel:RΩ̇` 253/0/0, `GuardCertHt:no-triᴸ` 3/0/0. 正对照 `GuardCertAccept:label-Ω+1` 2799/59/368. 切片看不见隐式参数和模块别名; 闭包只保证不引用.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 trustMe.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCert where

open import OCF.Align.GuardCertMain using (Good-Ω+1; ≲-Ω+1; value-Ω+1)
open import OCF.Align.GuardCertFold using (R-ψ; R-ψᵒ)
open import OCF.Align.GuardCertNf using (fr-zero; fr-suc; fr-lim; fr-end; fr-le; hp-c₁; hp-cT)
open import OCF.Align.GuardCertRel using (Rs; module EmbR; FlrLe; InvS; Md; HPf; hp-free)
open import OCF.Align.GuardCertHi using (Rc; CvL; fromRs; ι-Rc; RΩ̇₀; rep-Rc)
open import OCF.Align.GuardCertHt using (tr<ᴸ; assocᴸ; irrᴸ; no<ᴸ; recᴸ; recᴸ-β; no-triᴸ; no-botᴸ; no-viewᴸ; keep-Ω+2)
```
