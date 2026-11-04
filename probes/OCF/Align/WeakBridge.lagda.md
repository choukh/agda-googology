# 不带高度的树接上带高度的树: $\psi_0(\Omega_{\Omega+\theta})$, 一个定理覆盖 $\theta$ (判决: PARTIAL)

> 文件: [WeakBridgeBase](WeakBridgeBase.lagda.md) (层号族 `c⁺ θ`), [WeakBridgeNf](WeakBridgeNf.lagda.md) (规范位置), [WeakBridgeRel](WeakBridgeRel.lagda.md) (右边的 `≃`), [WeakBridgeC](WeakBridgeC.lagda.md) (关系 `C`), [WeakBridgeOp](WeakBridgeOp.lagda.md) (右边的运算, 加法), [WeakBridgeTr](WeakBridgeTr.lagda.md) (左边的 `≈`), [WeakBridgeEmb](WeakBridgeEmb.lagda.md) (左边的 `ι`, $\dot\Omega$), [WeakBridgeSel](WeakBridgeSel.lagda.md) (状态, 比较, 闭包的界), [WeakBridgeFold](WeakBridgeFold.lagda.md) (折叠), [WeakBridgeMain](WeakBridgeMain.lagda.md) (证书, 闭项, FGH), [WeakBridgeNext](WeakBridgeNext.lagda.md) ($\Omega\cdot2$ 的第一个差别), [WeakBridgeAccept](WeakBridgeAccept.lagda.md) (有限测试, 只有它是验收). 接 [GuardCert](GuardCert.lagda.md), [LadderInf](LadderInf.lagda.md).
>
> **判决: PARTIAL. 对一切 $\theta$: `Good-θ θ : Goodᴺ (T₀ʷ (c⁺ θ) (cf⁺ θ) (tc⁺ θ))`, 无条件, 经 `Good-≲` 搬自 `GᴺTᵠ 0 θ` (实例 ℕ, 高度 0), 一条定理, 不按 $\theta$ 定制, 含 `keep-Ω+2` 所说的 $c_1+2$, 含极限 $\theta$. 导入闭包干净. $\psi_0(\Omega_{\Omega\cdot2})$ 及以上没有做 (判断的第一个障碍见下), 没有否定.**
>
> **与 [GuardCert](GuardCert.lagda.md) 的差别: 没有 `Tgt` 写死在 $c_1+1$, 没有 `Sf`, `P = suc self`, `R-ψᵒ` 目标 $c_1$.** 右边换成 `LadderInfTree` 的 `Q 0 B φ χ`. 四件事:
>
> 1. **关系的下标是界 `M`, 不是层** ([WeakBridgeC](WeakBridgeC.lagda.md)). 负出现 (`cΩ` 的前提) 对 `M` 递归, 右边的层是隐式的. 所以右边的 `ι`, `trQ`, `tr⁻Q` 不用换下标, 左边的 `ι` 不改右边 (`R-ιL`), 两半分开证. `C-up`, `C-≅`: 界变大, 界沿 $\cong$.
> 2. **`omk`:** 左边 `ι` 读 $z$, 右边 `ι` 丢掉 `omk`. `cm` 记: $z\sim\hat z$, 右边是 $\hat z$ 经一串运算 `Ops` 的像, 模 `≃`. 在 `R-ιL` 里: 对 $z\sim\hat z$ 归纳得 $\iota z\sim\hat z$, 再用 `R-ap`. 这里 **不需要** `ι` 的复合律 (上一轮判断要 $\iota_r\circ\iota_q$ 对 $\iota_{r\circ q}$).
> 3. **`keepP` 只看节点的类** (`keepP-lo`, `keepP-hi`): 低层答 `false`, 高层答 `true`, 对一切 $\theta$, 含极限层上模 `⊴` 的搬运. 所以高层节点的链保留全部帧 (`trim-bk`), `cΩ` 的前提是 `CvL ξ ξ̂`.
> 4. **规范路径过极限层** (`pnt`, `nj-NT`): `⊴⁺` 把规范路径搬成规范路径. 这是 `Cfˢ` 由 `wf⁺` 具体给出才有的.
>
> **编译过的定理 (无条件, 无模块参数作假设; `θ` 是全称的模块参数).**
>
> | 定理 | 文件 | 陈述 |
> |---|---|---|
> | **`Good-θ`** | [Main](WeakBridgeMain.lagda.md) | `∀ θ → Goodᴺ (T⁺ θ)`, `T⁺ θ = T₀ʷ (c⁺ θ) (cf⁺ θ) (tc⁺ θ)` |
> | **`≲-θ`** | [Main](WeakBridgeMain.lagda.md) | `∀ θ → T⁺ θ ≲ᶻ R⁺ θ`, `R⁺ θ = toZ (I.Tᵠ 0 θ ev₀ zero)`, `I = LadderInfTree HSℕ` |
> | `value-θ`, `fgh-agree` | [Main](WeakBridgeMain.lagda.md) | 两棵树的计值 $\cong$, FGH 逐点相等 |
> | `Good-Ω+2`, `Good-Ω+ω`, `Good-Ω+ω+1`, `fgh` | [Main](WeakBridgeMain.lagda.md) | 闭项 |
> | `same-Ω+1` | [Main](WeakBridgeMain.lagda.md) | `T⁺ 1` 就是 `GuardCertMain` 的树 (`refl`) |
> | `R-ψ`, `R-ψᵒ` | [Fold](WeakBridgeFold.lagda.md) | 折叠的互模拟, 目标 0 或低层, 目标高层 |
> | `RΩ̇⁺`, `R-ιL`, `fromRs`, `ΩH` | [Emb](WeakBridgeEmb.lagda.md) | $\dot\Omega$ 对一切 $a\cong j$; 左边 `ι` |
> | `hp⁺`, `nfP`, `pnt` | [Nf](WeakBridgeNf.lagda.md) | `HPf (c⁺ θ) (tc⁺ θ)`; 低层节点的规范形; `⊴⁺` 保持规范路径 |
> | `keepP-lo`, `keepP-hi`, `trim-emp`, `trim-bk`, `nj-hiQ`, `nj-hiR`, `nj-NT`, `kb-lo`, `ka-hi` | [Sel](WeakBridgeSel.lagda.md) | 对 `c⁺ θ′` 的结构递归 |
> | `⊴⁺`, `wf⁺`, `sf⁺`, `cf⁺`, `tc⁺`, `pull⁺`, `hi-sem`, `key⁺`, `nb⁺`, `nf-nb` | [Base](WeakBridgeBase.lagda.md) | 层号族 |
> | `R-ιQ`, `R-trQ`, `R-tr⁻Q`, `Tᴿ`, `R⊕`, `rep-C` | [Op](WeakBridgeOp.lagda.md) | 关系对右边的运算封闭 |
> | `cf₂`, `keep-Ω·2` | [Next](WeakBridgeNext.lagda.md) | $c_2$ 是好层号; 键是 $c_2$ 的帧对高层节点也答 `false` |
>
> **条件定理.** 没有.
>
> **没有做到的, 第一个障碍 (判断, 没有编译的否定).** $\Omega\cdot2$: 层 `c₂` (`cf₂` 已是定理). `C` 的右边要到 `Q 1 α φ χ`, 多 `qcl`, `qΩ↓`, `Ψ`, `ι↓`. 差别的第一处: 这里有两种键的帧 ($c_1$, $c_2$), `keepP` 不再只看节点的类 (`keep-Ω·2`), 节点 $c_1+j$ 的规范位置是 `bra (j+1) e …`, 所以高层也有 `bra` 对 `bra` 的比较 (`nj-NT` 只管低层). 表里同时有两个键. 判断: 把 [Fold](WeakBridgeFold.lagda.md) 改成对一个 "层的接口" 参数化 (节点的类, 规范形, 键), 再写高度 1 的那三行, 约 1500 到 3000 行. 没有试.
>
> **目标 3 的后半, `LadderOrd`, 没有做.** 判断: 这里只用到高度结构的底 (高度 0), 对 `LadderOrd` 的高度没有任何新东西; 要接 $\psi_1(1)$ 以上, 先要过上一段. `LadderInf` 的证书在这里只用了一个实例 ℕ 的一个高度.
>
> **`≲` 还是同值.** `≲-θ` 只有一个方向 (界 $c\sqsubseteq c'$), 同值的部分: **计值 $\cong$ 是定理 (`value-θ`)**, 界的相等只有有限测试. 没有证 `R⁺ θ ≲ᶻ T⁺ θ`, 没有否定.
>
> **标签.** 这条链上没有标签定理: `GᴺTᵠ` 的标签贴在克隆世界 (`LadderInfW*`, `LadderNFW*`), 与主线的联系是代码逐字相同和有限测试. `T⁺ 1` 与 `GuardCertMain` 同一棵树, 那边有 `label-Ω+1`, 两个证书的计值 $\cong$ 这里没有写. **读法 $\psi_0(\Omega_{\Omega+\theta})$ 对一般 $\theta$ 是判断.** 判断: 只要一条 `Q 0` 与 [OCF.Free.Tree](../Free/Tree.lagda.md) 的互模拟, 就能从 `AΩ̇.label-Ω̇` 得到, 约 400 行, 没有写.
>
> **判断 (没有编译).** 1. `no-join`, `no-lim-cmp`, `¬tri`, `Barrier` 不被触犯: 比较只经 `cmpN`, `cmpK` 的字面上界 (树没变), `FlrLe`, `CvL` 不进比较; `Tri` 只用于右边的高度 ℕ. 2. 这条证书不按 $\theta$ 定制, 但按 "高度 0" 定制: `nb⁺`, `key⁺` 依赖 `c⁺` 的形状. 3. 不算 "树自足": 判据还是 "有 `≲` 到一棵已有证书的树", 对面的形状来自记号.
>
> **逐阶段的输入.** 树: 没有 (`T₀ʷ` 不变). `Tc`: `tc⁺ θ`, 全是 `Tc-Ω₁`. 证书: 无.
>
> **读了记号的 (如实).** 定义与证书不读记号. 形状: `T₀ʷ` 与 `LadderInfTree` 的形状受记号影响, 见 [GuardWeak](GuardWeak.lagda.md), [LadderInf](LadderInf.lagda.md); 新增的不变量 (`CvL`, `Ops`, `NT`) 是桥逼出来的. 标签与记号只在 [Accept](WeakBridgeAccept.lagda.md) (这一篇实际只比较树, 读塔的比较器来自 `GuardWeakAccept`).
>
> **审计.** 见文末. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 trustMe.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridge where

open import OCF.Align.WeakBridgeMain using (T⁺; R⁺; ≲-θ; Good-θ; value-θ; Good-Ω+2; Good-Ω+ω; Good-Ω+ω+1; fgh; fgh-agree; same-Ω+1)
open import OCF.Align.WeakBridgeNext using (c₂; cf₂; keep-Ω·2)
```

## 审计

- **导入闭包 (编译器保证):** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.GuardTight --only OCF.Align.GuardWeak --only OCF.Align.GuardCert --only OCF.Align.GuardBridge --only OCF.Align.GuardRead --only OCF.Align.LadderInf --only OCF.Align.LadderNF --only OCF.Align.WeakBridge OCF.Align.WeakBridge`: 退出码 0, 禁用表命中 0, `--only` 之外 0. `WeakBridgeMain`, `WeakBridgeFold`, `WeakBridgeNext` 同样. `WeakBridgeAccept` 退出码 1 (读记号, 例外).
- **定义级切片 `depslice.py` (语法级, 看不见隐式参数和模块别名; 到达块数/记号块/词命中):** `Good-θ` 1903/0/0, `≲-θ` 1148/0/0, `R-ψ` 1132/0/0, `R-ψᵒ` 981/0/0, `RΩ̇⁺` 739/0/0, `keepP-hi` 357/0/0, `⊴⁺` 254/0/0, `keep-Ω·2` 273/0/0. **正对照** `WeakBridgeAccept:k-1` 630/48/10.
- 闭包只保证不引用, 不说明没有受记号启发.
