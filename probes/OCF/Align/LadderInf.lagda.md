# 高度抽象与 ℕ∪{∞}

> **判决 (编译过的定理, 无条件, `--safe`).** 目标 1: **HOLDS**. 目标 2: **HOLDS**. 目标 3: **PARTIAL** (只有 $\theta=0$ 有标签). 目标 4: **HOLDS** (实例 $\omega+\omega$), 字面的 `Ordᴵ` 实例不存在 (编译过的否定, 只杀这个结构原样搬过去).
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `GᴺTᵠ` | 对一切高度结构 `𝕊 : HtS`, 一切 $m$, $\alpha$: `Goodᴺ (toZ (Tᵠ m α ev z))` | [LadderInfMain](LadderInfMain.lagda.md) |
> | `bridge` | `N.Tᵠ m α ≈ᴿ I.Tᵠ m α′` ($\alpha\cong\alpha'$): ℕ 实例与 `LadderNFTree` 的树同值 | [LadderInfBridge](LadderInfBridge.lagda.md) |
> | `agree-ℕ`, `fgh-ℕ` | 两边证书的计值 $\cong$, FGH 逐点相等 | [LadderInfAgree](LadderInfAgree.lagda.md) |
> | `G∞ α` | $\psi_0(\Omega_{\psi_1(1)+\alpha})$, 一切 $\alpha$, 无条件 | [LadderInfCert](LadderInfCert.lagda.md) |
> | `anchor`, `forceᴺ-∞0`, `fgh-∞0` | $\dot\Omega_\infty\,0$ 的值就是 `GᴺTω` 的值 | [LadderInfAgree](LadderInfAgree.lagda.md) |
> | `G₂ n α`, `G₂ψ₁+Ω` | 实例 $\omega+\omega$: 高度 `top n`, 一切 $n$, $\alpha$; `top 1` 的第 0 行读作 $\Omega_{\psi_1(1)+\Omega}$ (读法是判断) | [LadderInfCert](LadderInfCert.lagda.md) |
> | `label-∞0`, `label-fin` | 克隆世界: 标签 $\psi_0(\Omega_{\psi_1(1)})$; 有限部分带已有标签 | [LadderInfAccept](LadderInfAccept.lagda.md) |
> | `no-triᴼ`, `no-botᴼ`, `no-viewᴼ` | $(\mathrm{Ord}^I,<^I,0)$ 上字段 `tri`, `bot`, `view` 不成立 | [LadderInfOrd](LadderInfOrd.lagda.md) |
>
> **上一轮的判断对不对.** "高度只经 `Hi`, `tri`, `upd-lt` 用到": **大体对, 但不够.** 三处是那个判断没看到的:
>
> 1. **对高度的递归.** `Vs`, `LVq`, `LV`, `Ω̇`, `RΩ̇`, `𝟏⊑Ω̇`, `Ω̇G′` 都对 $m$ 递归. 所以结构要有 `Rec`, `Rec-β`. `Vs` 的展开原来是定义性的, 现在是命题相等 (`outV`, `intoV`, `out-intoV`); 证书原来就只经 `outV`, `intoV` 走, 所以只在 `ι↓` 一带要加 `subst`.
> 2. **`ι↓` 的目标不只是 $n+1$.** $\iota_{\downarrow\infty}$ 跳过很多层, `qwk` 过 `ι↓` 要 `Sub n a b → Sub m (…) (…)`, 而 `Sub n` 对高于 $n$ 的格没有信息. 所以 `ι↓ d : Q n k φ χ → Q m α φ (cap χ n (flo k))`, `cap` 把高于 $n$ 的格设成平凡. 这是这一轮唯一的树的修改; 在 ℕ 实例上 `cap χ n x` 与 `upd χ n x` 在 `Sim∼ (n+1)` 下一致 (`cap∼`), 所以树的值不变 (`bridge`).
> 3. **第 0 行.** `Ω̇ m zero` 按 `view` 分根层、闭包、链三种写法, 对这三种写法一次证完 (`rowG`), 不按阶段定制.
>
> 另外 `Rq` 的 `rΩ↓`, `rcl` 原来允许两边的 $n$ 不同再用 `SameQ` 排除, 抽象后 `LVq m zero (suc q′) = ⊥` 这种定义写不出, 改成两边同一个 $q$; `InvD` 那一段对 $q$ 的两边同时模式匹配要 K, 改成归纳谓词 `Inv` (同一个论证).
>
> **`HtS` 的字段清单 (编译过, `LadderInfBase`).**
>
> | 字段 | 用处 | 只用于 |
> | --- | --- | --- |
> | `Ht`, `_<ᴸ_` | 高度 | |
> | `h₀`, `no<`, `bot` | 根层 `tl` 的高度; `Eh h₀`, `Hi-0` | `tl` 在 `Q h₀`; 求值的环境 |
> | `tr<` | 目标 $H<m$ 的 `Sub`, `ι↓` 的节点 | |
> | `irr` | `upd`, `lo`, `cap` 的律 | |
> | `tri` (全局) | 定义 `upd`, `lo`, `cap` 与律; `Ψ` 的三个分支 | `Ψ`, `R-Ψ`, `Climb` 的调用都有公共上界 $m$; `upd`, `lo`, `cap` 没有 |
> | `Rec`, `Rec-β` | 上面第 1 点 | 宇宙多态: $Q$ 用 `Set₁`, $R$ 用 `Set₁`, $G$ 用 `Set₂` |
> | `view` | 第 0 行 | |
> | `tr-assoc`, `view-step` | 链行的单调 `mono-rowL` | 只有 `chain` 这一行 |
>
> 律 (`upd-self`, `upd-lt`, `upd-gt`, `lo-lt`, `lo-triv`, `cap-lt`, `cap-gt`, `cap-self`, `c-∪`, `c-sw`, `as-upd`) 由 `tri`, `irr`, `tr<` 证, 不是字段.
>
> **闭包定理的改动量 (`LadderNF*` 对 `LadderInf*`, 代码行, 脚本比较).** 15 个模块每个 9-38 行, 大部分是头部的导入; `Rel` 104, `Strict2` 49, `Mono` 35, `Root` 37, `Tail` 171 (都是 `ι↓` 带 $q$ 与缩进), `Omega` 294 (`Inv`, 链行). 没有新的支配论证.
>
> **目标 2 的实际第一个障碍.** 上一轮预期的 `ql F` 的 `VisQ` 不是障碍: `ID` 的 `VisQ zero (pD E)` 里 $b\prec0$ 是空的 (`G-stepL`). 差 $\iota_{\downarrow\infty}(\iota_\downarrow x)$ 与 $\iota_{\downarrow\infty}x$ 的 `Rq` 是 `R-ιι↓`, 形状与 `D-ι↓` 相同, 如预期; 要的是 `tr-assoc` (`R-cl-cast`, `R-Ω↓-cast`). 真正花工夫的是上面第 2 点.
>
> **目标 4: 不用 `Ordᴵ` 就过了 $\psi_1(1)+\Omega$.** 只要把 ∞ 也放进高度: $\omega+\omega$ (`LadderInfTop2`), `top (n+1)` 是闭包行, 节点可以在 `top n`. 字段全部成立, 闭包定理一行不改. 所以 `noTimes` 说的 "ℕ 高度标签不够" 在这里不成问题: 标签是 $\omega+\omega$ 的元素. 证书是定理, 读法 (`top 1` 的第 0 行是 $\Omega_{\psi_1(1)+\Omega}$) 是判断, 没有标签.
>
> **`Ordᴵ` 字面实例 (见 [LadderInfOrd](LadderInfOrd.lagda.md)).** `tr<`, `irr`, `no<`, `Rec`, `Rec-β`, `tr-assoc` 成立; `tri` 假 (`no-triᴼ`, 就是 `¬tri`); `bot`, `view` 假 (常值 $0$ 的极限, 退化情形, 修 `View` 就能绕开, 判断). 判断 (没有编译): 用字面公共上界 `<ᴵ-dec` 代替 `tri` 时, 三件事要改. (a) `Ψ` 的比较是有上界的, 但 `<ᴵ-dec` 的相等是 $\cong$ 不是 $\equiv$, `teq refl` 要换成 `Q n k` 到 `Q H k` 的高度搬运, 现在没有. (b) `upd`, `lo`, `cap` 对一切 $i$ 比较, 要把 `Fv` 换成 $i<m$ 上的族. (c) `<ᴵ` 的路径不唯一, `SameQ` 要放宽到 $\cong$ 的高度. 这三件是工程量还是更深, 没有试. 判断: 下一个真正需要 `Ordᴵ` 高度的地方在 $\psi_1(\Omega)$ 一带 (高度不可数), 不在 $\psi_1(1)+\Omega$.
>
> **`view-step` 的边界 (判断).** 它要链的下一项是上一项的后继, 所以 $\omega\cdot k$ 够, $\omega^2$ 不够 ($F\,(i+1)=\omega\cdot(i+1)$ 自己是极限). 放宽成 "$n<m$ 时 $\iota_\downarrow(\dot\Omega_n\,0)\sqsubseteq\dot\Omega_m\,0$" 看上去是对 $m$ 的归纳加共尾, 没有写.
>
> **是否按阶段定制: 否.** 闭包定理是 `HtS` 的一个定理, 第 0 行三种写法一次证完. `view` 决定哪个高度用哪种写法, 这是实例的数据, 闭包定理不看.
>
> **受记号影响的形状 (如实说).** 与 [LadderNF](LadderNF.lagda.md) 的账相同, 这不是 "树自足". 新增: `chain` 这一行 (第 0 项是 1, 其余 $\iota_\downarrow(\dot\Omega_{F\,i}\,0)$) 是记号 $\psi_1(1)$ 的基本列; `view` 的闭包/链的分法是记号的后继/极限. 结构本身 (`HtS`) 不读记号, 但 "高度是良序, 第 0 行分三种" 这个形状是从记号读来的.
>
> **审计 (本文件以外跑).** 见文末.
>
> **有限测试.** [LadderInfClosed](LadderInfClosed.lagda.md) §2: `fgh₀∞ 0 = 1`, `T₀∞`, `T₁∞`, `T₂Ω` 是极限. [LadderInfAccept](LadderInfAccept.lagda.md) §3.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. `HtS` 是结构参数, 三个实例 (`HSℕ`, `HS∞`, `HS₂`) 都闭合.

## 审计

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf OCF.Align.LadderInf`: 禁用表命中 0, `--only` 之外 0; 闭包内没有 `LadderNFW*`, `LadderNFAccept`, `ScafLadder*`, `LadderInfW*`, `LadderInfAccept`, `LadderMonoW*`, `LadderMonoAccept`. `LadderInfMain`, `LadderInfCert`, `LadderInfAgree`, `LadderInfClosed`, `LadderInfOrd`, `LadderInfTop2` 同样.
- **定义级切片 `depslice.py`:** `GᴺTᵠ` 1010 块, 记号 0, 词命中 0; `G∞` 1015, 0, 0; `G₂ψ₁+Ω` 1016, 0, 0; `T₁∞` 1017, 0, 0; `anchor` 463, 0, 0; `bridge` 390, 0, 0; `Ω̇` 87, 0, 0. 
- **正对照:** `label-∞0` (读记号) 3269 块, 记号 92, 词命中 380; 既有的 `Tω-cert-label` 2450 块, 记号 92, 词命中 378.
- 切片是语法级的, 模块别名和隐式参数看不见; 闭包是编译器保证的, 但不说明定义没有受记号启发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInf where

open import OCF.Align.LadderInfBase public using (HtS; View; base; clos; chain; Tri)
open import OCF.Align.LadderInfCert public using (Gℕ; G∞; G∞0; G∞1; G₂; G₂ψ₁+Ω)
open import OCF.Align.LadderInfAgree public using (agree-ℕ; fgh-ℕ; agree-fin; anchor; forceᴺ-∞0; fgh-∞0)
open import OCF.Align.LadderInfBridge public using (bridge)
open import OCF.Align.LadderInfClosed public using (T₀∞; T₁∞; T₂Ω; fgh₀∞; fgh₁∞; fgh₂Ω)
open import OCF.Align.LadderInfOrd public using (no-triᴼ; no-botᴼ; no-viewᴼ)
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [LadderInfBase](LadderInfBase.lagda.md) | 结构 `HtS` |
| [LadderInfTree](LadderInfTree.lagda.md) | 树, `ι↓`, `cap`, `view` 的第 0 行 |
| `LadderInf{Rel,Cx,Rules,Rules2,Rules3,Strict,Strict2,Strict3,Class,ClassF,Good,Vis,Read,Iota,Tr,Add,Psi,PsiH,Eval,Tail,Mono,Root,Omega}` | 闭包定理, 由 `Survey/scripts/laddernf/mk_inf.py` 与 `inf_patches.py` 从 `LadderNF*` 生成 |
| [LadderInfMain](LadderInfMain.lagda.md) | `GᴺTᵠ`, 对 `HtS` |
| [LadderInfNat](LadderInfNat.lagda.md), [LadderInfTop](LadderInfTop.lagda.md), [LadderInfTop2](LadderInfTop2.lagda.md) | 实例 ℕ, ℕ∪{∞}, ω+ω |
| [LadderInfCert](LadderInfCert.lagda.md) | 实例上的证书 |
| [LadderInfDn](LadderInfDn.lagda.md), [LadderInfDnSelf](LadderInfDnSelf.lagda.md) | 跨高度 `Dn`, `D-self` |
| [LadderInfBridge](LadderInfBridge.lagda.md), [LadderInfBridgeTop](LadderInfBridgeTop.lagda.md) | 跨世界的模拟 |
| [LadderInfAgree](LadderInfAgree.lagda.md) | 与原来的树, `anchor` |
| [LadderInfClosed](LadderInfClosed.lagda.md) | 闭项, FGH, 有限测试 |
| [LadderInfOrd](LadderInfOrd.lagda.md) | 字面的 `Ordᴵ` 实例 |
| [LadderInfAccept](LadderInfAccept.lagda.md), `LadderInfW*` | 验收, 标签 |
