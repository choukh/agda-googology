# 主线直接标: 标签不再走克隆的证书; 第一个新高度上字面的 `Lab` 是假的

> **判决 (编译过, 无条件, `--safe`). 目标 2 (主线直接标): HOLDS. 目标 1 (标签推到高度 $\omega\cdot2$, $\omega^2$): 字面 `Lab` 是假的, 有编译过的否定; 替代读法到第 0 行 (PARTIAL). 目标 3 (一般的 $M$): 定理形式对一切 `HtB`, `PxB` 成立, 但 `PxB` 只能逐个实例, 而且在码 `ω·ᶜ 1` 上不存在.** 这是标签路线, 文件读记号, 不算记号无关. 证书没有改动, 也不依赖标签.
>
> | 定理 | 陈述 | 文件 | 世界 |
> | --- | --- | --- | --- |
> | `label-∞`, `label-fin`, `label-top`, `label-ψ₁+Ω`, `label-ψ₁+Ω·n`, `label-ψ₁+Ω+1` | 与 `LadderLabAccept` 同陈述, 但 `GᴺTᵠ` 是**主线** `LadderInfMain` 的 | [OrdLabAccept](OrdLabAccept.lagda.md) | 主线 |
> | `ord-top₂`, `ord-top²`, `ord-fin₂`, `ord-∞`, `ord-fin∞` | 上面经 `agree₂`, `agree²`, `agree∞` 搬到 `LadderOrd` 的树: `Lab (forceᴺ _ (G₂.GᴺTᵠ (e₂ (top n)) α ev p))` $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot n+\theta})$ | 同上 | 主线 |
> | `nf-main`, `mono-main` | `LadderNFMain.GᴺTᵠ`, `LadderMonoMain.GᴺTω` 上的标签, 此前只在克隆上 | 同上 | 主线 |
> | `clone-top`, `clone-∞`, `clone-fin`, `fgh-top` | $\llbracket$ 主线计值 $\rrbracket\cong$ 克隆计值, FGH 逐点相等, 对一切带标签的输入, 两边的环境任意 | [OrdLabCross](OrdLabCross.lagda.md) | 跨世界 |
> | `lab⟦⟧`, `cross` | 主线的 `Lab` 搬到克隆世界的 `Lab`; 同标签则互模拟 | 同上 | 跨世界 |
> | `chain-row` | 对一切 `HtB`: 链行第 0 行 $\cong$ `lim h`, `h 0` 是 `ωZ` 的计值, `h (i+1)` $\cong$ 高度 `F i` 的第 0 行. 不读记号 | [OrdLabChain](OrdLabChain.lagda.md) | 主线 |
> | `chain-needs-zero` | 对一切 `HtB`, 链行, $\omega$-共尾的 $u$: `Lab` (第 0 行) $\psi_0(\Omega_u)$ $\Rightarrow$ $u[0]=0$ | [OrdLabRead](OrdLabRead.lagda.md) | 主线 |
> | `no-lab-M₂`, `no-lab-pos`, `no-lab-ω²` | 码 `ω·ᶜ 1` 的顶, 码 `ω²ᶜ` 的位置 $\omega\cdot2$ 不带 $\psi_0(\Omega_{\psi_1(1)\cdot2})$; 码 `ω²ᶜ` 的顶不带 $\psi_0(\Omega_{\psi_1(2)})$ | [OrdLabReadTop](OrdLabReadTop.lagda.md) | 主线 |
> | `no-PxB`, `no-PxB-M₂` | 若 $m$, $F_0$ 是链行, $F_1$ 是闭包行, 则没有任何 `PxB`; 码 `ω·ᶜ 1` 就是这样 | [OrdLabBInst](OrdLabBInst.lagda.md) | 主线 |
> | `label-Tᴸ` | `Tᴸ` = `lim` $n\mapsto$ 第 $n$ 行 (`e₂ (top n)`) 带字面标签 $t=\psi_0(\Omega_{\psi_1(1)\cdot2})$. `Tᴸ` 由 `LadderOrd` 的树取极限得到, 但不是 `LadderOrd` 的某棵树 | [OrdLabReadTop](OrdLabReadTop.lagda.md) | 主线 |
> | `tail-M₂`, `same-M₂` | 码 `ω·ᶜ 1` 的顶 $=[\omega,t[0],t[1],\dots]$; 与 `Tᴸ` 互相 $\sqsubseteq$ | 同上 | 主线 |
> | `tail-pos`, `same-pos`, `fgh-pos` | 码 `ω²ᶜ` 的位置 $\omega\cdot2$ $=[\omega,t[1],t[2],\dots]$; 与 `Tᴸ` 互相 $\sqsubseteq$; $n\ge1$ 时 FGH 与 `Tᴸ` 相等 | 同上 | 主线 |
> | `head-ω²0`, `head-ω²1`, `tail-ω²2` | $\omega^2$ 顶的第 0, 1 项带 $\psi_0(\Omega_{\psi_1(2)})$ 的字面标签; 第 2 项 $\cong$ 上面的位置 | 同上 | 主线 |
> | `label-cert` (`OrdLabBTop`) | 对一切 `HtB`, `PxB`: 证书计值带 $\psi_0(\Omega_{P\,m\,\theta})$, 前提是标准形 | [OrdLabBTop](OrdLabBTop.lagda.md) | 主线 |
> | `Px-ω`, `label-ω`, `label-ωfin` | `HB ωᶜ` 有 `PxB`; 不经 `agree` 直接贴在 `LadderOrdTree (HB ωᶜ)` 上 | [OrdLabBInst](OrdLabBInst.lagda.md) | 主线 |
>
> **有限测试 (不是证明).** [OrdLabReadTest](OrdLabReadTest.lagda.md): 比较器是树的形状与 FGH, `refl`. 盲区: 只看几个点. 读法就是由这几条找到的, 定理形式是 `chain-needs-zero`.
>
> **为什么之前要克隆 (读 `Survey/scripts/laddernf/mk_w.py`, `LadderNFAccept` 文件头).** `Lq`, `Lab` 建在 `OCF.Align.Level` 上, 主线建在 `OCF.Free.Level` 上, 两份数据类型字面相同但不是同一个类型. 当时选的方向是把证书改导入, 克隆到标签世界 (`LadderLabZInfW*`). `OCF.Free.Lab` 走过相反方向, 但只切了 $\psi_0(\Omega_{\Omega\cdot2})$ 的链, 没有 `sψ`, `oτ`, `omk` 等后来的补丁.
>
> **怎么做的.** 相反方向对现在的标签链也可行, 而且便宜: `Survey/scripts/ordlab/mk_rebase.py` 从 `LadderLab*` 做定义级切片, 边界是主线与 `EBO`. 克隆的证书 `LadderLabZInfW*`, `LadderLabZNFW*` 换成主线同名模块, 不进切片. 与主线逐字相同的块转出; 到达不了 `Level` 的纯记号块也转出 (所以 `NF₁`, `Sb`, `Ctbl` 与克隆世界是同一个类型, `clone-top` 才陈述得出来). 得到 `OrdLabZ*` 38 个切片, 约 4750 行定义, 代码行逐字; 标签类 10 个模块只改导入. 没有新的数学补丁. 证书的克隆数量: 0.
>
> **`Lab` 为什么假 (判决的核心).** 树的链行字面是 $[\omega,\ \dot\Omega_{F_0},\ \dot\Omega_{F_1},\dots]$ (`rowL`, 第 0 项 `𝟏L`). 这与 $\psi_1(1)[n]=\Omega\cdot n$ 对齐, 因为 $\psi_1(1)[0]=0$. 而 $\psi_1(1)\cdot2$ 的基本列第 0 项是 $\psi_1(1)$. 上一轮写的 "看上去是把 `sψ`, `singψ`, `PxS` 对 $k$ 一致化" 不对: 那是记号一侧, 卡住的是树的第 0 项. 定义不能因验收改动, 所以字面 `Lab` 到这里停. 第 3 项起 ($\psi_1(1)\cdot3$, 也就是 $\omega^2$ 顶的第 3 项) 和第 $\alpha\ge1$ 行没有结果: **未走通, 不是否定.** 第 1 行的第 0 项有有限测试 `t5`, 判断它继承同样的差别.
>
> **第一个障碍.** `Row₀` 的 `rl` 要 `fsn (P m []) 0 ≡ []`. 对 $\psi_1(1)\cdot2$:
>
> `ψ¹ ∷ OCF.Align.EBO.trm (OCF.Align.EBO.fsn↓ ψ¹ [] 0) != [] of type Data.List.List OCF.Align.EBO.PT when checking that the expression refl has type fsn (ψ¹ ∷ ψ¹ ∷ []) 0 ≡ []`
>
> `no-PxB` 说明这不是选错了 $P$: 在码 `ω·ᶜ 1` 上任何 $P$ 都不行. **`no-PxB` 否定的只是** "`PxB`/`Row₀` 逐项一致" 用在这种形状的码上. 它不否定: 别的码 (`ω²ᶜ` 没有被 `no-PxB` 覆盖, 只有固定读法的 `no-lab-pos`, `no-lab-ω²`); 改记号或改验收标准; 树的强度.
>
> **下一步 (判断, 没有试).** 要过 $\omega\cdot2$ 有两条: (a) 改记号: $\Omega_u[0]=1$ ($u$ 的末项下标非 0 时), 其余不动, 这对已有的项不变, 码用 `ω²ᶜ` 对齐, 代价是 `EBO` 的克隆和 `NF₁` 闭包的重证, 另外这是按树的形状改尺子, 验收的含义变弱; (b) 只比较 "除第 0 项外逐项一致" 的弱标签, 但 `Lab-uniq` 就不成立了, 而层号要用它. 这两条都超出本轮.
>
> **目标 3.** `label-cert` 对一切 `HtB`, `PxB` 成立 (`OrdLabB*`, 只换名字, 一行不用改: 类不用 `view-step`). 但没有 "`Lab` 对 `Str` 码归纳" 这样的定理: `no-PxB`, `chain-needs-zero` 说明链行的前缀必须是 $\psi_v(b+1)$, 这对一般的 $M$ 不成立. 现状只能逐个实例: `HB ωᶜ` 直接有, `HS∞`, `HS₂` 的段经 `agree` 进码 `ωᶜ`, `ω·ᶜ 1`, `ω²ᶜ`.
>
> **受记号影响的形状 (如实说).** 这组文件就是读记号的. `OrdLabChain` 不读记号, 只是把 `rowL` 的定义写成定理. `Tᴸ` 是为了配记号的基本列造的, 只用于说明值, 不是候选定义.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 没有写新的 `Goodᴺ`.

## 审计

- **没有克隆的证书:** 模块导入闭包 (`OrdLabAccept`, `OrdLabRead`, `OrdLabReadTop`, `OrdLabBInst`) 里 `LadderLabZInfW*`, `LadderLabZNFW*`, `LadderLabZQ` 命中 0 (脚本比较导入). 闭包里还有 `LadderLabZStandardOmega`, `LadderLabZSystemOmega` 等标签模块和 `OCF.Align.Correspond`, `OCF.Align.Level`: 那是转出纯记号块时带进来的模块层依赖. `OrdLabCross` 有意导入克隆世界. 注意切片级的 "纯" 是语法近似, 编译通过才是这里的依据: 如果转出的块碰了树, 类型对不上.
- **主线不受影响:** 本轮只新建文件. `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd OCF.Align.LadderOrd`: 通过. 加 `--only OCF.Align.OrdLabChain`, 对 `OCF.Align.OrdLabChain`: 通过, 禁用表命中 0.
- **定义级切片 `depslice.py`:** `OrdLabChain:chain-row` 1046 块, 记号 0, 词命中 0; `goodLim` 43, 0, 0; `LadderOrdMain:GᴺTᵠ` 1023, 0, 0.
- **正对照:** `OrdLabAccept:label-top` 2536 块, 记号 78, 词命中 381; `ord-top₂` 3398, 78, 382; `label-Tᴸ` 3406, 78, 385; `chain-needs-zero` 3440, 78, 392. 切片是语法级的, 模块别名和隐式参数看不见.
- **重新生成:** `mk_rebase.py`, `mk_b.py` 写到别的目录, 54 个生成文件与仓库里的逐字节相同.
- **禁用构造:** `OrdLab*` 的 `postulate`, 洞, 停机与正性编译指示, `trustMe`, `REWRITE`, `cubical` 命中 0; 选项都含 `--safe --without-K`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLab where

open import OCF.Align.OrdLabAccept public using (label-∞; label-∞1; label-∞0; label-fin; label-top; label-fin₂; label-ψ₁+Ω·n; label-ψ₁+Ω; label-ψ₁+Ω+1; ord-top₂; ord-top²; ord-fin₂; ord-∞; ord-fin∞; nf-main; mono-main)
open import OCF.Align.OrdLabCross public using (⟦_⟧; lab⟦⟧; cross; clone-top; fgh-top; clone-∞; clone-fin)
open import OCF.Align.OrdLabRead public using (ω-lab; tω·2; tω²; module NoChain; module GenRow)
open import OCF.Align.OrdLabReadTop public using (Tᴸ; label-Tᴸ; M₂-row; tail-M₂; no-lab-M₂; same-M₂; pos-row; tail-pos; no-lab-pos; fgh-pos; same-pos; top-row; head-ω²0; head-ω²1; tail-ω²2; no-lab-ω²)
open import OCF.Align.OrdLabBInst public using (rule4; module NoPx; no-PxB-M₂; Px-ω; label-ω; label-ωfin)
import OCF.Align.OrdLabReadTest
import OCF.Align.OrdLabChain
import OCF.Align.OrdLabBTop
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [OrdLabAccept](OrdLabAccept.lagda.md) | 主线上的标签定理 |
| [OrdLabCross](OrdLabCross.lagda.md) | 克隆与主线的定理 |
| [OrdLabChain](OrdLabChain.lagda.md) | 链行的展开, 不读记号 |
| [OrdLabRead](OrdLabRead.lagda.md), [OrdLabReadTop](OrdLabReadTop.lagda.md) | 一般否定, 实例 |
| [OrdLabReadTest](OrdLabReadTest.lagda.md) | 有限测试 |
| [OrdLabBInst](OrdLabBInst.lagda.md) | `PxB` 的实例与边界 |
| `OrdLab{Base,Class,Rel,Psi,Eval,Inst,NFOmega,NFTop,Forget,Top}` | 标签类, `Survey/scripts/ordlab/mk_rebase.py` 由 `LadderLab*` 改导入 |
| `OrdLabB{Base,Class,Rel,Psi,Eval,Top}` | 同上对 `HtB`, `Survey/scripts/ordlab/mk_b.py` |
| `OrdLabZ*` | 标签链的切片, 不用读 |
