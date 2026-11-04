# 序数高度

> **判决 (编译过, 无条件, `--safe`).** 目标 1 (结构的弱化): **HOLDS, 但有一处偏离**: `HtB` 的 `tri` 的相等是 $\equiv$ 不是 $\cong$, 见下. 目标 2 (`Ordᴵ` 带证书的子类型作高度): **HOLDS**. 目标 3 (第一个跨过去的高度, 与 `HS∞`, `HS₂` 一致): **HOLDS**, 读法是判断. 目标 4: 判断, 另有两条编译过的否定.
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `GᴺTᵠ` | 对一切 `𝕊 : HtB`, 一切 $m$, $\alpha$: `Goodᴺ (toZ (Tᵠ m α ev z))` | [LadderOrdMain](LadderOrdMain.lagda.md) |
> | `HB` | 对一切码 `M : Code`, `HB M : HtB`, 字段全闭合 | [LadderOrdPos](LadderOrdPos.lagda.md) |
> | `Gᵒ M α`, `Gᵖ M p α` | 对一切 $M$, 位置 $p$, $\alpha$ 有 `Goodᴺ`, 无条件 | [LadderOrdCert](LadderOrdCert.lagda.md) |
> | `Gˢ h α`, `code-val h` | 对一切带证书 `Str η` 的 $\eta$; 高度的值与 $\eta$ 互相 `≼` | [LadderOrdCert](LadderOrdCert.lagda.md), [LadderOrdStr](LadderOrdStr.lagda.md) |
> | `Gη η α`, `dom₀ η` | 对一切 `η : Ordᴵ`, 无证书; 只保证高度的值不低于 $\eta$ | 同上, [LadderOrdCode](LadderOrdCode.lagda.md) |
> | `Gω·2`, `Gω²`, `Gω^ω`, `Gε₀` | 检查点 | [LadderOrdCert](LadderOrdCert.lagda.md) |
> | `grow r`, `growᵖ` | `HtB` 上 $n<m$ 时第 0 行的计值字面严格增长 | [LadderOrdGrow](LadderOrdGrow.lagda.md) |
> | `bridge∞`, `bridge₂`, `bridge²` | `T∞.Tᵠ m α ≈ᴿ O∞.Tᵠ (e∞ m) α′` 等: `HS∞`, `HS₂` 的树与码上的树同值 | [LadderOrdInst](LadderOrdInst.lagda.md), 一般形式 [LadderOrdCross](LadderOrdCross.lagda.md) |
> | `agree₂`, `fgh₂`, `agree∞`, `fgh∞`, `agree²`, `fgh²` | 计值 $\cong$, FGH 逐点相等, 对一切 $m$, $\alpha$ | [LadderOrdAgree](LadderOrdAgree.lagda.md) |
> | `agree-NF`, `fgh-NF`, `anchor-ω`, `fgh-ω` | 接到 `LadderNFMain` 的树与 `GᴺTω` (带标签的 $\psi_0(\Omega_{\psi_1(1)})$) | [LadderOrdAgree](LadderOrdAgree.lagda.md) |
> | `cross₂`, `cross²` | `HS₂` 的每个第 0 项 $\prec$ `ω·ᶜ 1` 的顶, $\prec$ `ω²ᶜ` 的顶 | [LadderOrdAgree](LadderOrdAgree.lagda.md) |
> | `Tω·2`, `Tω²`, `Tω^ω`, `Tε₀`, `T-feed`, `fgh…` | 闭项与 FGH | [LadderOrdClosed](LadderOrdClosed.lagda.md) |
> | `viewE→LPO`, `viewE-val` | 每个 `Ordᴵ` 都有写法 (含 "空") 推出 LPO; 在码的值上成立 | [LadderOrdNeg](LadderOrdNeg.lagda.md) |
> | `no-all-Ord`, `all-Ord→LPO` | 一个 `HtB` 含全部 `Ordᴵ`: 字面忠实推出 $\bot$, 忠实到值推出 LPO | 同上 |
> | `no-tri-code`, `no-cofinal`, `no-step²` | 码的全局三歧假; `HB M` 不穷尽 `Ordᴵ`; `view-step` 在 $\omega^2$ 上假 | 同上 |
>
> **上一轮的问题: 工程量还是更深.** 两者都不是, 三件事都由选载体消去了. 把高度取成 "$M$ 之下位置的规范形" `Pos (cs M)`:
>
> - (a) `teq refl` 不用换成高度搬运: 位置表示唯一, 相等就是 $\equiv$. 与 $\cong$ 的关系是定理: `rk-inj` (秩 $\cong$ 推出位置 $\equiv$), `rk-dec` (三歧写回 `<ᴵ-dec` 的形式).
> - (b) `upd`, `lo`, `cap` 不用改: `Fv = Ht → Flr` 的 `Ht` 已经是 $M$ 之下的段, 字面公共上界就是 $M$.
> - (c) `Rq` 的同一个 $q$ 不用放宽: $<$ 是命题 (`<-prop`), 只在跨世界时用一次 (`R-Ω↓-castʳ`, `R-cl-castʳ`).
>
> 所以闭包定理 27 个模块只有 `LadderOrdOmega` 有补丁 (31 行新代码: `low⊑`, `step-mono`, `mono-rowL`), 其余除了名字逐字相同 (`Survey/scripts/ladderord/mk_ord.py`, 脚本比较). **偏离要说明:** 让 `HtB` 的相等字面是 $\cong$ 的版本没有写; (a), (b), (c) 在那个版本里是否是工程量, 这里没有回答. 上面只说明它不需要.
>
> **`HtB` 的字段清单 (11 个, [LadderOrdBase](LadderOrdBase.lagda.md)).** `Ht`, `_<ᴸ_`, `h₀`, `tr<`, `<-prop`, `bot`, `tri`, `rk`, `rk<`, `view`, `view-ok`. 导出: `irr`, `no<`, `tr-assoc`, `Rec`, `Rec-β`. 与 `HtS` 比, 去掉 `irr`, `no<`, `tr-assoc`, `Rec`, `Rec-β`, `view-step`, 加 `<-prop`, `rk`, `rk<`, `view-ok`.
>
> - **`Rec-β` 没有函数外延.** 右边要字面是 `Rec X F n`. 递归走秩的字面路径, 秩的相等用 `e` 带着, 基本情形消掉 (`RecR`). 位置不是彼此的子项, 秩才是; 所以秩要把 $<$ 映到字面路径, 这要 `plus` 的累积和 (`Sb`).
> - **`view-step` 是假的 (`no-step²`).** 换成对高度归纳 `low⊑`: 一切 $n<m$ 有 $\iota_\downarrow(\dot\Omega_n\,0)\sqsubseteq\dot\Omega_m\,0$. 上一轮写的 "看上去是对 $m$ 的归纳加共尾" 是对的; 要的就是 `view-ok`.
>
> **码.** `cz`, `cs c`, `cl g`, `cl g` 的值是 $\sum_j(g_j+1)$. 累加天生严格, 没有退化极限, 头部判定零/后继/极限. 这是证书做进结构的 `Ordᴵ` 子类型 (`val`, `val-Str`). 带证书的 `Ordᴵ` 全部以原值进来 (`code`, `code-val`). 不带证书的 `Ordᴵ` 用 `⌈_⌉` 进来, 非严格极限被求和放大, 只保证不低 (`dom₀`). 这不能修: `viewE→LPO`. **这更正了上一轮 "`bot`, `view` 假是退化极限造成的, 修 `View` 就能绕开" 的判断**: 加上 "空" 情形也要判定极限是否退化, 推出 LPO. 证书是必需的.
>
> **第一个跨过去的高度 (判断).** 码 `ω·ᶜ 1` 的顶, 值 $\omega\cdot2$, 第 0 行是 $\sup_i\iota_\downarrow(\dot\Omega_{\omega+i}\,0)$. 读作 $\psi_0(\Omega_{\Omega\cdot\omega\cdot2})$. 按 $\psi_1(\alpha)=\Omega\cdot\omega^\alpha$ 的读法, $\omega^2$ 是 $\psi_0(\Omega_{\psi_1(2)})$, $\omega^\omega$ 是 $\psi_0(\Omega_{\psi_1(\omega)})$, $\varepsilon_0$ 是 $\psi_0(\Omega_{\psi_1(\varepsilon_0)})$; `T-feed` 读作 $\eta=\psi_0(\Omega_{\Omega\cdot\eta})$ 一带. **都没有标签.** 定理只到: 这些树有 `Goodᴺ`; 第 0 行严格高于下面的 (`grow`, `cross₂`); 下面的值与 `HS∞`, `HS₂` 一致; `ωᶜ` 的顶就是带标签的 $\psi_0(\Omega_{\psi_1(1)})$ (`anchor-ω`).
>
> **目标 4 (判断, 没有编译).** 只靠 `Ordᴵ` 高度不够. $\psi_1(\Omega)=\Omega\cdot\Omega$ 是 $\Omega\cdot\eta$ ($\eta<\Omega$) 的上确界, 共尾度 $\Omega$; 这里每个高度都在一个可数的 $M$ 里, `HB` 拿到的是它下面的全部, 但拿不到它本身. 它的第 0 行要是 $\sup_\eta\iota_\downarrow(\dot\Omega_\eta\,0)$, 其中 $\eta$ 跑遍一切可数高度, 要一个高度类型装下所有 $\eta$ 并有三歧, 这是 `no-all-Ord`, `all-Ord→LPO` 否定的 (单一高度类型), 也是壁垒定理的形状. 这两条不否定下面的办法: 像 $\Omega$ 在对象层那样, 第 0 行是一个绑定高度的节点, 折叠走链 $\eta_0<\eta_1<\dots$, 字面公共上界只沿链存在 (`cl` 链本身). 这要 (i) $M\subset M'$ 之间的上移, 现在只有实例 `bridge²` 这样的模拟, 没有树上的算子; (ii) 节点跨 $M$; (iii) `Ψ` 过这个节点时的目标比较. 没有试, **未走通, 不是否定**. `T-feed` 说明输出回灌作高度本身没有障碍, 但那仍在 $\psi_1(\Omega)$ 之下.
>
> **有限测试 (不是证明).** [LadderOrdClosed](LadderOrdClosed.lagda.md) §2: `fghω·2`, `fghω²`, `fghε₀` 在 0 上是 1, 在 1 上是 2; `Tω·2`, `Tω²`, `Tω^ω`, `Tε₀`, `T-feed` 是极限.
>
> **是否按阶段定制: 否.** 闭包定理, `low⊑`, `grow` 是 `HtB` 的定理, 对高度归纳. 实例 `HB M` 对 $M$ 一致, 不分阶段. `viewC` 按码的头分三种写法, 这是数据.
>
> **受记号影响的形状 (如实说).** 与 [LadderInf](LadderInf.lagda.md) 的账相同, 这不是 "树自足": 第 0 行分根层/闭包/链, 链行第 0 项是 1, 都读自记号; 高度 $\eta$ 对应 $\Omega\cdot(1+\eta)$ 的读法也是. 新增的 `Code`, `Pos`, `Str`, `rk` 是 Brouwer 树的累加形式, 没有看记号. 码的链取块的结束点 (`blk i end`), 这决定了树的基本列; 在 `HS∞`, `HS₂` 的范围内与原来的一致 (定理), 再往上没有和记号对过.
>
> **没有做的.** 一般的 $M\subset M'$ 定理 (只有 `bridge²` 这一个实例); 标签 (没有试); `Cross` 的左边是 `HtS` 世界, 两个 `HtB` 世界之间没有写.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. `HtB` 是结构参数, 实例 `HB M` 对每个 $M$ 闭合.

## 审计

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd OCF.Align.LadderOrd`: 禁用表命中 0, `--only` 之外 0; 闭包内没有 `*W*` 克隆, `*Accept`, `ScafLadder*`. `LadderOrdCert`, `LadderOrdClosed`, `LadderOrdAgree`, `LadderOrdNeg`, `LadderOrdInst`, `LadderOrdGrow`, `LadderOrdStr` 单独跑同样.
- **定义级切片 `depslice.py`:** `Gᵒ` 1082 块, 记号 0, 词命中 0; `Gη` 1085, 0, 0; `Gˢ` 1090, 0, 0; `Gω²` 1087, 0, 0; `Gε₀` 1091, 0, 0; `T-feed` 1092, 0, 0; `cross₂` 1902, 0, 0; `agree₂` 1873, 0, 0; `bridge₂` 475, 0, 0; `HB` 77, 0, 0; `grow` 1049, 0, 0; `all-Ord→LPO` 33, 0, 0.
- **正对照:** `LadderInfAccept:label-∞0` (读记号) 3268 块, 记号 92, 词命中 379.
- 切片是语法级的, 模块别名和隐式参数看不见; 闭包是编译器保证的, 但不说明定义没有受记号启发.
- **禁用构造:** 全部 `LadderOrd*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; 全部带 `--safe --without-K`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrd where

open import OCF.Align.LadderOrdBase public using (HtB; ViewOk)
open import OCF.Align.LadderOrdPos public using (Code; cz; cs; cl; Pos; end; low; blk; _<ᴾ_; <ᴾ-tri; <ᴾ-prop; val; rkP; rk-inj; rk-dec; HB)
open import OCF.Align.LadderOrdCode public using (⌈_⌉; dom₀; _≼_; ωᶜ; ω·ᶜ; ω²ᶜ; ω^ωᶜ; ε₀ᶜ)
open import OCF.Align.LadderOrdStr public using (Str; code; code-val; val-Str)
open import OCF.Align.LadderOrdCert public using (Tᵖ; Tᵒ; Gᵖ; Gᵒ; Gˢ; Gη; Gω·2; Gω²; Gω^ω; Gε₀; growᵖ)
open import OCF.Align.LadderOrdClosed public using (Tᶜ; fghᶜ; Tω·2; Tω²; Tω^ω; Tε₀; fghω·2; fghω²; fghω^ω; fghε₀; η*; T-feed; fgh-feed)
open import OCF.Align.LadderOrdInst public using (bridge∞; bridge₂; bridge²; rk-fin₂; rk-top₀; rk-top-suc; rk-end₂)
open import OCF.Align.LadderOrdAgree public using (agree₂; fgh₂; agree∞; fgh∞; agree-NF; fgh-NF; anchor-ω; fgh-ω; agree²; fgh²; cross₂; cross²)
open import OCF.Align.LadderOrdNeg public using (viewE→LPO; viewE-val; no-tri-code; no-step²; no-cofinal; no-all-Ord; all-Ord→LPO)
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [LadderOrdBase](LadderOrdBase.lagda.md) | 结构 `HtB`, 由秩导出 `Rec`, `Rec-β` |
| [LadderOrdPos](LadderOrdPos.lagda.md) | 码, 位置, 序, 秩, 第 0 行的写法, 实例 `HB` |
| [LadderOrdCode](LadderOrdCode.lagda.md) | 检查点的码, `⌈_⌉`, `≼` |
| [LadderOrdStr](LadderOrdStr.lagda.md) | 严格 `Ordᴵ` 的精确码 |
| `LadderOrd{Tree,Rel,Cx,Rules,Rules2,Rules3,Strict,Strict2,Strict3,Class,ClassF,Good,Vis,Read,Iota,Tr,Add,Psi,PsiH,Eval,Tail,Mono,Root,Omega,Main,Dn,DnSelf}` | 闭包定理, 由 `Survey/scripts/ladderord/mk_ord.py` 从 `LadderInf*` 生成, 只有 `Omega` 有补丁 |
| [LadderOrdGrow](LadderOrdGrow.lagda.md) | `grow` |
| [LadderOrdCross](LadderOrdCross.lagda.md), [LadderOrdCrossEq](LadderOrdCrossEq.lagda.md) | 跨世界的模拟, 由 `Survey/scripts/ladderord/mk_cross.py` 从 `LadderInfBridge` 改写 |
| [LadderOrdInst](LadderOrdInst.lagda.md) | `HS∞`, `HS₂` 进码的实例 |
| [LadderOrdCert](LadderOrdCert.lagda.md) | 实例上的证书 |
| [LadderOrdClosed](LadderOrdClosed.lagda.md) | 闭项, FGH, 有限测试 |
| [LadderOrdAgree](LadderOrdAgree.lagda.md) | 值的一致, `cross` |
| [LadderOrdNeg](LadderOrdNeg.lagda.md) | 否定 |
