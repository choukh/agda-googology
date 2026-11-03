# 折叠的外部规格: 闭包定义作判官 (判决: PARTIAL)

> 问题: 现在判断一棵树对不对靠记号的标签. 序数坍缩函数自己有一个不是记号的定义: Buchholz 的 $\psi_v(a)$ 是闭包 $C_v(a)$ 外最小的序数. 把它写到树上, 能不能当判官? 底座: [OCFSpecBase](OCFSpecBase.lagda.md) (规格), [OCFSpecRule](OCFSpecRule.lagda.md) (折叠的每一行), [OCFSpecAnchor](OCFSpecAnchor.lagda.md) ($v=0$ 锚点), [OCFSpecOne](OCFSpecOne.lagda.md) ($v=1$, 穿透), [OCFSpecTwo](OCFSpecTwo.lagda.md) (第一个不平凡的托架), [OCFSpecNeg](OCFSpecNeg.lagda.md) (否定), [OCFSpecLv](OCFSpecLv.lagda.md) (`Lv` 上的陈述).
>
> **判决: PARTIAL. 规格本身成立: 定义里没有记号, 也没有折叠; 只看值; 值唯一. 它接受已知对的树, 拒绝已知错的树, 这些都是编译过的定理, 范围到 $\psi_0(\Omega+\Omega)$ 与 $\psi_1(\Omega)$. 够不到 $\Omega_\Omega$: 输入类型 `Ordᶜ` 装不下它, 而且每个 $\Omega$-共尾节点要一个手写的托架, 一般定理没有写. 所以现在它是低处的判官, 不是 EBO 的判官. 它不判大数.**
>
> **规格 (`IsPsi v a t`).** 闭包 `Cl₊` 是树上的归纳谓词: 基底 $x<\Omega_v$, 加法, $\psi_u(\xi)$ ($u,\xi\in C$, $\xi<a$), 值相等. $\psi_u(\xi)$ 的取值是规格自己 (对 $\xi$ 的 `Acc` 递归), **不是折叠**. `IsPsi v a t` 说 $t$ 是 $C_v(a)\cap\Omega_{v+1}$ 的严格上确界: `lt`, `ub`, `cof` 三个字段. 由 `ub` 得 $t\notin C_v(a)$ (`¬in`).
>
> **为什么不是 "$C$ 外最小".** 朴素的两种写法都推出 LPO, 已编译: "`t` 以下全在 $C$ 里" (`naive→LPO`, $v=0$, $t\ge2$), "成员都与 $t$ 可比" (`gap→LPO`, $v=1$), 连 "成员与 $\Omega_2$ 可比" 也是 (`headsplit→LPO`). 严格上确界没有判定. 经典地它与 "$C$ 外最小" 等价, 依据 Buchholz 的 $C_v(a)\cap\Omega_{v+1}=\psi_v(a)$ (纸面, 未编译; 扩展到下标是项的情形是判断, 蓝本是 ExBuchholz 的 `Vals_eq`). 比较只在陈述里, 从不判定, 不碰壁垒.
>
> **编译过的定理: 规格的性质.** `IsPsi-a`, `IsPsi-t` (对 $a$, $t$ 的值不变), `IsPsi-uniq` (值唯一), `IsPsi-mono` (对 $a$ 单调, 不要求标准形), `ψ̂-mono` (跨下标), `ψ̂-prin` (值对加法封闭), `Ω-floor`. `Acc` 的选择无关 (`irr`).
>
> **编译过的定理: 折叠的行.** `T0` ($\psi_v(0)=\Omega_v$, 一切 $v$), `Tsuc` (后继行), `Tlim` (ω-极限行), `Tsup`/`Tchain` (链行, 要一个托架 `Bracket`), `pen-right` (穿透行的实例). 前提都是值上的. 后继行的前提 $b\in C_v(b+1)$ 就是标准形条件: 没有文法, 就是闭包的成员.
>
> **编译过的定理: 接受.** 树都是折叠的字面输出 (`ψ⁰Ω₁≡`, `ψΩΩ≡`, `tp-eq` 都是 `refl`).
>
> | 输入 | 定理 | 值 |
> |---|---|---|
> | $\psi_0(0),\psi_0(1),\psi_0(\omega)$ | `anchor-0`, `anchor-1`, `anchor-ω` | $1,\omega,\omega^\omega$ |
> | `Reg₀` 的全部 ($a<\varepsilon_0$ 的区域, 对 $+$, $\psi^0$ 封闭) | `correct₀`, `reg-ψ`, `reg-add`; 链 `s-δ` | |
> | $\psi_0(\Omega)$ | `anchor-Ω` | $\varepsilon_0$ |
> | $\psi_0(\Omega+y)$, $y\in$ `Reg₀`, 如 $+1$, $+\omega$ | `anchor-Ω+`, `anchor-Ω+1`, `anchor-Ω+ω` | |
> | $\psi_0(\Omega+\Omega)$ | `anchor-ΩΩ` | 第一个不平凡的托架 |
> | $\psi_1(0),\psi_1(1)$, 可数严格增输入 | `T0`, `ψ₁1`, `correct₁` | |
> | $\psi_1(\Omega)$ | `pen-right` | 穿透 |
> | $\varepsilon_0\preccurlyeq a\preccurlyeq\Omega$ 的 $\psi_0(a)$ | `gap` | 缺口: 都是 $\varepsilon_0$ |
>
> 没有一个已知对的树被拒绝 (这一范围内). Bachmann-Howard ($\psi_0(\Omega_2)$) 没有到: 见下面的代价.
>
> **编译过的否定: 拒绝.**
>
> | 树 | 定理 | 它错在哪 |
> |---|---|---|
> | $\psi^0(\varepsilon_0+1)$ | `fold-wrong-at-gap`, `gap-value` | 输入不标准. 规格给 $\varepsilon_0$, 折叠给 $\varepsilon_0\cdot\omega$ 以上 |
> | $\psi^0(\Omega_1')$ (Value 的反例) | `bad-branch-rejected` | 分支坏, 值不变, 折叠给 $1$ |
> | $\psi^0(w+\Omega)$, $w=\varepsilon_0+1$ | `good-rejected`, `Good-not-value-fragment` | `Good` 且分支单调, 值 $\approx\Omega$, 折叠 $>\varepsilon_0$ |
> | 静态替身 $\psi^0(\Omega+\omega)$ 当 $\psi_0(\Omega+\Omega)$ | `static-rejected` | $\omega$-共尾的替身, 值严格小 |
> | `rise` 的 $\sup\psi_1(\delta_n)$ 当 $\psi_1(\Omega)$ | `rise-rejected`, `rise≺pen` | 判决错, 应当穿透 |
>
> **够不到的两棵, 如实说.** 旧地板的树 (`¬TΩ2-label`, $\psi_0(\Omega_\Omega^2)$ 处) 与 `Zero.dev` ($W[0]$ 之下): 都在 $\Omega_\Omega$ 之上, 规格现在没有那里的正确值可比, 没有编译的否定. `static-rejected` 与 `rise-rejected` 是它们的机制的最小实例, 不是它们本身. `D3-question` (Value) 仍开放.
>
> **规格看不见基本列 (`spec-blind`, `slow`).** $\omega$ 与 $\omega^+$ 都过 $\psi_0(1)$ 的规格, FGH 在 2 处是 $8$ 与 $2048$. 对任何 $k$ 有过规格的树, 它在 $k$ 处的 FGH 只是 $k+1$. 规格保证的只有序数值. 纲领说大数是树上 FGH 的值: 它判定 "这棵树的序数值对", 不判定 "这个数够大". 我的判断: 作序数的判官够了, 作大数的判官不够, 要另一个管基本列的树侧条件, 这里没有. `Lab` 同时管这两件事; 规格只替代前一件.
>
> **关键发现.**
>
> 1. **折叠只在标准形上正确, 而标准形可以没有文法.** $a\in C_v(a)$ (`N`), $a\in C_v(a+1)$ (`Sel`), 都是闭包的成员. `Reg` 就是 "折叠走到的点都标准", 是一个新的树侧合法性标准. `Reg` 与 `Good` 不是一回事: `Good` 让证书走得通, `Reg` 让值对.
> 2. **"分支按值单调" 不是折叠尊重值的片段**, Value 的这条猜测是错的: `Good-not-value-fragment`, 用 [Uniform](Uniform.lagda.md) 现成的 `Good-add`, `Good-Ω`, `Good-ψ⁰`. 要的是标准形. 编译的是 Uniform 的 `Good`; [InaccThetaGood](InaccThetaGood.lagda.md) 的 `Good` 是它在 `Lv` 上的同形版本, 那里的同一个反例我没有编译 (判断: 同样成立, 因为 $x\mapsto w+x$ 按 $\sqsubseteq^\mathsf{o}$ 单调, 而 `Good` 不看值).
> 3. **规格绕开了 $\psi^0$ 的值同余.** 它是值上的关系, 折叠只是被判的对象, 所以 `ψ⁰-not-cong` 不再是障碍, 而是 "这棵树错" 的一个证明 (`bad-branch-rejected`).
> 4. **托架是全部工作量所在** (`Bracket`): 规格对链的要求只有一条, $\xi\in C_0(a)$, $\xi<a$ 时 $\xi$ 落在某个 $a[\gamma_n]$ 以下. 在 $\Omega$ 上它是平凡的 (`ub` 的归纳假设), 在 $\Omega+\Omega$ 上要四重不变量 ([OCFSpecTwo](OCFSpecTwo.lagda.md) §4). 其中的头部分情况 `D` 在 $v\ge1$ 推出 LPO (`headsplit→LPO`), 所以同样的证明在 $\psi_1$ 的 $\Omega_2$-共尾节点上不成立, 要换成否定式的论证 (判断, 没有试).
> 5. **`Ordᶜ` 不够大 (`rejected-if-gap`).** $\Omega_{\ell_0}$ 的值不是 $\Omega_\Omega$: 它是替身. 已验收的 `ts` 读成 $\psi_0(\Omega_{\ell_0}+1)$ 会被规格拒绝 (条件式的定理, 条件 `H` 经典地成立, 是判断, 未证). 所以规格要搬到输入能真正是 $\Omega_\Omega$ 的载体上. `Lv` 可以 ([OCFSpecLv](OCFSpecLv.lagda.md), `ΩΩ-spec`, `ΩΩ+1-spec`, 只有陈述, 不要 `S`). Uniform4 的数据树是环境下的树族, 值怎么定义没有想清楚.
>
> **对 value-equality-verdict 四条的交代.**
>
> 1. "$\psi^0$ 对高层不尊重值, 要限制到分支按值单调的片段": 前半句依赖, 后半句**推翻** (`Good-not-value-fragment`). 片段是标准形. 而且 V3 不需要这个同余.
> 2. "层 4 不降, V1 搬标签, V2 要记号侧良基性": **部分推翻.** 这是第三条路 V3, 它不引用记号, 不要记号侧层 3, 不要 "基本列极限等于值". 没有推翻的是成本: 每个节点仍要上界 (托架), 我没有证据说它比逐项匹配便宜.
> 3. "层 3 更难, `no-Bound`": **依赖, 未触及.** 规格不进证书. 层 3 要结构的 $\sqsubseteq$, 规格给的是值序, 能否换掉 `mono-lab` 没有试.
> 4. "替身机制是定义正确值所必需": **确认, 且从纸面变成编译** (`static-rejected`, `rise-rejected` 是最小实例).
>
> **归类: 这不是由树带路.** 它是**另一个外部来源**: 不是记号, 是 Buchholz 的集合论定义. 规格里没有项文法、标准形判定、比较函数、基本列, 但闭包的三条规则是人从文献里拿来的, 不是树逼出来的; `Cl₊` 的推导树的形状就是项 (加法与 $\psi$), 只是它是序数集合的定义, 不是语法. 它回答目标的后半句 ("判断它是否正确"), 不回答前半句 ("写出下一步"). 换到 $I$ 或更高, 要有人先写出那里的闭包定义 (Rathjen 式有文献), 树不会自己写. 所以判据里只有 "有树侧的合法性标准" 这一条有进展 (`Reg`, `N`).
>
> **代价估计 (判断, 未编译).**
>
> - 本文 8 个文件, 总 2180 行, 代码 1439 行, 到 $\psi_0(\Omega+\Omega)$. 其中规格与折叠的行 (Base, Rule) 代码 454 行是一次性的, 对一切 $v$. 一个新的 $\Omega$-共尾形状, 以 Two 量: 相对标准形一遍, 代码约 110 行, 与 Anchor 同构; 托架约 140 行. 逐站手写不可接受, 必须有一般的托架定理: "标准形 $a$, $\xi\in C_v(a)$, $\xi<a$ $\Rightarrow$ $\xi$ 落在 $a[\gamma_n]$ 以下".
> - 这条定理的内容就是 ExBuchholz 的 `Closure` (Buchholz 3.3–3.6, 1833 行 Lean, 加 `FS`, `Sum`): 那里的 `SubBound`, `bach_pre` 的陷阱是真的数学, 在这里也会出现, 而 $C$ 的推导树就是项. 在 `--safe --without-K` 下估计 **6000–9000 行**, 这是第 5 站与 EBO 共用的主要部分, 因为 Lean 的证明对 EBO 一致.
> - 搬到 `Lv` 上: Base 加 Rule 重写, `add` 带 `subst`, 没有 `<ᴵ-dec`, 估计 800–1200 行. 一般的 `ΩO v`: 目前只有 $v=0,1$, 估计 100–200 行. $v\ge1$ 的托架不能用 `D`: 风险未知, 可能需要新想法.
> - 合计到 EBO 约 **8000–12000 行**, 第 5 站不会便宜多少: 一般定理是一次付清的. 现行第 4 层 (Value 记的数字: 树侧 BTBO ≈1850, EBO 阶段 ≈2250, 记号侧序对应 ≈2250) 比这小, 但逐站累积且读记号. 所以这条路不省行数, 换来的是记号无关. 这是粗估: 量级我有把握, 数字没有.
>
> **审计 (`depslice.py`, 语法级).** 到达的记号定义都是 0: `OCFSpecBase:IsPsi` (到达 40 块), `OCFSpecRule:Tchain` (76), `OCFSpecAnchor:anchor-Ω` (228), `OCFSpecTwo:anchor-ΩΩ` (310), `OCFSpecOne:pen-right` (222), `OCFSpecOne:rise-rejected` (252), `OCFSpecNeg:static-rejected` (252), `OCFSpecNeg:good-rejected` (313), `OCFSpecLv:IsPsiᴸ` (34). 正对照 `InaccFloorAccept:ψ₀t`: 43. 模块导入的传递闭包里也没有 `EBO`, `Correspond`, `Standard*`, `Stage2`, `Value`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 导入链里没有 `OCF.Align.EBO`. 只新建文件 `OCFSpec*`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpec where

open import OCF.Align.OCFSpecBase using (IsPsi; IsPsi-a; IsPsi-t; IsPsi-uniq; IsPsi-mono; ψ̂-mono; ¬in; C; Cl₊; irr)
open import OCF.Align.OCFSpecRule using (T0; Tsuc; Tlim; Tsup; Tchain; ψ̂-prin; Ω-floor; ΩO)
open import OCF.Align.OCFSpecAnchor using (anchor-0; anchor-1; anchor-ω; anchor-Ω; anchor-Ω+; anchor-Ω+1; anchor-Ω+ω; gap; correct₀; reg-ψ; reg-add; ΩO-0)
open import OCF.Align.OCFSpecOne using (ΩO-1; correct₁; ψ₁1; pen-right; rise-rejected; rise≺pen)
open import OCF.Align.OCFSpecTwo using (anchor-ΩΩ)
open import OCF.Align.OCFSpecNeg using
  (naive→LPO; gap→LPO; headsplit→LPO; fold-wrong-at-gap; gap-value; bad-branch-rejected;
   Good-not-value-fragment; good-rejected; static-rejected; spec-blind; slow; rejected-if-gap)
open import OCF.Align.OCFSpecLv using (IsPsiᴸ; ΩΩ-spec; ΩΩ+1-spec)
```
