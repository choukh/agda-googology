# 值验收: 互相 $\sqsubseteq^0$ 不能推广, 编译过的否定

> **判决 (编译过, 无条件, `--safe`): PARTIAL.** 目标是把值验收 (树与带字面标签的树互相 $\sqsubseteq^0$) 变成一般定理. **结论相反: 这个形式的值验收在 $\omega\cdot2$ 第 0 行之上是假的, 不管读法是什么.** 码 $\omega\cdot2$ 的第 $\alpha\ge1$ 行, $\omega^2$, $\omega\cdot3$, $\omega^\omega$, $\varepsilon_0$ 的顶, `T⊤`, 都不 $\sqsubseteq^0$ 任何带字面标签的树. 还能证的是链行上的类 (`va-chain`, `vv-chain`) 和换成 $\preccurlyeq$ 的条件定理. 这是验收文件, 读记号; 证书没有改动, 也不依赖标签.
>
> **为什么.** $\sqsubseteq^0$ 的叶子是 $\cong$. 所以 $X\sqsubseteq^0Y$ 要求 $X$ 的每个 $\prec$ 子树 $c$ 都 $\cong$ 到 $Y$ 的子树. 带字面标签的树的子树都带字面标签 (`lab-≺`). 而链行的第 0 项固定是 $\omega$, 记号的基本列有一条结构律 (`chain-rule`, 对一切项, 不要标准形): 若 $s[0]=\psi_0(1)$, 则 $s[1]=A(p)$, $s[2]=A(p+p)$, 沿第 0 项走同样步数后 $s[2]$ 落到 $s[1]$. 高度 $\omega\cdot2$ 的第 0 行 $[\omega,t[0],t[1],\dots]$ 违反它 (`no-any-M₂`), 所以它不带任何标签. 但它又是上面每一行的 $\prec$ 子树 (`grow`, `V-≺`). 所以 `same-M₂` 只能成立在这一行本身: 它一旦作为 `suc` 的前驱或 $\prec$ 子树出现, 互相 $\sqsubseteq^0$ 就断了 (`suc-sep` 是最小的例子, 就是 `⊑-not-suc`). 第 1 行的具体位置有有限测试 (`ValLabTest`): $X_1[1][0][2][0][2][0][1]=\mathrm{suc}\,X_0$.
>
> | 定理 | 陈述 | 文件 | 档 |
> | --- | --- | --- | --- |
> | `lab-≺` | $c\prec Y$, `Lab Y t` $\Rightarrow$ $\exists s$, `Lab c s` | [ValLabBase](ValLabBase.lagda.md) | 定理 |
> | `ω-term` | 同一棵树带 $\psi_0(1)$ 与 $t$, 则 $t=\psi_0(1)$ | 同上 | 定理 |
> | `classify` | $s$ $\omega$-共尾, $s[0]=\psi_0(1)$ $\Rightarrow$ 四个形状之一, 或 $s[1]=\psi_0(\psi_0(1))$ | 同上 | 定理 |
> | `chain-rule` | 对一切 $s$: `Lab (lim h) s`, $h_0$ 带 $\psi_0(1)$, $h_1\to^k w$ ($w$ 带 $\psi_0(1)$), $h_2\to^k y$ $\Rightarrow$ $y\cong h_1$. $\to$ 是取第 0 项 | 同上 | 定理 |
> | `rule-ctl` | 正对照: 带标签的 $\psi_0(\Omega_{\psi_1(1)})$ 满足 `chain-rule`, $k=2$ | [ValLabPos](ValLabPos.lagda.md) | 定理 |
> | `no-lab-pat`, `no-lab-pat₂` | 对一切 `HtB`: $m$, $F_0$ 链行, $F_1$ 是下面 $\ge F_0$ 的闭包行或链行 $\Rightarrow$ 对一切 $s$, $V_m0$ 不带 $s$ | [ValLabRow](ValLabRow.lagda.md) | 定理 |
> | `no-⊑`, `no-val-above`, `no-val-row` | 一行没有标签 $\Rightarrow$ 上面的行, 同高度第 $\alpha\ne0$ 行不 $\sqsubseteq^0$ 带标签的树 | 同上 | 定理 |
> | `no-any-M₂`, `no-any-pos` | 码 $\omega\cdot2$ 的顶, 码 $\omega^2$ 的位置 $\omega\cdot2$: 对一切 $s$ 不带 $s$ | [ValLabNeg](ValLabNeg.lagda.md) | 定理 |
> | `no-val-M₂`, `no-val-pos` | 第 $\alpha\ne0$ 行 | 同上 | 定理 |
> | `no-val-ω²`, `no-val-ω²-top` | $\omega^2$ 码里位置 $\omega\cdot2$ 以上一切行 | 同上 | 定理 |
> | `no-val-ω·3`, `no-val-ω^ω`, `no-val-ε₀` | 这些码的顶 | 同上 | 定理 |
> | `no-val-T⊤` | `T⊤` 不 $\sqsubseteq^0$ 任何带字面标签的树 | [ValLabNegTop](ValLabNegTop.lagda.md) | 定理 |
> | `VA`, `VV`, `va→vv`, `va-sub` | 两个类; `VA` 推出子树都带标签 | [ValLabPos](ValLabPos.lagda.md) | 定义, 定理 |
> | `no-VA-T⊤`, `no-VA-ω²`, `no-VA-M₂`, `no-VA-ω·3`, `no-VA-ω^ω`, `no-VA-ε₀` | 上面写成类 | 同上 | 定理 |
> | `va-chain`, `vv-chain` | 对一切 `HtB`, 链行: `VA`/`VV` 由 $Z$ 给, 错开 $a$ 位 | 同上 | 定理 |
> | `va-M₂`, `va-pos` | 已有的两个成员 | 同上 | 定理 |
> | `suc-sep` | `VV (suc X) (t+1)`, 对一切 $t$ 没有 `VA (suc X) t` | 同上 | 定理 |
> | `no-NF-ω·2` | $\psi_0(\Omega_{\psi_1(1)\cdot2})$ 不是 `NF₁` | 同上 | 定理 |
>
> **条件定理.** `vv-ω²-if`: 若有 $Z_k$ 带 $\psi_0(\Omega_{\psi_1(2)})[k]$, 单调, 且位置 `blk i end` 的第 0 行 $\approx^{\mathsf v}Z_{i+1}$, 则 $\psi_0(\Omega_{\psi_1(2)})$ 的 `VV`. $i=1$ 无条件 (`hyp-2`). $i\ge2$ 就是下面的第一个障碍.
>
> **有限测试 (不是证明).** [ValLabTest](ValLabTest.lagda.md): 比较器是树的形状, `refl`. 盲区: 只看一条路径.
>
> **否定的范围.** 否定的是 "互相 $\sqsubseteq^0$ 用作这些行的验收". 前提可满足: `Lab Y t` 有实例 (`label-Tᴸ`), 同样的 `no-⊑` 不挡 `same-M₂`, 因为 $V_{\omega\cdot2}0$ 不是它自己的 $\prec$ 子树. **不否定:** $\preccurlyeq$ 下的验收; 这些树的强度; 读法; 用改过的记号或改过的基本列作尺子.
>
> **判断 (没有编译).** 规则要改成 $\preccurlyeq$ (`VV`), 或者放宽到只在第 0 行比较: 只有这样 `T⊤` 才有机会. `VV` 对这些行是不是真的: 判断是真的, 差别只有 "链行多一个头", 头被下一项支配 (`ChainRow.step`). 没有证明.
>
> **第一个障碍 (`VV` 到第 $\alpha\ge1$ 行).** 参照树 $Y$ 要带字面标签 $\psi_0(\Omega_{\psi_1(1)\cdot2+1})$. 三件事都缺:
>
> 1. **造 $Y$.** 主线的树不行: 字面的行第 0 项是 1 (`rowL`, `no-PxB`), `Row₀` 的 `rl` 要 `fsn (P m []) 0 ≡ []`:
>
>    `ψ¹ ∷ OCF.Align.EBO.trm (OCF.Align.EBO.fsn↓ ψ¹ [] 0) != [] of type Data.List.List OCF.Align.EBO.PT when checking that the expression refl has type fsn (ψ¹ ∷ ψ¹ ∷ []) 0 ≡ []`
>
>    要一棵去掉头的树, 这是树的克隆 (不是证书克隆: $Y$ 的计值由标签类给, 读记号, 不用写新的 `Goodᴺ`).
> 2. **标准形.** `Lq` 的出口 `labelᵠ` 要 `NF₁`, 而 `no-NF-ω·2`. `Goodᴸ` 的 `limᴸ`, `ĉᴸ-mk` 的单调来自 `mono-lab`, 所以 `label-Tᴸ` 的绕法 (只取极限) 在折叠里用不上: 下标要 `HS`, `HS` 要 $\sqsubseteq^0$ 的步进. 要扩 `Sb`, 判断照 `sψ`, `singψ` 的补丁做, `StandardOmega` 克隆加 `OrdLabZ*` 重生成.
> 3. **比较.** $X$ 的闭包链点 $y_k$ 与 $Y$ 的链点 $y_k'$ 只同值不 $\cong$, 所以要比较 $\dot\Omega_n(\mathrm{lv}\,y_k)$ 与 $\dot\Omega_n(\mathrm{lv}\,y_k')$. `V-≼` 只对字面的 $\sqsubseteq^{\mathsf I}$, `≼↛⊑` 说由值推不出它, `rows-blind` 说行律不够, `ψ⁰-not-cong` 说一般的同余是假的. 判断: 两边只差 "极限节点多一个头", 可以写成结构关系 (Z 层 `Hd`, 层号上 `Hdᴵ`, 不是一般的 $\preccurlyeq$), 沿 `CrossMSim` 的路走; 约 2000 行新证明, 没有写. **未走通, 不是否定.**
>
> **高处.** `T⊤` 的 `VV` 还要 $\psi_0(\Omega_{\psi_1(\gamma_n)})$ 的字面树, 那要上面的办法对一般的码成立. 没有试. `T⊤` 的读法仍是判断.
>
> **`NF₁`.** 没有扩展. `label-Tᴸ`, `va-M₂`, `va-pos` 绕开 (只取极限), 本组的定理都不要 `NF₁`; `no-NF-ω·2` 把缺口写成定理. `WeakBridgeLabel` 的 `label-θ` 只到 $\psi_0(\Omega_{\Omega+\theta})$, 在这里用不上.
>
> **受记号影响的形状 (如实说).** 这组文件就是读记号的. `ValLabLadder` 不读记号, 由 `ValueJudgeLadder` 机械改写.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 没有写新的 `Goodᴺ`, 没有证书克隆.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLab where

open import OCF.Align.ValLabBase public using (lab-≺; ω-term; classify; Zk; chain-rule)
open import OCF.Align.ValLabNeg public using (no-any-M₂; no-any-pos; no-val-M₂; no-val-pos; no-val-ω²; no-val-ω²-top; no-val-ω·3; no-val-ω^ω; no-val-ε₀)
open import OCF.Align.ValLabNegTop public using (no-val-T⊤)
open import OCF.Align.ValLabPos public using (VA; VV; va→vv; va-sub; module Chain; va-M₂; va-pos; suc-sep; no-VA-T⊤; no-VA-ω²; no-VA-M₂; no-VA-ω·3; no-VA-ω^ω; no-VA-ε₀; vv-ω²-if; hyp-2; no-NF-ω·2; rule-ctl)
import OCF.Align.ValLabRow
import OCF.Align.ValLabLadder
import OCF.Align.ValLabTest
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [ValLabBase](ValLabBase.lagda.md) | 标签沿树走, $\omega$ 的标签, 分类, 链律. 只有记号与 `Lab` |
| [ValLabLadder](ValLabLadder.lagda.md) | `V`, `V-≺`, `clos-row` 对 `HtB`, 由 `Survey/scripts/vallab/mk_ladder.py` 从 `ValueJudgeLadder` 生成. 不读记号 |
| [ValLabRow](ValLabRow.lagda.md) | 对一切 `HtB`: 没有标签的行, 上面的行 |
| [ValLabNeg](ValLabNeg.lagda.md), [ValLabNegTop](ValLabNegTop.lagda.md) | 实例; `T⊤` |
| [ValLabPos](ValLabPos.lagda.md) | 两个类, 链行, 分离, 条件定理, 标准形, 正对照 |
| [ValLabTest](ValLabTest.lagda.md) | 有限测试 |

## 审计

本组只新建文件, 已有文件没有导入 `ValLab*`. 复现: `Survey/scripts/vallab/audit.sh`.

- **导入闭包 (`importclosure.py`).** `--only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd OCF.Align.LadderOrd`: 禁用表命中 0, `--only` 之外 0, 退出码 0. 同上加 `--only OCF.Align.CrossM`, 对 `OCF.Align.CrossM`: 0, 0, 退出码 0. 加 `--only OCF.Align.ValueJudgeBase --only OCF.Align.ValLabLadder`, 对 `OCF.Align.ValLabLadder`: 0, 0, 退出码 0. 正对照 `OCF.Align.ValLabRow`: 禁用表命中 8, 退出码 1; `OCF.Align.ValLabNegTop`: 退出码 1.
- **定义级切片 (`depslice.py`; 块数, 记号块, 词命中).** `LadderOrdMain:GᴺTᵠ` 1023, 0, 0; `CrossMClosed:T⊤` 1193, 0, 0; `ValLabLadder:V-≺` 1046, 0, 0. 正对照 `ValLabNeg:no-any-M₂` 3508, 79, 415; `ValLabNegTop:no-val-T⊤` 3655, 79, 417; `ValLabBase:chain-rule` 164, 68, 33. 切片是语法级的, 模块别名和隐式参数看不见.
- **禁用构造.** `ValLab*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `REWRITE`, `--cubical`; 全部带 `--safe --without-K`.
- **检查器的坑 (实测).** 比较 `ChainRow.h (chain-row …) n` 的两个写法, 或隐式的 $\alpha$, $h$ 没给时, 堆 15G 耗尽 (退出码 251). 办法: 行写成顶层名字或变量 (`Rω`, `gen-pos`, `ctl-row`), 码写成变量 (`Br`), 隐式全给.
