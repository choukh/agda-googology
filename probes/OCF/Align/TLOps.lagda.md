# 树的算子语言: 三个词, 一条定理

> 路线审查 ([RouteReview](../../Survey/RouteReview.md)) §4.3 实验 2. **判决: PARTIAL.** 档次逐条写在下面. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不读记号; 记号只在 [TLOpsAccept](TLOpsAccept.lagda.md).
>
> 一句话: `GᴺΩ̇` 与 `GᴺTᵠ` 成了同一条定理 (`ψW` 加 `C′`, 对一切字面合法的高度 $p:A$) 的实例, `Gν` 与它们共用同一个迭代引理 `Iter`, 但没有进入 `ψW`, 因为要动态高度, 只做到定义 ([TLOpsDW](TLOpsDW.lagda.md)). **树是新树, 不是旧树**; 新树与旧树的序数值定理只到 $\psi_0(\Omega_\Omega)$. 不能一般化的义务是 `Hn`: 这里用世界前缀 $u+$ 绕过, 已写明.

## 算子语言

不是记号的语法. 只有树的三个算子, 外加它们上的一个递归 (折叠).

| 词 | 在层的类型 $A$ 上 | 在数据树 `𝓞 p a u` 上 | 折叠 $\psi_\tau$ |
|---|---|---|---|
| ℕ-极限 | `alim f` | `ol F` | 逐项 |
| $\Omega$-极限 | `asuc a` | `oi`, `od`: 分支是 $k$ 层的元素 | $k<\tau$ 保留; 否则回灌闭包, 载体是层 $k$ |
| 回灌闭包 | 高度的 `asuc p` | `oc x h`: 分支是世界 $v$ | 留在数据里, 目标换掉; 计值时走链 |

**生成原则.** 层 $(p,a)$ 读 $\Omega\cdot p+a$, $p$, $a$ 都是字面合法的 $A$. `Ω̇ p a` 按两个坐标的构造子写: `a` 是后继: $\Omega$-极限; `a` 是极限: ℕ-极限; `a` 是 0: 看 `p`: 后继: 回灌闭包, 分支 $v\mapsto(p',v)$; 极限: ℕ-极限; 0: 1. 新一站不加构造子, 不加闭包定理: 写一个新的 $A$. 字面合法的 $A$ 可以来自输出的读出 (`lit`).

`LadderOrd` 的第 0 行三分 (`View`) 在这里不存在: 它就是 `p` 的三个构造子. `Code`, `Pos`, `HtB`, `rk`, `Rec` 都不需要: 高度是 $A$ 本身, 比较走字面公共上界 (`Hk`, `trH`), 答案是字面的.

折叠的 `o0`, `os` 两行 ($\psi(0)=\Omega_\tau$, $\psi(a+1)=\psi(a)\cdot\omega$) 不属于三个算子, 是翻译账第 1 条.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `ψW` | [TLOpsMain](TLOpsMain.lagda.md) | 折叠保 `WF`, 一切 $p:A$, 一切层, 一切目标, 一步, 不碰链 | 定理 |
| `tR`, `ψL′` | 同上 | 折叠保 $\trianglelefteq$ | 定理 |
| `Ωh⊴` | [TLOpsLe](TLOpsLe.lagda.md) | 高度单调: 回灌作高度的唯一前提 | 定理 |
| `C′`, `G-Tᵖ`, `HS-Tᵖ`, `Lit-Tᵖ` | [TLOpsPre](TLOpsPre.lagda.md) | `WF` 给证书; $\psi_0(\Omega_{\Omega\cdot p+a})$ 有 `HS`, 无条件, **带世界前缀** | 定理; 读法是判断 |
| `Clo` | [TLOpsClo](TLOpsClo.lagda.md) | 单调族的顶层回灌闭包有 `Lit₀`, **没有前缀** | 定理 |
| `Top`, `Feed` | 同上 | $\eta\mapsto\psi_0(\Omega_{\Omega\cdot p+\eta})$, $\eta\mapsto\psi_0(\Omega_{\Omega\cdot\eta})$ 的闭包 | 定理; 读法是判断 |
| `Iter`, `IterUp` 与 `inst-feed`, `inst-ν`, `inst-γ`, `inst-cell` | [TLOpsAbs](TLOpsAbs.lagda.md) | 单调迭代; 四个载体 | 定理 (引理本身很浅) |
| `T₀≅Y` | [TLOpsSim](TLOpsSim.lagda.md) | 高度 0 的新树与 `CumReadCF.Y` 互模拟 | 定理 |
| `T₀≅ψ⁰`, `T₁≅`, `Tω≅ψ⁰` | [TLOpsAccept](TLOpsAccept.lagda.md) | $\psi_0(\Omega_\eta)$ 与 Level 的 $\psi^0(\Omega_\eta)$ $\cong$ | 定理 |
| `TΩ≅`, `label-TΩ`, `TΩ≈`, `fghΩ` | 同上 | `Top azero` 与 `BTBOᴵ` $\cong$, 带 $\psi_0(\Omega_\Omega)$ 的标签 | 定理 (基本列验收) |
| `C′` 条件于 `Hn` | [TLOpsForce](TLOpsForce.lagda.md) | 无前缀版, 前提未证 | 条件 |
| `Ω̇₂`, `ψ`, `Tᴰ` (三元层) | [TLOpsDW](TLOpsDW.lagda.md) | 动态高度的数据树与折叠; 闭包 $\Omega^2$ 是一行数据 | 只有定义 |

## 三条定理

| 旧定理 | 新位置 | 是否实例 |
|---|---|---|
| `OCF/Free/Main.GᴺΩ̇` | `Ω̇-inst` ($p=1$), [TLOpsClosed](TLOpsClosed.lagda.md) | `HS-Tᵖ` 的实例, **新树** |
| `LadderOrdMain.GᴺTᵠ` | `Tᵠ-inst` (任意 $p:A$) | `HS-Tᵖ` 的实例, **新树**; 不再要 `HtB` |
| `CrossMNode.Gν` | `Feed`; `inst-ν.T≅` 把旧的 `νT` 本身写成 `IterUp` 的实例 | `Clo` 与 `Iter` 的实例; 不是 `ψW` 的实例 |

旧树本身不是 `HS-Tᵖ` 的实例: 证书不同, 基本列不同.

## 第三步的硬点: Ω+1

**$\gamma$-链不要新算子.** `ψᵒ` 的 `injᵇ` 行 (这里 `ψ⁰` 的 `oi` 上升行) 是载体为层 $k$ 的回灌闭包: 一步是 $z\mapsto\psi_k(h\,z)$, 输出是 $z\mapsto\psi_\tau(h\,z)$ (`inst-γ`). 所谓 "同一闭包在不同目标下算两次" 就是这两个目标. 前提 (`Ωfst`, `ψL′`, `hMi`) 对一切项成立.

**五元节点 `ĉᴸ` 不要了.** `oc x h` 只有第一支和分支. 折叠到目标 $\tau$ 时 `oc` 的两支都折叠, 计值 (`force`) 时链总是当前这一项在第 0 层的输出. 不冻结链.

## 翻译账: 残余

| # | 义务 | 来自 | 现状 |
|---|---|---|---|
| 1 | `ψ⁰ … o0 = Ω̇at`, `ψ⁰ … (os x) = ol (rep …)`, 以及为它要的 `add`, `add≈`, `add⊴`, `AddW` | 折叠的定义 $\psi(0)=\Omega_\tau$, $\psi(b+1)[n]=\psi(b)\cdot n$ (Buchholz 规则的形状). 三个算子导不出来, 去掉它闭包点就错 (判断: $\psi_\tau(a+1)=\psi_\tau(a)+\omega$ 时 $\psi_0(\Omega_{\Omega+1})$ 只到 $\psi_0(\Omega_\Omega\cdot\omega)$) | 保留. 是算子的通用引理, 不按阶段 |
| 2 | **`Hn`**: 闭包的世界 $u$ 是第一支读出的第一位置 ([TLOpsForce](TLOpsForce.lagda.md)) | 不是记号的规则. 是比较要字面公共上界 (壁垒) 的后果: 分支 `h` 只在 $u\triangleleft v$ 上有定义, 链点 $v$ 必须字面含 $u$. 是 `Hon`, `Vis`, `Dem` 的同一件事 | **未证. 用世界前缀 $u+$ 绕过 (`⊞-fst`). 暂停, 未走通, 不是否定** |
| 3 | 世界规范形 `mx`, `Mis`, `m≈` | 同一个闭包必须有同一条链, 结构序才比得了 (`rf`). 比较两个不同的闭包在 $\trianglelefteq$ 下做不到 | 保留. 通用引理 |
| 4 | `lit`, `graft₀`: 链点要字面第一位置 | 壁垒的同类后果 | 保留. 定义依赖证书 (`Clo` 读 `Yl`, `up`) |
| 5 | 第一支 $(p,1)$, 顶层起点 $\eta_0=1$ (`s₀`) | 闭包从哪里开始, 读自 $\psi_0(\Omega_\Omega)$ 的基本列 | `Fam` 的字段, 可换, 值应不变 (判断) |
| 6 | 跨新旧树的序数值 | 新树自己没有问题; 旧树是尺子 | 只到 $\psi_0(\Omega_\Omega)$. 其上 **未走通**: 要新树与 `Q` 之间带基底的值嵌入, `CumVal` 判断超 3000 行 |

**消失了的 (编译事实, 导入闭包见下).** `Z`, `ĉᴸ`, `Ωˢ`, `toZ`, `Flr`, `Ev`, `bound`, `sup`, `Mlev`, `Top`, `Hon`, `Vis`, `Dem`, `AboveV`, `AboveΩ`, `FlOver`, `Cx`, `Ctxᶜ`, `View`, `HtB`, `Code`. 代价是第 2 条的前缀. 它们之中 `Hon`, `Vis`, `Dem` 没有被解决, 是被前缀绕过.

## 累加

`Tᵖ` 的数据树闭包走 $u+\mathrm{rd}\,y$: 世界前缀. 没有 `cumA`, 没有 `asuc`, 没有 $\eta+$, 每个链点只前缀一次世界, 不是链上累加, 但它是用算术代替证据, 与 `ordᴰ` 同类. 作者要全去, 这一条没有去掉. `no-⊞-left` 说前缀的左边不单调; 这里只在同一闭包的同一世界上用前缀 (`⊞-⊲` 只动右边), 不碰它. `Cumsum.overshoot` 说累加改非主数处的值; 前缀在主数处被吸收是**判断**, 这里没有定理.

`Clo`, `Top`, `Feed` 的最外层闭包没有前缀, 这也是 `TΩ≅` 能成立的原因 (`T₁₀` 带前缀, 与它只有测试).

## 有限测试

[TLOpsTest](TLOpsTest.lagda.md), 比较器 `same d w` (深度, 宽度, 只读形状). 盲区: 不读第 $w$ 项以后, 不读深度 $d$ 以下, 不读值.

| 比较 | 结果 |
|---|---|
| 新 $T_{1,0}$, $T_{2,0}$ 对 `NoCumPre.Tᵖ` | 深度 6 宽 2 相同 |
| `Top azero` 对 `T⁰` | 深度 6 宽 2 相同 (已是定理) |
| $T_{1,0}$ 对 `TF 0` (`OCF.Free`) | 深度 4 相同, 5 不同 |
| $T_{1,1}$ 对 `TF 1` | 深度 5 相同, 6 不同 |
| $T_{2,0}$ 对 `FC.TΩ₂` | 深度 6 相同, 7 不同 |
| $T_{\omega,0}$ 对 `LM.Tω₀`, 错开一位 | 深度 3 相同 |
| `Feed.T` 对 `CM.T⊤` | 深度 2 相同 (弱) |
| $T_{1,0}$ (带前缀) 对 `Top azero` (无前缀) | 深度 4 相同, 5 不同 |
| 控制: $T_{1,0}$ 对 $T_{1,1}$ | 深度 4 就不同 |

不同来自前缀: 链的下标不同. 不否定序数值, 也不证明序数值相同.

## 判断 (纸面, 没有编译)

- 读法: `Tp p` 读 $\psi_0(\Omega_{\Omega\cdot p})$, `Feed.T` 读 $\psi_0(\Omega_{\Omega^2})$. 高于 $\psi_0(\Omega_\Omega)$ 的强度都是估计.
- `Feed.T` 与 `T⊤` 同值. 没有定理.
- 前缀在折叠到第 0 层时被吸收, 不改序数值. 没有定理.
- 把 `Gν` 放进 `ψW`: [TLOpsDW](TLOpsDW.lagda.md) 的数据树已经编译, 层 $(r,c,a)$ 的 $c$ 动态, 世界规范形多两个候选. 证书的移植 (`≈`, `ψQ`, `ψW`, `C′`) 判断是机械的, 约 1500 行, 要把 $p\equiv p'$ 换成 $\approx$, 把高度拆成两个 $A$ 列. **没有做.** 做完才是三条定理成为同一条定理的实例.

## 第一个障碍

`TLOpsDW` 上照搬 `TLOpsEq` 的证书时, 高度是一个记录 `H`, 字典序看不见:

    Termination checking failed for the following functions:
      add, add⁰, addL
    Problematic calls:
      addL W gu₀ (◁-tr j i) j x gx m gm um tm ...
      add W gu₀ (lw t) x gx m gm um tm km

原因: `addL` 的 `x` 的类型是 `Low …`, 不归约到数据类型, 这一列被屏蔽; 旧版靠隐式高度 $p:A$ 这一列下降. 把高度拆成两列 $(r,c)$ 之后 `add`, `ψ` 编译过 (`TLOpsDW`). 这不是路线的障碍, 是工程量. 真正的障碍仍是翻译账第 2 条与第 6 条.

## 壁垒

下标类型没有变, 不要全局三歧. `trH` 走 `Hk` 的字面公共上界, `cmpN`, `cmpF` 走世界或 $\mathrm{Lg}$ 的上界, 都是有界的; `barrier`, `¬tri`, `no-bra-cmp`, `no-tri-code`, `no-all-Ord` 的前提都不被要求. `Toy.loop`: 不可数下标不是可数层的构造子; `oc` 的分支只在数据里, 计值只取链上可数个. `no-cum-⊲`: 这里的前缀不走 `cumA`.

## 审计

`importclosure.py` 对 `TLOpsPre`, `TLOpsClo`, `TLOpsClosed`, `TLOpsSim`, `TLOpsAbs`, `TLOpsDW`, `TLOpsDTest` 干净; 正对照 `TLOpsAccept` 禁用表命中 18, 脚本返回 1. `depslice.py`: `TLOpsPre:G-Tᵖ` 到达 268 块, 记号块 0; `TLOpsClosed:T⊤′` 到达 59 块, 记号块 0 (切片看不见模块别名, 这里 `Feed` 是模块, 以导入闭包为准); 正对照 `TLOpsAccept:label-TΩ` 到达 1019 块, 记号块 92. 这些只保证不引用, 不说明没受记号启发: 折叠的形状从 `NoCum*` 继承, 那里读过记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOps where

open import OCF.Align.TLOpsPre using (HS-Tᵖ; G-Tᵖ) public
open import OCF.Align.TLOpsMain using (ψW; ψL′) public
open import OCF.Align.TLOpsClo using (Fam; module Clo; module Top; module Feed) public
open import OCF.Align.TLOpsAbs using (module Iter; module IterUp; module inst-feed; module inst-ν; module inst-γ; module inst-cell) public
open import OCF.Align.TLOpsSim using (T₀≅Y) public
open import OCF.Align.TLOpsForce using (Hn; G-T) public
open import OCF.Align.TLOpsClosed using (Ω̇-inst; Tᵠ-inst; Tp; HS-Tp; T·2; T·ω; T·ω2; T·ε₀; TΩ; T⊤′; HS⊤′; lv⊤′; fgh⊤′) public
open import OCF.Align.TLOpsDW using (Ω̇₂; Tᴰ) public
```
