# 序数值的判据: 相对的行, 字面的规格, 基本列的下界 (判决: PARTIAL)

> 问题: 现在的树侧判据只管合法性和界, 不管值. `T₁∞`, `T₂Ω` 有 `Goodᴺ`, 读作什么只是判断. `IsPsi` 只到 $\psi_0(\Omega+\Omega)$.
>
> **判决: PARTIAL.** 目标 1 (相对判据): **HOLDS 的部分**是 "读法是判断" 收窄成了编译过的上下界, 对一切高度结构; 上界没有标签, 因为仓库里没有更高的带标签的树. 目标 2 (规格推广): **条件定理**, 字面的 $\Omega_\Omega$, $\Omega_{\Omega\cdot2}$ 上有 `FixRow`, 前提没有证. 目标 3: 分档表现见下面的表, 有两棵旧树只有机制的对应, 没有定理. 目标 4: `Reg⁰` 排除 `slow` 是定理, 不决定大数也是定理 (最小反例).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`. 判据的定义与定理导入闭包干净, 只有 [ValueJudgeAccept](ValueJudgeAccept.lagda.md) 例外, 文件头写明.
>
> ## 判据的陈述
>
> **J1 `Rows W` ([ValueJudgeRow](ValueJudgeRow.lagda.md)).** $W:\mathrm{Ht}\times\mathrm{Ord}^I\to$ 第 0 层的树. 同余; $W_m a\prec^{\mathsf v} W_m(a+1)$; $W_m(\lim f)\approx^{\mathsf v}\lim W_m(f\,n)$; 链行 $W_m0\approx^{\mathsf v}\lim W_{F i}0$; 闭包行 $W_n0\prec^{\mathsf v}W_m0$. 定义里没有折叠, 没有证书, 没有记号, 只有结构 `HtS`.
>
> **J1′ `IsFix F T` ([ValueJudgeFix](ValueJudgeFix.lagda.md)).** $T$ 是 $y_0\cong F(1)$, $y_{k+1}\cong F(\mathrm{lv}\,y_k)$ 的上确界. 对 $F$ 相对. 它决定值: 封闭 `fix-closed`, 最小 `fix-least`, 唯一 `fix-uniq`.
>
> **J2 `IsPsiᴸ v a t` ([OCFSpecLv](OCFSpecLv.lagda.md), 性质在 [ValueJudgeSpec](ValueJudgeSpec.lagda.md)).** Buchholz 闭包的严格上确界, 载体 `Ordᴸ`, 输入可以是字面的 $\Omega_\Omega$. 不要判决 `S`.
>
> **J3 `Reg⁰` ([TreeJudgeBase](TreeJudgeBase.lagda.md) §6).** 极限节点上 $h_n$ 在 $h_{n+1}$ 的 1-走步上. 不看值.
>
> 比较只在陈述里, 从不判定. 判据不进定义, 不碰壁垒 (`dec≈→LPO`).
>
> ## 编译过的定理
>
> **无条件, 对一切结构 `𝕊 : HtS`** ([ValueJudgeLadder](ValueJudgeLadder.lagda.md), [ValueJudgeRowV](ValueJudgeRowV.lagda.md)). `V m a` 是 `Tᵠ m a` 的计值, 与证书无关 (`V-G`).
>
> | 定理 | 陈述 | 不空的理由 |
> |---|---|---|
> | `ι-top` | $\bar\psi(\dot\Omega_m a)$ 与 $\bar\psi(\iota_r\dot\Omega_m a)$ 同值 | 无前提 |
> | `V-≺` | $V_m a\prec V_m(a+1)$, 结构序 | 无前提 |
> | `V-lim` | $V_m(\lim f)\cong\lim V_m(f\,n)$ | 无前提 |
> | `V-≼`, `V-⊑`, `V-≺≺` | 对 $\sqsubseteq^{\mathsf I}$ 单调, 严格. 不要字面公共上界 | 无前提 |
> | `V-chain` | `view m = chain F`: $V_m0\approx^{\mathsf v}\lim V_{F i}0$. `anchor` 的一般形式 | `HS∞`, `HS₂` 的 `refl` |
> | `clos-row` | `view m = clos r`: $V_m0\cong\lim y_k$, $y_0$ 是 $\iota_\downarrow\dot\Omega_n1$ 的值, $y_{k+1}$ 是 $\iota_\downarrow\dot\Omega_n(\mathrm{lv}\,y_k)$ 的值 | 同上 |
> | `base-row` | `view h₀ = base`: 同样的链, 链点是 $\psi^0(\Omega_\eta)$ 的值 | 同上 |
> | `V-clos-≺`, `clos-first≺` | $V_n0\prec^{\mathsf v}V_m0$; 第 0 个链点严格低于 $V_m0$ | 同上 |
> | `clos-below` | $\eta$ 字面低于 $\mathrm{lv}\,y_k$: $\iota_\downarrow\dot\Omega_n\eta$ 的值 $\prec^{\mathsf v}V_m0$ | $\eta=1$, $k=0$ 由 `1≺F` |
> | `V-rows` | `Rows V` | 无前提 |
>
> **闭合的实例** ([ValueJudgeInst](ValueJudgeInst.lagda.md)). 右边的 `T₀∞` 等是 [LadderInfClosed](LadderInfClosed.lagda.md) 的定义右边.
>
> | 定理 | 陈述 |
> |---|---|
> | `T₀∞≺T₁∞` | `forceᴺ _ (G∞ 0)` $\prec^{\mathsf v}$ `forceᴺ _ (G∞ 1)` |
> | `T∞-step`, `T∞-lim`, `T∞-mono`, `T∞-strict` | $\infty$ 这一行对 $\alpha$ 的行为 |
> | `T₀-sup`, `fin≺T₀`, `fin₁≺` | $T_0^\infty$ 是 $V_{\mathsf{fin}\,i}0$ 的上确界, 每个都严格在它以下. $V_{\mathsf{fin}\,n}1\prec^{\mathsf v}V_{\mathsf{fin}\,(n+1)}0$ |
> | `T₀ᵀ≈T₀∞` | `HS₂` 的 $V_{\mathsf{top}\,0}0$ 与 `HS∞` 的 $T_0^\infty$ 值相等 (跨世界) |
> | `T₁ᵀ≺T₂Ω`, `T₀ᵀ≺T₁ᵀ` | $V_{\mathsf{top}\,0}0\prec^{\mathsf v}V_{\mathsf{top}\,0}1\prec^{\mathsf v}T_{2\Omega}$ |
> | `T₀∞≺T₂Ω′` | `forceᴺ _ (G∞ 0)` $\prec^{\mathsf v}$ `forceᴺ _ (G₂ 1 0)` (跨世界) |
> | `T₂Ω≺next`, `T₂Ω≺top₂` | $T_{2\Omega}\prec^{\mathsf v}V_{\mathsf{top}\,1}1$, $V_{\mathsf{top}\,2}0$ |
> | `uip∞`, `uip₂` | 高度的证明唯一, 消掉 `ValueJudgeBridge` 的条件 |
>
> **关于 `IsFix`:** `fix-closed`, `fix-least`, `fix-uniq`, `fix-static` (替身过不了). 前提 `Fm`, `Fs` 对 `V` 成立 (`V-⊑`, `V-≺≺`).
>
> **带条件** (条件写在类型里或模块参数里):
>
> | 定理 | 条件 | 为什么可满足 |
> |---|---|---|
> | `Br.Br₁`, `V₁-F`, `V₁≺` ([ValueJudgeBridge](ValueJudgeBridge.lagda.md)) | `Uq`: `<ᴸ` 证明唯一 | `uip∞`, `uip₂` 证了 |
> | `fix-of-Br`, `FixV` ([ValueJudgeRowV](ValueJudgeRowV.lagda.md)) | `Br r`: 一切 $\eta$ 上 $\iota_\downarrow$ 的值是 $V_n\eta$ | $\eta=0,1$ 是定理 (`D-self`, `V₁-F`). $\eta\ge2$ 判断成立, 没有证 |
> | `FixRow.fix` ([ValueJudgeSpec](ValueJudgeSpec.lagda.md)) | `H`, `stp`, `a≼A`, `Cut` | `fix-Ω` ([ValueJudgeSpecLow](ValueJudgeSpecLow.lagda.md)): 同一个证明在 `Ordᶜ` 上, $A=\Omega_1$, 前提无条件成立, 重得 `anchor-Ω` |
> | `CutΩΩ.ψ₀ΩΩ` | `H`, `stx`, `ΩRefl`, `ΩStep`, `ΩPrin` | 判断, 经典地成立. `H` 就是下面各站的规格 |
> | `spec-of`, `spec-clos`, `spec-base` ([ValueJudgeSpecTree](ValueJudgeSpecTree.lagda.md)) | 同 `FixRow` | 同上 |
> | `spec-ΩΩ`, `spec-Ω·2` ([ValueJudgeSpecInst](ValueJudgeSpecInst.lagda.md)) | 同上. 结论对 `emb (V (fin 0) 0)`, `emb (V (fin 1) 0)`, 输入字面 | 判断 |
>
> **`rejected-if-gap` 怎么解决:** 它的毛病是 $\Omega_{\ell_0}$ 是替身. `IsPsiᴸ` 的输入是 `Ω LΩ`, 字面的 $\Omega_\Omega$, 第 0 层的树 `emb` 进来, 替身不再出现. 代价搬到了 `Cut`.
>
> **否定, 都是编译过的, 写明否定什么:**
>
> | 定理 | 否定什么 | 不否定什么 |
> |---|---|---|
> | `rows-blind` ([ValueJudgeRowNeg](ValueJudgeRowNeg.lagda.md)) | `Rows` 单独决定值: 单高度结构上 `lvT` 与 `V` 都满足, 第 0 项不同 | 加第 0 行和后继行的锚之后 |
> | `reg-blind`, `reg-fast`, `reg-gap` ([ValueJudgeReg](ValueJudgeReg.lagda.md)) | `Reg⁰` 加值决定大数 | 带速度的条件 |
>
> ## 分档表现 (目标 3)
>
> | 树 | 对错 | J1 / `IsFix` | J2 `IsPsiᴸ` | J3 `Reg⁰` | 档 |
> |---|---|---|---|---|---|
> | `V` 全族 (含 `Tω₀` 的值 `T₀∞`) | 对 | `V-rows` | 只有条件定理 | 见下 | 定理 |
> | `TΩ·2` 的同值树 `V (fin 1) 0` | 对 | `V-rows`, `clos-row` | `spec-Ω·2`, 条件 | 没有测 | 定理 / 条件 |
> | `BTBOᴵ` 的同值树 `V (fin 0) 0` | 对 | `base-row` | `spec-ΩΩ`, 条件 | 没有测 | 定理 / 条件 |
> | `T₀∞` | 对 | `T₀-sup` | 没有 | 测试过 (`t0-reg`) | 定理, 测试 |
> | `T₁∞`, `T₂Ω` | 判断为对 | `T₀∞≺T₁∞`, `T₁ᵀ≺T₂Ω` | 没有 | **`regD 2 8 3` 是 false** (`t1-reg`, `t2-reg`) | 定理, 测试 |
> | `slow` | 值对, 大数退化 | 不看 | 过 (`slow`, 既有) | **拒绝** `slow-not-reg`, `slow-floor` | 定理 |
> | `wrong-fold` 的 `PW` | 错 | 不是这个形状, 不适用 | 没有写 | **拒绝** `wrong-fold-not-reg`, 对任何 `S` | 定理 |
> | 静态替身 $\psi^0(\Omega+\omega)$ | 错 | `fix-static` 拒绝 (前提: 链爬过 $\omega$) | `static-rejected` (既有, `Ordᶜ`) | 没有测 | 定理, 前提未对这棵树证 |
> | `ver` 的树 | 错 | 不是这个形状, 不适用 | 没有定理. 机制同 `rise-rejected` (判断) | 没有测 | 无 |
> | `ω`, `ω⁺` | 同值, FGH 不同 | 不分开 | 不分开 (`spec-blind`) | **不分开** `reg-blind` | 定理 |
>
> `TΩ·2`, `BTBOᴵ` 这两行说的是同值的 `V (fin n) 0`. 同值的依据: `ValueJudgeBridgeN` 接 `LadderNFTree`; 接 `OCF/Free/Closed` 的 `TΩ₂` 与 `BTBOᴵ` 本身的那一步这里没有写.
>
> **`Reg⁰` 那一行要小心:** `T₁∞`, `T₂Ω` 的 `false` 没有定位. 可能是步数不够, 比较深度的假阴性, 或它们真的不满足 `Reg⁰`. 顶层前三对是过的 (`t1-pair₀`–`t1-pair₂`). 步数加到 60 在 6G, 280 秒内没有结果. 所以**不能说这些树 `Reg⁰`**, `Reg⁰` 作为对高处树的判据没有被验证.
>
> ## 大数 (目标 4)
>
> `Reg⁰` 下: FGH 沿走步单调 (`walk-mono`), 对参数单调 (`arg-mono`), $k\ge2$ 时 $\ge2k$ (`reg-floor`). 排除 `slow`. **最小反例:** $\omega$ 与 $\omega^+$ 都 `Reg⁰`, FGH 在 2 处 8 对 2048 (`reg-blind`). 任何严格增的 $g$ 给值 $\omega$ 的 `Reg⁰` 树, FGH 没有上界 (`reg-fast`). `tᵍ` 值严格大于 $\omega$, `Reg⁰`, FGH 在 2 处也是 8 (`reg-gap`). 所以缺的是基本列的**速度**, 不是形状. 判断: 要的是一个把第 $n$ 项的某个范数压在 $n$ 的函数以下的条件 (`archive/` 里范数基本列那一路), 这里没有试.
>
> ## 第一个障碍
>
> 1. **`Br` 在 $\eta\ge2$.** `ι↓` 读 `omk` 的第一格, `ψᵠ` 读第二格. $\Omega_{n}$ 的节点是 `omk z (ι z)`, 两格相关, 但 `Rq` 只记分别的关系. $\eta=1$ 时链点在 `Q n 0`, 没有 `omk`, 所以 `Br₁` 过得去. 判断: 要一个记住第二格是第一格的 `ι` 的新关系, 对 `⊞`, `ψᵠ`, `Ψ`, `tr` 重做一遍, 量级是 `LadderInfRel` 加 `LadderInfDn`, 约 800 行. **不是走不通.**
> 2. **规格的 `ΩRefl`.** $\Omega_u\prec\Omega_{\mathrm{lv}\,x}$ 推 $u\prec x$, 只对第 0 层的 $x$. 证不出的一步: 要从 $\Omega_{u}\preccurlyeq z$ ($z$ 在第 $\mathrm{lv}\,x'$ 层) 把后继保住, 而 $u$ 与 $\mathrm{lv}\,x'$ 之间没有字面路径, 不能把 $z$ 搬上去. 只有 $x'=0$ 的情形能搬 (第 0 层的树可以抄到任何层). 这与 `ΩO` ([OCFSpecRule](OCFSpecRule.lagda.md), 只证了 $v=0,1$) 同类. **没有否定, 写 STUCK.**
> 3. **`H`.** $\psi_0(\Omega_\ell)$ 对一切链点的规格, 就是一般的托架定理 (`OCFSpec` 的估计).
> 4. **跨世界 `T₁ᵀ` 与 `T₁∞`.** 没有证. 现成的模拟以 ℕ 为源 (`mk_inf_bridge.py`). 所以 `T₁∞` 自己的上界只有 `T∞ 2`; `T₂Ω` 的上界落在 `T₁ᵀ` 上. 判断: 同值, 定义逐行相同.
> 5. **上界没有标签.** 带标签的树到 $\psi_0(\Omega_{\psi_1(1)})$ 为止, 就是下界. `LadderLab*` 有结果后, 把 `T₁∞` 夹进去只差一个比较.
>
> ## 哪些形状受记号影响
>
> `Rows` 只提 `HtS`, 但 `HtS` 的 `view` (闭包, 链) 是记号的后继/极限读来的 ([LadderInf](LadderInf.lagda.md) 已写明). `IsFix` 的形状 "下一层是这一层的不动点" 是从 $\Omega_{\ldots+\Omega}$ 的基本列看来的, 树侧的证明不看记号. `IsPsiᴸ` 是 Buchholz 的闭包, 另一个外部来源, 不是树逼出来的. `reg-gap` 的构造是看 `Reg⁰` 的定义写的, 与记号无关. **这不算 "让树自足":** 判据管的是已写出的树, 不写下一步; `Rows` 的后继行只是不等式, 它的内容 (内层折叠) 没有被判据捕捉.
>
> ## 审计
>
> `importclosure.py OCF.Align.ValueJudge`: 退出码 0, 禁用表命中 0 (编译器保证). `ValueJudgeAccept` 单独跑: 禁用表命中 8, 文件头写明. `depslice.py` (语法级, 看不见隐式参数和模块别名), 到达块数 / 记号块 / 词命中: `Rows` 31/0/0, `IsFix` 37/0/0, `V-rows` 1076/0/0, `T₀∞≺T₁∞` 1055/0/0, `T₁ᵀ≺T₂Ω` 1072/0/0, `T₀ᵀ≈T₀∞` 1844/0/0, `ψ₀ΩΩ` 75/0/0, `spec-ΩΩ` 1105/0/0, `spec-Ω·2` 1095/0/0, `fix-Ω` 236/0/0, `rows-blind` 1087/0/0, `reg-gap` 49/0/0, `wrong-fold-not-reg` 50/0/0. 正对照 `LadderInfAccept:label-∞0`: 3268/92/379. 闭包干净不说明定义没受记号启发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudge where

open import OCF.Align.ValueJudgeBase public using (_≼_; _≈ᵛ_; _≺ᵛ_)
open import OCF.Align.ValueJudgeFix public using (IsFix; fix-uniq; fix-static; module Row)
open import OCF.Align.ValueJudgeRow public using (Rows)
open import OCF.Align.ValueJudgeRowNeg public using (rows-blind; const-rejected; top-low-rejected)
open import OCF.Align.ValueJudgeInst public using
  (T₀≺T₁; T∞-step; T∞-lim; T∞-mono; T∞-strict; T₀-sup; fin≺T₀; fin₁≺; T₀ᵀ≈T₀∞; T₀ᵀ≺T₁ᵀ; T₁ᵀ≺T₂Ω; T₀∞≺T₂Ω; T₂Ω≺next; T₂Ω≺top₂;
   closed-T₀; closed-T₁; closed-T₂Ω; T₀∞≺T₁∞; T₀∞≺T₂Ω′; uip∞; uip₂)
open import OCF.Align.ValueJudgeSpec public using (module FixRow; module CutΩΩ; IsPsiᴸ-uniq; IsPsiᴸ-mono; ¬inᴸ)
open import OCF.Align.ValueJudgeSpecLow public using (fix-Ω)
open import OCF.Align.ValueJudgeSpecInst public using (spec-ΩΩ; spec-Ω·2)
open import OCF.Align.ValueJudgeReg public using (arg-mono; walk-mono; reg-floor; slow-not-reg; slow-floor; reg-blind; reg-fast; reg-gap)
open import OCF.Align.ValueJudgeCheck public using (wrong-fold-not-reg; t0-reg; t1-reg; t2-reg; slow-reg)
```

## 导航

| 文件 | 内容 | 闭包 |
|---|---|---|
| [ValueJudgeBase](ValueJudgeBase.lagda.md) | 值序 `≼` (无记号世界), `≺→s≼`, `⊑→≼` | 干净 |
| [ValueJudgeLadder](ValueJudgeLadder.lagda.md) | `ι-top`, `V-≺`, `V-lim`, `V-chain`, `clos-row` | 干净 |
| [ValueJudgeBridge](ValueJudgeBridge.lagda.md) | `D-ψΨ`, `Br₁`, `V₁≺` | 干净, 参数 `Uq` |
| [ValueJudgeBridgeN](ValueJudgeBridgeN.lagda.md) | `LadderInfBridgeTop` 换实例 | 干净 |
| [ValueJudgeInst](ValueJudgeInst.lagda.md) | 实例上的上下界 | 干净 |
| [ValueJudgeFix](ValueJudgeFix.lagda.md) | `IsFix` | 干净 |
| [ValueJudgeRow](ValueJudgeRow.lagda.md), [ValueJudgeRowV](ValueJudgeRowV.lagda.md), [ValueJudgeRowNeg](ValueJudgeRowNeg.lagda.md) | `Rows`, `V-rows`, `rows-blind` | 干净 |
| [ValueJudgeSpec](ValueJudgeSpec.lagda.md), [ValueJudgeSpecTree](ValueJudgeSpecTree.lagda.md), [ValueJudgeSpecInst](ValueJudgeSpecInst.lagda.md), [ValueJudgeSpecLow](ValueJudgeSpecLow.lagda.md) | `Lv` 上的规格, `FixRow` | 干净 |
| [ValueJudgeReg](ValueJudgeReg.lagda.md) | `Reg⁰` 与大数 | 干净 |
| [ValueJudgeCheck](ValueJudgeCheck.lagda.md) | 旧树, 有限测试 | 干净 |
| [ValueJudgeAccept](ValueJudgeAccept.lagda.md) | 标签对照 | **不干净**, 读记号 |
