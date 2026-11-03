# 终局: EBO $=\psi_0(\Lambda)$ 的闭项到底要什么 (从终点往回推)

> 底座 [EBOTopStage](EBOTopStage.lagda.md) (接口与通用定理), [EBOTopLow](EBOTopLow.lagda.md) (闭实例), [EBOTopRaw](EBOTopRaw.lagda.md) (真正的塔), [EBOTopLink](EBOTopLink.lagda.md) (塔的头两项), [EBOTopBarrier](EBOTopBarrier.lagda.md) (壁垒检查), [EBOTopIR](EBOTopIR.lagda.md) (侦察). 都不含记号; 记号只在验收 [EBOTopAccept](EBOTopAccept.lagda.md).
>
> **判决: 接口成立且居留, 终点是条件定理, 条件收缩成一句话. 目前的全部站点都在塔的第 3 项 $x_3=\psi_0(\Omega_{\Omega_\Omega})$ 之内; 从 $x_3$ 到 EBO 不需要新的数学, 只要 $x_3$ 的证明走 `next` 的闭包. 还差两件: 比较从哪里来, 与闭包定理本身. 这两件都没有做, EBO 没有定义出来.**
>
> **阶段定理要交付什么 (编译过的).** 对裸层号路线, 恰好是一族 (`Residual` $\Leftrightarrow$ `Family`, `toStage`, `res→fam`, `fam→res`):
>
> $$\forall n.\ \mathrm{HS}\big(\psi_0(\Omega_{L_n})\big),\quad L_0=0,\ L_{n+1}=\Omega_{L_n}$$
>
> 其余全部已是无条件定理: 闭项本身 (`Raw.EBOᵀ`, 对任何判决 `S` 都有定义, `EBO-lim`), FGH (`big`), 塔的步进 (`infl`, `spine`), 不动点 (`fixpoint`), $\Omega$ 的连续性 (`Ω-Λ⊑`). 再往下一层, `Family` 只要提第 0 层的输入 (`family-from`, `DiagN`): 对每个 $n$, $T_n\,y=\psi_0(\Omega^{(n+1)}_y)$ 在含 1 的好输入集上保持 `HS`, 单调, 膨胀. `n = 0` 就是 [Diagonal](Diagonal.lagda.md) 的形状.
>
> **编译过的定理.**
>
> 1. **`Top` (条件于 `Stage`).** `Stage` 的 21 个字段 (世界 6, 证书 6, 回灌 2, 层序 2, 层极限 3, 只对塔 2) 给出闭项 `EBOᵀ`, 证书 `EBO-HS`, `FGH`, 不动点 `fixpoint`. 对角线是一个定义, 写在 `Stage` 里 (`Tow`, `L`, `x`, `Λ`), 不按阶段定制. 比较不在接口里. 塔的步进不是字段, 是推论 (`spine`).
> 2. **不动点, 树语言 (`EBOTopRaw`, 无条件).** $\Omega_\Lambda$ 的层号与 $\Lambda$ 的关系是**层序 $\sqsubseteq$ 的两个方向** (`next Λ ≃ Λ`). 不是结构互模拟 (`¬≅`), 也没有 $\prec$ (`¬≺₁`, `¬≺₂`), 所以结构三歧在不动点上不成立 (`¬tri-fix`). $\prec$ 良基 (`accL`, `≺-irrefl`).
> 3. **闭实例 `instᶜ` (无条件).** 世界是 [Level](Level.lagda.md), `feed = toLevel ∘ ψ⁰`, 证书是 [Uniform](Uniform.lagda.md). 通用定义给出的闭项就是 `BTBOᴵ` (`Same.EBOᵀ≅BTBO`), 标签 $\psi_0(\Omega_\Omega)$ 是 [Label](Label.lagda.md) 的定理. 附带: `Low-fix`, $\psi_0(\Omega_x)\simeq x$ 在 `Ordᴵ` 里是定理, 此前只是估计. `no-WLPO`: 若 `Stage → WLPO` 可证则 WLPO 可证. **BTBO 与 EBO 的差别只在一处: `next` 里有没有折叠** (`toLevel ∘ ψ⁰ ∘ Ω` 对 `toLv ∘ Ω`).
> 4. **塔的头两项 (`Heads`, 对一切 `S`).** `h₀ : HS x₀`, `h₁ : HS x₁`, 由 `Uniform` 经公共形式 `P₀`.
> 5. **塔的形状 (`tower-form`, `G-one`, `x-form`, 对一切 `S`).** $L_{n+2}=\mathrm{limᴼ}\ 0\ (G_n)$, 第 0 项是上一个 $L$. 所以塔本身的节点全在第 0 层, 目标 0, 从不问 `S`.
> 6. **必要性 (`must`, `must-step`, 对一切 `S`, 一切 $k$).** `Family` 蕴含: 目标 $k$ 的链上每一点的层号的输出 `HS`, 且相邻步进. 所以**只做低目标不够**.
> 7. **目标的字面上界 (`ψ-bound`, 对一切 `S`, 一切模式).** $i\sqsubseteq$ `toLv` $(\psi_i\,t)$. 链点的层号字面地包含目标的前驱.
> 8. **一步闭包就够 (`G-good`, 条件定理).** 好层号对 `next` 封闭则全部塔高成立.
> 9. **这些都是同一棵树 (`same-TΩΩ`, `reach-T₅`).** `x 3` 就是 `TΩΩ`, 第 5 站 $T_5$ 是它的第 $(1,0,0,2,1)$ 项.
>
> **编译过的否定 (壁垒检查, `EBOTopBarrier`).** 接口**没有**下面这些字段, 它们都不能有:
>
> - `no-BT-field` (`noBT`): 好层号上路径全部可比, 在 $L_2$ 上是假的.
> - `no-global`, `¬triᴵ` (`¬tri`): 层号全局可比是假的, 裸层号上不动点自己就是反例.
> - `no-⊤`: 好的谓词不能是全部, $\lim[1,0,0,\dots]$ 的输出不 `HS`.
> - `no-all-branch`: 好的谓词不能对 `limᴼ` 的全部分支封闭, 哪怕参数层 0.
> - `no-L3` (`no-Ω₂`): 只要 $2$ 算第 0 层的好输入, [InaccTheta](InaccTheta.lagda.md) 的 `LvG` 在 $L_3$ 上就推出 WLPO. **那个设计到不了塔的第 3 项**, 这比 "第 5 站用不到它" 更强.
> - `bad-S` (`no-uniform`): 好层号含全部 `E a` 且好蕴含 `LvT`, 推出 WLPO.
> - `bad-dec` (`dec-A→WLPO`): 好输入可判定推出 WLPO (以 `Funext` 为参数).
> - `no-topᴵ`, `cof`: `Ordᴵ` 没有共尾元, 裸层号有; `Ordᴵ` 有 `<ᴵ-dec`, 裸层号没有 `BT`. 两难 (`barrier-form`) 在接口上是 "比较与共尾元, 实例选一个".
> - `triv`: 接口**不管强度**. 退化实例也居留, 闭项是 $\lim[0,0,\dots]$. 居留不等于强, 强度要看折叠 (`OCFSpec*`) 与验收.
>
> **逐字段的差距表.** "低端" 是 `instᶜ` (全部无条件). "塔" 是裸层号上的 `Raw S`.
>
> | 字段 | 低端 | 塔 | 状态 |
> |---|---|---|---|
> | `Lv`, `Tr`, `base`, `out`, `Ω` | `Ordᴵ`, `Ordᶜ` | `Lv`, `Ordᴸ` ([InaccTreeBase](InaccTreeBase.lagda.md)) | 定理 |
> | `ψ₀` | `ψ⁰` | `PF.ψⁿ 0` ([InaccFloorTree](InaccFloorTree.lagda.md)) | **以 `S` 为参数**; `S` 不正确时闭项也有定义, 只是值不对 |
> | `feed` | `toLevel ∘ ψ⁰` (要 `HS`) | `toLv` (不要证据) | 定理 |
> | `_⊑_`, `infl`, `lub`, `ub`, `lub-Ω`, `Ω-Λ` | `⊑ᴵ`, `Sim→⊑ᴵ`, `lim`, `refl`, `Ω-Λᴸ` | `⊑`, `infl`, `lim`, `ub`, `refl`, `Ω-Λ⊑` | 定理, 全部层号 |
> | `GoodL`, `GoodT` | "$\ell\sqsubseteq$ 下一项" | **`Residual`** | 塔: 开放, 等价于 `Family` |
> | `seed`, `good-seed` | 1, `seed-good` | 0, `gz` | 定理 |
> | `good-Ω`, `cert` | `Uniform` (全部 $a$) | `gΩ`, `gc` | 塔: $n\le1$ 定理 (`Heads`); $n=2$: 只在 `Ordᴵ` 世界是定理, 裸层号上开放; $n\ge3$ 开放 |
> | `good-feed` | `clo` (`Ψ⁰-mono`) | `gf` | 塔: 开放 |
> | `good-Λ` | `good-Λᴸ` | `gΛ` | 塔: 由 `Family` 与 `spine` 推出 (`FromFamily`), 不是新工作 |
>
> **哪些开放问题真的挡路** (上面的定理 + 下面标明的判断):
>
> | 问题 | 回答 | 依据 |
> |---|---|---|
> | $\psi_k$ 的证书, 一切 $k$ | **必须.** 目标还要到可数序数 ($\omega$) 与不可数 ($\Omega\cdot2$) | `must` (定理, $k$ 自然数); `n8`, `reach-W` (有限) |
> | 参数层 $\ge1$ 的 `limᴼ` 作下标 | **必须, 下标躲不开.** 但分支只要好输入, 不要全部 | `reach-Ω₂`, `level-Ω₂`, `HS-Kk`, `no-L3` (定理). 这正是 `LevelK*` 在做的事, 不是绕路. 注意: 参数层不止自然数. `n7`, `n8` 的目标是 $\omega$, `reach-W` 是 $\Omega\cdot2$; 按 $k:\mathbb N$ 递归的地板塔不够 (判断, 对照 `LevelKTower`) |
> | 判决 `S` 处处正确 | **不要.** 对原始层号全部正确是 WLPO (`no-uniform`). 目标 0 与字面自然数目标不问 (`rise-diag`, `silent-1`). 目标一旦不是字面自然数就问 (`asked`, `query`, `kind-rise`/`kind-ver`). 要的只是塔上走到的那些对 (判断: `Family` 只提那些点, 没有定理说这个子集有简单的判定) | `VerdictSpec*` 给规格与唯一性, 不是绕路; 但全局正确不是目标 |
> | `I` 层 | 不要 | `Stage` 没有它, $x_n$ 不提它; [InaccStrike](InaccStrike.lagda.md) |
> | `Syn` 文法 | 绕路, 也违反纲领 4 | [AGENTS](../../../AGENTS.md); `UniformLv*` 已经把它去掉到第 5 站 |
> | 单一 `WF` 证书够到 $\Omega_\Omega$ | 绕路, 已否定 | `¬WF-L₁`, `no-BT-field` |
> | 数据树 `O`, `Goodᴺ` 再往上逐站 | **不是必经之路** (判断). 那些站都在 $x_3$ 之内, 塔的定义不用数据树. 它们的价值是闭包定理的证明模式, 不是站点本身 | `same-TΩΩ`; [UniformNF5Main](UniformNF5Main.lagda.md) |
> | `Lab` (逐项标签) | 不挡闭项, 挡 "这是 EBO" 这句话 | `OCFSpec*` 或 `Lab`; 此处只有有限检查 |
>
> **第一个具体障碍.** 塔的第 3 项. $L_0,L_1$ 的 `Family` 是定理; $L_2$ 在 `Ordᴵ` 世界是定理, 但那个世界没有共尾元, 走不到 $L_3$ (`no-topᴵ`). 裸层号有共尾元, 但 $x_2$ 看来就要 `S` (`reach-x₂` 加探针, 判断). 第一个两边都没有的是 `HS (x 3)`, 它要同时解决三件: 参数层 $\ge1$ 的好输入 (`no-L3`), 非自然数目标的比较 (`asked`), 跨分支的比较 ($W$, `reach-W`). 精确的第一步: `HS (T₁ (natT 2))`, 即 $\psi_0(\Omega_{\Omega_2})$, 它的链就是 `Cert-Tw` 的塔, 缺的是把 `no-Ω₂` 换掉.
>
> **还差的最小清单.**
>
> 1. **比较 (定义一侧).** 一个不读记号的派发, 在塔走到的对上正确. `S` 或者证据. 现状: 目标 0 与字面自然数已解决; [InaccModulus](InaccModulus.lagda.md) 的 `Dᵐ` 到可数段 (验收用标准形, `Reg` 的封闭性只有采样); 单分支的比较有字面上界 (`ψ-bound`), 比较本身没有写; 跨分支 ($W$) 有 [UniformLv](UniformLv.lagda.md) 的按高度分层, 那是逐层输入.
> 2. **闭包定理 (证书一侧).** `Residual`: 一个谓词, 含 0, 对 $\ell\mapsto\Omega_\ell$ 封闭, 蕴含输出 `HS`. 现状: [InaccTheta](InaccTheta.lagda.md) 的 `Good-ψ` 到目标 1, 相对于 `S`; 分层的 `LevelK*` 在写. 闭包定理的证明必须是一步的 (`G-good`).
> 3. **验收 (标签).** `Lab` 或外部规格. 不挡闭项. 现状: 有限检查 (`e0`–`e4`, `n4`–`n8`), `ψ₀Λ-tower` 给形状.
>
> 第 1, 2 件可以互相换: **如果层号的分支带证据, 证书进定义**. `EBOTopIR` 说这个循环 Agda 接受 (侦察, 只有 `rise`, 证据是假设 `ev`, 闭包定理进块没有试). 但 $\mathrm{HS}$ 作好输入不够: `ω`, `ω′` 都 `HS` 而互不为前驱 (`noBT`), 所以好输入还要是有向族 (判断, 与 `Reg-ω`, `Reg-ω⁺` 一致).
>
> **判断 (未编译).**
>
> - "EBO 的基本列走遍全部标准项, 所以层号和目标上没有更窄的片段". 依据是 Lean 的 `fs_mono`, `exists_lt_fs_numeral` ([OrdinalNotationsGuide](../../Survey/OrdinalNotationsGuide.md) §5.2) 与上面的有限路径, 这里没有证.
> - "从 $x_3$ 到一切 $x_n$ 不需要新的数学". 条件形式是 `G-good`, 但 $x_3$ 的证明是否确实走 `next` 的闭包, 要等它证出来.
> - "好输入可以只取链可达的树". `no-uniform` 的反例族不可达, 所以这条否定挡不住它; 但可达集的刻画没有写.
>
> **有限检查 (`EBOTopAccept`).** `e0`–`e4`: `S` 为变量时 $x_n$ 与 `EBOψ n` 在宽 2–3, 深 5–6 内无偏离. `n4`–`n8`: $x_3$ 的基本列走到 $\psi_1,\psi_2,\psi_\omega$. `reach-W`: 记号走到 $W$. `low-ok`: 低端闭项对 $\psi_0(\Omega_\Omega)$ 宽 3 深 6. 这些不是定理.
>
> **审计.** 除验收外, 全部文件的导入链到不了 `EBO`, `EBOI`, `Correspond`, `Standard*`, `SystemOmega`, `Bachmann`, `Closure` (模块级, 脚本检查). `EBOTopStage` 只导入标准库. 全文 `--safe --without-K` (`Low`, `Raw`, `Barrier`, `Link`, `Accept` 加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示; `Stage`, `Residual`, `DiagN`, `Block` 的参数都是假设, 已标明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTop where

open import OCF.Align.EBOTopStage using (Stage; module Top)
open import OCF.Align.EBOTopLow using (instᶜ; no-WLPO; triv; module Low)
open import OCF.Align.EBOTopRaw using
  (next; tower; Λ; infl; fixpoint; ¬≅; ¬≺₁; ¬≺₂; ¬tri-fix; cof; tower-form; G-one; G-good; module Raw; module Reduce; module Must)
open import OCF.Align.EBOTopLink using (module Heads)
open import OCF.Align.EBOTopBarrier using (no-BT-field; no-global; ¬triᴵ; no-topᴵ; barrier-form; bad-dec; module Good; module Forms)
open import OCF.Align.EBOTopIR using (module Block)
```
