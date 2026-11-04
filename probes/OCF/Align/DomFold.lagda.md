# 更高定义域上的折叠: 第一路径守卫 (判决: PARTIAL)

> 底座 [GuardTight](GuardTight.lagda.md). 接口 [DomFoldDom](DomFoldDom.lagda.md), 下一层 [DomFoldNext](DomFoldNext.lagda.md), 树 [DomFoldBase](DomFoldBase.lagda.md), [DomFoldTree](DomFoldTree.lagda.md), 对角线 [DomFoldDiag](DomFoldDiag.lagda.md), 加法 [DomFoldAdd](DomFoldAdd.lagda.md), 否定 [DomFoldNeg](DomFoldNeg.lagda.md), 读位置 [DomFoldRead](DomFoldRead.lagda.md). 都不用记号的定义, 导入闭包干净. 记号只在验收 [DomFoldAccept](DomFoldAccept.lagda.md).
>
> **判决: PARTIAL. 对任何 `DomX` 只有一个折叠 (`Tn`, `Fold`), 塔 `Xₙ` 对 $n$ 一致, 不逐层新写. $\Omega_{n+2}$ 有 `WFˢ`, 这是无条件定理 (`WF-Ωᶠ`, `Cf-Ωₙ`), 所以 $\psi_k(\Omega_{\Omega_{n+2}})$ 是闭项 (`Tψₙ`). 到此是定义编译过, 正确性只有有限测试. $\psi_0(\Omega_{\Omega_3})$ 作为序数还没有定义: 树是带链的符号, 链点读回成分支要 `GoodFeed`, 没有证. 第一个障碍是编译过的定理 (`chain-stuck`): 同键的活帧高到 $\Omega_1+3$ 时, 第一路径守卫挡住链点. $\Omega_{\Omega_\eta}$ 没有写.**
>
> **任务 1: 局部比较的折叠 (编译).**
>
> | 东西 | 哪里 | 说明 |
> |---|---|---|
> | 守卫 `Fg` | [Next](DomFoldNext.lagda.md) §1 | $x\approx y$ 或 $x$ 经第一路径在 $y$ 之下. 第一路径没有分支, 所以搬运带对一切表的转移 (`fg→⊴`). 这是 `no-WFˢ-Ω⁺` 逼出来的 |
> | 比较 `cmpFF`, `bd′` | [Next](DomFoldNext.lagda.md) §1, §2 | 字面上界之下的两条第一路径可比. 上界由分支现造: 帧 $x$ 的表项是 $x+1$, 地板与 $x$ 都是它的第一路径 (`fg<suc`, `bound′`). 这是 `cmpW` 的形状, 表随分支增长. 只比第一路径, 不比两个分支路径 |
> | `WF-Ωᶠ`, `Cf-Ωᶠ` | [Next](DomFoldNext.lagda.md) §4 | **对任何 `DomX`, 无条件.** `no-WFˢ-Ω⁺` 只杀旧守卫 (`no-fg-Ω3-Ω2`) |
> | `emb⊴`, `WFˢ-emb` | [Next](DomFoldNext.lagda.md) §3 | 嵌入保持带转移的 `⊴`. 用下层转移对 `cov` 的实例, 不翻译表 |
> | `Fold`, `Tn`, `tn` | [Tree](DomFoldTree.lagda.md) | 目标 `tn n` 不走路径, 不进地板. `rb` 读回, `oĉ` 带第 `ix` 层的链 (待计值) |
> | `ψ₁ᶠ` | [Diag](DomFoldDiag.lagda.md) | 任何带证书的层号折叠到第 1 层 |
>
> **任务 2: $\psi_0(\Omega_{\Omega_3})$ 的层.** `DiagOf X₁` 的 `feed`: $u_{k+1}=\psi_2(\Omega_{u_k})$, $u_0=\Omega_2$ (`base`), 同一个定义对 `X₀` 给 $\psi_1$ (取代 [GuardTightUp](GuardTightUp.lagda.md) 的 `Diag`, 不要路径与表). `Diag.Tdiag`: **条件定义, 模块参数 `GoodFeed` 没有证.** 另一条路是 `Tψ₀ₙ 1`: 在 `X₂` 上一次写出, 闭项, 无条件, 是符号.
>
> **任务 3: 对 $n$ 一致.** `Xₙ`, `Ωₙ`, `Cf-Ωₙ`, `Tψₙ`, `Tψ₀ₙ` 都是一个定义. 字段 `ix`, `nodeC`, `nodeF`, `emᵈ`, `base` 由 `Next.X′` 算出.
>
> **$\Omega_{\Omega_\eta}$: 没有写.** 三个具体卡点:
>
> 1. `no-tn-ω⁺` (编译): 不走路径的目标止于 $\omega$. 对目标 $\omega+1$ 是 WLPO. 所以 $\psi_{\omega+1}$ 的目标只能走路径, 回到 `no-fg-1-Ω₁`, `no-fg-floor`.
> 2. 下标不是自然数: `ix` 取值 $\mathbb N$, `tn` 的链只对自然数层. 要换成带路径的链目标, 这同样走回上一条 (判断).
> 3. 极限层的 `DomX`: $\mathbb D_{\lim f}$ 要沿 `s n : f n ⊑ᴵ f (suc n)` 搬运. `Next` 的上升是字面的 `inj₁`, 所以 `emb` 的分支由 `()` 处理. `s` 的 `s⊑ e q` 带 `≅ᴵ`, 这时 `emb` 的分支要拉回 $\eta'$, 拉回只到 $\cong$, 路径 `emb<` 要用 $\approx$ 搬运, 要自反证据. 写法判断是一个 `Hom` 记录加 `XLim`, 约 700 到 1000 行, 没有试. 自然数塔的余极限 $\mathbb D_\omega$ 字面, 判断写得出, 约 400 行, 没有写; 它给 $\psi_0(\Omega_{\Omega_\omega})$, 到 $\Omega_{\omega+1}$ 就碰第 1 条.
>
> **第一个障碍 ([Neg](DomFoldNeg.lagda.md), 编译).** `below-floor`, `no-fg-floor`, `chain-stuck`: $\Omega_1+3$ 在 `Lv₅` 之下 (带分支的路径), 不经第一路径. `Yₑ` 的闭包的下界就是 $\Omega_1+3$, 链点 `Lv₅` 过不了. 旧守卫放得过它但没有 `WFˢ`. **两个守卫各败一边, 这只否定这两个守卫.** 真闭包 (目标不低于 `ix`) 不受影响, 分支集仍共尾 (判断). 带链的闭包受影响, 从 $\psi_0(\Omega_{\Omega_2\cdot2+1})$ 这一带开始 (判断: $W$ 的类比过了测试, 那里地板是 $\Omega_1$; 地板高了就是 `chain-stuck`).
>
> 可能的方向 (判断, 没有写): 紧的读位置把地板压回最小的分支 (`tail-free` 的类比, 目标不高于 $\Omega_2+\Omega_1$ 时够用); 分支换成 $M+x$ (第一路径自动成立, 值相等但基本列不逐项一致, 与 [Value](Value.lagda.md) 同类); 守卫带路径与它的证据 (要 `Fold` 的表, 下标依赖表).
>
> **有限测试 ([Accept](DomFoldAccept.lagda.md), 全部 `refl`; 比较器看种类, 闭包的共尾层, 走分支 $c+k$; `agree` 还看界).**
>
> | 目标 | 证书 | 深度, 宽度 | 结果 |
> |---|---|---|---|
> | `X₀` 对旧树 $\Omega$, $\Omega\cdot2$, $\Omega\cdot3$, 第 5 站 (`r-*`) | 定理 | `agree` 8–10, 2 | 一致, 含界 |
> | $\psi_0,\psi_1,\psi_2(\Omega_{\Omega_2})$ (`a-*`) | 定理 | 12; 10, 2 | 一致, 对照 `a-ctl₁` |
> | 分支 $x=\Omega_1,\Omega_1+1,$ `Lv₅` (`b-*`) | 定理 | 10, 2 | 一致 |
> | 链: $\gamma_1,\gamma_2$, 基本列第 1 项 (`z-*`, `o-*`) | 定理 | 10–12, 2 | 一致 |
> | 分支上的折叠对下一层的折叠 (`e-*`) | 定理 | `agreeE` 9, 2 | 一致, **含界** (都用恒等读法) |
> | $\Omega_2+1$ (`s-*`), $\Omega_2\cdot2$, $\Omega_2\cdot2+1$ (`m-*`, `ms-*`) | 定理 | 8–12, 2 | 一致 |
> | $W$ 的类比, 走 `maxF` (`c-W₁`, `c-W₂`) | 定理 | 20, 1; 12, 2 | 一致 |
> | $\psi_0,\psi_2,\psi_3(\Omega_{\Omega_3})$ (`v-*`), $u_0,u_1$ | 定理 | 12; 10, 2 | 一致 |
> | $n=0,1,2$ (`n-*`) | 定理 | 12, 2 | 一致 |
> | $u_2$ 与第 1 项 (`U₂`), `Diag` (`DiagT₀`, `DiagT₁`) | **变量** | 7, 2 | 一致; 只说这个深度没问到它 |
>
> 这些测试不说明 $\mathsf{Good}$ 成立, 也不说明链点读得回. 恒等读法下界不紧, 高层的紧读法没有写.
>
> **逐阶段的输入.** 树: 没有. 层号的 `WFˢ`: $\Omega_{n+2}$, `emb`, 加法是定理, 对一切 $n$. `Tc`: 高层只有 `Tc-id`. `GoodFeed`: 条件. `Xω`, `XI`: 没有.
>
> **受记号影响的形状 (如实).** 第一支与下界取 `base` ($\gamma_0=\Omega_\mu$). 闭包带第 `ix` 层的链 ($\gamma_{k+1}=\psi_\mu(b[\gamma_k])$, 规则 6). 读回的形状来自 [GuardTightUp](GuardTightUp.lagda.md). `feed`, `Diag` 的序列. 这些是看记号定的, 定义不读记号. **树侧逼出的:** `Fg` (由 `no-WFˢ-Ω⁺`), `tn` (由 `no-fg-1-Ω₁`), 分支的后继作局部上界 (由 `bd`, `cmpFF`), `gapL`. 这不算树自足: `base` 的选取没有树侧判据, 只有测试.
>
> **壁垒 (判断, 没有形式对比).** `inj₁ _ <′ inj₂ _` 是 `⊥`, 经第一路径在 $\Omega_1$ 之下的只有 $0$ (`first-Ω₁`), 所以有界比较不含 `Ordᴰ` 的初始段, `barrier` 的前提不成立. `bd′` 只比第一路径, 不是 `no-bra-cmp`. `no-tn-ω⁺` 与 `dec→WLPO`, `no-read-ᴵ` 同形: 这说明 `tn` 不能推到 $\omega+1$. `¬tri` 没有变: `Ordᴵ` 的部分仍是字面上界之下的 `<ᴵ-dec`. 我没有得到触犯壁垒的结论, 也没有证明这一组定义永不触犯.
>
> **审计.** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.GuardTight --only OCF.Align.DomFold OCF.Align.DomFold`: 干净, 这是编译器保证. `DomFoldAccept` 读记号. `depslice.py`: `WF-Ωᶠ`, `Tn`, `Tψ₀ₙ`, `chain-stuck` 到达记号 0; 正对照 `DomFoldAccept:a-ψ₀` 到达 48 块. 全文 `--safe --without-K` (加 `--lossy-unification`), 无公设, 无洞, 无停机或正性编译指示. 模块参数: `DomX`, `Dom` 是定义域; `Fold` 的参数是层号与证书; **`Diag` 的 `GoodFeed` 是假设**; `DomFoldAccept` 里 `U₂`, `DiagT₀`, `DiagT₁` 的证书是测试装置.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFold where

open import OCF.Align.DomFoldDom using (DomX; X₀; module FlrOf)
open import OCF.Align.DomFoldNext using (module FgOf; module Next; Xₙ; Ωₙ; Cf-Ωₙ)
open import OCF.Align.DomFoldDiag using (Tψₙ; Tψ₀ₙ; ψ₁ᶠ; module DiagOf)
open import OCF.Align.DomFoldNeg using (no-fg-Ω3-Ω2; no-fg-1-Ω₁; first-Ω₁; no-fg-floor; below-floor; chain-stuck; no-tn-ω⁺; fg→⊑ⁿ)
open import OCF.Align.DomFoldRead using (convTc)
import OCF.Align.DomFoldBase
import OCF.Align.DomFoldTree
import OCF.Align.DomFoldAdd
```
