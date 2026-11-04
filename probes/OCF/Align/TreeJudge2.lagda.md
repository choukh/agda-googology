# 树侧判据 (二): `ghost` 实例化到真树, `HF` 的界限, 判据的修正 (判决: PARTIAL)

> 底座 [TreeJudge2Base](TreeJudge2Base.lagda.md) (`ghostᴸ`, `Pinch`, `pinch`), [TreeJudge2Rel](TreeJudge2Rel.lagda.md) (闭包以下的折叠, `head-≅`), 否定 [TreeJudge2Id](TreeJudge2Id.lagda.md) (`no-id`), `HF` 的类定理 [TreeJudge2Hf](TreeJudge2Hf.lagda.md), 有限测试 [TreeJudge2Test](TreeJudge2Test.lagda.md), [TreeJudge2TestW](TreeJudge2TestW.lagda.md) (不干净). 接 [TreeJudge](TreeJudge.lagda.md), [TreeJudgeBase](TreeJudgeBase.lagda.md).
>
> **判决: PARTIAL. 目标 1 做到一半: 恒等读法的树没有证书是定理了 (`no-id`, 目标 $\Omega+1$, 测试报错的最小目标). 没有 `trim` 的树还是有限测试: 机制定位了, 走树没有写. 目标 2 证不出: 紧的 `T₀` 过不了 `HF` (测试), 而且第 2 项上同头的界跟着分支走 (`b-t2`, 测试), 这是 `Pinch` 的影子, **判断: 它很可能没有证书, 但这是判断**; 我没有它有或没有证书的定理. `T₀′`, `T₀ʷ` 在同样的取样里界恒为 1, 也没有定理. 目标 3: `HF` 对一类闭包是定理 (`hf-class`), 上一轮要的桥是假的 (`no-bridge`), 没有 "紧读法的树满足 `HF`" 这条一般定理, 而且它对 `T₀` 是假的 (测试). 目标 4: 判据改了: 必要条件换成 `Pinch` (定理), `HF` 降为读法的诊断.**
>
> ## 编译过的定理 (无条件, 无假设性模块参数)
>
> | 定理 | 文件 | 陈述 |
> |---|---|---|
> | **`no-id`** | [Id](TreeJudge2Id.lagda.md) | `Goodᴺ (T₀ L₁ (wf₁ , sfL) tcI) → ⊥`. $L_1=\Omega+1$, 恒等读法 |
> | `ghostᴸ` | [Base](TreeJudge2Base.lagda.md) | `ghost` 的前提只要在 $\tau\cong\mathrm{lv}(t_0)$ 上成立. 对一切 `Z` |
> | `Pinch`, `pinch` | [Base](TreeJudge2Base.lagda.md) | $\tau\cong\mathrm{lv}(t_0)$ 时, 分支 $\tau$ 的证书推出闭包的证书, 界 $\ge\tau+1$, 头的层号 $\sqsubseteq\mathrm{lv}(t_0)$, 则没有证书. 对一切 `Z`. `Ghostᴸ→Pinch`, `ghost→ᴸ`: 严格的推广 |
> | `pin` | [Id](TreeJudge2Id.lagda.md) `Xn` | `Pinch` 在真树上的实例 |
> | `head-≅`, `head-any` | [Rel](TreeJudge2Rel.lagda.md), [Hf](TreeJudge2Hf.lagda.md) | $\Omega_\Omega$ 在空上下文里, 层 0 的任意目标, 任意世界, 任意读法: 头 $\cong^{\mathsf z}$ `Ref` |
> | `no-bridge` | [Hf](TreeJudge2Hf.lagda.md) | 目标 `t0` 与目标 `tp q₁ tt`: 同一个头. **"头相同推出目标相同" 是假的** |
> | `hf-class` | [Hf](TreeJudge2Hf.lagda.md) | 目标在第一支: 头 $\cong^{\mathsf z}$, 界模前序是 1. 这一类上 `HF` 是定理, 任意读法 (`Fst.ub`, `Fst.lb`, `bd-t0`) |
> | `bd-bra`, `hf-fails` | [Hf](TreeJudge2Hf.lagda.md) | 目标穿过 `bra τ`: 界 $\succ$ `pr τ`; $\tau$ 是极限时界 $\not\sqsubseteq1$. 头不变. 这一类上 `HF` 假 |
>
> **前提可满足.** `no-id`, `no-bridge` 没有前提要满足; `Goodᴺ` 对这个家族不是自相矛盾的: 同一个折叠, 紧的读法在 $\Omega$ 上有证书 (`Good-Ω₁`). `pinch` 的前提: 真树上有实例 `pin`, 它的 $G_0$ 量词是不是空的 (即头 $t_0$ 有没有证书) 没有证, 见下面 "条件". `ghostᴸ` 的前提: 玩具树 `toy-ghost` ([TreeJudgeNeg](TreeJudgeNeg.lagda.md)) 满足 `Ghost`, 所以满足它. `hf-class` 的 `st`, `st′` 任意; `tp q₁ tt` 的 `q₁` 是字面路径. `hf-fails` 的 `aq`: 表里有 $\tau$ 的证据时成立, 这正是 `no-id` 的第 3 步给的 (`Rest`), 恒等读法的折叠真走到这里.
>
> ## `ghost` 为什么要推广
>
> `ghost` 要**一切** $\tau$ 上界 $\ge\tau+1$. 读定义: 分支 $b+1$ 的地板是 `fk b`, 界 $b+1$ (`pr`). 测试 `b-ghost₂`: 恒等读法在分支值 2 上同头的界是 2, 不是 3. **所以 `ghost` 实例化不到这棵树 (判断加测试, 没有写成定理), 上一轮 "约 300 行" 的估计也不成立.** 证明只用 $\tau=\mathrm{lv}(t_0)$; 头是极限时 $\tau$ 是极限, `pr τ = τ`, 界读到 $\tau+1$. 这是 `ghostᴸ`. `Pinch` 再去掉字面的第一路径, 因为 $f\,0$ 不能分情形 ([Id](TreeJudge2Id.lagda.md) 的头注). 实际约 900 行.
>
> ## 条件
>
> 没有条件定理. 没有证的相关命题 (不是这些定理的前提): 头 $t_0$ 自己有证书. 如果没有, `no-id` 还是对的, 但 `pin` 的 $G_0$ 量词是空的, 树没有证书多一个理由. 判断: 有, 没有证.
>
> ## 有限测试 (`refl`, 不是证明)
>
> `Tk p hp k`: 走 $p$ 处闭包的分支 $k$ 的第一路径, 只看头的指纹等于 $hp$ 处的头的闭包, 取最大的界. 表是分支 $k=0,1,\dots$ (分支值 $k+1$).
>
> | 树 | 测试 | 深, 宽 | 表 |
> |---|---|---|---|
> | 恒等读法, $\Omega+1$ | `b-id` | 8, 2 | **1, 2, 3, 4, 5** (`no-id` 成立) |
> | 紧的 `T₀`, $\Omega+1$, 第 1 项 | `b-t` | 8, 2 | 1, 1, 1, 1, 1 |
| **紧的 `T₀`, $\Omega+1$, 第 2 项** | `b-t2`, `b-t2₄` | 9, 2; 11, 2 | **1, 1, 2, 3, 4**: 分支值减 1 |
| `T₀′`, $\Omega+1$, 第 2 项 | `b-t2′` | 9, 2 | 1, 1, 1, 1, 1, 1 |
| `T₀ʷ`, $\Omega+1$, 第 2 项 | `b-w2` | 9, 2 | 1, 1, 1, 1, 1, 1 |
> | `T₀′`, $\Omega+1$ | `b-t′` | 8, 2 | 1, 1, 1, 1, 1 |
> | `T₀ʷ`, $\Omega+1$ | `b-w` | 8, 2 | 1, 1, 1, 1, 1 |
> | `OCF.Free` 的 `TΩ·2` (有证书 `certᵀ`) | `b-free` | 8, 2 | 1, 1, 1, 1, 1 |
> | 没有 `trim`, $\Omega+1$ | `b-n` | 8, 2 | 1, 1, 1 |
> | **没有 `trim`, $\Omega+2$** (比上一轮的 $\Omega\cdot2$ 小) | `b-n₂` | 7, 2 | **1, 2, 3** |
> | 带 `trim`, 同一位置 | `b-t₂` | 7, 2 | 1, 1, 1 |
>
> `HF` 的取样: **紧的 `T₀`, $\Omega+1$: 同头异界.** `v-t₁`, `v-t₂`, `v-same`: `lm 1` 界 1, `pC` 界 2, 头的指纹深 9 宽 3 相同. `run 10 9 3` 报的就是这一对路径 (约一小时, 在 scratch 里跑过一次, 不在文件里, 所以这一句是运行记录). 上一轮的接受测试是宽度 2, 看不到: `run 10 9 2` 在同一棵树上不报 (同一次运行). `T₀′`, `T₀ʷ` 在 `pC` 上界 1 (`v-t′`, `v-w`); `T₀ʷ` 的 `run 8 7 2` 不报 (`hf-w`).
>
> ## 判据的新陈述
>
> | 档 | 条款 | 说什么 | 地位 |
> |---|---|---|---|
> | 定理 | **`Pinch` 排除证书** | **链的第 0 点的值 $\tau$ 读进了一个闭包的界, 而这个闭包的头不高于 $t_0$: 没有证书** | 必要条件的逆否, 对一切 `Z`. 不可判定 |
> | 测试 | `Tk`: 同头的界跟着分支走 | 头固定, 界随分支值增长 | `Pinch` 的取样. 在后继分支上看到的只是影子: `Pinch` 要的是极限分支 |
> | 诊断 | `HF` | 同头同界 | **不是必要条件** (`hf-indep`), 不是充分条件. 对这类闭包等价于读法的一个性质 (`hf-class`, `hf-fails`). 它报的违反有两种: 跟着分支走的 (`Pinch` 形状), 不跟着走的 (`hf-indep` 的玩具, 有证书). `T₀` 的 2 对 1 看起来是后一种, `b-t2` 说它是前一种的影子 |
>
> **`HF` 与 `Pinch` 的差别是一张表 (表里 "没有" 都是定理, 其余见档):**
>
> | 树 | 证书 | `HF` | `Tk` 跟着走 | `Pinch` |
> |---|---|---|---|---|
> | `hf-indep` 的玩具 | 有 (定理) | 违反 (定理) | 不 | 不可能 (定理, 由 `pinch`) |
> | `toy-ghost` | 没有 (定理) | 不判断 | 跟着 (纸面) | 成立 (`Ghost`) |
> | 恒等读法, $\Omega+1$ | **没有 (定理 `no-id`)** | 违反 (测试 `hf-id`) | 跟着 (测试) | 成立 (实例 `pin`) |
> | 没有 `trim`, $\Omega+2$ | **没有证** | 违反 (测试 `hf-n₂`) | 跟着 (测试) | 没有写 |
> | 紧的 `T₀`, $\Omega+1$ | **没有证** | 违反 (测试, 宽 3) | **跟着 (测试 `b-t2`, 分支值减 1, 只在有限分支)** | 没有写 |
> | `T₀′`, `T₀ʷ`, $\Omega+1$ | 没有证 | `pC` 上界 1; `T₀ʷ` 的 `run 8 7 2` 不报 | 不 (测试) | 没有写 |
> | `TΩ·2` | 有 (定理 `certᵀ`) | 不报 (测试) | 不 (测试) | 不可能 (定理, 由 `pinch`) |
> | `Good-Ω₁` | 有 (定理) | 不报 (上一轮的测试) | 没有测 | 不可能 (定理, 由 `pinch`) |
>
> **这个判据不判定 "对": 过了 `Tk` 不说明有证书.** 它也不管值 (`hf-blind`, `force-≃` 不变).
>
> ## 第一个障碍
>
> 1. **没有 `trim` 的树.** 机制 (判断, 由测试与读定义得出, 没有编译): $\Omega+2$ 上 $X$ 是 `[lm 1, lm 1]`, 分支 $\tau$ 过四层折叠 ($\psi_0,\psi_{\Omega+1},\psi_\Omega,\psi_{\Omega+1}$). 没有 `trim` 时 `riseΩ` 的 $\xi=\pi$, 帧 $\tau$ 经 `stξ` 进了输出的上下文, 闭包在 $\psi_0$ 计值时 `selSt` 读到它 (`floors` 的 `fromSt`), 所以来源不是目标路径 (恒等读法那里是 `fromTgt`), 状态不变量要从 `IsJ` 加强到帧的 `Evd` 带位置. 同一套办法应该能写, 判断约 1200 行, 没有写, **不是走不通**.
> 2. **紧的 `T₀`.** `b-t2`: 第 2 项的分支值 $k+1$ 上, 头不变的闭包界是 $k$. 这与恒等读法差一步 (恒等是 $k+1$), 所以 `Pinch` 的 $\tau+1$ 这个形状不一定直接适用; 要的是更弱的: 极限分支 $\tau$ 的第 $n$ 项上界 $\succeq f\,n$ 减一, 而 $f\,n$ 终于超过头 `Ref` 的层号. 这时头律直接断. **这一步在极限分支上没有测到** (分支 $\omega$, `lm 3` 路径的测试 900 秒超时, 没有结果, 不算一致也不算不一致), 走树也没有写: 过三遍折叠 ($\psi_0,\psi_\Omega,\psi_\Omega$), 路径里有第一支, 来源判断是 `fromSt`, 与 [GuardBridge](GuardBridge.lagda.md) 说的 `owk` 那一行同一件事 (`T₀′` 只改这一行, 表恒为 1). `T₀-too-high` 否定的是桥, 不是证书, 这一点不变. `T₀′`, `T₀ʷ`: 没有定理, 没有否定.
3. **`HF` 的一般定理.** 要的是非空上下文上的界公式. `floors` 给来源, 但 "活帧的值由头决定" 这个方向我没有候选: `head-any` 说头什么都不读, 所以任何活帧的值都不能由头决定. 判断: 在非空上下文上, `HF` 只能由 "活帧是紧的" 这样的条件保证, 这不是头的性质.
>
> ## 哪些形状受记号影响
>
> 定义都不读记号. `Tc-id`, `T₀` 的来路同 [GuardTight](GuardTight.lagda.md), 紧的读法看目标定. 这里的 `Pinch` 是从 `ghost`/`noW` 抽象出来的, 它的形状是 "界读到 τ, 头不读", 是树侧的陈述, 但 `HF` 与 `tail-free` 的动机来自 `ScafLadderTop`, 看记号定的, 见 [TreeJudge](TreeJudge.lagda.md). `TreeJudge2TestW` 的 `Rs` 项取自读记号的 `GuardReadAccept`, 只作测试的读法. 没有读记号判定任何东西; `no-id` 的目标 $\Omega+1$ 是看树侧 `run` 的报错定的.
>
> **这不算 "让树自足":** 树侧的合法性标准现在有一条定理形式的必要条件, 还是只说 "哪里错", 不说 "下一步写什么".
>
> ## 审计
>
> `importclosure.py`: `TreeJudge2`, `Base`, `Rel`, `Id`, `Hf`, `Test` 闭包干净 (编译器保证, 退出码 0). `TestW` 不干净 (碰到记号, 文件头写明). `depslice.py` (语法级) 结果在报告里. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`. 模块参数: `Walk`, `Hd`, `Rest`, `Xn`, `Xp`, `Xm`, `FactsG` 由 `no-id` 实例化或是证明的中间层; `RelT`, `HfT` 的 `tc` 是任意读法, 不是假设. 全部模块参数都不是条件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2 where

open import OCF.Align.TreeJudge2Base using (Ghostᴸ; ghostᴸ; ghost→ᴸ; Pinch; pinch; Ghostᴸ→Pinch)
open import OCF.Align.TreeJudge2Rel using (Ref; module RelT)
open import OCF.Align.TreeJudge2Id using (no-id; module Xn)
open import OCF.Align.TreeJudge2Hf using (module HfT)
open import OCF.Align.TreeJudge2Test using (b-id; b-t; b-t′; b-free; b-n; b-n₂; b-t₂; b-ghost₂; v-t₁; v-t₂; v-same; v-t′; b-t2; b-t2₄; b-t2′; hf-id; hf-n₂; hf-t₂)
```
