# 层号一次性封闭 (判决: PARTIAL)

> 底座 [LevelFixCore](LevelFixCore.lagda.md) (块), [LevelFixVal](LevelFixVal.lagda.md) (读回, $\Omega$, 闭包定理), [LevelFixX](LevelFixX.lagda.md), [LevelFixBase](LevelFixBase.lagda.md), [LevelFixTree](LevelFixTree.lagda.md) (折叠, 脚本改写自 `DomFoldBase`, `DomFoldTree`), [LevelFixU](LevelFixU.lagda.md) (定义域 $\mathbb U$), [LevelFixFold](LevelFixFold.lagda.md) (闭项), [LevelFixNeg](LevelFixNeg.lagda.md). 记号只在 [LevelFixAccept](LevelFixAccept.lagda.md).
>
> **判决: PARTIAL. 一个归纳-递归类型 `LF` 就是全部层号, 没有 $n$, $\eta$ 编号, 目标 1 全部是它的值, `Legal` 的闭包定理对一切层号一步 (`Legal-Ω̂`), 塔与 $\Lambda$ 都合法 (`Legal-Λ`). 折叠只有一个定义 (`Tn`, 一个定义域 $\mathbb U$). 但折叠要的证书 `Cf-toU` 多一个条件 `Un`: 节点的名字满足 UIP. 这对自然数名字是定理, 所以 $\psi_k(\Omega_{\Omega_n})$, $\psi_k(\Omega_{\Omega_\omega})$ 无条件是闭项; $x_3=\psi_0(\Omega_{\Omega_\Omega})$ 起, 包括 $\psi_0(\Lambda)$, 只是条件于 `Un` 的闭项 (`x̂-if`, `ψ₀Λ-if`). 没有 `HS`, 不给 `Family` 的项.**
>
> **定义.**
>
> - `data LF`: `zero`, `suc`, `lim`, `lc : (k : LF) (c : Raw k) (t : LF) (g : (η : Raw k) → Gd k c η → LF) → LF`.
> - `Raw k`: 第 k 层的值, 节点在 k 之下的位置, 带形式的 `em` (低层放上来), `top` ($\Omega_k$).
> - `Gd k c η`: c 是 η 的字面第一位置, 且 `Lgl k η`.
>
> 块里只有 `Set` 值的函数, 没有证明. **折叠的输出读回来还在同一类型:** `rb : O k π → LG 𝕌`, `fromU : LG 𝕌 → LF`, `feed`, 再作下标 `Ω̂ (feed …)` 不需要新类型 (`Ωfeed`).
>
> **目标 1 (编译).** `Ω₁+1`, `Ω₁·2`, `ψ₁θ` (对合法且 `Un` 的 $\theta$), `Ω₂`, `Ω₃`, `Ωω`, `ΩΩ₂`, `ΩΩ η`, `ΩΩᴵ` (对一切 `Ordᴵ`), `tw`, `Λ`. $\Omega$ 的三行都是 `refl` (`Ω̂-suc`, `Ω̂-lim`, `Ω̂-lc`). 与 [EBOTopRaw](EBOTopRaw.lagda.md) 的 `next` 同形, 差别是节点带下界和守卫.
>
> **目标 2.**
>
> | 东西 | 哪里 | 档 |
> |---|---|---|
> | `Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)`, `Ω̂-CP`, `lgl→Legal`, `branch` | [Val](LevelFixVal.lagda.md) | 定理, 无条件, 一步, 不按阶段 |
> | `Legal-tw`, `tw-step`, `Legal-Λ`, `Legal-ΩΛ`, `Legal-Ωω`, `Legal-ΩΩ₂`, `Legal-ΩΩ`, `Legal-add` | [Val](LevelFixVal.lagda.md) | 定理 (`Legal-ΩΩᴵ` 要 `Legal (ofI η)`: `Ordᴵ` 的 lim 只带 `⊑ᴵ`, 不是字面第一位置) |
> | `Cf-toU : Legal x → Un x → Cfˢ (toU x)`, `WF-U`, `self-U`, `cp⊴` | [U](LevelFixU.lagda.md) | 定理, **条件 `Un`** |
> | `uip-nat`, `Un-up`, `Un-T`, `Un-Ωω`, `Un-add` | [U](LevelFixU.lagda.md) | 定理, 无假设 |
> | `Tψ-Ωn`, `Tψ-Ωω`, `x̂₀`, `x̂₁`, `x̂₂`, `feed`, `Ωfeed` | [Fold](LevelFixFold.lagda.md) | 闭项; 正确性只有测试 |
> | `x̂-if`, `ψ₀Λ-if` | [Fold](LevelFixFold.lagda.md) | **条件定义**, `Un` 是假设 |
>
> **`no-WFˢ-Ω⁺`:** 不适用, 也没有被推翻. 守卫是字面第一位置, `cp⊴` 给带转移的 `⊴`, 反例 $\Omega+3,\Omega\cdot2$ 不满足守卫 (`no-cp-Ω3-Ω2`). **`chain-stuck`: 没有解决.** 同一个窄守卫, 带链的闭包在这里仍是符号 (`oĉ`), 链点读成分支要 `Gd`, 没有定理, 判断是在 `chain-stuck` 那里过不了. 判断 "分支换成 $M+x$" 可以绕开这一点, 代价见 [Value](Value.lagda.md), 没有写.
>
> **目标 3.** **不给 `Family` 的项.** `Family` 是 $\mathrm{HS}(\psi_0(\Omega_{L_n}))$, 这里没有 `HS`, 也没有把闭包计值到第 0 层的树: `T⁰ 0` 里有符号 `oŝ`, `oĉ`, 计值要 `Goodᴺ`. 这里给的是低一档的东西: 塔的**层号证书**到 $L_2$ 无条件 (`x̂₀`, `x̂₁`, `x̂₂`), 对一切 $n$ 与 $\Lambda$ 条件于 `Un`. `Legal` 全部给 (`Legal-tw`, `Legal-Λ`), 但 `Legal` 不是 `HS`. **闭项不等于正确.** 塔本身 (`tw`) 不读折叠, 所以 `G-good` 的形状 (一步闭包) 在 `Legal` 这一档是真的; 在 `HS` 这一档不知道.
>
> **第一个障碍.**
>
> 1. **名字的回路 (编译报错, 不是否定定理).** $\mathbb U$ 的下标是依赖对 $(k,c)$. 同一个下标过两个守卫证据时要从 `el k c ⊑̂ el k a` 反演 `Gd k c a`. Agda 拒绝 (`LevelFixU` §2 有原文), 反演要 $k\equiv k$ 的回路平凡, 这就是 `Un`. `LF` 里有函数, 判断: 没有函数外延证不出 (`--cubical` 下判断证得出, 这里的选项是 `--without-K`, 没有试). `Un` 不是假的, 没有证明它假. 这个条件在 $x_3$ 就碰到: $\Omega_{\Omega_\Omega}$ 的分支里有 $\Omega_{\omega+1}$, 名字是 $\omega$.
> 2. **非自然数的名字 (编译).** `no-Lgl-Ωlim`: 块里不能比较不同孩子的值 (正性拒绝 `LF` 上的 `≡`, `LevelFixCore` 的 `P1`), 所以 $\Omega_{\omega+1}$ 的分支集比应有的窄: $\Omega_\omega+k$ 在, $\Omega_\omega\cdot2$ 不在. 目标是非自然数层时闭包没有链 (`ix` 给 0): 这是 `no-tn-ω⁺` 的同一个点, 这里没有绕开.
> 3. **读位置.** 只有 `Tc-id`. 界比较在 $\Omega+1$, $\Omega\cdot2$ 上不一致 (`b-Ω+1`, `b-Ω+1₂`, `b-Ω2`), 与 `GuardTight` 恒等读法的现象相同. 紧读法在 $\mathbb U$ 上没有写.
>
> 名字回路这一点: 依赖对加数据守卫是编译过的报错; 另外三个 (守卫读 `up` 的像; 非依赖的 `(k, x)` 带见证; 证据换成对证明的关系) 只在纸面上推到同一处 (`up` 不单射, 或表的上界又有回路), **没有写, 没有编译**. 所以停在这里, 写成条件. **这是未走通, 不是否定.**
>
> **有限测试 ([Accept](LevelFixAccept.lagda.md), 全部 `refl`).** 比较器 `dfO`, `dfL` 看种类, 闭包的共尾层, 第一支, 走 $c+k$, 不看界; `misQ` 看界.
>
> | 目标 $L$ in $\psi_0(\Omega_L)$ | 比较器, 深度, 宽度 | 结果 |
> |---|---|---|
> | $\Omega$; $\Omega+1$; $\Omega\cdot2$; $\Omega\cdot2+1$; $\Omega\cdot3$ | `dfO`, 14; 12; 12; 11; 11, 宽 3 | 一致 (`a-*`) |
> | $\Omega_2$, $\Omega_3$, $\Omega_\omega$ | `dfO`, 12, 3 | 一致 |
> | $\Omega_\omega+1$, $\Omega_2\cdot2$, $\Omega_2\cdot2+1$ | `dfO`, 11; 11; 10, 3 | 一致; 后两个在 `chain-stuck` 那一带, 这只说符号的形状 |
> | $\psi_1,\psi_2(\Omega_{\Omega_2})$ 读回 | `dfL`, 10, 3 | 一致 |
> | 对照 `ctl₁`, `ctl₂` | | 比较器分得开 |
> | 界对 `LadderNFTree`: $\Omega$ | `misQ`, 10, 3 | 一致 (`b-Ω`); 这个深度走到的分支不多 |
> | 界对 `LadderNFTree`: $\Omega+1$, $\Omega\cdot2$ | `misQ`, 10, 3 | **不一致**, 3 对 2 (`b-Ω+1`), 2 对 1 (`b-Ω2`); 宽 2 也不一致, 2 对 1 (`b-Ω+1₂`) |
>
> 盲区: `brsU` 只走字面的 $c+k$; 下界不是字面后继, `em`, `top` 时不走分支. $x_3$ 以上没有测: 没有闭项.
>
> **是否还有外部编号或逐阶段新类型.** 类型: 没有. `natF`, `ix`, `nodeC` 里的 $\mathbb N$ 是目标的编号, 与 [DomFold](DomFold.lagda.md) 的 `tn` 同一个来源 (`no-tn-ω⁺`), 不是定义域的编号. **`Un` 的证明目前逐类给 (`uip-nat`).**
>
> **受记号影响的形状.** 第一支与下界取 $\Omega_k$ (`cO`, $\gamma_0=\Omega_\mu$). 带链的闭包与 `ix`. 这些从 `DomFold` 继承. **树侧逼出的:** 字面第一位置守卫 (`no-WFˢ-Ω⁺`), `top` (极限层不写跨孩子的步进), `em` (`up` 不要函数外延). `Lgl` 与 `Legal` 的形状是证明要的. 不算树自足: `cO` 的选取没有树侧判据.
>
> **证书形状 (判断).** `GuardTight` 的 `Good-Ω₁` 走的是到 `OCF/Free` 的桥, 那棵树的界是 `⊑ᴵ`, 这里是字面第一位置, 判断要重写桥, 不是搬. `LadderNF` 靠 $\mathbb N$ 高度 (`Hi`, `tri`, `upd-lt`), 这里的自然数名字段可以对应, 非自然数名字没有对应物. 判断: 证书先要解决第 1, 3 个障碍.
>
> **壁垒 (判断, 没有形式对比).** `cmpD` 只比字面上界之下的第一位置, `<̂` 不含 `Raw zero` 的初始段 (第一位置之外的元不在其下), 所以 `barrier` 的前提不成立; `no-bra-cmp` 不碰: 没有比两个分支路径; `no-read`, `no-read-ᴵ` 不碰: 没有判决, 分支由守卫挡. `Ordᴵ` 没有进定义域 (`rd` 由不合法的 `b₀` 空满足), `no-topᴵ` 不适用. `Toy.loop`: `LF` 的 `lc` 不是可数层的构造子, 它的下标是结构更小的 `k` 算出来的类型. 我没有证明这组定义永不触犯壁垒.
>
> **审计.** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.GuardTight --only OCF.Align.DomFold --only OCF.Align.LevelFix OCF.Align.LevelFix`: 干净 (`LevelFixAccept` 按预期不干净). `depslice.py`: `Legal-Ω̂` 38, `Gd` 19, `Cf-toU` 128, `Tψ-Ωω` 358, `ψ₀Λ-if` 345, 记号块都是 0; 正对照 `LevelFixAccept:a-Ωω` 读记号 (LevelFixAccept:a-Ωω reached 425 | notation-module chunks 48 | token hits elsewhere 5). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 模块参数: `LevelFixBase`, `LevelFixTree` 的 `X` 是定义域; **`Un` 作函数参数, 是条件**, `x̂-if`, `ψ₀Λ-if` 依赖它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFix where

open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Lgl; Cp; cmpC)
open import OCF.Align.LevelFixVal using (up; Ω̂; tw; Λ; Legal; CP; Legal-Ω̂; Ω̂-CP; Legal-tw; Legal-Λ; Legal-ΩΛ; Legal-Ωω; Legal-ΩΩ₂; Legal-ΩΩ; Legal-add; branch; Ω₁+1; Ω₁·2; Ω₂; Ω₃; Ωω; ΩΩ₂; ΩΩ; ΩΩᴵ)
open import OCF.Align.LevelFixU using (𝕌; XF; toU; fromU; Un; uip-nat; Un-T; Un-Ωω; Cf-toU; cp⊴)
open import OCF.Align.LevelFixFold using (Tψ; feed; Ωfeed; x̂₀; x̂₁; x̂₂; x̂-if; ψ₀Λ-if; Tψ-Ωn; Tψ-Ωω; ψ₁θ)
open import OCF.Align.LevelFixNeg using (no-Lgl-Ωlim; no-cp-Ω3-Ω2)
```
