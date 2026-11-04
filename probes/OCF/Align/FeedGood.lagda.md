# `GoodFeed`: 按现在的形状是假的; 链的第二项无条件; 第三项卡在闭包以上 (判决: PARTIAL)

> 底座 [FeedGoodRel](FeedGoodRel.lagda.md), [FeedGoodFirst](FeedGoodFirst.lagda.md), [FeedGoodTc](FeedGoodTc.lagda.md), [FeedGoodNeg](FeedGoodNeg.lagda.md). 验收 [FeedGoodAccept](FeedGoodAccept.lagda.md). 接 [GuardTightUp](GuardTightUp.lagda.md), [GuardReadRd](GuardReadRd.lagda.md), [EBOTopRaw](EBOTopRaw.lagda.md). 定义与定理文件的导入闭包干净, 记号只在验收.
>
> **判决: PARTIAL. `Diag.TΩ₂` 的条件没有去掉, 没有无参数的 $\psi_0(\Omega_{\Omega_2})$ 闭项.**
>
> - **`no-GoodFeed : GoodFeed → ⊥` (编译, 无条件).** `cfF` 对一切 `GL`, 而 `tcG` 可以读分支的证明. 只杀 "对一切 `GL`", 不杀链.
> - **`no-≈₁ : Lv₅ ≈ feedL u₀ → ⊥` (编译).** 这个中间目标写错了: 目标穿过分支 2, 界是 2. 正确的是 `feed≈ : feedL u₀ ≈ Lv₅²`, `Lv₅² = lc 2 (F 1) (λ η e → F η)` (编译, 无条件).
> - **`Cf-u₁ : Cfˢ (feedL u₀)` (编译, 无条件).** 第二项是好层号, 是 `Fold`, `rbO` 算出来的那一棵, 不是另写的 `Lv₅`. `Tc-u₁ : Tc (feedL u₀)`: 紧读法, 由 `Tc-Lv₅` 搬来. `u₁`, `u₁ᵗ : GL`. `T₁`, `T₁ᵗ`: $\psi_0(\Omega_{u_1})$ 的闭项, 无模块参数.
> - **这些都是层号合法 (`WFˢ`), 不是 `Goodᴺ`/`HS`.** `T₁ᵗ` 上没有 `Goodᴺ`. 比 `LevelKTower` 的 `Cert∀` (给 `WFᴬ`) 没有多出 ψ₀ 输出的结论.
> - **`FeedChain` (条件, 没有证):** 只沿链, 没有被 `no-GoodFeed` 杀掉. `TΩ₂ᶜ`: 定义对 $n$ 不分情况, 以它为参数.
>
> **恒等读法不是 "暂时可用的": 判断.** `⊴-cross`, `cross₃` (编译): 界不同的两份闭包不是同一个键, $\trianglelefteq$ 把分支里的点搬过去只能走第一支. 测试 `c-sib-id`, `c-sib-ti`: $\psi_1(\Omega_{\Omega+1})$ 的读回里, `dir` 要搬运的两份树, 恒等读法界 2 对 3, 紧读法到深度 7 一致. `b-id*`, `b-ti*`: 第 5 站 `Lv₅` 上恒等读法界 $=\tau$ ($\tau=2,3,5$), `Tc-Lv₅` 界 $=1$. `c-u₁`, `c-T₁`, `c-T₁ᵗ`, `c-u₂ⁱ`, `c-u₂ᵗ`: 对 EBO 比种类, 深度 5–8, 宽度 2, 带对照; 种类检验不看界. 所以判断: 恒等读法下 `cfF` 在 $u_2$ 处不成立. **没有证成定理:** 差一步, 要证 $k$ 不在 $R$ 的第一支之下, 且 `dir` 的目标是一个极限, 对所有项都要论证. 恒等读法给的 `u₁`, `T₁` 是闭项, 正确性没有保证.
>
> **第一个障碍: `Cfˢ (F⁺ (suc Ω₁) tc)`, 紧的 `tc`, 即 $\psi_1(\Omega_{\Omega+1})$.** 这是 $u_2$ 之前最小的未知站. `R-ψ` 的对面是 `Ordᶜ`, 下标只有 `Ordᴵ`, $\Omega_1+1$ 不在其中, 所以互模拟到不了, 闭包以上要一条新的闭包定理. 这与 `Goodᴺ` 卡在 $\psi_0(\Omega_{\Omega+1})$ 是同一处, 只是目标是 1, 且要的是带转移的 `⊴`. 判断, 约 2000 行起, 没有写. `Tc (feedL u)` 对一般的 $u$ 也没有: [GuardReadRd](GuardReadRd.lagda.md) 的切口写在 `Ordᶜ` 上, `FeedGoodTc` 只因 `feed≈` 才搬得过来.
>
> **与 `Family` 的关系.** `Family` 说 $\forall n.\ \mathrm{HS}(\psi_0(\Omega_{L_n}))$, 世界是 `Ordᴸ`, 带判决 `S`. `must 1 m` 说它蕴含目标 1 的链 `chk 1 m` 上每一点给出 `HS`: 这条链与 $u_m$ 同形 (判断, 没有形式的桥, 两个世界不同). 这里的结果**不是 `Family` 的实例**: `Family` 要 `HS`, 这里 $m=0,1$ 只有层号合法. `HS` 的对应物 `Goodᴺ` 只到 $u_0$ (`Good-Ω₁`, 已有), 类比 $x_2$. 没有增加任何一项. 方向也对: `Family` 蕴含这条链上的 `HS`, 这里连 `HS` 需要的层号也只走到 $u_1$.
>
> **读了记号的 (如实).** 定义与定理没有读 (导入闭包干净). 第一个障碍的定位与 `c-sib*` 的路径是看树得到的, 没有看记号. `u₀`, `u_{n+1}=ψ₁(Ω_{u_n})` 这条链的形状, `∅ 2` 的路径来自 EBO 的基本列 (`GuardTightUp` 已如实写). 这不算树自足.
>
> **已排除的确认.** `Diag` 只用 `Dom₀` 上的树, `no-WFˢ-Ω⁺` 不直接挡这条, 这里确实没用到 `𝔻₁`. 没有带高度或逐层输入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FeedGood where

open import OCF.Align.FeedGoodNeg using (no-≈₁; no-cfF; no-GoodFeed; ⊴-cross; cross₃)
open import OCF.Align.FeedGoodFirst using (R-ψ; ψ≅ψ¹; rb₁-rel; WF≈; Cf≈; lc-good; Lv₅²; feed≈; Cf-u₁; u₁; T₁; FeedChain; TΩ₂ᶜ; prefix₁)
open import OCF.Align.FeedGoodTc using (Tc-≈; rd²; Tc-u₁; u₁ᵗ; T₁ᵗ)
```
