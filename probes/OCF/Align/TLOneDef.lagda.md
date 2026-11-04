# `tH` 实验 (一): 原则版的定义

> 入口 [TLOne](TLOne.lagda.md). **只有定义, 导入闭包不含记号.** 路线审查 `probes/Survey/RouteReview.md` §4.3 实验 1 的第一步. 原则: **凡折叠输出都可作下标, 凡下标都可作 Ω-极限的层.** 算子: ℕ-极限, 层 $k$ 的 Ω-极限, 回灌闭包. 只用现成的规则, 不新增构造子.
>
> **时间线 (写这个文件时读过什么).** 读了: `AGENTS.md`, `probes/README.md`, `RouteReview` §1, §2, §4.3, `TreeLangFeed`, `CrossMClosed`, `CrossMNode`, `CrossMInst`, `OCF/Free/Level`, `OCF/Free/Tree`, `OCF/Free/Force`, `LadderOrdTree`, `LadderOrdCert`, `LadderOrdClosed`, `LadderOrdNeg`, `LadderOrdPos` 开头, `LadderOrdGrow`, `CrossNextSum`, `CrossNext`, `ValueJudgeLadder` 前 300 行.
> **污染要如实说.** 任务要求里给了 $\psi_0(\Omega_{\Omega^2+1})$ 和 "要折叠 $\Omega_u$ 本身" 这句话; `RouteReview` §2, `CrossM`, `CrossNext` 的正文转述了 `fs-ψΩ1-1`, `fs-2` 的结论 (没读它们的定义); `CrossMTop` 的 `tH` 在写这个文件之前已读. 所以这里的 "原则版" 对 `tH` 的形状不是盲的, 对记号的定义和基本列的计算是没有看的: `CrossMAccept`, `CrossNextAccept`, `EBO` 都没有打开.

**每一步的理由.** 层号有两个槽: Ω-极限的层 $\alpha$ (`Ω̇ m α`) 和高度 (`Pos (cs M)`). 原则没有说进哪个槽, 两个都试.

| 名字 | 写法 | 理由 |
| --- | --- | --- |
| `Tᶠ` | `ψ̄ (Ω̇ (suc lv⊤))` | 任务说的字面写法: `OCF/Free` 的树, 层是 `suc lv⊤` |
| `Tᴬ` | `Tᵖ ωᶜ end (suc lv⊤)` | 同一件事在带高度的树上, $\alpha$ 槽 |
| `Tᴮ` | `Tᵖ (cs ⌈lv⊤⌉) end zero` (`Tᴮ′ lv⊤`) | 高度槽: 下标进码, 比它高一格 |
| `Tᶜ` | `νT 𝒯 (cs ⌈lv⊤⌉)` (`Tᶜ′ lv⊤`) | 再取闭包: 已有的节点 `𝒯` 换起点 |
| `Tᵏ′ lv⊤ k` | 上面的迭代, `Tᵏ′ lv⊤ 0 = Tᶜ` | 把上面两步迭代 |
| `T̃ᴬ` | $\alpha\mapsto$ `Tᵖ ωᶜ end (suc α)` 的回灌闭包, 从 `T⊤` 起 | 闭包不限于高度, 走 `Sum` |
| `T̃ᴰ` | $\eta\mapsto$ `νT 𝒯 (cs ⌈η⌉)` 的回灌闭包, 从 `T⊤` 起 | "下一个闭包点" 这个算子的闭包 |

全部带证书, 因为都是已有闭包定理的实例. 没有写新的 `Goodᴺ` 证明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOneDef where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Free.Tree using (Ω̇; ψ̄)
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; ωᶜ)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ)
open import OCF.Align.CrossMNode using (νZ; Gν; νT; νHS; νlv)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMClosed using (T⊤; HS⊤; lv⊤)
open import OCF.Align.CrossNextSum using (module Sum)
```

## §1 字面写法

```agda
-- OCF/Free 的树, 层是 suc lv⊤
Gᶠ : Goodᴺ (toZ (ψ̄ (Ω̇ (suc lv⊤)) ev₀ zero))
Gᶠ = GᴺΩ̇ (suc lv⊤) ev₀ zero

Tᶠ : Ordᶜ zero
Tᶠ = forceᴺ _ Gᶠ

-- 带高度的树, α 槽, 对任何世界任何位置
Tᴬ′ : ∀ M → Pos (cs M) → Ordᶜ zero
Tᴬ′ M p = forceᴺ _ (Gᵖ M p (suc lv⊤))

Tᴬ : Ordᶜ zero
Tᴬ = Tᴬ′ ωᶜ end
```

## §2 高度槽, 闭包

对下标 $x$ 参数化. 闭项是 $x=$ `lv⊤` 的实例. 这不只是风格: 检查器比较闭合世界上 `forceᴺ` 的两个不同写法要化简证书 ([CrossMInst](CrossMInst.lagda.md) 的提示), 所以定理都对变量 $x$ 证, 再代入.

```agda
Tᴮ′ : Ordᴵ → Ordᶜ zero
Tᴮ′ x = forceᴺ _ (Gᵖ (cs ⌈ x ⌉) end zero)

Tᶜ′ : Ordᴵ → Ordᶜ zero
Tᶜ′ x = νT 𝒯 (cs ⌈ x ⌉)

lvᶜ′ : Ordᴵ → Ordᴵ
lvᶜ′ x = νlv 𝒯 (cs ⌈ x ⌉)

Tᴮ Tᶜ : Ordᶜ zero
Tᴮ = Tᴮ′ lv⊤
Tᶜ = Tᶜ′ lv⊤

lvᶜ : Ordᴵ
lvᶜ = lvᶜ′ lv⊤

-- 迭代: 每一步把上一个闭包点喂给高度, 再取闭包. 对起点 x 参数化
itᶜ : Ordᴵ → ℕ → Ordᴵ
itᶜ x zero    = x
itᶜ x (suc k) = lvᶜ′ (itᶜ x k)

-- Tᵏ′ lv⊤ 0 = Tᶜ, 第 k 个之后的闭包点
Tᵏ′ : Ordᴵ → ℕ → Ordᶜ zero
Tᵏ′ x k = Tᶜ′ (itᶜ x k)
```

## §3 回灌闭包不限于高度

`Sum` 对任何带证书的分支族给闭包点, 不要单调性, 代价是分支带前缀. 这是 `TreeLangFeed` 的 `Clo` 的一个证书实例: 链 $y_0=$ `T⊤`, $y_{k+1}=(y_k+1)\oplus b(\mathrm{lv}\,y_k)$.

```agda
bᴬ : Ordᴵ → Z
bᴬ η = toZ (Tᵖ ωᶜ end (suc η) ev₀ zero)

module ClᴬM = Sum bᴬ (λ η → Gᵖ ωᶜ end (suc η)) (Gν 𝒯 ωᶜ)

T̃ᴬ : Ordᶜ zero
T̃ᴬ = ClᴬM.T̃

bᴰ : Ordᴵ → Z
bᴰ η = νZ 𝒯 (cs ⌈ η ⌉)

module ClᴰM = Sum bᴰ (λ η → Gν 𝒯 (cs ⌈ η ⌉)) (Gν 𝒯 ωᶜ)

T̃ᴰ : Ordᶜ zero
T̃ᴰ = ClᴰM.T̃

fghᶠ fghᴬ fghᴮ fghᶜ fgh̃ᴬ fgh̃ᴰ : ℕ → ℕ
fghᶠ = FGH Tᶠ
fghᴬ = FGH Tᴬ
fghᴮ = FGH Tᴮ
fghᶜ = FGH Tᶜ
fgh̃ᴬ = FGH T̃ᴬ
fgh̃ᴰ = FGH T̃ᴰ
```
