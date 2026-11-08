# 保留真实旧 Ω 的回灌闭项严格超过前缀地板

对象是 BoundedFoldClosed.output，固定前缀 a=flL P 每轮进入回灌。
证明涵盖 a 的 Ω 分支，不把它替换为纯可数样本；目标仍为 P 层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFoldValueFeedback where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.BoundedFoldClosed using (a; act; next; output)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

open Ops (T hz)

add-mono : ∀ {S} {a b c d : HB S} → a ≤ᵛ b → c ≤ᵛ d → (a ⊞ c) ≤ᵛ (b ⊞ d)
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)

positive : ∀ (c : HB (T hz)) → hs hz ≤ᵛ act c
positive hz = s≤s z≤
positive (hs c) = ≤l 0 (positive c)
positive (hl f) = ≤l 0 (positive (f 0))
positive (hΩ κ g) = ≤Ω (bot (T hz) κ) (positive (g (bot (T hz) κ)))

inflate : ∀ (c : HB (T hz)) → c ≤ᵛ act c
inflate hz = z≤
inflate (hs c) = ≤l 1 (add-mono (inflate c) (positive c))
inflate (hl f) = l≤ (λ n → ≤l n (inflate (f n)))
inflate (hΩ κ g) = Ω≤Ω (λ e → inflate (g e))

-- 所有实际反馈项都覆盖原前缀，包括Ω种类。
floor≤next : ∀ c → a ≤ᵛ next c
floor≤next c = ≤-trans (≤⊞ a c) (inflate (a ⊞ c))

partial-floor : ∀ n → partial (λ _ → a) n ≤ᵛ partial (λ j → next (chain next j)) n
partial-floor zero = floor≤next (chain next zero)
partial-floor (suc n) = add-mono (partial-floor n) (floor≤next (chain next (suc n)))

repeat-floor≤output : repeat a ≤ᵛ output
repeat-floor≤output = l≤ (λ n → ≤l n (partial-floor n))

-- 实际第零输出是repeat(act a)，其第1项已有a+1的下界。
strict-floor≤output : hs a ≤ᵛ output
strict-floor≤output = ≤l 0 (≤l 1 (add-mono (inflate a) (positive a)))

output-not≤floor : output ≤ᵛ a → ⊥
output-not≤floor p = ¬s≤ᵛ a (≤-trans strict-floor≤output p)
```

这给真实合法闭项的无条件严格值下界，排除其值不高于原前缀地板。
它不把输出读成某个 ψ₀ 值：尚未把 P 层输出折到可数层。
也不证明一般 Safe 输入上的折叠同余，更不把静态 mixed≈θω 自动送过折叠。
本例源高度为后继，尚未覆盖源高度本身含 Ω 的全混合输入。
