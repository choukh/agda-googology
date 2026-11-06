# 改 "在上" 的折法, 否定一路 (零): 值关系的小引理

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延. 只导入 [CRwBase](CRwBase.lagda.md) 与接口 [Fold1If](Fold1If.lagda.md) 的 §1, §2 (塔, `mul`, 不带世界的值关系 `_≤ᵛ_`).
>
> 接口只给了值关系的规则, 没有给自反, 传递与 `⊞` 的单调. 本篇补上 (对一切种类结构), 供后面各篇用. 传递的证明与 `Fab5ValRel.≤-trans` 同形 (去掉世界与坐标条件).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1Base where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
```

```agda
module _ {S : KS} where
  ≤ᵛ-refl : (a : HB S) → a ≤ᵛ a
  ≤ᵛ-refl hz = z≤
  ≤ᵛ-refl (hs a) = s≤s (≤ᵛ-refl a)
  ≤ᵛ-refl (hl f) = l≤ (λ n → ≤l n (≤ᵛ-refl (f n)))
  ≤ᵛ-refl (hΩ κ g) = Ω≤Ω (λ c → ≤ᵛ-refl (g c))

  ≤ᵛ-trans : {a b c : HB S} → a ≤ᵛ b → b ≤ᵛ c → a ≤ᵛ c
  ≤ᵛ-trans z≤ q = z≤
  ≤ᵛ-trans (l≤ h) q = l≤ (λ n → ≤ᵛ-trans (h n) q)
  ≤ᵛ-trans p (≤l n q) = ≤l n (≤ᵛ-trans p q)
  ≤ᵛ-trans p (≤Ω c q) = ≤Ω c (≤ᵛ-trans p q)
  ≤ᵛ-trans p (≤s q) = ≤s (≤ᵛ-trans p q)
  ≤ᵛ-trans (s≤s p) (s≤s q) = s≤s (≤ᵛ-trans p q)
  ≤ᵛ-trans (≤s p) (s≤s q) = ≤s (≤ᵛ-trans p q)
  ≤ᵛ-trans (≤l n p) (l≤ h) = ≤ᵛ-trans p (h n)
  ≤ᵛ-trans (≤Ω c p) (Ω≤Ω H) = ≤Ω c (≤ᵛ-trans p (H c))
  ≤ᵛ-trans (Ω≤Ω H) (Ω≤Ω H′) = Ω≤Ω (λ c → ≤ᵛ-trans (H c) (H′ c))

  ≤⊞ : (a b : HB S) → a ≤ᵛ a ⊞ b
  ≤⊞ a hz = ≤ᵛ-refl a
  ≤⊞ a (hs b) = ≤s (≤⊞ a b)
  ≤⊞ a (hl f) = ≤l 0 (≤⊞ a (f 0))
  ≤⊞ a (hΩ κ g) = ≤Ω (bot S κ) (≤⊞ a (g (bot S κ)))

  ⊞≤ˡ : {a b : HB S} (x : HB S) → a ≤ᵛ b → a ⊞ x ≤ᵛ b ⊞ x
  ⊞≤ˡ hz p = p
  ⊞≤ˡ (hs x) p = s≤s (⊞≤ˡ x p)
  ⊞≤ˡ (hl f) p = l≤ (λ n → ≤l n (⊞≤ˡ (f n) p))
  ⊞≤ˡ (hΩ κ g) p = Ω≤Ω (λ c → ⊞≤ˡ (g c) p)

  ⊞≤ʳ : (a : HB S) {x y : HB S} → x ≤ᵛ y → a ⊞ x ≤ᵛ a ⊞ y
  ⊞≤ʳ a (z≤ {b = y}) = ≤⊞ a y
  ⊞≤ʳ a (s≤s p) = s≤s (⊞≤ʳ a p)
  ⊞≤ʳ a (≤s p) = ≤s (⊞≤ʳ a p)
  ⊞≤ʳ a (l≤ h) = l≤ (λ n → ⊞≤ʳ a (h n))
  ⊞≤ʳ a (≤l n p) = ≤l n (⊞≤ʳ a p)
  ⊞≤ʳ a (≤Ω c p) = ≤Ω c (⊞≤ʳ a p)
  ⊞≤ʳ a (Ω≤Ω H) = Ω≤Ω (λ c → ⊞≤ʳ a (H c))

  mul≤ : {x y : HB S} → x ≤ᵛ y → ∀ n → mul x n ≤ᵛ mul y n
  mul≤ p zero = p
  mul≤ {x} {y} p (suc n) = ≤ᵛ-trans (⊞≤ˡ x (mul≤ p n)) (⊞≤ʳ (mul y n) p)
```

## 结论 (按档)

- **[定理]** `≤ᵛ-refl`, `≤ᵛ-trans`, `≤⊞`, `⊞≤ˡ`, `⊞≤ʳ`, `mul≤` (对一切种类结构).
