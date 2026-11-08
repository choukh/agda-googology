# 世界索引树的搬运组合

独立接手的第一项摆脱侧实验。沿用 `NegFab6Idx` 的玩具树，
检验把世界放进类型后是否还必须使用函数外延才能组合搬运。
本文件只证明结构互模拟，不声称序数值验收、合法性或 ψ₀Λ 闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldCompose where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.Fab6Base using
  (Cd; _⊲_; hself; hsuc; hlim; hLim; hEx; ⊲ᴮ-tr)
open import OCF.Lean.NegFab6Idx using (W; wz; ws; wl; wn; lift)

assoc : ∀ {a b c d : Cd} (p : a ⊲ b) (q : b ⊲ c) (r : c ⊲ d) →
  ⊲ᴮ-tr (⊲ᴮ-tr p q) r ≡ ⊲ᴮ-tr p (⊲ᴮ-tr q r)
assoc p q hself = refl
assoc p q (hsuc r) = cong hsuc (assoc p q r)
assoc p q (hlim n r) = cong (hlim n) (assoc p q r)

-- 固定世界内逐支比较；没有比较裸下标的律。
data _≈_ {B : Cd} : W B → W B → Set where
  z≈ : wz ≈ wz
  s≈ : ∀ {a b} → a ≈ b → ws a ≈ ws b
  l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → wl f ≈ wl g
  n≈ : ∀ {f g} → (∀ e p → f e p ≈ g e p) → wn f ≈ wn g

refl≈ : ∀ {B} (a : W B) → a ≈ a
refl≈ wz = z≈
refl≈ (ws a) = s≈ (refl≈ a)
refl≈ (wl f) = l≈ (λ n → refl≈ (f n))
refl≈ (wn g) = n≈ (λ e p → refl≈ (g e p))

lift-compose : ∀ {A B C} (p : A ⊲ B) (q : B ⊲ C) (a : W A) →
  lift q (lift p a) ≈ lift (⊲ᴮ-tr p q) a
lift-compose p q wz = z≈
lift-compose p q (ws a) = s≈ (lift-compose p q a)
lift-compose p q (wl f) = l≈ (λ n → lift-compose p q (f n))
lift-compose p q (wn g) = n≈ branch
  where
  branch : ∀ e r → g e (⊲ᴮ-tr p (⊲ᴮ-tr q r)) ≈ g e (⊲ᴮ-tr (⊲ᴮ-tr p q) r)
  branch e r rewrite assoc p q r = refl≈ (g e (⊲ᴮ-tr p (⊲ᴮ-tr q r)))
```

翻译账：没有新增树构造子；组合律由世界搬运的操作要求提出，
没有使用记号的基本列。这里只覆盖一个种类的玩具；推广到塔、
给内部 View、合法闭项及值比较仍待完成。不能据此宣称摆脱了路径证据：
证据仍在分支参数内。
