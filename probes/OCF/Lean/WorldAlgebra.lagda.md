# 世界搬运与前缀运算

这是 `WorldCompose` 的继续，不改变玩具树或旧结论。
先验证搬运保加法以及加法结合，结论是逐支互模拟，非命题相等，
不使用函数外延。全部搬运都携带字面的第一位置证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldAlgebra where

open import OCF.Lean.Fab6Base using (Cd; _⊲_; hsuc; ⊲ᴮ-tr)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldCompose

sym≈ : ∀ {B} {a b : W B} → a ≈ b → b ≈ a
sym≈ z≈ = z≈
sym≈ (s≈ p) = s≈ (sym≈ p)
sym≈ (l≈ p) = l≈ (λ n → sym≈ (p n))
sym≈ (n≈ p) = n≈ (λ e r → sym≈ (p e r))

trans≈ : ∀ {B} {a b c : W B} → a ≈ b → b ≈ c → a ≈ c
trans≈ z≈ z≈ = z≈
trans≈ (s≈ p) (s≈ q) = s≈ (trans≈ p q)
trans≈ (l≈ p) (l≈ q) = l≈ (λ n → trans≈ (p n) (q n))
trans≈ (n≈ p) (n≈ q) = n≈ (λ e r → trans≈ (p e r) (q e r))

lift-cong : ∀ {A B} (p : A ⊲ B) {a b} → a ≈ b → lift p a ≈ lift p b
lift-cong p z≈ = z≈
lift-cong p (s≈ q) = s≈ (lift-cong p q)
lift-cong p (l≈ q) = l≈ (λ n → lift-cong p (q n))
lift-cong p (n≈ q) = n≈ (λ e r → q e (⊲ᴮ-tr p r))

add-cong : ∀ {B} {a a′ b b′ : W B} → a ≈ a′ → b ≈ b′ → (a ⊕ b) ≈ (a′ ⊕ b′)
add-cong p z≈ = p
add-cong p (s≈ q) = s≈ (add-cong p q)
add-cong p (l≈ q) = l≈ (λ n → add-cong p (q n))
add-cong p (n≈ q) = n≈ (λ e r → add-cong (lift-cong (hsuc r) p) (q e r))

lift-add : ∀ {A B} (p : A ⊲ B) (a b : W A) →
  lift p (a ⊕ b) ≈ (lift p a ⊕ lift p b)
lift-add p a wz = refl≈ (lift p a)
lift-add p a (ws b) = s≈ (lift-add p a b)
lift-add p a (wl f) = l≈ (λ n → lift-add p a (f n))
lift-add p a (wn g) = n≈ (λ e r →
  add-cong (sym≈ (lift-compose p (hsuc r) a)) (refl≈ (g e (⊲ᴮ-tr p r))))

add-assoc : ∀ {B} (a b c : W B) → ((a ⊕ b) ⊕ c) ≈ (a ⊕ (b ⊕ c))
add-assoc a b wz = refl≈ (a ⊕ b)
add-assoc a b (ws c) = s≈ (add-assoc a b c)
add-assoc a b (wl f) = l≈ (λ n → add-assoc a b (f n))
add-assoc a b (wn g) = n≈ (λ e r → trans≈
  (add-cong (lift-add (hsuc r) a b) (refl≈ (g e r)))
  (add-assoc (lift (hsuc r) a) (lift (hsuc r) b) (g e r)))
```

翻译账：无新构造子与记号输入。定理由前缀进入分支的运算提出；
并未证明序数加法的值语义，也没有给出 Ω-节点的合法性。
