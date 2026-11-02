# 层号判决的范数模: 项的大小不超过走步长度的语法核心 (验收)

> **验收节.** `sz-step`: 共尾度 ω 的**任意**项 (不要求标准形) 走一步 `t ↦ t[1]`, 大小至多减 1. 这是范数能从树读出的全部原因: 分支 1 不丢信息. 分支 0 没有这个性质 (`ψ_u(b+1)[0] = 0`). 结论在 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusSize where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc; +-comm; +-identityʳ; +-suc; +-monoˡ-≤; +-monoʳ-≤; +-cancelʳ-≤; +-cancelˡ-≤; m≤m+n; m≤n+m; ≤-reflexive; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.Standard using (sz; szᴾ)
open import OCF.Align.Bachmann using (fs-gt)
open import OCF.Align.Correspond using (cof-ne; fs-rep; fs-ω)
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; cof; cofA; cofψ0; cofψ₊; pred; pred-suc; fsn; fsT; fsT0; fsT₊; fsTc; γT; Ωt; sucT; cmpᵀ; lt; eq; gt; Cmp) renaming (ψ to ψᵗ)

sz-sucT : ∀ a → sz (sucT a) ≡ suc (sz a)
sz-sucT [] = refl
sz-sucT (x ∷ xs) = trans (cong (szᴾ x +_) (sz-sucT xs)) (+-suc (szᴾ x) (sz xs))

sz-pred : ∀ a → cof a ≡ c1 → sz a ≡ suc (sz (pred a))
sz-pred a e = trans (cong sz (sym (pred-suc a e))) (sz-sucT (pred a))
```

## §1 Ω-基本列的大小

`szL`: 共尾度 Ω_{ν+1} 的项至少有叶子那么大. `szT`: 把叶子换成 η, 大小的变化恰好由叶子的大小 `2 + sz ν` 控制.

```agda
szL : ∀ b {ν} → cof b ≡ cΩ ν → suc (suc (sz ν)) ≤ sz b
szLA : ∀ u b k → cof b ≡ k → ∀ {ν} → cofA u k ≡ cΩ ν → suc (suc (sz ν)) ≤ suc (sz u + sz b) + 0
szLC : ∀ u b μ m → cof b ≡ cΩ μ → ∀ {ν} → cofψ₊ u μ m ≡ cΩ ν → suc (suc (sz ν)) ≤ suc (sz u + sz b) + 0
szL0 : ∀ u k → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν → suc (suc (sz ν)) ≤ suc (sz u + 0) + 0

szL [] ()
szL (ψᵗ [] [] ∷ []) ()
szL (ψᵗ u (y ∷ ys) ∷ []) e = szLA u (y ∷ ys) (cof (y ∷ ys)) refl e
szL (ψᵗ (w ∷ ws) [] ∷ []) e = szL0 (w ∷ ws) (cof (w ∷ ws)) refl e
szL (x ∷ y ∷ ys) e = ≤-trans (szL (y ∷ ys) e) (m≤n+m _ (szᴾ x))

szLA u b c0 p ()
szLA u b c1 p ()
szLA u b cω p ()
szLA u b (cΩ μ) p e = szLC u b μ (cmpᵀ (sucT μ) u) p e
szLC u b μ lt p refl = ≤-trans (szL b p) (≤-trans (m≤n+m _ (sz u)) (≤-trans (n≤1+n _) (m≤m+n _ 0)))
szLC u b μ eq p refl = ≤-trans (szL b p) (≤-trans (m≤n+m _ (sz u)) (≤-trans (n≤1+n _) (m≤m+n _ 0)))
szLC u b μ gt p ()
szL0 u c0 p ()
szL0 u c1 p refl = subst (λ z → suc z ≤ suc (sz u + 0) + 0) (sz-pred u p)
  (≤-trans (m≤m+n _ 0) (≤-reflexive (cong suc (+-comm (sz u) 0) ◂ cong (λ z → suc z) (sym (+-comm (sz u) 0)) ◂ sym (+-comm (suc (sz u + 0)) 0) ◂ refl)))
  where
    _◂_ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    _◂_ = trans
    infixr 5 _◂_
szL0 u cω p ()
szL0 u (cΩ μ) p refl = ≤-trans (szL u p) (≤-trans (m≤m+n _ 0) (≤-trans (n≤1+n _) (m≤m+n _ 0)))
```

```agda
private
  canc : ∀ k {a b} → a + k ≤ b + k → a ≤ b
  canc zero {a} {b} p = subst₂′ (+-identityʳ a) (+-identityʳ b) p
    where
      subst₂′ : ∀ {x x′ y y′ : ℕ} → x ≡ x′ → y ≡ y′ → x ≤ y → x′ ≤ y′
      subst₂′ refl refl q = q
  canc (suc k) {a} {b} p = canc k (pre (subst (λ z → suc (a + k) ≤ z) (+-suc b k) (subst (_≤ (b + suc k)) (+-suc a k) p)))
    where
      pre : ∀ {x y} → suc x ≤ suc y → x ≤ y
      pre (s≤s q) = q

  h-sum : ∀ a B e F L → B + e ≤ F + L → (a + B) + e ≤ (a + F) + L
  h-sum a B e F L p rewrite +-assoc a B e | +-assoc a F L = +-monoʳ-≤ a p

  h-psi : ∀ s B e F L → B + e ≤ F + L → (suc (s + B) + 0) + e ≤ (suc (s + F) + 0) + L
  h-psi s B e F L p rewrite +-identityʳ (s + B) | +-identityʳ (s + F) = s≤s (h-sum s B e F L p)

  h-sing : ∀ B e F L → B + e ≤ F + L → (suc (B + 0) + 0) + e ≤ (suc (F + 0) + 0) + L
  h-sing B e F L p rewrite +-identityʳ B | +-identityʳ B | +-identityʳ F | +-identityʳ F = s≤s p

  h-leaf : ∀ su sν e → su ≡ suc sν → (suc (su + 0) + 0) + e ≤ e + suc (suc sν)
  h-leaf .(suc sν) sν e refl rewrite +-identityʳ sν | +-identityʳ sν | +-comm e (suc (suc sν)) = ≤-refl

szT  : ∀ b {ν η} → cof b ≡ cΩ ν → sz b + sz η ≤ sz (fsT b η) + suc (suc (sz ν))
szTA : ∀ u b k {η} → cof b ≡ k → ∀ {ν} → cofA u k ≡ cΩ ν →
       (suc (sz u + sz b) + 0) + sz η ≤ sz (fsT₊ u b k η) + suc (suc (sz ν))
szTC : ∀ u b μ m {η} → cof b ≡ cΩ μ → ∀ {ν} → cofψ₊ u μ m ≡ cΩ ν →
       (suc (sz u + sz b) + 0) + sz η ≤ sz (fsTc u b μ m η) + suc (suc (sz ν))
szT0 : ∀ u k {η} → cof u ≡ k → ∀ {ν} → cofψ0 u k ≡ cΩ ν →
       (suc (sz u + 0) + 0) + sz η ≤ sz (fsT0 u k η) + suc (suc (sz ν))

szT [] ()
szT (ψᵗ [] [] ∷ []) ()
szT (ψᵗ u (y ∷ ys) ∷ []) e = szTA u (y ∷ ys) (cof (y ∷ ys)) refl e
szT (ψᵗ (w ∷ ws) [] ∷ []) e = szT0 (w ∷ ws) (cof (w ∷ ws)) refl e
szT (x ∷ y ∷ ys) {ν} {η} e = h-sum (szᴾ x) (sz (y ∷ ys)) (sz η) (sz (fsT (y ∷ ys) η)) _ (szT (y ∷ ys) e)

szTA u b c0 p ()
szTA u b c1 p ()
szTA u b cω p ()
szTA u b (cΩ μ) p e = szTC u b μ (cmpᵀ (sucT μ) u) p e
szTC u b μ lt {η} p refl = h-psi (sz u) (sz b) (sz η) (sz (fsT b η)) _ (szT b p)
szTC u b μ eq {η} p refl = h-psi (sz u) (sz b) (sz η) (sz (fsT b η)) _ (szT b p)
szTC u b μ gt p ()
szT0 u c0 p ()
szT0 u c1 {η} p refl = h-leaf (sz u) (sz (pred u)) (sz η) (sz-pred u p)
szT0 u cω p ()
szT0 u (cΩ μ) {η} p refl = h-sing (sz u) (sz η) (sz (fsT u η)) _ (szT u p)
```

## §2 规则 6: 大小不减

`γ₁ = ψ_ν(b[Ω_ν])` 至少和叶子 `Ω_{ν+1}` 一样大, 所以 `b[γ₁]` 不小于 `b`. 这里用 γ-链的第 1 项, 所以是 `n = 1` 的性质, `n = 0` 时 `γ₀ = Ω_ν` 比叶子小 1.

```agda
private
  no+ : ∀ b x → b + suc x ≤ b → ⊥
  no+ zero x ()
  no+ (suc b) x (s≤s p) = no+ b x p

  arith : ∀ s b F₀ F₁ → b + (suc (s + 0) + 0) ≤ F₀ + suc (suc s) → b + (suc (s + F₀) + 0) ≤ F₁ + suc (suc s) →
          suc (suc s) ≤ b → b ≤ F₁
  arith s b zero F₁ a _ c = ⊥-elim (no+ b _ (≤-trans a c))
  arith s b (suc f) F₁ _ d _ = canc (suc (suc s)) (≤-trans (+-monoʳ-≤ b big) d)
    where
      big : suc (suc s) ≤ suc (s + suc f) + 0
      big rewrite +-identityʳ (s + suc f) | +-suc s f = s≤s (s≤s (m≤m+n s f))

sz-γ : ∀ b {ν} → cof b ≡ cΩ ν → sz b ≤ sz (fsT b (γT b ν 1))
sz-γ b {ν} e = arith (sz ν) (sz b) (sz (fsT b (Ωt ν))) (sz (fsT b (γT b ν 1)))
                     (szT b e) (szT b e) (szL b e)
```

## §3 `sz-step`

```agda
stT : ∀ t → cof t ≡ cω → sz t ≤ suc (sz (fsn t 1))
stA : ∀ u b k → cof b ≡ k → cofA u k ≡ cω → (b ≡ [] → ⊥) →
      sz (ψᵗ u b ∷ []) ≤ suc (sz (E.fsn (ψᵗ u b ∷ []) 1))
st0 : ∀ u k → cof u ≡ k → cofψ0 u k ≡ cω → (u ≡ [] → ⊥) →
      sz (ψᵗ u [] ∷ []) ≤ suc (sz (E.fsn (ψᵗ u [] ∷ []) 1))

stT [] ()
stT (ψᵗ [] [] ∷ []) ()
stT (ψᵗ u (y ∷ ys) ∷ []) e = stA u (y ∷ ys) (cof (y ∷ ys)) refl e (λ ())
stT (ψᵗ (w ∷ ws) [] ∷ []) e = st0 (w ∷ ws) (cof (w ∷ ws)) refl e (λ ())
stT (x ∷ y ∷ ys) e = subst (szᴾ x + sz (y ∷ ys) ≤_) (+-suc (szᴾ x) (sz (fsn (y ∷ ys) 1))) (+-monoʳ-≤ (szᴾ x) (stT (y ∷ ys) e))

private
  ψ-mono : ∀ s B F → B ≤ suc F → suc (s + B) + 0 ≤ suc (suc (s + F) + 0)
  ψ-mono s B F p rewrite +-identityʳ (s + B) | +-identityʳ (s + F) | sym (+-suc s F) = s≤s (+-monoʳ-≤ s p)

  leaf′ : ∀ B F → B ≤ suc F → suc (B + 0) + 0 ≤ suc (suc (F + 0) + 0)
  leaf′ B F p rewrite +-identityʳ B | +-identityʳ B | +-identityʳ F | +-identityʳ F = s≤s p

stA u [] k ke e nz = ⊥-elim (nz refl)
stA u (y ∷ ys) c0 ke e _ = ⊥-elim (cof-ne y ys ke)
stA u (y ∷ ys) c1 ke e _ = subst (λ z → sz (ψᵗ u (y ∷ ys) ∷ []) ≤ suc (sz z)) (sym (fs-rep u y ys ke 1))
  (subst (λ z → suc (sz u + z) + 0 ≤ suc (suc (sz u + sz (pred (y ∷ ys))) + 0)) (sym (sz-pred (y ∷ ys) ke))
    (ψ-mono (sz u) (suc (sz (pred (y ∷ ys)))) (sz (pred (y ∷ ys))) ≤-refl))
stA u (y ∷ ys) cω ke e _ = subst (λ z → sz (ψᵗ u (y ∷ ys) ∷ []) ≤ suc (sz z)) (sym (fs-ω u y ys ke 1))
  (ψ-mono (sz u) (sz (y ∷ ys)) (sz (fsn (y ∷ ys) 1)) (stT (y ∷ ys) ke))
stA u (y ∷ ys) (cΩ ν) ke e _ = go (cmpᵀ (sucT ν) u) refl e
  where
    go : ∀ m → cmpᵀ (sucT ν) u ≡ m → cofψ₊ u ν m ≡ cω → sz (ψᵗ u (y ∷ ys) ∷ []) ≤ suc (sz (fsn (ψᵗ u (y ∷ ys) ∷ []) 1))
    go lt em ()
    go eq em ()
    go gt em _ = subst (λ z → sz (ψᵗ u (y ∷ ys) ∷ []) ≤ suc (sz z)) (sym (fs-gt u y ys ν ke em 1))
      (ψ-mono (sz u) (sz (y ∷ ys)) (sz (fsT (y ∷ ys) (γT (y ∷ ys) ν 1))) (≤-trans (sz-γ (y ∷ ys) ke) (n≤1+n _)))

st0 [] k ke e nz = ⊥-elim (nz refl)
st0 (w ∷ ws) c0 ke () _
st0 (w ∷ ws) c1 ke () _
st0 (w ∷ ws) cω ke e _ = subst (λ z → sz (ψᵗ (w ∷ ws) [] ∷ []) ≤ suc (sz z)) (sym (E.fsn0-eq w ws 1 ke))
  (leaf′ (sz (w ∷ ws)) (sz (fsn (w ∷ ws) 1)) (stT (w ∷ ws) ke))
st0 (w ∷ ws) (cΩ μ) ke () _

sz-step : ∀ t → cof t ≡ cω → sz t ≤ suc (sz (fsn t 1))
sz-step = stT
```
