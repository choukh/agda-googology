# 终局 (六): 塔的头两项无条件 `HS`, 对一切 `S`

> 不含记号. 结论写在 [EBOTop](EBOTop.lagda.md). $x_0,x_1$ 只用第 0, 1 层, `S` 不被问. 这里把它们连到 [Uniform](Uniform.lagda.md) 的定理: 两边的折叠都归到 `O₀` 上同一个函数 `P₀`. $x_2=\psi_0(\Omega_\Omega)$ 在 `Ordᴵ` 世界是定理 (`EBOTopLow`), 因为那里的层号带证据; 裸层号上它走到下标 $\omega\cdot2+2$ (`reach-x₂`), 那里对变量 `S` 的 `diff 11 3` 不归约 (探针). 手算: 目标 $\omega+m$ 的链过 `up m′`, $m'\ne m$ 时变成 `sib`. 所以 $x_2$ 看来要 `S`, 这一条是判断, 没有编译的否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTopLink where

open import Data.Nat using (ℕ; zero; suc)

open import OCF.Align.Level as L using (Ordᶜ; ψ⁰; ψ⁰≅ψ; ≅-refl⁰; ≅-sym)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.EBOTopLow using (rd-≅; rd-HS) renaming (rd to rdᴸ)
open import OCF.Align.InaccTreeBase as R using (Ordᴸ; Tree; limᵢ; up; iter)
open import OCF.Align.InaccFloorTree using (Sib)
open import OCF.Align.EBOTopRaw using (rd; module Raw)
import OCF.Align.EBOTopStage as St
open St using (O₀; _≅⁰_; ≅⁰-refl; ≅⁰-sym; ≅⁰-trans; ≺⁰-respʳ; z≅; s≅; l≅)
```

## §1 `O₀` 上的公共形式

```agda
_⊕_ : O₀ → O₀ → O₀
a ⊕ O₀.zero  = a
a ⊕ O₀.suc b = O₀.suc (a ⊕ b)
a ⊕ O₀.lim f = O₀.lim (λ n → a ⊕ f n)

⊕-cong : ∀ {a a′ b b′} → a ≅⁰ a′ → b ≅⁰ b′ → (a ⊕ b) ≅⁰ (a′ ⊕ b′)
⊕-cong ea z≅     = ea
⊕-cong ea (s≅ e) = s≅ (⊕-cong ea e)
⊕-cong ea (l≅ h) = l≅ (λ n → ⊕-cong ea (h n))

P₀ : O₀ → O₀
P₀ O₀.zero    = O₀.suc O₀.zero
P₀ (O₀.suc a) = O₀.lim (iter (P₀ a ⊕_) O₀.zero)
P₀ (O₀.lim f) = O₀.lim (λ n → P₀ (f n))

iter-⊕ : ∀ {a a′} → a ≅⁰ a′ → ∀ n → iter (a ⊕_) O₀.zero n ≅⁰ iter (a′ ⊕_) O₀.zero n
iter-⊕ e zero    = z≅
iter-⊕ e (suc n) = ⊕-cong e (iter-⊕ e n)

P₀-cong : ∀ {a b} → a ≅⁰ b → P₀ a ≅⁰ P₀ b
P₀-cong z≅     = s≅ z≅
P₀-cong (s≅ e) = l≅ (iter-⊕ (P₀-cong e))
P₀-cong (l≅ h) = l≅ (λ n → P₀-cong (h n))

tw : ℕ → O₀
tw = iter P₀ (O₀.suc O₀.zero)

-- HS 只看 ≅⁰ 类
HS-resp : ∀ {a b} → a ≅⁰ b → St.HS a → St.HS b
HS-resp z≅     St.hz        = St.hz
HS-resp (s≅ e) (St.hs h)    = St.hs (HS-resp e h)
HS-resp (l≅ k) (St.hl h st) = St.hl (λ n → HS-resp (k n) (h n))
  (λ n q → ≺⁰-respʳ (st n (≺⁰-respʳ q (≅⁰-sym (k n)))) (k (suc n)))
```

## §2 两边都归到 `P₀`

```agda
module Rw (S : Sib) where
  open Raw S

  add-link : (a b : Ordᴸ R.zero) → rd (a R.+ b) ≅⁰ (rd a ⊕ rd b)
  add-link a R.zero    = ≅⁰-refl _
  add-link a (R.suc b) = s≅ (add-link a b)
  add-link a (R.lim f) = l≅ (λ n → add-link a (f n))
  add-link a (limᵢ () f)
  add-link a (up () x)

  iter-link : ∀ p p′ → rd p ≅⁰ p′ → ∀ n → rd (iter (p R.+_) R.zero n) ≅⁰ iter (p′ ⊕_) O₀.zero n
  iter-link p p′ e zero    = z≅
  iter-link p p′ e (suc n) = ≅⁰-trans (add-link p _) (⊕-cong e (iter-link p p′ e n))

  P-link : (y : Ordᴸ R.zero) → rd (ψ₀ y) ≅⁰ P₀ (rd y)
  P-link R.zero    = ≅⁰-refl _
  P-link (R.suc a) = l≅ (iter-link _ _ (P-link a))
  P-link (R.lim f) = l≅ (λ n → P-link (f n))
  P-link (limᵢ () f)
  P-link (up () x)

  ch : ℕ → Ordᴸ R.zero
  ch = iter ψ₀ (R.suc R.zero)

  ch-link : ∀ m → rd (ch m) ≅⁰ tw m
  ch-link zero    = ≅⁰-refl _
  ch-link (suc m) = ≅⁰-trans (P-link (ch m)) (P₀-cong (ch-link m))

  x₀-link : rd (x 0) ≅⁰ P₀ (tw 0)
  x₀-link = P-link (R.suc R.zero)

  x₁-link : rd (x 1) ≅⁰ O₀.lim (λ m → P₀ (tw m))
  x₁-link = l≅ (λ m → ≅⁰-trans (P-link (ch m)) (P₀-cong (ch-link m)))

add-linkᴸ : (a b : Ordᶜ L.zero) → rdᴸ (a L.+ b) ≅⁰ (rdᴸ a ⊕ rdᴸ b)
add-linkᴸ a L.zero    = ≅⁰-refl _
add-linkᴸ a (L.suc b) = s≅ (add-linkᴸ a b)
add-linkᴸ a (L.lim f) = l≅ (λ n → add-linkᴸ a (f n))
add-linkᴸ a (L.limᵢ () f)
add-linkᴸ a (L.up () x)

iter-linkᴸ : ∀ p p′ → rdᴸ p ≅⁰ p′ → ∀ n → rdᴸ (iter (p L.+_) L.zero n) ≅⁰ iter (p′ ⊕_) O₀.zero n
iter-linkᴸ p p′ e zero    = z≅
iter-linkᴸ p p′ e (suc n) = ≅⁰-trans (add-linkᴸ p _) (⊕-cong e (iter-linkᴸ p p′ e n))

P-linkᴸ : (y : Ordᶜ L.zero) → rdᴸ (ψ⁰ y) ≅⁰ P₀ (rdᴸ y)
P-linkᴸ L.zero    = ≅⁰-refl _
P-linkᴸ (L.suc a) = l≅ (iter-linkᴸ _ _ (P-linkᴸ a))
P-linkᴸ (L.lim f) = l≅ (λ n → P-linkᴸ (f n))
P-linkᴸ (L.limᵢ () f)
P-linkᴸ (L.up () x)

Gᴸ : ℕ → Ordᶜ L.zero
Gᴸ = iter (λ x → L.ψ L.zero (λ q → q) (L.up L.zero x)) (L.suc L.zero)

G-link : ∀ m → rdᴸ (Gᴸ m) ≅⁰ tw m
G-link zero    = ≅⁰-refl _
G-link (suc m) = ≅⁰-trans (rd-≅ (≅-sym (ψ⁰≅ψ (≅-refl⁰ _)))) (≅⁰-trans (P-linkᴸ (Gᴸ m)) (P₀-cong (G-link m)))

U₀ : St.HS (P₀ (tw 0))
U₀ = HS-resp (P-linkᴸ (L.suc L.zero)) (rd-HS (Uniform L.zero))

U₁ : St.HS (O₀.lim (λ m → P₀ (tw m)))
U₁ = HS-resp (l≅ (λ m → ≅⁰-trans (P-linkᴸ (Gᴸ m)) (P₀-cong (G-link m)))) (rd-HS (Uniform (L.suc L.zero)))
```

## §3 结论

```agda
module Heads (S : Sib) where
  open Raw S
  open Rw S

  h₀ : St.HS (rd (x 0))
  h₀ = HS-resp (≅⁰-sym x₀-link) U₀

  h₁ : St.HS (rd (x 1))
  h₁ = HS-resp (≅⁰-sym x₁-link) U₁
```
