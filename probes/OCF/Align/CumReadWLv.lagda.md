# 带闭包的层: 实例与合法性

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). `upL`: 下标读成层. `_+ₗ_`: 层的加法. `M x α`: $x\cdot\alpha$. `Ωᴸ`: $\Omega_1$ 这一层. `P n`: $\Omega^{n+1}$, `Pω`: $\Omega^\omega$. 都有 `Legal` 的证明, 所以 `Tψ` 给出闭项. **强度只是判断.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadWLv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Free.Level using (FGH)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadW

upL : A → Lv
upL azero = lz
upL (asuc a) = ls (upL a)
upL (alim f) = ll (λ n → upL (f n))

up⊳ : ∀ {a b} → a ⊲ b → upL a ⊳ upL b
up⊳ C.self = self
up⊳ (C.suc p) = suc (up⊳ p)
up⊳ (C.lim n p) = lim n (up⊳ p)

Legal-up : ∀ a → Lg a → Legal (upL a)
Legal-up azero w = tt
Legal-up (asuc a) w = Legal-up a w
Legal-up (alim f) (st , w) = (λ n → up⊳ (st n)) , (λ n → Legal-up (f n) (w n))

Ωᴸ : Lv
Ωᴸ = lc (ls lz) upL

Legal-Ω : Legal Ωᴸ
Legal-Ω = (λ w g → up⊳ (pos g)) , (λ w v gw′ gv p → up⊳ p) , tt , (λ w g → Legal-up w (lgw g))

infixl 6 _+ₗ_
_+ₗ_ : Lv → Lv → Lv
a +ₗ lz = a
a +ₗ ls b = ls (a +ₗ b)
a +ₗ ll f = ll (λ n → a +ₗ f n)
a +ₗ lc t g = lc (a +ₗ t) (λ w → a +ₗ g w)

+⊳ : ∀ a {b c} → b ⊳ c → a +ₗ b ⊳ a +ₗ c
+⊳ a self = self
+⊳ a (suc p) = suc (+⊳ a p)
+⊳ a (lim n p) = lim n (+⊳ a p)
+⊳ a (fst p) = fst (+⊳ a p)

+fst : ∀ a b → a ⊳ a +ₗ b
+fst a lz = self
+fst a (ls b) = suc (+fst a b)
+fst a (ll f) = lim 0 (+fst a (f 0))
+fst a (lc t g) = fst (+fst a t)

Legal-+ : ∀ a b → Legal a → Legal b → Legal (a +ₗ b)
Legal-+ a lz u v = u
Legal-+ a (ls b) u v = Legal-+ a b u v
Legal-+ a (ll f) u (st , v) = (λ n → +⊳ a (st n)) , (λ n → Legal-+ a (f n) u (v n))
Legal-+ a (lc t g) u (tg , dir , wt , wg) =
  (λ w gw′ → +⊳ a (tg w gw′)) , (λ w v g₁ g₂ p → +⊳ a (dir w v g₁ g₂ p)) , Legal-+ a t u wt , (λ w gw′ → Legal-+ a (g w) u (wg w gw′))

-- x·α
M : Lv → A → Lv
M x azero = lz
M x (asuc a) = M x a +ₗ x
M x (alim f) = ll (λ n → M x (f n))

M⊳ : ∀ x {a b} → a ⊲ b → M x a ⊳ M x b
M⊳ x C.self = self
M⊳ x {b = asuc b} (C.suc p) = ⊳-tr (M⊳ x p) (+fst (M x b) x)
M⊳ x (C.lim n p) = lim n (M⊳ x p)

Legal-M : ∀ x → Legal x → ∀ a → Lg a → Legal (M x a)
Legal-M x u azero w = tt
Legal-M x u (asuc a) w = Legal-+ (M x a) x (Legal-M x u a w) u
Legal-M x u (alim f) (st , w) = (λ n → M⊳ x (st n)) , (λ n → Legal-M x u (f n) (w n))

-- x·Ω: 闭包, 分支 x·η
_·Ω : Lv → Lv
x ·Ω = lc (M x one) (M x)

Legal-·Ω : ∀ x → Legal x → Legal (x ·Ω)
Legal-·Ω x u =
  (λ w g → M⊳ x (pos g)) , (λ w v g₁ g₂ p → M⊳ x p) , Legal-M x u one tt , (λ w g → Legal-M x u w (lgw g))

P : ℕ → Lv
P zero = Ωᴸ
P (suc n) = P n ·Ω

Legal-P : ∀ n → Legal (P n)
Legal-P zero = Legal-Ω
Legal-P (suc n) = Legal-·Ω (P n) (Legal-P n)
```

**闭项.** 这些都是 `Tψ` 的值, 类型是第 0 层的树. 判断: $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega^2})$. **没有 `HS`, 没有标签.**

```agda
Tᵂ₁ : Ord₀
Tᵂ₁ = Tψ Ωᴸ Legal-Ω

TΩ+ : ∀ a → Lg a → Ord₀
TΩ+ a w = Tψ (Ωᴸ +ₗ upL a) (Legal-+ Ωᴸ (upL a) Legal-Ω (Legal-up a w))

TΩ· : ∀ a → Lg a → Ord₀
TΩ· a w = Tψ (M Ωᴸ a) (Legal-M Ωᴸ Legal-Ω a w)

TP : ℕ → Ord₀
TP n = Tψ (P n) (Legal-P n)

fgh : Ord₀ → ℕ → ℕ
fgh = FGH
```
