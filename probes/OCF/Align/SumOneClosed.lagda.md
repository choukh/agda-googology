# 和形式过 $\Omega_{\Omega+1}$ (三): 闭项

> 不含记号. 入口 [SumOne](SumOne.lagda.md). $S=\cdot\omega$ 的实例. `T₀` 读 $\psi_0(\Omega_\Omega)$, `T₁` 读 $\psi_0(\Omega_{\Omega+1})$; 读法只有 [SumOneAccept](SumOneAccept.lagda.md) 写明的那些是定理. 没有证书参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneClosed where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FL
open import OCF.Align.SumOneTree using (D₊; nl)

ω⋅ : ∀ {Kd : A → A → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W
ω⋅ c = nl (λ _ → c)

open import OCF.Align.SumOneFold ω⋅ public

ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

G : ℕ → A → ℕ
G n azero = 0
G n (asuc a) = suc (G n a)
G n (alim f) = G n (f n)

fgh : ℕ → ℕ
fgh = FL.FGH (ord T₁)
```
