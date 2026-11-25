# YiBtVal：`T₃ᵐ` 不低于参照的 ψ₀(Ω_ω)

**验收文件，档位：编译定理 (下界，不是同值)。** `T₃ᵐ` 的第 1 项的第 0 支的第 `m` 支是 `closedᵐ` 作用在层号 `read0 (1 + copies 1 m)` 上，这个层号命题相等于 `fin (m+2)` (`H-fin`)；
接 [YiBtValFin](YiBtValFin.lagda.md) 的 `lower-finᵐ` (对任意 `Plain`, `Legal`)，两次经过极限层号上 `top` 的部分和一行 (`psum≽`)，再对 `n` 取上确界。被验收的是 [YiRawFoldTw3](YiRawFoldTw3.lagda.md) 的 `T₃ᵐ`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; Legal; read0)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.Align.YiLvFoldAdd using (plus; copies)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldInst using (closedᵐ)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩)
open import OCF.Align.YiBtValFin using (lower-finᵐ; psum≽)
import OCF.Align.Level as L
import OCF.Align.Value as V
open V using (_≼_; ≼-trans; ≼l; l≼; ⊑→≼)
```

## 1 层号的计算

```agda
S : ℕ → R
S zero = G.zero
S (suc n) = G.suc (S n)

plus-S : ∀ n → plus B.zero one (S n) ≡ S (suc n)
plus-S zero = refl
plus-S (suc n) = cong G.suc (plus-S n)

copies-S : ∀ m → copies B.zero one m ≡ S (suc m)
copies-S zero = refl
copies-S (suc m) = trans (cong (plus B.zero one) (copies-S m)) (plus-S (suc m))

one+S : ∀ n → one +ʳ S n ≡ S (suc n)
one+S zero = refl
one+S (suc n) = cong G.suc (one+S n)

read0-S : ∀ n → read0 (S n) ≡ fin n
read0-S zero = refl
read0-S (suc n) = cong B.suc (read0-S n)

H-fin : ∀ m → read0 (one +ʳ copies B.zero one m) ≡ fin (suc (suc m))
H-fin m = trans (cong (λ z → read0 (one +ʳ z)) (copies-S m))
  (trans (cong read0 (one+S (suc m))) (read0-S (suc (suc m))))

closedᵐ-at : ∀ n K → fin n ≡ K → ∀ (pl : Plain K) (Lg : Legal K) →
  L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closedᵐ K pl Lg)
closedᵐ-at n .(fin n) refl pl Lg = lower-finᵐ n pl Lg
```

## 2 下界

```agda
T₃ᵐ-at : ∀ m → L.ψ⁰ (L.Ω ⟨ suc (suc m) ⟩) ≼ read T₃ᵐ
T₃ᵐ-at m = ≼l 1 (≼l 0 (≼l m (psum≽ _ m
  (closedᵐ-at (suc (suc m)) (read0 (one +ʳ copies B.zero one m)) (sym (H-fin m)) _ _))))

Ω-mono : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ L.ψ⁰ (L.Ω ⟨ suc (suc n) ⟩)
Ω-mono n = ⊑→≼ (L.ψ⁰ (L.Ω ⟨ n ⟩)) (L.Ψ⁰-mono (L.Sim→⊑ᴵ (λ q → L.suc (L.suc q))))

T₃ᵐ-Ωω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read T₃ᵐ
T₃ᵐ-Ωω = l≼ (λ n → ≼-trans (Ω-mono n) (T₃ᵐ-at n))
```
