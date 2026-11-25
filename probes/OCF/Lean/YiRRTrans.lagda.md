# N 的传递性：分支关系自反时成立
不读记号；编译定理：层号的各槽位上分支关系自反（`Rfl`，孩子层同样）时 `N` 传递（`trans`），第 0、1 层无条件（`rfl₀`、`rfl₁`）。编译否定：第 2 层的 `Rfl` 不成立（`no-rfl₂`：第 1 层有不自反的树 `bad`）。
所以第 2 层及以上 `N` 是否传递未走通（没有证明，也没有反例）；用到自反的只有 `w≼w` 与 `≼w`/`≼W` 接 `w≼w` 三处，`Le` 的 `w≼w` 同样。`YiRRFold.fl`、`YiRRClimb.climb` 不用传递性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRTrans where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRRRel

Rfl : L → Set
Rfl zero     = ⊤
Rfl (nd s h) = ((p : Pos (nd s h)) (z : Br (nd s h) p) → NB (nd s h) p z z) × ((c : Ch s) → Rfl (h c))

trans : (ℓ : L) → Rfl ℓ → {a b c : Tr ℓ} → N ℓ a b → N ℓ b c → N ℓ a c
trans ℓ ρ z≼ e = z≼
trans ℓ ρ (l≼ h) e = l≼ (λ n → trans ℓ ρ (h n) e)
trans ℓ ρ d (≼s e) = ≼s (trans ℓ ρ d e)
trans ℓ ρ d (≼l n e) = ≼l n (trans ℓ ρ d e)
trans ℓ ρ d (≼w e) = ≼w (trans ℓ ρ d e)
trans ℓ ρ d (≼W z ez k) = ≼W z ez (λ z′ r → trans ℓ ρ d (k z′ r))
trans ℓ ρ d (≼u e) = ≼u (trans ℓ ρ d e)
trans ℓ ρ (s≼s d) (s≼s e) = s≼s (trans ℓ ρ d e)
trans ℓ ρ (≼s d) (s≼s e) = ≼s (trans ℓ ρ d e)
trans ℓ ρ (≼l n d) (l≼ h) = trans ℓ ρ d (h n)
trans zero ρ (≼w {p = ()} d) (w≼w h)
trans (nd s h) ρ (≼w {p = p} d) (w≼w k) = ≼w (trans (nd s h) ρ d (k _ _ (proj₁ ρ p _)))
trans zero ρ (w≼w {p = ()} h) (w≼w k)
trans (nd s h) ρ (w≼w {p = p} k) (w≼w k′) = w≼w (λ z z″ r → trans (nd s h) ρ (k z z (proj₁ ρ p z)) (k′ z z″ r))
trans zero ρ (≼W {p = ()} z ez k) (w≼w k′)
trans (nd s h) ρ (≼W {p = p} z ez k) (w≼w k′) = ≼W z ez (λ z′ r → trans (nd s h) ρ (k z′ r) (k′ z′ z′ (proj₁ ρ p z′)))
trans zero ρ (≼u {c = ()} d) (u≼u e r)
trans (nd s h) ρ (≼u d) (u≼u e r) = ≼u (trans (nd s h) ρ d e)
trans zero ρ (u≼u {c = ()} dx dy) (u≼u ex ey)
trans (nd s h) ρ (u≼u {c = c} dx dy) (u≼u ex ey) = u≼u (trans (nd s h) ρ dx ex) (trans (h c) (proj₂ ρ c) dy ey)

rfl₀ : Rfl zero
rfl₀ = tt

rfl₁ : Rfl L1
rfl₁ = (λ { (inj₂ (tt , inj₁ tt)) z → nrefl₀ z ; (inj₂ (tt , inj₂ ())) z }) , λ _ → tt

trans₁ : {a b c : Tr L1} → N L1 a b → N L1 b c → N L1 a c
trans₁ = trans L1 rfl₁
```

## 第 2 层的 Rfl 不成立

`bad`: 第 1 层零层槽位的结点, 分支在零处为 1, 别处为 0; 它不自反.

```agda
L2 : L
L2 = nd sS (λ _ → L1)

p₀ : Pos L1
p₀ = inj₂ (tt , inj₁ tt)

φ : Tr zero → Tr L1
φ zero      = suc zero
φ (suc _)   = zero
φ (lim _ _) = zero

bad : Tr L1
bad = Ω p₀ φ

no-Ω0 : ∀ {ℓ p g} → N ℓ (Ω p g) zero → ⊥
no-Ω0 ()

bad-not : N L1 bad bad → ⊥
bad-not (≼w (≼s d)) = no-Ω0 d
bad-not (w≼w h) with h zero (suc zero) z≼
... | ()
bad-not (≼W z ez k) = no-Ω0 (k (suc zero) (ez (suc zero) (inj₁ refl)))

no-rfl₂ : Rfl L2 → ⊥
no-rfl₂ ρ = bad-not (proj₁ ρ (inj₂ (tt , inj₁ tt)) bad)
```
