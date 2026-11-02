# 奇异下标的定时检验: 下标分层在 `ψ₀(Ω_Ω)` 处的否定 (验收)

> **验收节.** 结论在 [InaccSingular](InaccSingular.lagda.md).
>
> `InaccModulusRank` 的 `Strata` 对下标深度分层: `Nr (d+1)` 的下标在 `Nr d`, 而 `Nr d` 对基本列封闭. **`no-grade`: 这样的分层不能含 `ψ₀(Ω_Ω)`. `no-grade-2`: 也不能含 `ψ₀(Ω_Ω+Ω₁)`. `no-grade-top`: 也不能含 `ψ₀(Ω_Ω·2)`, 因为前者是它的基本列第 1 项 (从 0 数) 的下标.** 所以 `GV` 对这个类不能用深度递归, 即使判决已经正确. 否定只针对 ℕ-分层; 用项序的良基归纳不受影响, 但本仓库没有那条归纳 (记号侧的良基性未做).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingularGrade where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Align.Bachmann using (fs-gt)
import OCF.Align.EBO as E
open E using (T; cof; c1; cω; cΩ; fsT; fsn; pred; γT; Ωt; 𝟏; natT) renaming (ψ to ψᵗ)
```

## §1 分层的公理

`Grade C`: `C d` 对基本列、`pred` 与参数、尾项封闭, 主项的下标在下一层, 第 0 层的下标只有 0. `Strata` 的 `Sub (Nr d)` 正是这种形状 (`Nr 0` 只含 0, `Nr (d+1)` 的下标在 `Nr d`; 这里说 "形状", 没有形式化实例, 因为 `Nr` 本身不含 Ω₁, 含 Ω₁ 且封闭的版本由本文知不能含 `ψ₀(Ω_Ω)`).

```agda
record Grade (C : ℕ → T → Set) : Set where
  field
    g-nil : ∀ {u a xs} → C 0 (ψᵗ u a ∷ xs) → u ≡ []
    g-fs  : ∀ {d t} → C d t → cof t ≡ cω → ∀ n → C d (fsn t n)
    g-pr  : ∀ {d t} → C d t → cof t ≡ c1 → C d (pred t)
    g-tl  : ∀ {d x xs} → C d (x ∷ xs) → C d xs
    g-arg : ∀ {d u a xs} → C d (ψᵗ u a ∷ xs) → C d a
    g-sub : ∀ {d u a xs} → C (suc d) (ψᵗ u a ∷ xs) → C d u

Ω₁ OO : T
Ω₁ = Ωt (natT 1)
OO = Ωt Ω₁

ψ₀ : T → T
ψ₀ a = ψᵗ [] a ∷ []

γ : ℕ → T
γ = γT OO []

γ-suc : ∀ k → γ (suc k) ≡ ψ₀ (Ωt (γ k))
γ-suc k = refl

fs-γ : ∀ n → fsn (ψ₀ OO) n ≡ γ (suc n)
fs-γ n = fs-gt [] (ψᵗ Ω₁ []) [] [] refl refl n
```

## §2 否定

`γ (k+2)` 的参数是 `Ω_{γ(k+1)}`, 下标是 `γ(k+1)`. 所以每下降一层都还能再取一次下标; 到第 0 层时矛盾. 这个论证只用了 `ψ₀(Ω_Ω)` 的基本列的形状.

```agda
module No {C : ℕ → T → Set} (G : Grade C) where
  open Grade G

  descend : ∀ d → (∀ m → C d (γ (suc m))) → ⊥
  descend zero    h with () ← g-nil {u = γ 1} (g-arg {u = []} (h 1))
  descend (suc d) h = descend d (λ m → g-sub {u = γ (suc m)} (g-arg {u = []} (h (suc m))))

  no-grade : ∀ d → C d (ψ₀ OO) → ⊥
  no-grade d c = descend d (λ m → subst (C d) (fs-γ m) (g-fs c refl m))
```

`ψ₀(Ω_Ω·2)` 的 γ-链: `Γ 0 = 1`, `Γ (k+1) = ψ₀(Ω_Ω + Ω_{Γ k})`. 所以 `Γ 1 = ψ₀(Ω_Ω+Ω₁)` 是 `Γ 2` 的下标. 它的基本列第 0 项是 `ψ₀(Ω_Ω+1)`, 后者的第 1 项是 `ψ₀(Ω_Ω)`. **`no-grade-2`: 不存在包含 `Γ 1` 的分层, 所以 `ψ₀(Ω_Ω·2)` 的标签不能走 `Strata`.**

```agda
  t₁ t₂ : T
  t₁ = ψ₀ (ψᵗ Ω₁ [] ∷ ψᵗ [] [] ∷ [])          -- ψ₀(Ω_Ω+1)
  t₂ = ψ₀ (ψᵗ Ω₁ [] ∷ ψᵗ (natT 1) [] ∷ [])    -- ψ₀(Ω_Ω+Ω₁)

  no-grade-1 : ∀ d → C d t₁ → ⊥
  no-grade-1 d c = no-grade d (subst (C d) e (g-fs c refl 1))
    where
      e : fsn t₁ 1 ≡ ψ₀ OO
      e = refl

  no-grade-2 : ∀ d → C d t₂ → ⊥
  no-grade-2 d c = no-grade-1 d (subst (C d) e (g-fs c refl 0))
    where
      e : fsn t₂ 0 ≡ t₁
      e = refl

  OO·2 : T
  OO·2 = ψᵗ Ω₁ [] ∷ ψᵗ Ω₁ [] ∷ []

  fs-top : fsn (ψ₀ OO·2) 1 ≡ ψ₀ (ψᵗ Ω₁ [] ∷ ψᵗ t₂ [] ∷ [])
  fs-top = fs-gt [] (ψᵗ Ω₁ []) (ψᵗ Ω₁ [] ∷ []) [] refl refl 1

  no-grade-top : ∀ d → C d (ψ₀ OO·2) → ⊥
  no-grade-top zero    c with () ← g-nil {u = t₂} (g-tl (g-arg {u = []} (subst (C 0) fs-top (g-fs c refl 1))))
  no-grade-top (suc d) c = no-grade-2 d (g-sub {u = t₂} (g-tl (g-arg {u = []} (subst (C (suc d)) fs-top (g-fs c refl 1)))))
```
