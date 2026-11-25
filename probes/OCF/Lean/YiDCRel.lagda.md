# 验收一侧: 对参照按项序向下封闭的关系, `Leaf` 与 `LowKeep` 实填 (有限层号)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `M̃ n s x`: 有见证项 t, s ≤ᵀ t 且 `M n t x`.
> 在 `gradedᴰ` (`YiASIface.gradedᴬ` 把关系换成 `M̃`, 读法换成 "ν 是不超过 n 的自然数") 上: `rd0ᴰ`, `rdSᴰ`, `leafᴰ`, `lowKeepᴰ` (后者由 `YiASProofLow.lowKeepᶠ` 与前缀下的项序单调 `app≤` 组合).
> 不给出什么: `M̃` 上的其余律 (`Succ`, `Node`, `Emb`, `SelfKeep`, `UpKeep`) 没有填; 第 0 层出口见 [YiDCExit](YiDCExit.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDCRel where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiLegBlock using (Tr)
import OCF.Align.EboLeanDef as E
open E using (natT; sucT; 𝟏; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-trans′)
open import OCF.Align.EboLeanView using (cof0; ne)
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiANFam using (fin; M; ψᴺ; Ωᴺ)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGIface using (Graded; module Laws)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGFin using (blkᶠ; foldᶠ; rowsᶠ)
open import OCF.Lean.YiASIface using (gradedᴬ; domsᴬ)
open import OCF.Lean.YiASProofLow using (lowKeepᶠ)
open import OCF.Lean.YiASProofMin using (mΩt)
```

## 关系与读法

`gradedᴰ` 的 `Bd` 仍是 `gradedᴬ` 的 (底与底值对着 ψ_i(t₀), 用 `M` 陈述), 上下文仍是前缀 t₀.

```agda
M̃ : (n : ℕ) → E.T → Tr (fin n) → Set
M̃ n s x = Σ E.T λ t → (s ≤ᵀ t) × M n t x

Rdᴰ : ℕ → E.T → Set
Rdᴰ n ν = Σ ℕ λ m → (ν ≡ natT m) × (m ≤ⁿ n)

gradedᴰ : Graded blkᶠ foldᶠ rowsᶠ refᴱ 𝕍
gradedᴰ = record gradedᴬ { R = M̃ ; Rd = Rdᴰ }

η̃ : ∀ {n s x} → M n s x → M̃ n s x
η̃ {s = s} m = s , inj₂ refl , m

↓̃ : ∀ {n s s′ x} → s′ ≤ᵀ s → M̃ n s x → M̃ n s′ x
↓̃ le (t , le′ , m) = t , ≤-trans′ le le′ , m
```

## 项序

```agda
nat≤ : ∀ {m n} → m ≤ⁿ n → natT m ≤ᵀ natT n
nat≤ {n = zero}  z≤n = inj₂ refl
nat≤ {n = suc n} z≤n = inj₁ []<
nat≤ (s≤s l) with nat≤ l
... | inj₁ p = inj₁ (tl< p)
... | inj₂ e = inj₂ (cong (𝟏 ∷_) e)

Ω≤ : ∀ {m n} → m ≤ⁿ n → Ωᴺ m ≤ᵀ Ωᴺ n
Ω≤ l with nat≤ l
... | inj₁ p = inj₁ (hd< (lv< p))
... | inj₂ e = inj₂ (cong (λ u → E.ψ u [] ∷ []) e)

app≤ : ∀ j t₀ {a b} → a ≤ᵀ b → ψᴺ j (t₀ ++ a) ≤ᵀ ψᴺ j (t₀ ++ b)
app≤ j t₀ (inj₁ p)    = inj₁ (hd< (ar< (++-mono t₀ p)))
app≤ j t₀ (inj₂ refl) = inj₂ refl

suc-nat : ∀ m → sucT (natT m) ≡ natT (suc m)
suc-nat zero    = refl
suc-nat (suc m) = cong (𝟏 ∷_) (suc-nat m)
```

## 读法的两条与 `Leaf`

读法的零、后继两条与 `Leaf` 在 `M̃` 上同时成立 (`M` 上不能: `YiASProofPair.no-leaf`). `Leaf` 的见证项是本层的 Ω_n.

```agda
open Laws gradedᴰ domsᴬ using (Rd0; RdS; Leaf; LowKeep)

rd0ᴰ : Rd0
rd0ᴰ {ν = []}    e = 0 , refl , z≤n
rd0ᴰ {ν = _ ∷ _} e = ⊥-elim (cof0 _ ne e)

rdSᴰ : RdS
rdSᴰ {ν = ν} e (m , q , l) = suc m , trans (sym (pred-suc ν e)) (trans (cong sucT q) (suc-nat m)) , s≤s l

leafᴰ : Leaf
leafᴰ {ℓ = n} (m , refl , l) = Ωᴺ n , Ω≤ l , mΩt n
```

## `LowKeep`

见证项从 t 变成 ψ_j(t₀ + t).

```agda
lowKeepᴰ : LowKeep
lowKeepᴰ {j = j} b w β t₀ gb wl bd gx (t , le , m) =
  ψᴺ j (t₀ ++ t) , app≤ j t₀ le , lowKeepᶠ b w β t₀ gb wl bd gx m
```
