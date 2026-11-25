# 验收 (比较表那一行): 孩子取 ω 时的判据

> 验收文件 (读记号), 不进成品. 编译定理, 无前提: 表 `YiTBTab.rbᶜ` 下, 塔第 1 项的 Ω 树第 `ωᶜ` 支经孩子 2 朝第 2 层的那一行, 是孩子层 `h₁ ωᶜ` 的 Ω 树在 `h₁ ωᶜ` 上沿 `inc 2 self` 的折叠 (`lvlω`, `refl`), 对着 ψ₂(Ω_n) 对一切 n (`ωfam`), 所以对着 ψ₂(Ω_ω) (`ω-crit`, 不带项序封闭的 `M 2`; `ω̂ᶜ` 是 `M̂` 上的同一句).
> 机制: ℕ 极限层号 `h₁ ωᶜ` 的 Ω 树第 n 项是孩子 n 的 Ω 树的嵌入; 路径经孩子 2, n ≥ 3 时折叠的 ℕ 极限行经 `way` 落到孩子 n 的层 (`YiTBFam.sΩ-LF`), n ≤ 2 时嵌进第 2 层后自身折叠 (`Self.PF`).
> 范围: 只测了 `ωᶜ` 一个孩子与目标孩子 2; 一般的规范孩子没有做. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBLim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiTBTab using (rbᶜ)
open import OCF.Lean.YiTBFam
open import OCF.Lean.YiTBCrit using (o1; Bc; okBc; sbk)
open import OCF.Lean.YiRBFam using (tc; OKB)
open import OCF.Lean.YiRBCrit using (two; h₁; blk; hβ₂)
open import OCF.Lean.YiRLClos using (pfx; cum-form)
open import OCF.Lean.YiRLCrit using (of-fsn)
open import OCF.Lean.YiKVRel using (mz; mU; mw; _⊴_; ⊴r)
open import OCF.Lean.YiKCStep using (⊴-trans)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn; M; m⊴N; Mβ)
open import OCF.Lean.YiCLLow using (pth; ΩJ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiMHRel using (M̂; ĉ)
```

## 那一支

```agda
ℓω : L
ℓω = h₁ ωᶜ

oω : Ok ℓω
oω = o1 ωᶜ

gᶜ : Tr zero → Tr⁺ two
gᶜ c = ψ (tw 1) (Ok-tw 1) rbᶜ (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (blk c)

lvlω : gᶜ ωᶜ ≡ ψ ℓω oω (rb-no _) (Bc ωᶜ) two (inc 2 self) (Ωt two) (proj₁ (Ωt ℓω))
lvlω = refl
```

## ℕ 极限层号 `h₁ ωᶜ` 的 Ω 树沿 `inc 2 self` 朝第 2 层的折叠

```agda
pathω : ∀ k → self ∙ from0 (λ i → fn (suc (suc i))) (λ i → proj₁ oω (suc (suc i))) k ≡ pth (sbk k)
pathω zero    = refl
pathω (suc k) = cong (inc {s = sS} {h = λ _ → fn (suc (suc k))} tt) (pathω k)

module _ (r : Rb ℓω) (B : Base ℓω) (β : Tr⁺ two) (ok : OKB B) (hβ : M 2 (Ωᴺ 2) (proj₁ β)) where
  Fω : Tr ℓω → Tr⁺ two
  Fω = ψ ℓω oω r B two (inc 2 self) β

  Bx : (n : ℕ) → Tr ℓω → Base (fn n)
  Bx n x i u = ψ ℓω oω r B i (inc n u) (B i (inc n u)) x

  okx : (n : ℕ) (x : Tr ℓω) → OKB (Bx n x)
  okx n x i u = ⊴-trans (ok i (inc n u)) (ψ-⊵ ℓω oω r B i (inc n u) (B i (inc n u)) x)

  hβx : (x : Tr ℓω) → M 2 (Ωᴺ 2) (proj₁ (Fω x))
  hβx x = m⊴N 2 hβ (ψ-⊵ ℓω oω r B two (inc 2 self) β x)

  tm : (n : ℕ) → Tr ℓω
  tm n = up (pfx fn n) n (proj₁ (Ωt (fn n))) (proj₂ (Ωt (fn n)))

  whole : ∀ {t} n → M 2 t (proj₁ (Fω (tm n))) → M 2 t (proj₁ (Fω (proj₁ (Ωt ℓω))))
  whole {t} n m = mw (subst (λ Y → M 2 t (proj₁ (Fω Y))) (sym (cum-form fn n)) m) (◃l n)

  term3 : ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (Fω (tm (suc (suc (suc k))))))
  term3 k =
    subst (λ p → M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ (ψ (fn n) (proj₂ oω n) (proj₂ r n) (Bx n (pfx fn n)) two (inc tt p) (Fω (pfx fn n))
                                              (proj₁ (Ωt (fn n))))))
      (sym (pathω k))
      (sΩ-LF (proj₂ oω n) (proj₂ r n) (tc (sbk k)) (Bx n (pfx fn n)) (Fω (pfx fn n)) (okx n (pfx fn n)) (hβx (pfx fn n)))
    where
    n = suc (suc (suc k))

  term2 : M 2 (ψᴺ 2 (Ωᴺ 2)) (proj₁ (Fω (tm 2)))
  term2 = Self.PF 1 (proj₂ oω 2) (proj₂ r 2) (Bx 2 (pfx fn 2)) (Fω (pfx fn 2)) {P₀ = []} (hβx (pfx fn 2)) (Mβ 1)

  term1 : M 2 (ψᴺ 2 (Ωᴺ 1)) (proj₁ (Fω (tm 1)))
  term1 = Self.PF 1 (proj₂ oω 2) (proj₂ r 2) (Bx 2 (pfx fn 1)) (Fω (pfx fn 1)) {P₀ = []} (hβx (pfx fn 1))
            {x = proj₁ (emb two (proj₂ oω 2) (inc tt self) (Ωt (fn 1)))} (mU {t = []} {s = Ωᴺ 1} mz (Mβ 0))

  term0 : M 2 (ψᴺ 2 (Ωᴺ 0)) (proj₁ (Fω (tm 0)))
  term0 = Self.PF 1 (proj₂ oω 2) (proj₂ r 2) (Bx 2 (pfx fn 0)) (Fω (pfx fn 0)) {P₀ = []} (hβx (pfx fn 0))
            {x = proj₁ (emb two (proj₂ oω 2) (inc tt (inc tt self)) (Ωt zero))}
            (mU {t = []} {s = Ωᴺ 0} mz (mU {t = []} {s = Ωᴺ 0} mz (ΩJ 0 (Ωt zero) ⊴r)))

  ωfamᴮ : ∀ n → M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ (Fω (proj₁ (Ωt ℓω))))
  ωfamᴮ 0                   = whole 0 term0
  ωfamᴮ 1                   = whole 1 term1
  ωfamᴮ 2                   = whole 2 term2
  ωfamᴮ (suc (suc (suc k))) = whole (suc (suc (suc k))) (term3 k)

  ω-all : M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (Fω (proj₁ (Ωt ℓω))))
  ω-all = of-fsn (ωfamᴮ 0) (ωfamᴮ 1) (ωfamᴮ 2) (λ k → ωfamᴮ (suc (suc (suc k))))
```

## 判据在孩子 ω 处

```agda
ωfam : ∀ n → M 2 (ψᴺ 2 (Ωᴺ n)) (proj₁ (gᶜ ωᶜ))
ωfam = ωfamᴮ (rb-no _) (Bc ωᶜ) (Ωt two) (okBc ωᶜ) hβ₂

ω-crit : M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gᶜ ωᶜ))
ω-crit = ω-all (rb-no _) (Bc ωᶜ) (Ωt two) (okBc ωᶜ) hβ₂

ω̂ᶜ : M̂ (M 2) (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gᶜ ωᶜ))
ω̂ᶜ = ĉ (inj₂ refl) ω-crit
```
