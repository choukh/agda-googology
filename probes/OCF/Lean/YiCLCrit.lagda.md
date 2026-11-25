# 验收 (候选 A): 判据的前提缩到 ω 以上的后继; 量化域的一条事实

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 条件定理: `critS⁺ : A1S⁺ → (h : HC tB) → Rt h ≼ readRW W`, 前提 `A1S⁺` 是 `YiKCStep.A1S` 去掉 "前驱是有限数" 的情形 (那些由 `YiCLPhi.a1s-fin` 给出). `A1S⁺` 未证, 没有实例.
> 编译定理, 无前提 (`no-least`): 满足 `M⁰ ω x` 的第 0 层的树没有 `⊴` 意义下的最小元: `ωᶜ` (极限 0, 1, 2, …) 与 `ωᵉ` (极限 0, 2, 4, …) 都满足, 而同时在两者之下的树都不满足. 所以 η = ω+1 处的后继情形不能由一个规范实例经 `YiKCStep.clos` 得到.
> 不否定 `A1S`, 不否定候选 A 到 ψ₀(Ω_Ω+Ω₂); 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCLCrit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVRel using (M⁰; mz; m1; mL; mw; _⊴_; ⊴r; ⊴◃; ⊴-◃; ¬◃z; ψ₁ᵗ; readRW)
open import OCF.Lean.YiKCStep using (S; A1S; critS; ⊴-trans)
open import OCF.Lean.YiKCSem using (W)
import OCF.Align.EboLeanDef as E
open E using (HC; cof; c1; pred; fsn; natT; sucT; 𝟏)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Lean.YiNFOCase using (tB)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiCLPhi using (a1s-fin; nat⊴; inv-lim; ωᵀ; rep1)
```

## 判据的前提

一个项是不是有限数可判定 (`isNat`); 前驱是有限数的后继情形由 `a1s-fin` 给出.

```agda
tl : E.T → E.T
tl []      = []
tl (_ ∷ t) = t

no-hd₁ : ∀ {w ws a t} n → E.ψ (w ∷ ws) a ∷ t ≡ natT n → ⊥
no-hd₁ zero    ()
no-hd₁ (suc n) ()

no-hd₂ : ∀ {y ys t} n → E.ψ [] (y ∷ ys) ∷ t ≡ natT n → ⊥
no-hd₂ zero    ()
no-hd₂ (suc n) ()

no-tl : ∀ {t} → ((n : ℕ) → t ≡ natT n → ⊥) → (n : ℕ) → 𝟏 ∷ t ≡ natT n → ⊥
no-tl no zero    ()
no-tl no (suc n) q = no n (cong tl q)

isNat : (t : E.T) → (Σ ℕ λ n → t ≡ natT n) ⊎ ((n : ℕ) → t ≡ natT n → ⊥)
isNat []                        = inj₁ (0 , refl)
isNat (E.ψ [] [] ∷ t) with isNat t
... | inj₁ (n , q) = inj₁ (suc n , cong (𝟏 ∷_) q)
... | inj₂ no      = inj₂ (no-tl no)
isNat (E.ψ [] (y ∷ ys) ∷ t)     = inj₂ no-hd₂
isNat (E.ψ (w ∷ ws) a ∷ t)      = inj₂ no-hd₁

natT-suc : ∀ n → sucT (natT n) ≡ natT (suc n)
natT-suc zero    = refl
natT-suc (suc n) = cong (𝟏 ∷_) (natT-suc n)

A1S⁺ : Set
A1S⁺ = (η : E.T) (x : Tr zero) → cof η ≡ c1 → ((n : ℕ) → pred η ≡ natT n → ⊥) → M⁰ (pred η) x
     → S (ψ₁ᵗ (E.Ωt (pred η))) x → S (ψ₁ᵗ (E.Ωt η)) (suc x)

a1s-of : A1S⁺ → A1S
a1s-of s η x e r ih with isNat (pred η)
... | inj₂ no      = s η x e no r ih
... | inj₁ (n , q) =
  subst (λ t → S (ψ₁ᵗ (E.Ωt t)) (suc x)) (trans (sym (natT-suc n)) (trans (cong sucT (sym q)) (pred-suc η e)))
    (a1s-fin n (subst (λ t → M⁰ t x) q r))

critS⁺ : A1S⁺ → (h : HC tB) → Rt h ≼ readRW W
critS⁺ s = critS (a1s-of s)
```

## 量化域: 满足 `M⁰ ω x` 的树没有最小元

```agda
ωᶜ : Tr zero
ωᶜ = lim nat (λ n → ◃s)

dbl : ℕ → Tr zero
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

ωᵉ : Tr zero
ωᵉ = lim dbl (λ n → ◃t ◃s ◃s)

natM : ∀ k → M⁰ (natT k) (nat k)
natM zero    = mz
natM (suc k) = m1 (cof-nat k) (subst (λ t → M⁰ t (nat k)) (sym (pred-nat k)) (natM k))

dblM : ∀ k → M⁰ (natT k) (dbl k)
dblM zero    = mz
dblM (suc k) = m1 (cof-nat k) (subst (λ t → M⁰ t (suc (dbl k))) (sym (pred-nat k)) (mw (dblM k) ◃s))

ωᶜ-M : M⁰ ωᵀ ωᶜ
ωᶜ-M = mL refl (λ k → subst (λ t → M⁰ t ωᶜ) (sym (rep1 k)) (mw (natM k) (◃l k)))

ωᵉ-M : M⁰ ωᵀ ωᵉ
ωᵉ-M = mL refl (λ k → subst (λ t → M⁰ t ωᵉ) (sym (rep1 k)) (mw (dblM k) (◃l k)))
```

第 0 层的 `◃` 的两条反演.

```agda
inv-l : ∀ {x f a} → zero ⊢ x ◃ lim f a → Σ ℕ λ n → x ⊴ f n
inv-l (◃l n)   = n , ⊴r
inv-l (◃t d e) with inv-l e
... | n , le = n , ⊴◃ (◃-⊴ d le)
  where
  ◃-⊴ : {a b c : Tr zero} → zero ⊢ a ◃ b → b ⊴ c → zero ⊢ a ◃ c
  ◃-⊴ d ⊴r      = d
  ◃-⊴ d (⊴◃ d′) = ◃t d d′

inv-s : ∀ {x y} → zero ⊢ x ◃ suc y → x ⊴ y
inv-s ◃s       = ⊴r
inv-s (◃t d e) with inv-s e
... | ⊴r    = ⊴◃ d
... | ⊴◃ d′ = ⊴◃ (◃t d d′)

lim-s : ∀ {f a x} → lim f a ⊴ suc x → lim f a ⊴ x
lim-s (⊴◃ d) = inv-s d

no-lim : ∀ k {f a} → lim f a ⊴ nat k → ⊥
no-lim zero    (⊴◃ d) = ¬◃z d
no-lim (suc k) le     = no-lim k (lim-s le)

no-limᵉ : ∀ k {f a} → lim f a ⊴ dbl k → ⊥
no-limᵉ zero    (⊴◃ d) = ¬◃z d
no-limᵉ (suc k) le     = no-limᵉ k (lim-s (lim-s le))
```

有限的树不满足 `M⁰ ω`: `M⁰ ω y` 给出 `nat (suc k) ⊴ y`, 而 `nat (suc k) ⊴ nat k` 不成立.

```agda
nat≢ : ∀ k → nat (suc k) ≡ nat k → ⊥
nat≢ zero    ()
nat≢ (suc k) q = nat≢ k (cong prd q)
  where
  prd : Tr zero → Tr zero
  prd (suc x) = x
  prd x       = x

◃⊴ : {a b c : Tr zero} → zero ⊢ a ◃ b → b ⊴ c → a ⊴ c
◃⊴ d ⊴r     = ⊴◃ d
◃⊴ d (⊴◃ e) = ⊴◃ (◃t d e)

no-desc : ∀ k {a b} → a ⊴ b → a ≡ nat (suc k) → b ≡ nat k → ⊥
no-desc k       ⊴r     qa   qb   = nat≢ k (trans (sym qa) qb)
no-desc zero    (⊴◃ d) refl refl = ¬◃z d
no-desc (suc k) (⊴◃ d) refl refl = no-desc k (◃⊴ ◃s (inv-s d)) refl refl

fin-no : ∀ k {y} → y ⊴ nat k → M⁰ ωᵀ y → ⊥
fin-no k {y} le m =
  no-desc k (⊴-trans (nat⊴ (suc k) (subst (λ t → M⁰ t y) (rep1 (suc k)) (inv-lim refl m (suc k))) refl) le) refl refl

at1 : Tr zero → Tr zero
at1 (lim f _) = f 1
at1 x         = x

2≢1 : _≡_ {A = Tr zero} (suc (suc zero)) (suc zero) → ⊥
2≢1 ()

cross : ωᶜ ⊴ ωᵉ → ⊥
cross le = go le refl
  where
  go : ∀ {y} → y ⊴ ωᵉ → y ≡ ωᶜ → ⊥
  go ⊴r     q = 2≢1 (cong at1 q)
  go (⊴◃ d) refl with inv-l d
  ... | k , le′ = no-limᵉ k le′

no-least : ∀ y → y ⊴ ωᶜ → y ⊴ ωᵉ → M⁰ ωᵀ y → ⊥
no-least y (⊴◃ d) le′ m with inv-l d
... | k , le = fin-no k le m
no-least y ⊴r     le′ m = cross le′
```
