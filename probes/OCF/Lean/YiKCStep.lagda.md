# 候选 A: A1 对 `M⁰ η c` 的归纳, 余下后继一种情形 (验收)

> 验收文件 (读记号), 树、折叠、合法性一行不改. 编译定理: `ind : A1S → M⁰ η c → S (ψ₁ᵗ (Ωt η)) c`, 推论 `a1-of : A1S → A1`, `critS : A1S → (h : HC tB) → Rt h ≼ readRW W` (条件, 前提 A1S 是后继一种情形). 无前提: 零情形 `S0` (对一切 c), 松弛情形 `clos` (沿第 0 层的 `◃` 向上封闭).
> `S t c`: 对一切在标准底之上的源底 (`OKB`) 与一切在 Ω₁ 之上的起点, t 对着孩子 c 的 Ω 树经 `φ` (锚是第 2 层) 朝第 1 层的折叠. 松弛用链下的字面嵌入: 后继层号取回灌链的第 1 行, ℕ 极限层号取第 n 行 (底与起点换成前 n 项的折叠, 仍在量化域内).
> 不给出后继情形 (η = ν+1, c = suc x); 有限的 η 在 [YiKCFin](YiKCFin.lagda.md). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKCStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel
open import OCF.Lean.YiKVCheck using (o¹; h₁; c2; g₁)
open import OCF.Lean.YiKVValue using (A1)
open import OCF.Lean.YiKVInst using (a1-lim)
open import OCF.Lean.YiCertFold using (Base; B₀)
open import OCF.Lean.YiKCSem using (o2; W; critA1)
import OCF.Align.EboLeanDef as E
open E using (HC; cof; c1; pred; 𝟏)
open import OCF.Lean.YiMENote using (fsnψ1)
open import OCF.Lean.YiNFOCase using (tB)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
```

## 量化域: 底在标准底之上

```agda
OKB : ∀ {ℓ} → Base ℓ → Set
OKB {ℓ} B = (i : L) (u : i ≤ ℓ) → proj₁ (Ωt i) ⊴ proj₁ (B i u)

⊴-trans : ∀ {S : Sg} {a b c : T S} → a ⊴ b → b ⊴ c → a ⊴ c
⊴-trans p ⊴r     = p
⊴-trans p (⊴◃ d) = ⊴◃ (⊴-◃ p d)

ψ-⊵ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ)
    → proj₁ β ⊴ proj₁ (ψ ℓ o B j w β x)
ψ-⊵ ℓ o B j w β x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ (mono ℓ o B j w β d)

kk : zero ≤ two
kk = ab→≤ (crt o¹ c2)
```

## 陈述

`φA`: 锚是第 2 层 (底 `Ba` 任意), 目标第 1 层的 `φ`. `Φ⁺ c`: 源是孩子 c 的层.

```agda
module St (Ba : Base two) where
  φA : (m : L) → Ok m → Ab zero m → Base m → Tr⁺ one → Tr m → Tr⁺ one
  φA m om U Bm β y = φ two o2 Ba kk one (inc tt self) m om U Bm β y

  φA-⊵ : ∀ {s h} (om : Ok (nd s h)) (f : (c : Ch s) → Ab zero (h c)) (Bm : Base (nd s h)) (β : Tr⁺ one) (y : Tr (nd s h))
       → proj₁ β ⊴ proj₁ (φA (nd s h) om (ab f) Bm β y)
  φA-⊵ om f Bm β y with zl y
  ... | inj₁ refl = ⊴r
  ... | inj₂ d    = ⊴◃ (φm two o2 Ba kk one (inc tt self) _ om (ab f) Bm β d)

  Φ⁺ : (c : Tr zero) → Base (h₁ c) → Tr⁺ one → Tr (h₁ c) → Tr⁺ one
  Φ⁺ c Bm β y = φA (h₁ c) (proj₂ o¹ c) (crt o¹ c) Bm β y

  S : E.T → Tr zero → Set
  S t c = (Bm : Base (h₁ c)) (β : Tr⁺ one) → OKB Bm → M¹ Ω₁ᵗ (proj₁ β)
        → M¹ t (proj₁ (Φ⁺ c Bm β (proj₁ (Ωt (h₁ c)))))
```

## 链下的字面嵌入

后继层号 (孩子层不是地板): 结点不保留, 回灌链的第 1 项 `z₁ = next b` 在孩子层的 Ω 树之上 (b 是底在孩子层的分量), 第 1 行是 `next (φ z₁)`.

```agda
  sucH : ∀ {t s h} (om : Ok (nd sS (λ _ → nd s h))) (f : (c : Ch s) → Ab zero (h c))
    (Bm : Base (nd sS (λ _ → nd s h))) (β : Tr⁺ one)
    → proj₁ (Ωt (nd s h)) ⊴ proj₁ (Bm (nd s h) (inc tt self))
    → M¹ t (proj₁ (φA (nd s h) (proj₂ om tt) (ab f) (λ i u → Bm i (inc tt u)) β (proj₁ (Ωt (nd s h)))))
    → M¹ t (proj₁ (φA (nd sS (λ _ → nd s h)) om (ab (λ _ → ab f)) Bm β (proj₁ (Ωt (nd sS (λ _ → nd s h))))))
  sucH {s = s} {h} om f Bm β ok m =
    mw (G¹.m-right _ (mw (mw m (φm two o2 Ba kk one (inc tt self) (nd s h) (proj₂ om tt) (ab f) (λ i u → Bm i (inc tt u)) β
                                 (⊴-◃ ok (◃l zero)))) (◃l zero))) (◃l 1)
```

ℕ 极限层号: Ω 树的第 n 项字面地是 `up (前 n 项) n (孩子 n 的 Ω 树)` (`cum-form`), 它的 `φ` 是孩子 n 上的 `φ`, 底与起点换成前 n 项的折叠.

```agda
  pre : (g : ℕ → L) → ℕ → Tr (nd sL g)
  pre g zero    = zero
  pre g (suc n) = cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n

  cum-form : (g : ℕ → L) (n : ℕ)
    → cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n ≡ up (pre g n) n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n)))
  cum-form g zero    = refl
  cum-form g (suc n) = refl

  limH : ∀ {t} (g : ℕ → L) (om : Ok (nd sL g)) (f : (n : ℕ) → Ab zero (g n)) (Bm : Base (nd sL g)) (β : Tr⁺ one)
    → OKB Bm → M¹ Ω₁ᵗ (proj₁ β) → (n : ℕ)
    → ((Bm′ : Base (g n)) (β′ : Tr⁺ one) → OKB Bm′ → M¹ Ω₁ᵗ (proj₁ β′)
        → M¹ t (proj₁ (φA (g n) (proj₂ om n) (f n) Bm′ β′ (proj₁ (Ωt (g n))))))
    → M¹ t (proj₁ (φA (nd sL g) om (ab f) Bm β (proj₁ (Ωt (nd sL g)))))
  limH {t} g om f Bm β ok hβ n ih =
    mw (subst (λ Y → M¹ t (proj₁ (φA (nd sL g) om (ab f) Bm β Y))) (sym (cum-form g n))
         (ih (λ i u → ψ (nd sL g) om Bm i (inc n u) (Bm i (inc n u)) (pre g n))
             (φA (nd sL g) om (ab f) Bm β (pre g n))
             (λ i u → ⊴-trans (ok i (inc n u)) (ψ-⊵ (nd sL g) om Bm i (inc n u) (Bm i (inc n u)) (pre g n)))
             (G¹.m⊴ hβ (φA-⊵ om f Bm β (pre g n)))))
       (◃l n)
```

## 零情形: ψ₁(Ω₀) 对一切 c

ψ₁(Ω₀) = ψ₁(1) 的基本列是 Ω₁·n. c = 0 时折叠是 `next (next β)`; c = 1 时是保留的结点, 第一分支同上; c 是更高的后继时取链的第 0 行 `next β`; ℕ 极限取第 0 行.

```agda
  nn : (β : Tr⁺ one) → M¹ Ω₁ᵗ (proj₁ β) → M¹ (ψ₁ᵗ (E.Ωt [])) (proj₁ (next⁺ (next⁺ β)))
  nn β hβ = G¹.m-next (next⁺ β) refl (λ n → fsnψ1 u₁ (𝟏 ∷ []) n refl) (mw hβ (◃l zero))

  n1 : (β : Tr⁺ one) → M¹ Ω₁ᵗ (proj₁ β) → M¹ (ψ₁ᵗ (E.Ωt [])) (proj₁ (next⁺ β))
  n1 β hβ = G¹.m-next β refl (λ n → fsnψ1 u₁ (𝟏 ∷ []) n refl) hβ

  S0 : (c : Tr zero) → S (ψ₁ᵗ (E.Ωt [])) c
  S0 zero              Bm β ok hβ = nn β hβ
  S0 (suc zero)        Bm β ok hβ = mw (nn β hβ) ◃w
  S0 (suc (suc x))     Bm β ok hβ = mw (n1 β hβ) (◃l zero)
  S0 (suc (lim f a))   Bm β ok hβ = mw (n1 β hβ) (◃l zero)
  S0 (lim f a)         Bm β ok hβ = mw (S0 (f 0) (λ i u → Bm i (inc 0 u)) β (λ i u → ok i (inc 0 u)) hβ) (◃l zero)
```

## 松弛情形: 沿第 0 层的 `◃` 向上封闭

```agda
  closS : ∀ {t} (x : Tr zero) → S t x → S t (suc x)
  closS zero      s Bm β ok hβ = mw (s (B₀ zero) β (λ i u → ⊴r) hβ) ◃w
  closS (suc x)   s Bm β ok hβ =
    sucH (proj₂ o¹ (suc (suc x))) (λ _ → crt o¹ x) Bm β (ok _ (inc tt self))
      (s (λ i u → Bm i (inc tt u)) β (λ i u → ok i (inc tt u)) hβ)
  closS (lim f a) s Bm β ok hβ =
    sucH (proj₂ o¹ (suc (lim f a))) (λ n → crt o¹ (f n)) Bm β (ok _ (inc tt self))
      (s (λ i u → Bm i (inc tt u)) β (λ i u → ok i (inc tt u)) hβ)

  clos : ∀ {t x x′} → zero ⊢ x ◃ x′ → S t x → S t x′
  clos (◃s {x = x})           s = closS x s
  clos (◃l {f = f} {a = a} n) s Bm β ok hβ =
    limH (λ k → h₁ (f k)) (proj₂ o¹ (lim f a)) (λ k → crt o¹ (f k)) Bm β ok hβ n s
  clos (◃t d e)             s = clos e (clos d s)
```

## 归纳

极限情形是 `YiKVInst.a1-lim`. 余下后继情形, 作前提 `A1S`.

```agda
  A1S : Set
  A1S = (η : E.T) (x : Tr zero) → cof η ≡ c1 → M⁰ (pred η) x
      → S (ψ₁ᵗ (E.Ωt (pred η))) x → S (ψ₁ᵗ (E.Ωt η)) (suc x)

  ind : A1S → ∀ {η c} → M⁰ η c → S (ψ₁ᵗ (E.Ωt η)) c
  ind s (mz {x = c})          = S0 c
  ind s (m1 {t = η} {x = x} e r) = s η x e r (ind s r)
  ind s (mL {t = η} e h)      = λ Bm β ok hβ → a1-lim η _ e (λ n → ind s (h n) Bm β ok hβ)
  ind s (mΩ {p = ()} _ _ _)
  ind s (mU {c = ()} _ _)
  ind s (mw m d)              = clos d (ind s m)
```

## 判据的归约

标准底与起点在量化域内; `g₁ c` 就是标准底上的 `Φ⁺ c` (类型检查确认).

```agda
open St (B₀ two) public

a1-of : A1S → A1
a1-of s η c l = ind s l (B₀ (h₁ c)) (Ωt one) (λ i u → ⊴r) Mβ₀

critS : A1S → (h : HC tB) → Rt h ≼ readRW W
critS s = critA1 (a1-of s)
```
