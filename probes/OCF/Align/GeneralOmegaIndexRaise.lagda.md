# 原Ω层地板在任意前缀后提供整ω重复

Raises是树形证书：后继、Ω根或可选的ℕ分量。它不涉及标签、值判等，
也不假设run保持右加法。原ΩL及其右加任意层的floor可给该证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexRaise where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.GeneralOmegaIndexRun using (context-prefix)

data Raises {S : KS} : HB S → Set where
  successor : ∀ {a} → Raises (hs a)
  omega : ∀ {κ g} → Raises (hΩ κ g)
  limit : ∀ {f} n → Raises (f n) → Raises (hl f)
raises-add : ∀ {S} (a : HB S) {b} → Raises b → Raises (a ⊞ b)
raises-add a successor = successor
raises-add a omega = omega
raises-add a (limit n p) = limit n (raises-add a p)
raises-ι : ∀ {I F} i {a : HB (F i)} → Raises a → Raises (ι {I} {F} i a)
raises-ι i successor = successor
raises-ι i omega = omega
raises-ι i (limit n p) = limit n (raises-ι i p)

data FloorShape : LH → Set where
  successor : ∀ {x} → FloorShape (ls x)
  omega : ∀ {k g} → FloorShape (lΩ k g)
  limit : ∀ {f} n → FloorShape (f n) → FloorShape (ll f)
Ω-shape : ∀ x → FloorShape (ΩL x)
Ω-shape lz = successor
Ω-shape (ls x) = omega
Ω-shape (ll f) = limit 0 (Ω-shape (f 0))
Ω-shape (lΩ k g) = omega
plus-shape : ∀ {x} → FloorShape x → ∀ y → FloorShape (x ⊕L y)
plus-shape p lz = p
plus-shape p (ls y) = successor
plus-shape p (ll f) = limit 0 (plus-shape p (f 0))
plus-shape p (lΩ k g) = omega

floor-raises : ∀ {x} → FloorShape x → Raises (flL x)
sum-raises : ∀ f n → FloorShape (f n) → Raises (ΣF f n)
floor-raises successor = omega
floor-raises omega = omega
floor-raises (limit {f} n p) = limit n (sum-raises f n p)
sum-raises f zero p = raises-ι zero (floor-raises p)
sum-raises f (suc n) p = raises-add (ΣF f n) (raises-ι (suc n) (floor-raises p))

repeat-mono : ∀ {a b : Cd} → a ≤ᵛ b → Ops.repeat S⊥ a ≤ᵛ Ops.repeat S⊥ b
repeat-mono {a} {b} p = l≤ (λ n → ≤l n (parts n))
  where
  parts : ∀ n → Ops.partial S⊥ (λ _ → a) n ≤ᵛ Ops.partial S⊥ (λ _ → b) n
  parts zero = p
  parts (suc n) = add-mono (parts n) p

repeat-context : ∀ x (A B : HB (Lv x)) {C} → Raises C →
  Ops.repeat S⊥ (run x (A ⊞ B)) ≤ᵛ run x (A ⊞ (B ⊞ C))
repeat-context x A B (successor {a}) = repeat-mono (context-prefix x A B a)
repeat-context x A B (limit n p) = ≤l n (repeat-context x A B p)
repeat-context x A B (omega {κ} {g}) = l≤ (λ n → ≤l n (parts n))
  where
  H : Cd → Cd
  H d = run x (A ⊞ (B ⊞ g (code x κ d)))
  each : ∀ d → run x (A ⊞ B) ≤ᵛ H d
  each d = context-prefix x A B (g (code x κ d))
  parts : ∀ n → Ops.partial S⊥ (λ _ → run x (A ⊞ B)) n ≤ᵛ
    Ops.partial S⊥ (λ j → H (chain H j)) n
  parts zero = each (chain H zero)
  parts (suc n) = add-mono (parts n) (each (chain H (suc n)))
```

Ω-shape和plus-shape给所有实际ΩL前缀的非空实例；repeat-context对
原Ω对角的全部分和成立。一般g=0并无此floor证书，不在结论域内。
