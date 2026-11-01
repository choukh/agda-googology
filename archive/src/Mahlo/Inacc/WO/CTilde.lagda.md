# C̃_κ(a) 的分解引理

`u ∈ C̃_κ(a) :⟺ G_κ(u) ≺ a`（Def 2.8 (b)）。G 沿项结构是并（Def 2.7），所以子项也在 C̃_κ(a)；ψ 的情形按 (G4) 的分支。这些直接由定义计算，不进 `OTFacts`。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.CTilde (F : OTFacts) where

open OTFacts F

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.BoolLemmas

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

allLt-++⁻ : ∀ xs {ys b} → allLt (xs ++ ys) b ≡ true → allLt xs b ≡ true × allLt ys b ≡ true
allLt-++⁻ []       e = refl , e
allLt-++⁻ (x ∷ xs) e = let (e₁ , e₂) = ∧-true e ; (l , r) = allLt-++⁻ xs e₂ in ∧-intro e₁ l , r

allLt-++⁺ : ∀ xs {ys b} → allLt xs b ≡ true → allLt ys b ≡ true → allLt (xs ++ ys) b ≡ true
allLt-++⁺ []       l r = r
allLt-++⁺ (x ∷ xs) l r = let (e₁ , e₂) = ∧-true l in ∧-intro e₁ (allLt-++⁺ xs e₂ r)

-- 项参数显式：inC̃ 展开后是 all …，隐参推不出

inC̃-▹ : ∀ κ a b p → inC̃ κ a (b ▹ p) ≡ true → inC̃ κ a b ≡ true × inC̃ κ a ⟨ p ⟩ ≡ true
inC̃-▹ κ a b p g = allLt-++⁻ (G κ b) g

inC̃-φ : ∀ κ a b c → inC̃ κ a ⟨ phi b c ⟩ ≡ true → inC̃ κ a b ≡ true × inC̃ κ a c ≡ true
inC̃-φ κ a b c g = allLt-++⁻ (G κ b) g

inC̃-Ω : ∀ κ a b → inC̃ κ a ⟨ Om b ⟩ ≡ true → inC̃ κ a b ≡ true
inC̃-Ω κ a b g = g

-- κ = I：G_I(ψ_I d) = {d} ∪ G_I(d)
inC̃-ψII : ∀ a d → inC̃ IR a ⟨ psi IR d ⟩ ≡ true → inC̃ IR a d ≡ true × d ≺ a
inC̃-ψII a d g = let (e₁ , e₂) = ∧-true {x = lt d a} g in e₂ , lt! {s = d} {t = a} e₁

-- κ = I，π = Ω′_c ⪰ I：G_I(ψ_π d) = {d} ∪ G_I(π) ∪ G_I(d)
inC̃-ψIΩ : ∀ a c d → I′ ⪯ ⟨ Om c ⟩ → inC̃ IR a ⟨ psi (ΩR c) d ⟩ ≡ true
         → inC̃ IR a ⟨ Om c ⟩ ≡ true × inC̃ IR a d ≡ true × d ≺ a
inC̃-ψIΩ a c d (le! p) g rewrite p =
  let (e₁ , e₂) = ∧-true {x = lt d a} g ; (l , r) = allLt-++⁻ (G IR c) e₂ in l , r , lt! {s = d} {t = a} e₁

-- lt 自反为假
lt-irrefl : ∀ y → lt y y ≡ false
lt-irrefl y with lt y y in e
... | false = refl
... | true  = ⊥-elim (≺-irrefl {y} (lt! {s = y} {t = y} e))

-- ψ_I y ∉ C̃_I(y)：G_I(ψ_I y) ∋ y
ψ∉C̃ : ∀ y → inC̃ IR y ⟨ psi IR y ⟩ ≡ false
ψ∉C̃ y rewrite lt-irrefl y = refl
```

## 界的单调性；ψ_κ b（I ≺ κ）与 b + 1 的 G

```agda
allLt-mono : ∀ xs {b b′} → allLt xs b ≡ true → b ≺ b′ → allLt xs b′ ≡ true
allLt-mono []       e p = refl
allLt-mono (x ∷ xs) e p = let (e₁ , e₂) = ∧-true e in ∧-intro (lt≡ (≺-trans (lt! {s = x} e₁) p)) (allLt-mono xs e₂ p)

-- κ = Ω′_c ⪰ I：G_I(ψ_κ b) = {b} ∪ G_I(κ) ∪ G_I(b)（反向）
inC̃-ψIΩ⁺ : ∀ a c d → I′ ⪯ ⟨ Om c ⟩ → inC̃ IR a ⟨ Om c ⟩ ≡ true → inC̃ IR a d ≡ true → d ≺ a
          → inC̃ IR a ⟨ psi (ΩR c) d ⟩ ≡ true
inC̃-ψIΩ⁺ a c d (le! p) gκ gd (lt! d≺a) rewrite p = ∧-intro d≺a (allLt-++⁺ (G IR c) gκ gd)

-- G_I(ψ_I d) = {d} ∪ G_I(d)（反向）
inC̃-ψII⁺ : ∀ a d → inC̃ IR a d ≡ true → d ≺ a → inC̃ IR a ⟨ psi IR d ⟩ ≡ true
inC̃-ψII⁺ a d gd (lt! d≺a) = ∧-intro d≺a gd

-- G_κ(b ▹ 1) = G_κ(b)
inC̃-▹1 : ∀ κ a b → inC̃ κ a b ≡ true → inC̃ κ a (b ▹ phi zer zer) ≡ true
inC̃-▹1 κ a b g = allLt-++⁺ (G κ b) g refl
```
