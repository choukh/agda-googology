# 比较表那一行: 折叠

> 定义候选（摆脱侧，证据一类），未经作者采纳. 复制 `YiRWFold`, 只换 "Ω 形状层号, 目标经指定孩子 c′, 嵌入在孩子 c" 一行: 证据 `Rb` 是孩子层号上一张可缺的比较表; 表里有字面路径时按它二选一 (在孩子 c 的层上折, 或嵌进孩子 c′ 的层再折), 没有时逐字是原行 (`row-no`).
> 底、保留判定、结点从 `YiRWFold` 导入, 没有改. 来源: 附件 YiRC-RCD 的临时原型 (台账 U22), 代码照搬. 塔第 1 项的表 `rb1` 只在两个孩子都是字面自然数时给出比较.
> 不否定什么; 值的验收在 [YiTBCrit](YiTBCrit.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTBRow where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; kp; kp⁼; node⁺; nodeLe)
```

## 证据: 孩子层号上可缺的比较表

```agda
RbS : (s : Sh) → (Ch s → L) → Set
RbS sS     h = ⊤
RbS sL     g = ⊤
RbS (sΩ k) h = (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))

Rb : L → Set
Rb zero     = ⊤
Rb (nd s h) = RbS s h × ((c : Ch s) → Rb (h c))

rbS-no : (s : Sh) (h : Ch s → L) → RbS s h
rbS-no sS     h = tt
rbS-no sL     h = tt
rbS-no (sΩ k) h = λ _ _ → nothing

rb-no : (ℓ : L) → Rb ℓ
rb-no zero     = tt
rb-no (nd s h) = rbS-no s h , λ c → rb-no (h c)

dW : {A B X : Set} → Maybe (A ⊎ B) → (A → X) → (B → X) → X → X
dW (just (inj₁ a)) F G H = F a
dW (just (inj₂ b)) F G H = G b
dW nothing         F G H = H

dW-ind : {A B X : Set} (Q : X → Set) (m : Maybe (A ⊎ B)) {F : A → X} {G : B → X} {H : X}
       → ((a : A) → Q (F a)) → ((b : B) → Q (G b)) → Q H → Q (dW m F G H)
dW-ind Q (just (inj₁ a)) hF hG hH = hF a
dW-ind Q (just (inj₂ b)) hF hG hH = hG b
dW-ind Q nothing         hF hG hH = hH

dW-ind₂ : {A B X : Set} (Q : X → X → Set) (m : Maybe (A ⊎ B)) {F F′ : A → X} {G G′ : B → X} {H H′ : X}
        → ((a : A) → Q (F a) (F′ a)) → ((b : B) → Q (G b) (G′ b)) → Q H H′ → Q (dW m F G H) (dW m F′ G′ H′)
dW-ind₂ Q (just (inj₁ a)) hF hG hH = hF a
dW-ind₂ Q (just (inj₂ b)) hF hG hH = hG b
dW-ind₂ Q nothing         hF hG hH = hH

rb : {E X : Set} → Maybe E → (E → X) → X → X
rb (just e) F G = F e
rb nothing  F G = G

rb-ind : {E X : Set} (Q : X → Set) (m : Maybe E) {F : E → X} {G : X}
       → ((e : E) → Q (F e)) → Q G → Q (rb m F G)
rb-ind Q (just e) hF hG = hF e
rb-ind Q nothing  hF hG = hG

rb-ind₂ : {E X : Set} (Q : X → X → Set) (m : Maybe E) {F F′ : E → X} {G G′ : X}
        → ((e : E) → Q (F e) (F′ e)) → Q G G′ → Q (rb m F G) (rb m F′ G′)
rb-ind₂ Q (just e) hF hG = hF e
rb-ind₂ Q nothing  hF hG = hG
```

## 折叠与单调

```agda
mutual
  ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ ℓ o r B j w β zero      = β
  ψ ℓ o r B j w β (suc x)   = next⁺ (ψ ℓ o r B j w β x)
  ψ ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o r B j w β (f n)) (λ n → mono ℓ o r B j w β (a n))
  ψ ℓ o r B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o r B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y
  ψ (nd s h) o r B j (inu ws) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
  ψ (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
  ψ (nd sS h) o r B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
  ψ (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o r B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = dW (proj₁ r c c′)
    (λ u → ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
             (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
    (λ u → ψ (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
             (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
    (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

  mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)
  mono ℓ o r B j w β ◃s           = ◃l zero
  mono ℓ o r B j w β (◃l n)       = ◃l n
  mono ℓ o r B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) e
  mono (nd s h) o r B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) e
  mono (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) e
  mono (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) e
  mono (nd sL g) o r B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) e)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
    dW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₁ r c c′)
      (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
      (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (proj₂ (emb (h c′) (proj₂ o c′) u (y , e))))
      (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))
  mono (nd s h) o r B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) d
  mono (nd s h) o r B j (inu ws) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) d
  mono (nd (sΩ k) h) o r B j (ink v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) d
  mono (nd sS h) o r B j (inc c′ v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) d
  mono (nd sL g) o r B j (inc n v) β (◃c x m d) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) d)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c d) =
    dW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r c c′)
      (λ u → mono (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) d)
      (λ u → mono (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (emb-mono (h c′) (proj₂ o c′) u d))
      (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
  mono ℓ o r B j w β (◃t d d′) = ◃t (mono ℓ o r B j w β d) (mono ℓ o r B j w β d′)
```

## 行的形状

```agda
ψ₀ʳ : (ℓ : L) → Ok ℓ → Rb ℓ → Tr ℓ → Tr⁺ zero
ψ₀ʳ ℓ o r = ψ ℓ o r (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

row-tb : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e)
  ≡ dW (proj₁ r c c′)
      (λ u → ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
      (λ u → ψ (h c′) (proj₂ o c′) (proj₂ r c′) (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x) j v
               (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
      (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ₀ʳ (h c) (proj₂ o c) (proj₂ r c) y)
row-tb k h o r B j c′ v β x c y e = refl

row-no : ∀ k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → ψ (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up x c y e)
  ≡ ψ (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β x ⊞ ψ₀ʳ (h c) (proj₂ o c) (rc c) y
row-no k h o rc B j c′ v β x c y e = refl
```

## 塔第 1 项的表

两个孩子都是字面的自然数时按 ℕ 比较 (`way`), 否则没有.

```agda
nat : ℕ → Tr zero
nat zero    = zero
nat (suc n) = suc (nat n)

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

fn : ℕ → L
fn n = h₁ (nat n)

data IsNat : Tr zero → Set where
  isn : (n : ℕ) → IsNat (nat n)

isNat : (c : Tr zero) → Maybe (IsNat c)
isNat zero      = just (isn 0)
isNat (suc c) with isNat c
... | just (isn n) = just (isn (suc n))
... | nothing      = nothing
isNat (lim f a) = nothing

tb′ : ∀ {c c′} → Maybe (IsNat c) → Maybe (IsNat c′) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
tb′ (just (isn n)) (just (isn m)) = just (way fn (λ i → inc tt self) m n)
tb′ _ _ = nothing

tb : (c c′ : Tr zero) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
tb c c′ = tb′ (isNat c) (isNat c′)

rb1 : Rb (tw 1)
rb1 = tb , λ c → rb-no (h₁ c)

isNat-nat : ∀ n → isNat (nat n) ≡ just (isn n)
isNat-nat zero    = refl
isNat-nat (suc n) rewrite isNat-nat n = refl

tb-nat : ∀ n m → tb (nat n) (nat m) ≡ just (way fn (λ i → inc tt self) m n)
tb-nat n m rewrite isNat-nat n | isNat-nat m = refl
```
