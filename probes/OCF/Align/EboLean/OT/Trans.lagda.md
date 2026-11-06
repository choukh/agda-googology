# Lemma 2.4（二）：传递性

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Trans` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

对 `size s + size t + size u` 强归纳。和的层面是字典序的传递性；主元项层面分 φ／G′ 两类：
φ 对 G′ 由 (≺′4)、(≺′11) 直接化到子项；G′ 之间（Ω′、I、ψ_π）用一个统一的「键」：
`lev`（层）与 `fl`（旗），键的字典序恰是 (≺′5)–(≺′10) 及其 (≺′11) 反向；
只有同一 π 的两个 ψ_π 例外——它们按参数比较。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Trans where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OrderProps using (ltLx; lt-list)
open import OCF.Align.EboLean.OT.Unfold
open import OCF.Align.EboLean.OT.Linear

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; <-≤-trans; <⇒≤; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤;
                                       +-mono-<-≤; +-mono-≤-<; +-mono-<; m≤m+n; m≤n+m; m≤n⇒m≤1+n; n≤1+n; +-comm;
                                       <ᵇ⇒<; <⇒<ᵇ; <-trans; <-irrefl; <-asym)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ; ∧-identityʳ; ∧-zeroʳ; not-involutive)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. 工具

```agda
Tr : Tm → Tm → Tm → Set
Tr s t u = lt s t ≡ true → lt t u ≡ true → lt s u ≡ true

IH3 : ℕ → Set
IH3 m = ∀ s t u → size s + size t + size u < m → Tr s t u

-- 测度界
m<≤≤ : ∀ {a b c a′ b′ c′} → a < a′ → b ≤ b′ → c ≤ c′ → a + b + c < a′ + b′ + c′
m<≤≤ h₁ h₂ h₃ = +-mono-<-≤ (+-mono-<-≤ h₁ h₂) h₃
m≤<≤ : ∀ {a b c a′ b′ c′} → a ≤ a′ → b < b′ → c ≤ c′ → a + b + c < a′ + b′ + c′
m≤<≤ h₁ h₂ h₃ = +-mono-<-≤ (+-mono-≤-< h₁ h₂) h₃
m≤≤< : ∀ {a b c a′ b′ c′} → a ≤ a′ → b ≤ b′ → c < c′ → a + b + c < a′ + b′ + c′
m≤≤< h₁ h₂ h₃ = +-mono-≤-< (+-mono-≤ h₁ h₂) h₃

≤′ : ∀ n → n ≤ n
≤′ n = ≤-refl

-- 三项和的置换
p231 : ∀ x y z → y + z + x ≡ x + y + z
p231 = solve 3 (λ x y z → y :+ z :+ x := x :+ y :+ z) refl
p312 : ∀ x y z → z + x + y ≡ x + y + z
p312 = solve 3 (λ x y z → z :+ x :+ y := x :+ y :+ z) refl
p321 : ∀ x y z → z + y + x ≡ x + y + z
p321 = solve 3 (λ x y z → z :+ y :+ x := x :+ y :+ z) refl

-- 把 IH 的界换成置换后的形状
via : ∀ {m n k} → m ≡ n → k < m → k < n
via e h = subst (_ <_) e h

-- lt 的展开（≡ true 版本）
unf : ∀ p q → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → ltP′ p q ≡ true
unf p q h with caseEq (eqP p q)
... | inj₁ e = ⊥-elim (true≢false (trans (sym h) (trans (lt-unfold p q) (if-true e))))
... | inj₂ e = trans (sym (lt-unfold≠ p q e)) h

unf⁻ : ∀ p q → eqP p q ≡ false → ltP′ p q ≡ true → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true
unf⁻ p q e h = trans (lt-unfold≠ p q e) h

-- 结论端：p ≺ q ≺ r 时 p ≠ r
concl : ∀ p q r → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → lt ⟨ q ⟩ ⟨ r ⟩ ≡ true → ltP′ p r ≡ true → lt ⟨ p ⟩ ⟨ r ⟩ ≡ true
concl p q r h₁ h₂ h with caseEq (eqP p r)
... | inj₂ e = unf⁻ p r e h
... | inj₁ e with eqP-sound p r e
...   | refl = ⊥-elim (true≢false (trans (sym h₂) (lt-asym ⟨ p ⟩ ⟨ q ⟩ h₁)))

-- ⪯ 与 ≺ 的拼接（给定相应的 IH 实例）
le-lt : ∀ x y z → Tr x y z → le x y ≡ true → lt y z ≡ true → lt x z ≡ true
le-lt x y z tr h₁ h₂ with ∨-true h₁
... | inj₁ g = tr g h₂
... | inj₂ f with eqT-sound x y f
...   | refl = h₂

lt-le : ∀ x y z → Tr x y z → lt x y ≡ true → le y z ≡ true → lt x z ≡ true
lt-le x y z tr h₁ h₂ with ∨-true h₂
... | inj₁ g = tr h₁ g
... | inj₂ f with eqT-sound y z f
...   | refl = h₁

-- 大小引理（size ⟨ p ⟩ = 1 + sizeP p）
sz-ψa : ∀ a b → size a < size ⟨ psi (ΩR a) b ⟩
sz-ψa a b = s≤s (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤m+n (size a) (size b))))
```

## 2. G′ 项的键

```agda
G : PTm → Set
G p = isG p ≡ true

lev : PTm → Tm
lev (Om a)          = a
lev I               = ⟨ I ⟩
lev (psi (ΩR a) b)  = a
lev (psi IR b)      = ⟨ psi IR b ⟩
lev (phi a b)       = ⟨ phi a b ⟩

fl : PTm → ℕ
fl (Om a)         = 2
fl I              = 0
fl (psi (ΩR a) b) = 1
fl (psi IR b)     = 0
fl (phi a b)      = 0

ltKey : PTm → PTm → Bool
ltKey g h = lt (lev g) (lev h) ∨ (eqT (lev g) (lev h) ∧ (fl g <ᵇ fl h))

-- 同一 π 的两个 ψ
data Same : PTm → PTm → Set where
  same : ∀ π b d → Same (psi π b) (psi π d)

same? : ∀ x y → Same x y ⊎ (Same x y → ⊥)
same? (psi π b) (psi κ d) with caseEq (eqR π κ)
... | inj₁ e with eqR-sound π κ e
...   | refl = inj₁ (same π b d)
same? (psi π b) (psi κ d) | inj₂ e = inj₂ ns
  where
    ns : Same (psi π b) (psi κ d) → ⊥
    ns (same _ _ _) = true≢false (trans (sym (eqR-refl π)) e)
same? (phi _ _) _ = inj₂ (λ ())
same? (Om _)    _ = inj₂ (λ ())
same? I         _ = inj₂ (λ ())
same? (psi _ _) (phi _ _) = inj₂ (λ ())
same? (psi _ _) (Om _)    = inj₂ (λ ())
same? (psi _ _) I         = inj₂ (λ ())

-- 层是自身的 G′ 项：I 与 ψ_I b
data Self : PTm → Set where
  selfI : Self I
  selfψ : ∀ b → Self (psi IR b)

lev≤ : ∀ g → size (lev g) ≤ size ⟨ g ⟩
lev≤ (Om a)         = <⇒≤ (sz-Ω a)
lev≤ I              = ≤-refl
lev≤ (psi (ΩR a) b) = <⇒≤ (sz-ψa a b)
lev≤ (psi IR b)     = ≤-refl
lev≤ (phi a b)      = ≤-refl

lev< : ∀ g → G g → (size (lev g) < size ⟨ g ⟩) ⊎ Self g
lev< (Om a)         _ = inj₁ (sz-Ω a)
lev< I              _ = inj₂ selfI
lev< (psi (ΩR a) b) _ = inj₁ (sz-ψa a b)
lev< (psi IR b)     _ = inj₂ (selfψ b)
```

同一 π 的规则，与键的刻画。

```agda
-- 布尔形状
kΩΩ : ∀ {x y : Bool} → x ≡ false → x ∨ (y ∧ false) ≡ false
kΩΩ refl = ∧-zeroʳ _

x∨y∧false : ∀ {x y : Bool} → x ∨ (y ∧ false) ≡ x
x∨y∧false {x} {y} = trans (cong (x ∨_) (∧-zeroʳ y)) (∨-identityʳ x)

x∨y∧true : ∀ {x y : Bool} → x ∨ (y ∧ true) ≡ x ∨ y
x∨y∧true {x} {y} = cong (x ∨_) (∧-identityʳ y)

sameRule : ∀ π b d → lt ⟨ psi π b ⟩ ⟨ psi π d ⟩ ≡ lt b d
sameRule π b d with caseEq (eqT b d)
... | inj₁ e with eqT-sound b d e
...   | refl = trans (lt-refl-false (psi π b)) (sym (lt-irrefl b))
sameRule (ΩR a) b d | inj₂ e =
  trans (lt-unfold≠ (psi (ΩR a) b) (psi (ΩR a) d) (trans (cong (eqT a a ∧_) e) (∧-zeroʳ (eqT a a))))
        (sh (eqT-refl a) (lt-refl-false (Om a)))
  where
    sh : ∀ {ea oo bd : Bool} → ea ≡ true → oo ≡ false → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ bd
    sh refl refl = ∨-identityʳ _
sameRule IR b d | inj₂ e = trans (lt-unfold≠ (psi IR b) (psi IR d) e) (∨-identityʳ _)

-- Ω′ 对 Ω′ 单独先做（键刻画里要用）
keyΩΩ : ∀ a c → lt ⟨ Om a ⟩ ⟨ Om c ⟩ ≡ ltKey (Om a) (Om c)
keyΩΩ a c with caseEq (eqT a c)
... | inj₁ e with eqT-sound a c e
...   | refl = trans (lt-refl-false (Om a)) (sym (kΩΩ (lt-irrefl a)))
keyΩΩ a c | inj₂ e = trans (lt-unfold≠ (Om a) (Om c) e) (sym (x∨y∧false {lt a c} {eqT a c}))

keyG : ∀ g h → G g → G h → (Same g h → ⊥) → lt ⟨ g ⟩ ⟨ h ⟩ ≡ ltKey g h
keyG (phi _ _) _ () _ _
keyG _ (phi _ _) _ () _
keyG (Om a) (Om c) _ _ _ = keyΩΩ a c
keyG (Om a) I _ _ _ = trans (lt-unfold≠ (Om a) I refl) (sym (x∨y∧false {lt a ⟨ I ⟩} {eqT a ⟨ I ⟩}))
keyG (Om a) (psi (ΩR z) d) _ _ _ =
  trans (lt-unfold≠ (Om a) (psi (ΩR z) d) refl)
        (trans (cong not (cong (_∨ eqT z a) (keyΩΩ z a)))
               (trans (cong not (cong (_∨ eqT z a) (x∨y∧false {lt z a} {eqT z a}))) (trans (sym (lt-lin′ a z)) (sym (x∨y∧false {lt a z} {eqT a z})))))
keyG (Om a) (psi IR d) _ _ _ = trans (lt-unfold≠ (Om a) (psi IR d) refl) (trans (sym (lt-lin′ a ⟨ psi IR d ⟩)) (sym (x∨y∧false {lt a ⟨ psi IR d ⟩} {eqT a ⟨ psi IR d ⟩})))
keyG I (Om c) _ _ _ = trans (lt-unfold≠ I (Om c) refl) (trans (sym (le-lin c ⟨ I ⟩)) (sym (x∨y∧true {lt ⟨ I ⟩ c} {eqT ⟨ I ⟩ c})))
keyG I I _ _ _ = trans (lt-refl-false I) (sym (cong (_∨ false) (lt-irrefl ⟨ I ⟩)))
keyG I (psi (ΩR z) d) _ _ _ =
  trans (lt-unfold≠ I (psi (ΩR z) d) refl)
        (trans (cong not (cong (_∨ false) (lt-unfold≠ (Om z) I refl)))
               (trans (cong not (∨-identityʳ _)) (trans (sym (le-lin z ⟨ I ⟩)) (sym (x∨y∧true {lt ⟨ I ⟩ z} {eqT ⟨ I ⟩ z})))))
keyG I (psi IR d) _ _ _ = sym (∨-identityʳ _)
keyG (psi (ΩR a) b) (Om c) _ _ _ =
  trans (lt-unfold≠ (psi (ΩR a) b) (Om c) refl)
        (trans (cong (_∨ eqT a c) (trans (keyΩΩ a c) (x∨y∧false {lt a c} {eqT a c}))) (sym (x∨y∧true {lt a c} {eqT a c})))
keyG (psi (ΩR a) b) I _ _ _ =
  trans (lt-unfold≠ (psi (ΩR a) b) I refl)
        (trans (cong (_∨ false) (lt-unfold≠ (Om a) I refl)) (trans (∨-identityʳ _) (sym (x∨y∧false {lt a ⟨ I ⟩} {eqT a ⟨ I ⟩}))))
keyG (psi (ΩR a) b) (psi (ΩR c) d) _ _ ns with caseEq (eqT a c)
... | inj₁ e with eqT-sound a c e
...   | refl = ⊥-elim (ns (same (ΩR a) b d))
keyG (psi (ΩR a) b) (psi (ΩR c) d) _ _ ns | inj₂ e =
  trans (lt-unfold≠ (psi (ΩR a) b) (psi (ΩR c) d) (trans (cong (_∧ eqT b d) e) refl))
        (trans (sh e) (trans (cong (_∨ false) (trans (keyΩΩ a c) (x∨y∧false {lt a c} {eqT a c}))) (trans (∨-identityʳ _) (sym (x∨y∧false {lt a c} {eqT a c})))))
  where
    sh : ∀ {ea bd oo : Bool} → ea ≡ false → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ oo ∨ false
    sh refl = refl
keyG (psi (ΩR a) b) (psi IR d) _ _ _ =
  trans (lt-unfold≠ (psi (ΩR a) b) (psi IR d) refl) (keyG (Om a) (psi IR d) refl refl (λ ()))
keyG (psi IR b) (Om c) _ _ _ = trans (lt-unfold≠ (psi IR b) (Om c) refl) (sym (x∨y∧true {lt ⟨ psi IR b ⟩ c} {eqT ⟨ psi IR b ⟩ c}))
keyG (psi IR b) I _ _ _ = trans (lt-unfold≠ (psi IR b) I refl) (sym (trans (∨-identityʳ _) (lt-unfold≠ (psi IR b) I refl)))
keyG (psi IR b) (psi (ΩR c) d) _ _ _ =
  trans (lt-unfold≠ (psi IR b) (psi (ΩR c) d) refl)
        (trans (∨-identityʳ _) (trans (lt-unfold≠ (psi IR b) (Om c) refl) (sym (x∨y∧true {lt ⟨ psi IR b ⟩ c} {eqT ⟨ psi IR b ⟩ c}))))
keyG (psi IR b) (psi IR d) _ _ ns = ⊥-elim (ns (same IR b d))
```

## 3. G′ 之间的传递性

```agda
open import Data.Bool.Base using (T)
open import Data.Unit using (tt)

T⇒≡ : ∀ b → T b → b ≡ true
T⇒≡ true _ = refl

<ᵇ-true : ∀ m n → (m <ᵇ n) ≡ true → m < n
<ᵇ-true m n e = <ᵇ⇒< m n (subst T (sym e) tt)

<-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
<-true {m} {n} h = T⇒≡ (m <ᵇ n) (<⇒<ᵇ h)

∨3-true : ∀ {x y z : Bool} → x ∨ y ∨ z ≡ true → x ≡ true ⊎ y ≡ true ⊎ z ≡ true
∨3-true h with ∨-true h
... | inj₁ a = inj₁ a
... | inj₂ b with ∨-true b
...   | inj₁ c = inj₂ (inj₁ c)
...   | inj₂ d = inj₂ (inj₂ d)

eqP-complete : ∀ {p q} → p ≡ q → eqP p q ≡ true
eqP-complete {p} refl = eqP-refl p

-- 显式参数的布尔引入（隐参从展开后的目标推不出）
∨ˡ : ∀ (x y : Bool) → x ≡ true → x ∨ y ≡ true
∨ˡ x y h = ∨-introˡ {x} {y} h
∨ʳ : ∀ (x y : Bool) → y ≡ true → x ∨ y ≡ true
∨ʳ x y h = ∨-introʳ {x} {y} h
∧ⁱ : ∀ (x y : Bool) → x ≡ true → y ≡ true → x ∧ y ≡ true
∧ⁱ x y p q = ∧-intro {x} {y} p q

-- 键的字典序：层之间的传递性由参数给出
lexKey : ∀ lx ly lz fx fy fz → Tr lx ly lz
       → (lt lx ly ∨ (eqT lx ly ∧ (fx <ᵇ fy))) ≡ true
       → (lt ly lz ∨ (eqT ly lz ∧ (fy <ᵇ fz))) ≡ true
       → (lt lx lz ∨ (eqT lx lz ∧ (fx <ᵇ fz))) ≡ true
lexKey lx ly lz fx fy fz tr h₁ h₂ with ∨-true h₁ | ∨-true h₂
... | inj₁ a | inj₁ b = ∨-introˡ (tr a b)
... | inj₁ a | inj₂ b = ∨-introˡ (subst (λ w → lt lx w ≡ true) (eqT-sound ly lz (proj₁ (∧-true b))) a)
... | inj₂ a | inj₁ b = ∨-introˡ (subst (λ w → lt w lz ≡ true) (sym (eqT-sound lx ly (proj₁ (∧-true a)))) b)
... | inj₂ a | inj₂ b =
  ∨-introʳ (∧-intro (eqT-complete (trans (eqT-sound lx ly (proj₁ (∧-true a))) (eqT-sound ly lz (proj₁ (∧-true b)))))
                    (<-true (<-trans (<ᵇ-true fx fy (proj₂ (∧-true a))) (<ᵇ-true fy fz (proj₂ (∧-true b))))))

-- 三个层全是「自身」时的矛盾
allSelf : ∀ x y z → Self x → Self y → Self z → (Same x y → ⊥) → (Same y z → ⊥) → (Same x z → ⊥)
        → lt (lev x) (lev y) ≡ true → lt (lev y) (lev z) ≡ true → ⊥
allSelf _ _ _ selfI selfI _ _ _ _ l₁ _ = true≢false (trans (sym l₁) (lt-irrefl ⟨ I ⟩))
allSelf _ _ _ selfI (selfψ d) _ _ _ _ l₁ _ = true≢false (trans (sym l₁) (lt-unfold≠ I (psi IR d) refl))
allSelf _ _ _ (selfψ b) selfI selfI _ _ _ _ l₂ = true≢false (trans (sym l₂) (lt-irrefl ⟨ I ⟩))
allSelf _ _ _ (selfψ b) selfI (selfψ f) _ _ ns₃ _ _ = ns₃ (same IR b f)
allSelf _ _ _ (selfψ b) (selfψ d) _ ns₁ _ _ _ _ = ns₁ (same IR b d)

lexTr : ∀ x y z → G x → G y → G z → (Same x y → ⊥) → (Same y z → ⊥) → (Same x z → ⊥)
      → IH3 (size ⟨ x ⟩ + size ⟨ y ⟩ + size ⟨ z ⟩) → Tr (lev x) (lev y) (lev z)
lexTr x y z Gx Gy Gz ns₁ ns₂ ns₃ ih l₁ l₂ with lev< x Gx | lev< y Gy | lev< z Gz
... | inj₁ sx | _ | _ = ih (lev x) (lev y) (lev z) (m<≤≤ sx (lev≤ y) (lev≤ z)) l₁ l₂
... | inj₂ _ | inj₁ sy | _ = ih (lev x) (lev y) (lev z) (m≤<≤ (lev≤ x) sy (lev≤ z)) l₁ l₂
... | inj₂ _ | inj₂ _ | inj₁ sz = ih (lev x) (lev y) (lev z) (m≤≤< (lev≤ x) (lev≤ y) sz) l₁ l₂
... | inj₂ Sx | inj₂ Sy | inj₂ Sz = ⊥-elim (allSelf x y z Sx Sy Sz ns₁ ns₂ ns₃ l₁ l₂)

-- 情形 B（IR）：ψ_I b ≺ ψ_I d ≺ z
caseB-I : ∀ b d z → G z → (Same (psi IR d) z → ⊥) → IH3 (size ⟨ psi IR b ⟩ + size ⟨ psi IR d ⟩ + size ⟨ z ⟩)
        → lt ⟨ psi IR b ⟩ ⟨ psi IR d ⟩ ≡ true → ltKey (psi IR d) z ≡ true → lt ⟨ psi IR b ⟩ ⟨ z ⟩ ≡ true
caseB-I b d z Gz ns ih h₁ k₂ with ∨-true k₂
... | inj₂ e = trans (keyG (psi IR b) z refl Gz ns′)
                     (∨-introˡ (subst (λ w → lt ⟨ psi IR b ⟩ w ≡ true) (eqT-sound ⟨ psi IR d ⟩ (lev z) (proj₁ (∧-true e))) h₁))
  where
    ns′ : Same (psi IR b) z → ⊥
    ns′ (same _ _ f) = ns (same IR d f)
... | inj₁ l with lev< z Gz
...   | inj₁ st = trans (keyG (psi IR b) z refl Gz ns′)
                        (∨-introˡ (ih ⟨ psi IR b ⟩ ⟨ psi IR d ⟩ (lev z)
                                      (m≤≤< (≤′ (size ⟨ psi IR b ⟩)) (≤′ (size ⟨ psi IR d ⟩)) st) h₁ l))
  where
    ns′ : Same (psi IR b) z → ⊥
    ns′ (same _ _ f) = ns (same IR d f)
...   | inj₂ selfI = lt-unfold≠ (psi IR b) I refl
...   | inj₂ (selfψ f) = ⊥-elim (ns (same IR d f))

-- 情形 C（IR）：x ≺ ψ_I d ≺ ψ_I f
caseC-I : ∀ x d f → G x → (Same x (psi IR d) → ⊥) → IH3 (size ⟨ x ⟩ + size ⟨ psi IR d ⟩ + size ⟨ psi IR f ⟩)
        → ltKey x (psi IR d) ≡ true → lt ⟨ psi IR d ⟩ ⟨ psi IR f ⟩ ≡ true → lt ⟨ x ⟩ ⟨ psi IR f ⟩ ≡ true
caseC-I x d f Gx ns ih k₁ h₂ with lev< x Gx
... | inj₁ st = trans (keyG x (psi IR f) Gx refl ns′)
                      (∨-introˡ (ih (lev x) ⟨ psi IR d ⟩ ⟨ psi IR f ⟩
                                    (m<≤≤ st (≤′ (size ⟨ psi IR d ⟩)) (≤′ (size ⟨ psi IR f ⟩))) (l₁ k₁) h₂))
  where
    ns′ : Same x (psi IR f) → ⊥
    ns′ (same _ b _) = ns (same IR b d)
    l₁ : ltKey x (psi IR d) ≡ true → lt (lev x) ⟨ psi IR d ⟩ ≡ true
    l₁ k with ∨-true k
    ... | inj₁ a = a
    ... | inj₂ b = ⊥-elim (true≢false (sym (proj₂ (∧-true b))))
... | inj₂ selfI = ⊥-elim (true≢false (trans (sym (l₁ k₁)) (lt-unfold≠ I (psi IR d) refl)))
  where
    l₁ : ltKey I (psi IR d) ≡ true → lt ⟨ I ⟩ ⟨ psi IR d ⟩ ≡ true
    l₁ k with ∨-true k
    ... | inj₁ a = a
    ... | inj₂ b = ⊥-elim (true≢false (sym b))
... | inj₂ (selfψ b) = ⊥-elim (ns (same IR b d))

-- 情形 D（ΩR）：ψ_{Ω′a} b ≺ y ≺ ψ_{Ω′a} f 不可能
caseD-Ω : ∀ a b y f → G y → ltKey (psi (ΩR a) b) y ≡ true → ltKey y (psi (ΩR a) f) ≡ true → ⊥
caseD-Ω a b y f Gy k₁ k₂ with ∨-true k₁ | ∨-true k₂
... | inj₁ p | inj₁ q = true≢false (trans (sym q) (lt-asym a (lev y) p))
... | inj₁ p | inj₂ q = true≢false (trans (sym (subst (λ w → lt a w ≡ true) (eqT-sound (lev y) a (proj₁ (∧-true q))) p)) (lt-irrefl a))
... | inj₂ p | inj₁ q = true≢false (trans (sym (subst (λ w → lt w a ≡ true) (sym (eqT-sound a (lev y) (proj₁ (∧-true p)))) q)) (lt-irrefl a))
... | inj₂ p | inj₂ q = <-irrefl refl (<-trans (<ᵇ-true 1 (fl y) (proj₂ (∧-true p))) (<ᵇ-true (fl y) 1 (proj₂ (∧-true q))))

-- 情形 D（IR）：ψ_I b ≺ y ≺ ψ_I f
caseD-I : ∀ b y f → G y → (Same (psi IR b) y → ⊥) → IH3 (size ⟨ psi IR b ⟩ + size ⟨ y ⟩ + size ⟨ psi IR f ⟩)
        → ltKey (psi IR b) y ≡ true → ltKey y (psi IR f) ≡ true → lt ⟨ psi IR b ⟩ ⟨ psi IR f ⟩ ≡ true
caseD-I b y f Gy ns ih k₁ k₂ with ∨-true k₁
... | inj₂ e = subst (λ w → lt w ⟨ psi IR f ⟩ ≡ true) (sym (eqT-sound ⟨ psi IR b ⟩ (lev y) (proj₁ (∧-true e)))) (l₂ k₂)
  where
    l₂ : ltKey y (psi IR f) ≡ true → lt (lev y) ⟨ psi IR f ⟩ ≡ true
    l₂ k with ∨-true k
    ... | inj₁ a = a
    ... | inj₂ c = ⊥-elim (true≢false (sym (proj₂ (∧-true c))))
... | inj₁ p with lev< y Gy
...   | inj₁ st = ih ⟨ psi IR b ⟩ (lev y) ⟨ psi IR f ⟩ (m≤<≤ (≤′ (size ⟨ psi IR b ⟩)) st (≤′ (size ⟨ psi IR f ⟩))) p (l₂ k₂)
  where
    l₂ : ltKey y (psi IR f) ≡ true → lt (lev y) ⟨ psi IR f ⟩ ≡ true
    l₂ k with ∨-true k
    ... | inj₁ a = a
    ... | inj₂ c = ⊥-elim (true≢false (sym (proj₂ (∧-true c))))
...   | inj₂ selfI = ⊥-elim (true≢false (trans (sym (l₂ k₂)) (lt-unfold≠ I (psi IR f) refl)))
  where
    l₂ : ltKey I (psi IR f) ≡ true → lt ⟨ I ⟩ ⟨ psi IR f ⟩ ≡ true
    l₂ k with ∨-true k
    ... | inj₁ a = a
    ... | inj₂ c = ⊥-elim (true≢false (sym c))
...   | inj₂ (selfψ d) = ⊥-elim (ns (same IR b d))

transG : ∀ x y z → G x → G y → G z → IH3 (size ⟨ x ⟩ + size ⟨ y ⟩ + size ⟨ z ⟩)
       → lt ⟨ x ⟩ ⟨ y ⟩ ≡ true → lt ⟨ y ⟩ ⟨ z ⟩ ≡ true → lt ⟨ x ⟩ ⟨ z ⟩ ≡ true
transG x y z Gx Gy Gz ih h₁ h₂ with same? x y | same? y z
-- A：全同 π
transG _ _ _ Gx Gy Gz ih h₁ h₂ | inj₁ (same π b d) | inj₁ (same _ _ f) =
  trans (sameRule π b f)
        (ih b d f (m<≤≤ (sz-ψb π b) (<⇒≤ (sz-ψb π d)) (<⇒≤ (sz-ψb π f)))
            (trans (sym (sameRule π b d)) h₁) (trans (sym (sameRule π d f)) h₂))
-- B：x，y 同 π
transG _ _ z Gx Gy Gz ih h₁ h₂ | inj₁ (same (ΩR a) b d) | inj₂ ns =
  trans (keyG (psi (ΩR a) b) z Gx Gz ns′) (trans (sym (keyG (psi (ΩR a) d) z Gy Gz ns)) h₂)
  where
    ns′ : Same (psi (ΩR a) b) z → ⊥
    ns′ (same _ _ f) = ns (same (ΩR a) d f)
transG _ _ z Gx Gy Gz ih h₁ h₂ | inj₁ (same IR b d) | inj₂ ns =
  caseB-I b d z Gz ns ih h₁ (trans (sym (keyG (psi IR d) z Gy Gz ns)) h₂)
-- C：y，z 同 π
transG x _ _ Gx Gy Gz ih h₁ h₂ | inj₂ ns | inj₁ (same (ΩR c) d f) =
  trans (keyG x (psi (ΩR c) f) Gx Gz ns′) (trans (sym (keyG x (psi (ΩR c) d) Gx Gy ns)) h₁)
  where
    ns′ : Same x (psi (ΩR c) f) → ⊥
    ns′ (same _ b _) = ns (same (ΩR c) b d)
transG x _ _ Gx Gy Gz ih h₁ h₂ | inj₂ ns | inj₁ (same IR d f) =
  caseC-I x d f Gx ns ih (trans (sym (keyG x (psi IR d) Gx Gy ns)) h₁) h₂
-- D：x，y 不同 π，y，z 不同 π
transG x y z Gx Gy Gz ih h₁ h₂ | inj₂ ns₁ | inj₂ ns₂ with same? x z
transG _ y _ Gx Gy Gz ih h₁ h₂ | inj₂ ns₁ | inj₂ ns₂ | inj₁ (same (ΩR a) b f) =
  ⊥-elim (caseD-Ω a b y f Gy (trans (sym (keyG (psi (ΩR a) b) y Gx Gy ns₁)) h₁)
                              (trans (sym (keyG y (psi (ΩR a) f) Gy Gz ns₂)) h₂))
transG _ y _ Gx Gy Gz ih h₁ h₂ | inj₂ ns₁ | inj₂ ns₂ | inj₁ (same IR b f) =
  caseD-I b y f Gy ns₁ ih (trans (sym (keyG (psi IR b) y Gx Gy ns₁)) h₁)
                          (trans (sym (keyG y (psi IR f) Gy Gz ns₂)) h₂)
transG x y z Gx Gy Gz ih h₁ h₂ | inj₂ ns₁ | inj₂ ns₂ | inj₂ ns₃ =
  trans (keyG x z Gx Gz ns₃)
        (lexKey (lev x) (lev y) (lev z) (fl x) (fl y) (fl z) (lexTr x y z Gx Gy Gz ns₁ ns₂ ns₃ ih)
                (trans (sym (keyG x y Gx Gy ns₁)) h₁) (trans (sym (keyG y z Gy Gz ns₂)) h₂))
```

## 4. 涉及 φ 的情形

```agda
data Kind : PTm → Set where
  kφ : ∀ a b → Kind (phi a b)
  kG : ∀ g → G g → Kind g

kind : ∀ p → Kind p
kind (phi a b) = kφ a b
kind (psi π b) = kG (psi π b) refl
kind (Om a)    = kG (Om a) refl
kind I         = kG I refl

φG-lt : ∀ a b g → G g → lt ⟨ phi a b ⟩ ⟨ g ⟩ ≡ (lt a ⟨ g ⟩ ∧ lt b ⟨ g ⟩)
φG-lt a b (psi κ d) _ = lt-unfold≠ (phi a b) (psi κ d) refl
φG-lt a b (Om c)    _ = lt-unfold≠ (phi a b) (Om c) refl
φG-lt a b I         _ = lt-unfold≠ (phi a b) I refl

Gφ-lt : ∀ g a b → G g → lt ⟨ g ⟩ ⟨ phi a b ⟩ ≡ not (lt a ⟨ g ⟩ ∧ lt b ⟨ g ⟩)
Gφ-lt (psi κ d) a b _ = lt-unfold≠ (psi κ d) (phi a b) refl
Gφ-lt (Om c)    a b _ = lt-unfold≠ (Om c) (phi a b) refl
Gφ-lt I         a b _ = lt-unfold≠ I (phi a b) refl

φ-inj : ∀ {a b e f} → ⟨ phi a b ⟩ ≡ ⟨ phi e f ⟩ → (a ≡ e) × (b ≡ f)
φ-inj refl = refl , refl

-- φφφ（Veblen 比较的传递性）
φφφ : ∀ a b c d e f → IH3 (size ⟨ phi a b ⟩ + size ⟨ phi c d ⟩ + size ⟨ phi e f ⟩)
    → lt ⟨ phi a b ⟩ ⟨ phi c d ⟩ ≡ true → lt ⟨ phi c d ⟩ ⟨ phi e f ⟩ ≡ true → lt ⟨ phi a b ⟩ ⟨ phi e f ⟩ ≡ true
φφφ a b c d e f ih g₁ g₂ = main (∨3-true (unf (phi a b) (phi c d) g₁)) (∨3-true (unf (phi c d) (phi e f) g₂))
  where
    X = ⟨ phi a b ⟩ ; Y = ⟨ phi c d ⟩ ; Z = ⟨ phi e f ⟩
    fin : ltP′ (phi a b) (phi e f) ≡ true → lt X Z ≡ true
    fin = concl (phi a b) (phi c d) (phi e f) g₁ g₂
    -- IH 实例
    ace = ih a c e (m<≤≤ (sz-φˡ a b) (<⇒≤ (sz-φˡ c d)) (<⇒≤ (sz-φˡ e f)))
    bYZ = ih b Y Z (m<≤≤ (sz-φʳ a b) (≤′ (size Y)) (≤′ (size Z)))
    bYf = ih b Y f (m<≤≤ (sz-φʳ a b) (≤′ (size Y)) (<⇒≤ (sz-φʳ e f)))
    XYf = ih X Y f (m≤≤< (≤′ (size X)) (≤′ (size Y)) (sz-φʳ e f))
    bdZ = ih b d Z (m<≤≤ (sz-φʳ a b) (<⇒≤ (sz-φʳ c d)) (≤′ (size Z)))
    bdf = ih b d f (m<≤≤ (sz-φʳ a b) (<⇒≤ (sz-φʳ c d)) (<⇒≤ (sz-φʳ e f)))
    XdZ = ih X d Z (m≤<≤ (≤′ (size X)) (sz-φʳ c d) (≤′ (size Z)))
    Xdf = ih X d f (m≤<≤ (≤′ (size X)) (sz-φʳ c d) (<⇒≤ (sz-φʳ e f)))
    eca = ih e c a (via (p321 (size X) (size Y) (size Z)) (m<≤≤ (sz-φˡ e f) (<⇒≤ (sz-φˡ c d)) (<⇒≤ (sz-φˡ a b))))
    D₁ = lt a e ∧ lt b Z ; D₂ = eqT a e ∧ lt b f ; D₃ = lt e a ∧ le X f
    fin₁ : lt a e ≡ true → lt b Z ≡ true → lt X Z ≡ true
    fin₁ p q = fin (∨ˡ D₁ (D₂ ∨ D₃) (∧ⁱ (lt a e) (lt b Z) p q))
    fin₂ : eqT a e ≡ true → lt b f ≡ true → lt X Z ≡ true
    fin₂ p q = fin (∨ʳ D₁ (D₂ ∨ D₃) (∨ˡ D₂ D₃ (∧ⁱ (eqT a e) (lt b f) p q)))
    fin₃ : lt e a ≡ true → lt X f ≡ true → lt X Z ≡ true
    fin₃ p q = fin (∨ʳ D₁ (D₂ ∨ D₃) (∨ʳ D₂ D₃ (∧ⁱ (lt e a) (le X f) p (∨ˡ (lt X f) (eqT X f) q))))
    main : ((lt a c ∧ lt b Y) ≡ true) ⊎ ((eqT a c ∧ lt b d) ≡ true) ⊎ ((lt c a ∧ le X d) ≡ true)
         → ((lt c e ∧ lt d Z) ≡ true) ⊎ ((eqT c e ∧ lt d f) ≡ true) ⊎ ((lt e c ∧ le Y f) ≡ true)
         → lt X Z ≡ true
    main (inj₁ h₁) (inj₁ h₂) with ∧-true h₁ | ∧-true h₂
    ... | ac , bY | ce , dZ = fin₁ (ace ac ce) (bYZ bY g₂)
    main (inj₁ h₁) (inj₂ (inj₁ h₂)) with ∧-true h₁ | ∧-true h₂
    ... | ac , bY | ce , df = fin₁ (subst (λ w → lt a w ≡ true) (eqT-sound c e ce) ac) (bYZ bY g₂)
    main (inj₁ h₁) (inj₂ (inj₂ h₂)) with ∧-true h₁ | ∧-true h₂ | tri a e (AT-all a e)
    ... | ac , bY | ec , Yf | inj₁ (ae , _) = fin₁ ae (bYZ bY g₂)
    ... | ac , bY | ec , Yf | inj₂ (inj₁ a≡e) = fin₂ (eqT-complete a≡e) (lt-le b Y f bYf bY Yf)
    ... | ac , bY | ec , Yf | inj₂ (inj₂ (_ , ea)) = fin₃ ea (lt-le X Y f XYf g₁ Yf)
    main (inj₂ (inj₁ h₁)) (inj₁ h₂) with ∧-true h₁ | ∧-true h₂
    ... | ac , bd | ce , dZ = fin₁ (subst (λ w → lt w e ≡ true) (sym (eqT-sound a c ac)) ce) (bdZ bd dZ)
    main (inj₂ (inj₁ h₁)) (inj₂ (inj₁ h₂)) with ∧-true h₁ | ∧-true h₂
    ... | ac , bd | ce , df = fin₂ (eqT-complete (trans (eqT-sound a c ac) (eqT-sound c e ce))) (bdf bd df)
    main (inj₂ (inj₁ h₁)) (inj₂ (inj₂ h₂)) with ∧-true h₁ | ∧-true h₂
    ... | ac , bd | ec , Yf = fin₃ (subst (λ w → lt e w ≡ true) (sym (eqT-sound a c ac)) ec) (lt-le X Y f XYf g₁ Yf)
    main (inj₂ (inj₂ h₁)) (inj₁ h₂) with ∧-true h₁ | ∧-true h₂
    ... | ca , Xd | ce , dZ = le-lt X d Z XdZ Xd dZ
    main (inj₂ (inj₂ h₁)) (inj₂ (inj₁ h₂)) with ∧-true h₁ | ∧-true h₂
    ... | ca , Xd | ce , df = fin₃ (subst (λ w → lt w a ≡ true) (eqT-sound c e ce) ca) (le-lt X d f Xdf Xd df)
    main (inj₂ (inj₂ h₁)) (inj₂ (inj₂ h₂)) with ∧-true h₁ | ∧-true h₂
    ... | ca , Xd | ec , Yf = fin₃ (eca ec ca) (lt-le X Y f XYf g₁ Yf)

-- φφG
φφG : ∀ a b c d g → G g → IH3 (size ⟨ phi a b ⟩ + size ⟨ phi c d ⟩ + size ⟨ g ⟩)
    → lt ⟨ phi a b ⟩ ⟨ phi c d ⟩ ≡ true → lt ⟨ phi c d ⟩ ⟨ g ⟩ ≡ true → lt ⟨ phi a b ⟩ ⟨ g ⟩ ≡ true
φφG a b c d g Gg ih g₁ g₂ = main (∨3-true (unf (phi a b) (phi c d) g₁))
  where
    X = ⟨ phi a b ⟩ ; Y = ⟨ phi c d ⟩ ; W = ⟨ g ⟩
    cg = proj₁ (∧-true (trans (sym (φG-lt c d g Gg)) g₂))
    dg = proj₂ (∧-true (trans (sym (φG-lt c d g Gg)) g₂))
    fin : lt a W ≡ true → lt b W ≡ true → lt X W ≡ true
    fin p q = trans (φG-lt a b g Gg) (∧-intro p q)
    main : ((lt a c ∧ lt b Y) ≡ true) ⊎ ((eqT a c ∧ lt b d) ≡ true) ⊎ ((lt c a ∧ le X d) ≡ true) → lt X W ≡ true
    main (inj₁ h) with ∧-true h
    ... | ac , bY = fin (ih a c W (m<≤≤ (sz-φˡ a b) (<⇒≤ (sz-φˡ c d)) (≤′ (size W))) ac cg)
                        (ih b Y W (m<≤≤ (sz-φʳ a b) (≤′ (size Y)) (≤′ (size W))) bY g₂)
    main (inj₂ (inj₁ h)) with ∧-true h
    ... | ac , bd = fin (subst (λ w → lt w W ≡ true) (sym (eqT-sound a c ac)) cg)
                        (ih b d W (m<≤≤ (sz-φʳ a b) (<⇒≤ (sz-φʳ c d)) (≤′ (size W))) bd dg)
    main (inj₂ (inj₂ h)) with ∧-true h
    ... | ca , Xd = le-lt X d W (ih X d W (m≤<≤ (≤′ (size X)) (sz-φʳ c d) (≤′ (size W)))) Xd dg

-- φGφ
φGφ : ∀ a b g e f → G g → IH3 (size ⟨ phi a b ⟩ + size ⟨ g ⟩ + size ⟨ phi e f ⟩)
    → lt ⟨ phi a b ⟩ ⟨ g ⟩ ≡ true → lt ⟨ g ⟩ ⟨ phi e f ⟩ ≡ true → lt ⟨ phi a b ⟩ ⟨ phi e f ⟩ ≡ true
φGφ a b g e f Gg ih g₁ g₂ with tri ⟨ phi a b ⟩ ⟨ phi e f ⟩ (AT-all ⟨ phi a b ⟩ ⟨ phi e f ⟩)
... | inj₁ (XZ , _) = XZ
... | inj₂ (inj₁ X≡Z) with φ-inj X≡Z
...   | refl , refl = ⊥-elim (true≢false (trans (sym g₁′) ef))
  where
    g₁′ : lt a ⟨ g ⟩ ∧ lt b ⟨ g ⟩ ≡ true
    g₁′ = trans (sym (φG-lt a b g Gg)) g₁
    ef : lt a ⟨ g ⟩ ∧ lt b ⟨ g ⟩ ≡ false
    ef = not-true (trans (sym (Gφ-lt g a b Gg)) g₂)
φGφ a b g e f Gg ih g₁ g₂ | inj₂ (inj₂ (_ , ZX)) = ⊥-elim (main (∨3-true (unf (phi e f) (phi a b) ZX)))
  where
    X = ⟨ phi a b ⟩ ; W = ⟨ g ⟩ ; Z = ⟨ phi e f ⟩
    ag = proj₁ (∧-true (trans (sym (φG-lt a b g Gg)) g₁))
    bg = proj₂ (∧-true (trans (sym (φG-lt a b g Gg)) g₁))
    ef : lt e W ∧ lt f W ≡ false
    ef = not-true (trans (sym (Gφ-lt g e f Gg)) g₂)
    contra : lt e W ≡ true → lt f W ≡ true → ⊥
    contra p q = true≢false (trans (sym (∧-intro p q)) ef)
    perm : size Z + size X + size W ≡ size X + size W + size Z
    perm = p312 (size X) (size W) (size Z)
    main : ((lt e a ∧ lt f X) ≡ true) ⊎ ((eqT e a ∧ lt f b) ≡ true) ⊎ ((lt a e ∧ le Z b) ≡ true) → ⊥
    main (inj₁ h) with ∧-true h
    ... | ea , fX = contra (ih e a W (via perm (m<≤≤ (sz-φˡ e f) (<⇒≤ (sz-φˡ a b)) (≤′ (size W)))) ea ag)
                           (ih f X W (via perm (m<≤≤ (sz-φʳ e f) (≤′ (size X)) (≤′ (size W)))) fX g₁)
    main (inj₂ (inj₁ h)) with ∧-true h
    ... | ea , fb = contra (subst (λ w → lt w W ≡ true) (sym (eqT-sound e a ea)) ag)
                           (ih f b W (via perm (m<≤≤ (sz-φʳ e f) (<⇒≤ (sz-φʳ a b)) (≤′ (size W)))) fb bg)
    main (inj₂ (inj₂ h)) with ∧-true h
    ... | ae , Zb = contra (proj₁ (∧-true Zg)) (proj₂ (∧-true Zg))
      where
        Zg : lt e W ∧ lt f W ≡ true
        Zg = trans (sym (φG-lt e f g Gg)) (le-lt Z b W (ih Z b W (via perm (m≤<≤ (≤′ (size Z)) (sz-φʳ a b) (≤′ (size W))))) Zb bg)

-- GφG
GφG : ∀ g c d h → G g → G h → IH3 (size ⟨ g ⟩ + size ⟨ phi c d ⟩ + size ⟨ h ⟩)
    → lt ⟨ g ⟩ ⟨ phi c d ⟩ ≡ true → lt ⟨ phi c d ⟩ ⟨ h ⟩ ≡ true → lt ⟨ g ⟩ ⟨ h ⟩ ≡ true
GφG g c d h Gg Gh ih g₁ g₂ with tri ⟨ g ⟩ ⟨ h ⟩ (AT-all ⟨ g ⟩ ⟨ h ⟩)
... | inj₁ (gh , _) = gh
... | inj₂ (inj₁ g≡h) = ⊥-elim (true≢false (trans (sym (subst (λ w → lt c w ∧ lt d w ≡ true) (sym g≡h) g₂′)) cd))
  where
    g₂′ : lt c ⟨ h ⟩ ∧ lt d ⟨ h ⟩ ≡ true
    g₂′ = trans (sym (φG-lt c d h Gh)) g₂
    cd : lt c ⟨ g ⟩ ∧ lt d ⟨ g ⟩ ≡ false
    cd = not-true (trans (sym (Gφ-lt g c d Gg)) g₁)
... | inj₂ (inj₂ (_ , hg)) = ⊥-elim (true≢false (trans (sym (∧-intro cg dg)) cd))
  where
    V = ⟨ g ⟩ ; Y = ⟨ phi c d ⟩ ; W = ⟨ h ⟩
    cd : lt c V ∧ lt d V ≡ false
    cd = not-true (trans (sym (Gφ-lt g c d Gg)) g₁)
    ch = proj₁ (∧-true (trans (sym (φG-lt c d h Gh)) g₂))
    dh = proj₂ (∧-true (trans (sym (φG-lt c d h Gh)) g₂))
    perm : size Y + size W + size V ≡ size V + size Y + size W
    perm = p231 (size V) (size Y) (size W)
    cg = ih c W V (via perm (m<≤≤ (sz-φˡ c d) (≤′ (size W)) (≤′ (size V)))) ch hg
    dg = ih d W V (via perm (m<≤≤ (sz-φʳ c d) (≤′ (size W)) (≤′ (size V)))) dh hg

-- Gφφ
Gφφ : ∀ g c d e f → G g → IH3 (size ⟨ g ⟩ + size ⟨ phi c d ⟩ + size ⟨ phi e f ⟩)
    → lt ⟨ g ⟩ ⟨ phi c d ⟩ ≡ true → lt ⟨ phi c d ⟩ ⟨ phi e f ⟩ ≡ true → lt ⟨ g ⟩ ⟨ phi e f ⟩ ≡ true
Gφφ g c d e f Gg ih g₁ g₂ = trans (Gφ-lt g e f Gg) (not-≡false ef)
  where
    V = ⟨ g ⟩ ; Y = ⟨ phi c d ⟩ ; Z = ⟨ phi e f ⟩
    cd : lt c V ∧ lt d V ≡ false
    cd = not-true (trans (sym (Gφ-lt g c d Gg)) g₁)
    perm : size Y + size Z + size V ≡ size V + size Y + size Z
    perm = p231 (size V) (size Y) (size Z)
    contra : lt e V ≡ true → lt f V ≡ true → ⊥
    contra eg fg = main (∨3-true (unf (phi c d) (phi e f) g₂))
      where
        Zg : lt Z V ≡ true
        Zg = trans (φG-lt e f g Gg) (∧-intro eg fg)
        bad : lt c V ≡ true → lt d V ≡ true → ⊥
        bad p q = true≢false (trans (sym (∧-intro p q)) cd)
        main : ((lt c e ∧ lt d Z) ≡ true) ⊎ ((eqT c e ∧ lt d f) ≡ true) ⊎ ((lt e c ∧ le Y f) ≡ true) → ⊥
        main (inj₁ h) with ∧-true h
        ... | ce , dZ = bad (ih c e V (via perm (m<≤≤ (sz-φˡ c d) (<⇒≤ (sz-φˡ e f)) (≤′ (size V)))) ce eg)
                            (ih d Z V (via perm (m<≤≤ (sz-φʳ c d) (≤′ (size Z)) (≤′ (size V)))) dZ Zg)
        main (inj₂ (inj₁ h)) with ∧-true h
        ... | ce , df = bad (subst (λ w → lt w V ≡ true) (sym (eqT-sound c e ce)) eg)
                            (ih d f V (via perm (m<≤≤ (sz-φʳ c d) (<⇒≤ (sz-φʳ e f)) (≤′ (size V)))) df fg)
        main (inj₂ (inj₂ h)) with ∧-true h
        ... | ec , Yf = bad (proj₁ (∧-true Yg)) (proj₂ (∧-true Yg))
          where
            Yg : lt c V ∧ lt d V ≡ true
            Yg = trans (sym (φG-lt c d g Gg)) (le-lt Y f V (ih Y f V (via perm (m≤<≤ (≤′ (size Y)) (sz-φʳ e f) (≤′ (size V))))) Yf fg)
    ef : lt e V ∧ lt f V ≡ false
    ef with caseEq (lt e V ∧ lt f V)
    ... | inj₂ z = z
    ... | inj₁ o = ⊥-elim (contra (proj₁ (∧-true o)) (proj₂ (∧-true o)))

-- φGG
φGG : ∀ a b g h → G g → G h → IH3 (size ⟨ phi a b ⟩ + size ⟨ g ⟩ + size ⟨ h ⟩)
    → lt ⟨ phi a b ⟩ ⟨ g ⟩ ≡ true → lt ⟨ g ⟩ ⟨ h ⟩ ≡ true → lt ⟨ phi a b ⟩ ⟨ h ⟩ ≡ true
φGG a b g h Gg Gh ih g₁ g₂ =
  trans (φG-lt a b h Gh)
        (∧-intro (ih a ⟨ g ⟩ ⟨ h ⟩ (m<≤≤ (sz-φˡ a b) (≤′ (size ⟨ g ⟩)) (≤′ (size ⟨ h ⟩))) ag g₂)
                 (ih b ⟨ g ⟩ ⟨ h ⟩ (m<≤≤ (sz-φʳ a b) (≤′ (size ⟨ g ⟩)) (≤′ (size ⟨ h ⟩))) bg g₂))
  where
    ag = proj₁ (∧-true (trans (sym (φG-lt a b g Gg)) g₁))
    bg = proj₂ (∧-true (trans (sym (φG-lt a b g Gg)) g₁))

-- GGφ
GGφ : ∀ g h e f → G g → G h → IH3 (size ⟨ g ⟩ + size ⟨ h ⟩ + size ⟨ phi e f ⟩)
    → lt ⟨ g ⟩ ⟨ h ⟩ ≡ true → lt ⟨ h ⟩ ⟨ phi e f ⟩ ≡ true → lt ⟨ g ⟩ ⟨ phi e f ⟩ ≡ true
GGφ g h e f Gg Gh ih g₁ g₂ = trans (Gφ-lt g e f Gg) (not-≡false eg-fg)
  where
    V = ⟨ g ⟩ ; W = ⟨ h ⟩ ; Z = ⟨ phi e f ⟩
    ef : lt e W ∧ lt f W ≡ false
    ef = not-true (trans (sym (Gφ-lt h e f Gh)) g₂)
    perm : size Z + size V + size W ≡ size V + size W + size Z
    perm = p312 (size V) (size W) (size Z)
    eg-fg : lt e V ∧ lt f V ≡ false
    eg-fg with caseEq (lt e V ∧ lt f V)
    ... | inj₂ z = z
    ... | inj₁ o = ⊥-elim (true≢false (trans (sym (∧-intro eh fh)) ef))
      where
        eh = ih e V W (via perm (m<≤≤ (sz-φˡ e f) (≤′ (size V)) (≤′ (size W)))) (proj₁ (∧-true o)) g₁
        fh = ih f V W (via perm (m<≤≤ (sz-φʳ e f) (≤′ (size V)) (≤′ (size W)))) (proj₂ (∧-true o)) g₁
```

## 5. 组装

```agda
transP : ∀ p q r → IH3 (size ⟨ p ⟩ + size ⟨ q ⟩ + size ⟨ r ⟩) → Tr ⟨ p ⟩ ⟨ q ⟩ ⟨ r ⟩
transP p q r ih with kind p | kind q | kind r
... | kG x Gx  | kG y Gy  | kG z Gz  = transG x y z Gx Gy Gz ih
... | kφ a b   | kφ c d   | kφ e f   = φφφ a b c d e f ih
... | kφ a b   | kφ c d   | kG g Gg  = φφG a b c d g Gg ih
... | kφ a b   | kG g Gg  | kφ e f   = φGφ a b g e f Gg ih
... | kG g Gg  | kφ c d   | kG h Gh  = GφG g c d h Gg Gh ih
... | kG g Gg  | kφ c d   | kφ e f   = Gφφ g c d e f Gg ih
... | kφ a b   | kG g Gg  | kG h Gh  = φGG a b g h Gg Gh ih
... | kG g Gg  | kG h Gh  | kφ e f   = GGφ g h e f Gg Gh ih

TrL : List PTm → List PTm → List PTm → Set
TrL ps qs rs = ltLx ps qs ≡ true → ltLx qs rs ≡ true → ltLx ps rs ≡ true

listTr : ∀ ps qs rs → (∀ p q r → p ∈ ps → q ∈ qs → r ∈ rs → Tr ⟨ p ⟩ ⟨ q ⟩ ⟨ r ⟩) → TrL ps qs rs
listTr []       []       rs       H ()
listTr []       (q ∷ qs) []       H _ ()
listTr []       (q ∷ qs) (r ∷ rs) H _ _ = refl
listTr (p ∷ ps) []       rs       H ()
listTr (p ∷ ps) (q ∷ qs) []       H _ ()
listTr (p ∷ ps) (q ∷ qs) (r ∷ rs) H h₁ h₂ with caseEq (eqP p q) | caseEq (eqP q r)
... | inj₁ e₁ | inj₁ e₂ =
  trans (if-true (eqP-complete (trans (eqP-sound p q e₁) (eqP-sound q r e₂))))
        (listTr ps qs rs (λ p′ q′ r′ i j k → H p′ q′ r′ (there i) (there j) (there k))
                (trans (sym (if-true e₁)) h₁) (trans (sym (if-true e₂)) h₂))
... | inj₁ e₁ | inj₂ e₂ with eqP-sound p q e₁
...   | refl = trans (if-false e₂) (trans (sym (if-false e₂)) h₂)
listTr (p ∷ ps) (q ∷ qs) (r ∷ rs) H h₁ h₂ | inj₂ e₁ | inj₁ e₂ with eqP-sound q r e₂
...   | refl = trans (if-false e₁) (trans (sym (if-false e₁)) h₁)
listTr (p ∷ ps) (q ∷ qs) (r ∷ rs) H h₁ h₂ | inj₂ e₁ | inj₂ e₂ = trans (if-false e₃) pr
  where
    h₁′ : lt ⟨ p ⟩ ⟨ q ⟩ ≡ true
    h₁′ = trans (sym (if-false e₁)) h₁
    h₂′ : lt ⟨ q ⟩ ⟨ r ⟩ ≡ true
    h₂′ = trans (sym (if-false e₂)) h₂
    pr : lt ⟨ p ⟩ ⟨ r ⟩ ≡ true
    pr = H p q r (here refl) (here refl) (here refl) h₁′ h₂′
    e₃ : eqP p r ≡ false
    e₃ with caseEq (eqP p r)
    ... | inj₂ z = z
    ... | inj₁ o with eqP-sound p r o
    ...   | refl = ⊥-elim (true≢false (trans (sym h₂′) (lt-asym ⟨ p ⟩ ⟨ q ⟩ h₁′)))

step3 : ∀ s t u → IH3 (size s + size t + size u) → Tr s t u
step3 s t u ih h₁ h₂ =
  trans (lt-list s u)
        (listTr (toList s) (toList t) (toList u) H (trans (sym (lt-list s t)) h₁) (trans (sym (lt-list t u)) h₂))
  where
    H : ∀ p q r → p ∈ toList s → q ∈ toList t → r ∈ toList u → Tr ⟨ p ⟩ ⟨ q ⟩ ⟨ r ⟩
    H p q r i j k = transP p q r (λ s′ t′ u′ h →
      ih s′ t′ u′ (<-≤-trans h (+-mono-≤ (+-mono-≤ (∈-size′ s p i) (∈-size′ t q j)) (∈-size′ u r k))))

IH3n : ∀ n → IH3 n
IH3n zero    s t u ()
IH3n (suc n) s t u h = step3 s t u (λ s′ t′ u′ h′ → IH3n n s′ t′ u′ (<-≤-trans h′ (≤-pred h)))

lt-trans : ∀ s t u → lt s t ≡ true → lt t u ≡ true → lt s u ≡ true
lt-trans s t u = IH3n (suc (size s + size t + size u)) s t u ≤-refl
```

## 6. 导出

```agda
≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
≺-trans {x} {y} {z} (lt! h) (lt! g) = lt! (lt-trans x y z h g)

⪯-trans : ∀ {x y z} → x ⪯ y → y ⪯ z → x ⪯ z
⪯-trans {x} {y} {z} (le! h) (le! g) with ∨-true h | ∨-true g
... | inj₁ p | inj₁ q = le! (∨ˡ (lt x z) (eqT x z) (lt-trans x y z p q))
... | inj₁ p | inj₂ q with eqT-sound y z q
...   | refl = le! (∨ˡ (lt x y) (eqT x y) p)
⪯-trans {x} {y} {z} (le! h) (le! g) | inj₂ p | _ with eqT-sound x y p
...   | refl = le! g

≺⪯-trans : ∀ {x y z} → x ≺ y → y ⪯ z → x ≺ z
≺⪯-trans {x} {y} {z} (lt! h) (le! g) with ∨-true g
... | inj₁ q = lt! (lt-trans x y z h q)
... | inj₂ q with eqT-sound y z q
...   | refl = lt! h

⪯≺-trans : ∀ {x y z} → x ⪯ y → y ≺ z → x ≺ z
⪯≺-trans {x} {y} {z} (le! h) (lt! g) with ∨-true h
... | inj₁ p = lt! (lt-trans x y z p g)
... | inj₂ p with eqT-sound x y p
...   | refl = lt! g
```
