# 换一步: 第 0 层的关系给层的嵌入

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md). `ext`: 第 0 层的 `Rel x x′`, 加上基的嵌入, 给 `sum b x` 到 `sum b′ x′` 的前驱的保序对应. 第 0 层的树只有后继和 $\omega$-极限, 所以 `Rel` 的每一条都对应一个字面的放法: 和是累加的, 块放得下. 对应是一个关系 (`Gr`), 不是函数: 极限处取并, 不用谈相干.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloEmb where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ≪∘)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; sum; pt; sum-fst)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊲→≤; irr)
open import OCF.Align.AddCloRel using (Rel; r0; r1; r⨾; rf; rs; rp; rn; rt; ri)
```

## §1 对应

`Gr a a′`: 关系 `G` 覆盖 $a$ 的每个前驱, 落在 $a'$ 的前驱上, 在值上保严格序和弱序. 序只看值, 所以和层的证明无关.

```agda
record Gr (a a′ : A) : Set₁ where
  field
    G   : A → A → Set
    tot : ∀ {t} → t ≪ a → Σ A (λ t′ → (t′ ≪ a′) × G t t′)
    bl  : ∀ {t t′} → G t t′ → asuc t ≤ a
    br  : ∀ {t t′} → G t t′ → asuc t′ ≤ a′
    lt  : ∀ {t t′ d d′} → G t t′ → G d d′ → asuc t ≤ d → asuc t′ ≤ d′
    le  : ∀ {t t′ d d′} → G t t′ → G d d′ → t ≤ d → t′ ≤ d′
open Gr

-- 从 G₀ 扩到 G₁: 老的留下; 新的都不低于基
record Ext {b b′ a a′} (P₀ : Gr b b′) (P : Gr a a′) : Set where
  field
    inc : ∀ {t t′} → G P₀ t t′ → G P t t′
    hi  : ∀ {t t′} → G P t t′ → G P₀ t t′ ⊎ (b ≤ t × b′ ≤ t′)
open Ext

Ex-refl : ∀ {b b′} (P₀ : Gr b b′) → Ext P₀ P₀
Ex-refl P₀ = record { inc = λ g → g ; hi = inj₁ }

Ex-tr : ∀ {b b′ a a′ e e′} {P₀ : Gr b b′} {P₁ : Gr a a′} {P₂ : Gr e e′} → b ≤ a → b′ ≤ a′ → Ext P₀ P₁ → Ext P₁ P₂ → Ext P₀ P₂
Ex-tr {P₀ = P₀} {P₁} {P₂} ba ba′ E₁ E₂ = record { inc = λ g → inc E₂ (inc E₁ g) ; hi = go }
  where
  go : ∀ {t t′} → G P₂ t t′ → G P₀ t t′ ⊎ (_ ≤ t × _ ≤ t′)
  go g with hi E₂ g
  ... | inj₁ g₁ = hi E₁ g₁
  ... | inj₂ (p , q) = inj₂ (≤-trans ba p , ≤-trans ba′ q)

-- 右边变大, 字面的第一位置
wk : ∀ {a a′ a″} → a′ ⊲ a″ → Gr a a′ → Gr a a″
wk s P = record
  { G = G P
  ; tot = λ r → let t′ , q , g = tot P r in t′ , ≪∘ q s , g
  ; bl = bl P
  ; br = λ g → ≤-trans (br P g) (⊲→≤ s)
  ; lt = lt P
  ; le = le P }

wkE : ∀ {b b′ a a′ a″} (s : a′ ⊲ a″) {P₀ : Gr b b′} {P : Gr a a′} → Ext P₀ P → Ext P₀ (wk s P)
wkE s E = record { inc = inc E ; hi = hi E }
```

## §2 每一条关系都有放法

```agda
step₁ : ∀ {b b′} → Gr b b′ → Gr (asuc b) (asuc b′)
step₁ {b} {b′} P = record { G = G′ ; tot = T ; bl = BL ; br = BR ; lt = LT ; le = LE }
  where
  G′ : A → A → Set
  G′ t t′ = G P t t′ ⊎ ((t ≡ b) × (t′ ≡ b′))
  T : ∀ {t} → t ≪ asuc b → Σ A (λ t′ → (t′ ≪ asuc b′) × G′ t t′)
  T C.zero = b′ , C.zero , inj₂ (refl , refl)
  T (C.suc r) = let t′ , q , g = tot P r in t′ , C.suc q , inj₁ g
  BL : ∀ {t t′} → G′ t t′ → asuc t ≤ asuc b
  BL (inj₁ g) = ≤-suc (bl P g)
  BL (inj₂ (refl , refl)) = ≤-refl _
  BR : ∀ {t t′} → G′ t t′ → asuc t′ ≤ asuc b′
  BR (inj₁ g) = ≤-suc (br P g)
  BR (inj₂ (refl , refl)) = ≤-refl _
  LT : ∀ {t t′ d d′} → G′ t t′ → G′ d d′ → asuc t ≤ d → asuc t′ ≤ d′
  LT (inj₁ g) (inj₁ h) o = lt P g h o
  LT (inj₁ g) (inj₂ (refl , refl)) o = br P g
  LT (inj₂ (refl , refl)) (inj₁ h) o = ⊥-elim (irr b (≤-trans o (≤-trans (≤-suc (≤-refl _)) (bl P h))))
  LT (inj₂ (refl , refl)) (inj₂ (refl , refl)) o = ⊥-elim (irr b o)
  LE : ∀ {t t′ d d′} → G′ t t′ → G′ d d′ → t ≤ d → t′ ≤ d′
  LE (inj₁ g) (inj₁ h) o = le P g h o
  LE (inj₁ g) (inj₂ (refl , refl)) o = ≤-trans (≤-suc (≤-refl _)) (br P g)
  LE (inj₂ (refl , refl)) (inj₁ h) o = ⊥-elim (irr b (≤-trans (s≤ o) (bl P h)))
  LE (inj₂ (refl , refl)) (inj₂ (refl , refl)) o = ≤-refl _

step₁E : ∀ {b b′} (P : Gr b b′) → Ext P (step₁ P)
step₁E P = record { inc = inj₁ ; hi = go }
  where
  go : ∀ {t t′} → G (step₁ P) t t′ → G P t t′ ⊎ (_ ≤ t × _ ≤ t′)
  go (inj₁ g) = inj₁ g
  go (inj₂ (refl , refl)) = inj₂ (≤-refl _ , ≤-refl _)

-- 极限: 取并
module Lim {f f′ : ℕ → A} (P : ∀ n → Gr (f n) (f′ n)) (E : ∀ n → Ext (P n) (P (suc n)))
           (ff : ∀ n → f n ⊲ f (suc n)) (gg : ∀ n → f′ n ⊲ f′ (suc n)) where

  up : ∀ {n} k {t t′} → G (P n) t t′ → G (P (k + n)) t t′
  up zero g = g
  up (suc k) g = inc (E (k + _)) (up k g)

  swap : ∀ n m → n + m ≡ m + n
  swap zero m = sym′ m
    where
    sym′ : ∀ m → m ≡ m + 0
    sym′ zero = refl
    sym′ (suc m) = cong suc (sym′ m)
  swap (suc n) m = trans′ (cong suc (swap n m)) (s+ m n)
    where
    trans′ : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
    trans′ refl q = q
    s+ : ∀ m n → suc (m + n) ≡ m + suc n
    s+ zero n = refl
    s+ (suc m) n = cong suc (s+ m n)

  P∞ : Gr (alim f) (alim f′)
  P∞ = record
    { G = λ t t′ → Σ ℕ (λ n → G (P n) t t′)
    ; tot = T
    ; bl = λ { (n , g) → ≤l n (bl (P n) g) }
    ; br = λ { (n , g) → ≤l n (br (P n) g) }
    ; lt = λ { {t} {t′} {d} {d′} (n , g) (m , h) o → lt (P (m + n)) (up m g) (sb m n (up n h)) o }
    ; le = λ { {t} {t′} {d} {d′} (n , g) (m , h) o → le (P (m + n)) (up m g) (sb m n (up n h)) o }
    }
    where
    T : ∀ {t} → t ≪ alim f → Σ A (λ t′ → (t′ ≪ alim f′) × Σ ℕ (λ n → G (P n) t t′))
    T (C.lim n r) = let t′ , q , g = tot (P n) r in t′ , C.lim n q , n , g
    sb : ∀ m n {t t′} → G (P (n + m)) t t′ → G (P (m + n)) t t′
    sb m n {t} {t′} = subst (λ i → G (P i) t t′) (swap n m)

  P∞E : Ext (P 0) P∞
  P∞E = record { inc = λ g → 0 , g ; hi = go }
    where
    lowf : ∀ n → f 0 ≤ f n
    lowf zero = ≤-refl _
    lowf (suc n) = ≤-trans (lowf n) (⊲→≤ (ff n))
    lowg : ∀ n → f′ 0 ≤ f′ n
    lowg zero = ≤-refl _
    lowg (suc n) = ≤-trans (lowg n) (⊲→≤ (gg n))
    go₀ : ∀ n {t t′} → G (P n) t t′ → G (P 0) t t′ ⊎ (f 0 ≤ t × f′ 0 ≤ t′)
    go₀ zero g = inj₁ g
    go₀ (suc n) g with hi (E n) g
    ... | inj₁ g₁ = go₀ n g₁
    ... | inj₂ (p , q) = inj₂ (≤-trans (lowf n) p , ≤-trans (lowg n) q)
    go : ∀ {t t′} → Σ ℕ (λ n → G (P n) t t′) → G (P 0) t t′ ⊎ (f 0 ≤ t × f′ 0 ≤ t′)
    go (n , g) = go₀ n g
```

## §3 主定理

```agda
Ext-base : ∀ {b b′ b″ a a′} (s : b′ ⊲ b″) {P₀ : Gr b b′} {P : Gr a a′} → Ext (wk s P₀) P → Ext P₀ P
Ext-base s {P₀} {P} E = record { inc = inc E ; hi = go }
  where
  go : ∀ {t t′} → G P t t′ → G P₀ t t′ ⊎ (_ ≤ t × _ ≤ t′)
  go g with hi E g
  ... | inj₁ g₁ = inj₁ g₁
  ... | inj₂ (p , q) = inj₂ (p , ≤-trans (⊲→≤ s) q)

pt-lo : ∀ (d : ℕ → D azero) b k → b ≤ pt b d k
pt-lo d b zero = ≤-refl b
pt-lo d b (suc k) = ≤-trans (pt-lo d b k) (⊲→≤ (sum-fst (pt b d k) (d k)))

base-up : ∀ (d : ℕ → D azero) (k : ℕ) {b b′} (P₀ : Gr b b′) → Σ (Gr b (pt b′ d k)) (Ext P₀)
base-up d zero P₀ = P₀ , Ex-refl P₀
base-up d (suc k) {b′ = b′} P₀ with base-up d k P₀
... | P , E = wk (sum-fst (pt b′ d k) (d k)) P , record { inc = inc E ; hi = go }
  where
  go : ∀ {t t′} → G P t t′ → G P₀ t t′ ⊎ (_ ≤ t × b′ ≤ t′)
  go g = hi E g

ext : ∀ {x x′} → Rel azero x x′ → ∀ {b b′} (P₀ : Gr b b′) → Σ (Gr (sum b x) (sum b′ x′)) (Ext P₀)
ext-pt : ∀ {d d′} → (∀ n → Rel azero (d n) (d′ n)) → ∀ {b b′} (P₀ : Gr b b′) → ∀ n → Σ (Gr (pt b d n) (pt b′ d′ n)) (Ext P₀)

ext-pt p P₀ zero = P₀ , Ex-refl P₀
ext-pt {d} {d′} p {b} {b′} P₀ (suc n) with ext-pt p P₀ n
... | P , E with ext (p n) P
...   | P′ , E′ = P′ , Ex-tr (pt-lo d b n) (pt-lo d′ b′ n) E E′

ext r0 {b′ = b′} P₀ = wk (sum-fst b′ _) P₀ , wkE _ (Ex-refl P₀)
ext r1 P₀ = step₁ P₀ , step₁E P₀
ext (r⨾ {x} {x′} d e) {b} {b′} P₀ with ext d P₀
... | P₁ , E₁ with ext e P₁
...   | P₂ , E₂ = P₂ , Ex-tr (⊲→≤ (sum-fst b x)) (⊲→≤ (sum-fst b′ x′)) E₁ E₂
ext (rf {x′ = x′} {y = y} d) {b′ = b′} P₀ with ext d P₀
... | P , E = wk (sum-fst (sum b′ x′) y) P , wkE _ E
ext (rs {x′ = x′} d) {b′ = b′} P₀ with ext d (wk (sum-fst b′ x′) P₀)
... | P , E = P , Ext-base (sum-fst b′ x′) E
ext (rp {d} {d′} p) {b} {b′} P₀ = M.P∞ , M.P∞E
  where
  module M = Lim (λ n → proj₁ (ext-pt p P₀ n)) (λ n → proj₂ (ext (p n) (proj₁ (ext-pt p P₀ n))))
               (λ n → sum-fst (pt b d n) (d n)) (λ n → sum-fst (pt b′ d′ n) (d′ n))
ext (rn {d = d} k e) {b} {b′} P₀ with base-up d k P₀
... | Q , EQ with ext e Q
...   | P , E = wk (C.lim (suc k) C.self) P , wkE _ (Ex-tr (≤-refl b) (pt-lo d b′ k) EQ E)
ext (rt {x = x} {y = y} {d = d} k e e′) {b} {b′} P₀ with base-up d k P₀
... | Q , EQ with ext e Q
...   | P , E with ext e′ P
...     | P′ , E′ = P″ , record { inc = inc E₃ ; hi = hi E₃ }
  where
  d″ : ℕ → D azero
  d″ m = d (suc (m + k))
  eqP : ∀ m → pt (pt b′ d (suc k)) d″ m ≡ pt b′ d (suc (m + k))
  eqP zero = refl
  eqP (suc m) = cong (λ a → sum a (d″ m)) (eqP m)
  P″ : Gr (sum (sum b x) y) (alim (pt b′ d))
  P″ = record
    { G = G P′
    ; tot = λ r → T (tot P′ r)
    ; bl = bl P′
    ; br = λ g → ≤-trans (br P′ g) (l≤ (λ m → ≤l (suc (m + k)) (subst (λ a → pt (pt b′ d (suc k)) d″ m ≤ a) (eqP m) (≤-refl _))))
    ; lt = lt P′
    ; le = le P′ }
    where
    T : ∀ {t} → Σ A (λ t′ → (t′ ≪ alim (pt (pt b′ d (suc k)) d″)) × G P′ t t′) → Σ A (λ t′ → (t′ ≪ alim (pt b′ d)) × G P′ t t′)
    T (t′ , C.lim m q , g) = t′ , C.lim (suc (m + k)) (subst (λ a → t′ ≪ a) (eqP m) q) , g
  E₃ = Ex-tr (⊲→≤ (sum-fst b x)) (pt-lo d b′ (suc k)) (Ex-tr (≤-refl b) (pt-lo d b′ k) EQ E) E′
ext (ri {r = ()} q) P₀

Gr₀ : Gr azero azero
Gr₀ = record { G = λ _ _ → ⊥ ; tot = λ () ; bl = λ () ; br = λ () ; lt = λ () ; le = λ () }

emb : ∀ {x x′} → Rel azero x x′ → Gr (sum azero x) (sum azero x′)
emb d = proj₁ (ext d Gr₀)
```
