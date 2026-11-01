# Lemma 4.7 与 Lemma 4.9：C^a(A) 对下标的依赖

Setzer [Se98] §4.2 的两组引理。核心是 (a)(b)：在 `A ⊆ M(A)` 之下，`C^a(A)` 只随 `ã`（a 以下的最大基数）变化，且下标越小类越大：

> `ã ⪯ b ⟹ C^b(A) ⊆ C^a(A)`。

证明按 x 的 =NF 形状结构归纳（原文按 length(x)）；ψ 的下标 κ 不是 `psi κ c` 的结构子项，所以另写 `C-shiftR` 沿 `Reg` 递归——Ω 的情形在里面重复一遍。

本模块以 `OTFacts` 为参数；用到的字段：`≺-irrefl`、`≺-trich`、`≺-trans`、`tilde-OT`、`tilde⪯`、`tilde-idem`、`tilde-max`、`tilde-Car`、`Ω₁⪯R`、`⪯-φˡ` 等子项界。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Lemma47 (F : OTFacts) where

open OTFacts F

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OTLemmas
open import Mahlo.Inacc.WO.K
open import Mahlo.Inacc.WO.Base
open import Mahlo.Inacc.WO.CLemmas
open import Mahlo.Inacc.WO.OrderLemmas F

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

private variable
  ℓ ℓ′ : Level
  A B : Pred ℓ
```

## 0. 两条小推论

R′ 的形状都是基数；`ã ≺ κ ∈ Car ⟹ a ≺ κ`（否则 κ ⪯ a 给 κ ⪯ ã）。

```agda
Car-reg : ∀ κ → isCarT (regTm κ) ≡ true
Car-reg (ΩR a) = refl
Car-reg IR     = refl

tilde≺⇒≺ : ∀ {a κ} → OT a → OT κ → isCarT κ ≡ true → tilde a ≺ κ → a ≺ κ
tilde≺⇒≺ {a} {κ} oa oκ cκ p with ≺-or-⪰ a κ
... | inj₁ q   = q
... | inj₂ κ⪯a = ⊥-elim (≺⇒¬⪯ p (tilde-max oa oκ cκ κ⪯a))
```

## 1. 核心：`ã ⪯ b ⟹ C^b(A) ⊆ C^a(A)`（Lemma 4.7 (a)(b) 的证明体）

每个形状两支：分量都在 C^b(A) 时用归纳假设；x ∈ A ∩ b 时，若 x ≺ a 直接进 C^a(A)，否则 a ⪯ x，由 `A ⊆ M(A)` 得 x ∈ C^x(A)，再对分量用归纳假设（下标换成 x，仍有 ã ⪯ a ⪯ x）。

```agda
module _ {A : Pred ℓ} (h : A ⊆ M A) where

  mutual
    C-shift : ∀ {a b} → OT a → OT b → tilde a ⪯ b → ∀ x → C b A x → C a A x
    C-shift oa ob p zer         c = c! (C⊆OT c) (here [])
    C-shift oa ob p (zer ▹ q)   c = C-shiftP oa ob p q c
    C-shift oa ob p (a′ ▹ q ▹ r) c = C-shift+ oa ob p (a′ ▹ q) r tt c (C-+⁻ tt c)

    -- 和的情形：b 整个传入（终止检查需要），三步决策各写一个辅助函数
    C-shift+ : ∀ {a b′} → OT a → OT b′ → tilde a ⪯ b′ → ∀ b r → NZ b → C b′ A (b ▹ r)
             → (A (b ▹ r) × (b ▹ r) ≺ b′) ⊎ (C b′ A b × C b′ A ⟨ r ⟩) → C a A (b ▹ r)
    C-shift+ oa ob p b r nz c (inj₂ (cb , cc)) =
      C-+⁺ nz (C⊆OT c) (C-shift oa ob p b cb) (C-shiftP oa ob p r cc)
    C-shift+ {a} oa ob p b r nz c (inj₁ (x∈A , _)) =
      C-shift+′ oa ob p b r nz c x∈A (≺-or-⪰ (b ▹ r) a)

    C-shift+′ : ∀ {a b′} → OT a → OT b′ → tilde a ⪯ b′ → ∀ b r → NZ b → C b′ A (b ▹ r)
              → A (b ▹ r) → (b ▹ r) ≺ a ⊎ a ⪯ (b ▹ r) → C a A (b ▹ r)
    C-shift+′ oa ob p b r nz c x∈A (inj₁ x≺a) = A∩a⊆C (x∈A , C⊆OT c , x≺a)
    C-shift+′ oa ob p b r nz c x∈A (inj₂ a⪯x) =
      C-shift+″ oa ob p b r nz c a⪯x (C-+⁻ nz (h x∈A))

    C-shift+″ : ∀ {a b′} → OT a → OT b′ → tilde a ⪯ b′ → ∀ b r → NZ b → C b′ A (b ▹ r)
              → a ⪯ (b ▹ r)
              → (A (b ▹ r) × (b ▹ r) ≺ (b ▹ r)) ⊎ (C (b ▹ r) A b × C (b ▹ r) A ⟨ r ⟩)
              → C a A (b ▹ r)
    C-shift+″ oa ob p b r nz c a⪯x (inj₁ (_ , x≺x)) = ⊥-elim (≺-irrefl x≺x)
    C-shift+″ oa ob p b r nz c a⪯x (inj₂ (cb , cc)) =
      C-+⁺ nz (C⊆OT c)
        (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) b cb)
        (C-shiftP oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) r cc)

    C-shiftP : ∀ {a b} → OT a → OT b → tilde a ⪯ b → ∀ q → C b A ⟨ q ⟩ → C a A ⟨ q ⟩
    C-shiftP oa ob p I c = c! (C⊆OT c) (here [])

    C-shiftP {a} {b} oa ob p (phi b′ c′) c with C-φ⁻ c
    ... | inj₂ (cb , cc) =
      C-φ⁺ (C⊆OT c) (C-shift oa ob p b′ cb) (C-shift oa ob p c′ cc)
    ... | inj₁ (x∈A , x≺b) with ≺-or-⪰ ⟨ phi b′ c′ ⟩ a
    ...   | inj₁ x≺a = A∩a⊆C (x∈A , C⊆OT c , x≺a)
    ...   | inj₂ a⪯x with C-φ⁻ (h x∈A)
    ...     | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
    ...     | inj₂ (cb , cc) =
      C-φ⁺ (C⊆OT c)
        (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) b′ cb)
        (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) c′ cc)

    C-shiftP {a} {b} oa ob p (Om b′) c with C-Ω⁻ c
    ... | inj₂ cb = C-Ω⁺ (C⊆OT c) (C-shift oa ob p b′ cb)
    ... | inj₁ (x∈A , x≺b) with ≺-or-⪰ ⟨ Om b′ ⟩ a
    ...   | inj₁ x≺a = A∩a⊆C (x∈A , C⊆OT c , x≺a)
    ...   | inj₂ a⪯x with C-Ω⁻ (h x∈A)
    ...     | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
    ...     | inj₂ cb =
      C-Ω⁺ (C⊆OT c) (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) b′ cb)

    C-shiftP {a} {b} oa ob p (psi κ c′) c with C-ψ⁻ c
    ... | inj₂ (b≺κ , cκ , cc) =
      C-ψ⁺ (C⊆OT c)
        (tilde≺⇒≺ oa (proj₁ (proj₂ (OT-ψ⁻ (C⊆OT c)))) (Car-reg κ) (⪯≺-trans p b≺κ))
        (C-shiftR oa ob p κ cκ) (C-shift oa ob p c′ cc)
    ... | inj₁ (x∈A , x≺b) with ≺-or-⪰ ⟨ psi κ c′ ⟩ a
    ...   | inj₁ x≺a = A∩a⊆C (x∈A , C⊆OT c , x≺a)
    ...   | inj₂ a⪯x with C-ψ⁻ (h x∈A)
    ...     | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
    ...     | inj₂ (x≺κ , cκ , cc) =
      C-ψ⁺ (C⊆OT c) (⪯≺-trans a⪯x x≺κ)
        (C-shiftR oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) κ cκ)
        (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) c′ cc)

    C-shiftR : ∀ {a b} → OT a → OT b → tilde a ⪯ b → ∀ κ
             → C b A (regTm κ) → C a A (regTm κ)
    C-shiftR oa ob p IR c = c! (C⊆OT c) (here [])
    C-shiftR {a} {b} oa ob p (ΩR b′) c with C-Ω⁻ c
    ... | inj₂ cb = C-Ω⁺ (C⊆OT c) (C-shift oa ob p b′ cb)
    ... | inj₁ (x∈A , x≺b) with ≺-or-⪰ ⟨ Om b′ ⟩ a
    ...   | inj₁ x≺a = A∩a⊆C (x∈A , C⊆OT c , x≺a)
    ...   | inj₂ a⪯x with C-Ω⁻ (h x∈A)
    ...     | inj₁ (_ , x≺x) = ⊥-elim (≺-irrefl x≺x)
    ...     | inj₂ cb =
      C-Ω⁺ (C⊆OT c) (C-shift oa (C⊆OT c) (⪯-trans (tilde⪯ oa) a⪯x) b′ cb)
```

## 2. Lemma 4.7 (a)(b)

```agda
  -- (a) C^a(A) ≅ C^ã(A)
  C-tilde : ∀ {a} → OT a → C a A ≅ C (tilde a) A
  C-tilde {a} oa =
    (λ {x} c → C-shift (tilde-OT oa) oa
                 (subst (λ z → z ⪯ a) (sym (tilde-idem oa)) (tilde⪯ oa)) x c)
    , (λ {x} c → C-shift oa (tilde-OT oa) ⪯-refl x c)

  -- (b) a ⪯ b ⟹ C^b(A) ⊆ C^a(A)
  C-anti : ∀ {a b} → OT a → OT b → a ⪯ b → C b A ⊆ C a A
  C-anti oa ob p {x} c = C-shift oa ob (⪯-trans (tilde⪯ oa) p) x c
```

## 3. Lemma 4.7 (c)(d)

(c) `A ∩ ã ≅ B ∩ ã ⟹ C^a(A) ≅ C^a(B)`；(d) `a ≺ Ω₁ ⟹ C^a(A) ≅ OT`（每个 ψ_κ 的 κ ⪰ Ω₁ ≻ a，所以 ∅ ∈ K^a(y)）。

```agda
C-ext : A ⊆ M A → B ⊆ M B → ∀ {a} → OT a
      → (∀ {x} → x ≺ tilde a → A x → B x) → (∀ {x} → x ≺ tilde a → B x → A x)
      → C a A ≅ C a B
C-ext hA hB oa f g = ≅-trans (C-tilde hA oa) (≅-trans (C-cong f g) (≅-sym (C-tilde hB oa)))

module _ {A : Pred ℓ} where
  mutual
    K-∅ : ∀ {a} → OT a → a ≺ Ω₁ → ∀ y → OT y → Any (All A) (K a y)
    K-∅ oa p zer         o = here []
    K-∅ oa p (zer ▹ q)   o = KP-∅ oa p q o
    K-∅ oa p (b ▹ q ▹ r) o =
      let (ob , or , _) = OT-+⁻ o
      in Any-++⁺ˡ (⊗⁺ (K-∅ oa p (b ▹ q) ob) (KP-∅ oa p r or))

    KP-∅ : ∀ {a} → OT a → a ≺ Ω₁ → ∀ q → OT ⟨ q ⟩ → Any (All A) (KP a q)
    KP-∅ oa p I         o = here []
    KP-∅ oa p (phi b c) o with OT-φ⁻ o
    ... | ob , oc , _ , _ = Any-++⁺ˡ (⊗⁺ (K-∅ oa p b ob) (K-∅ oa p c oc))
    KP-∅ oa p (Om b)    o with OT-Ω⁻ o
    ... | ob , _ = Any-++⁺ˡ (K-∅ oa p b ob)
    KP-∅ {a} oa p (psi κ c) o with OT-ψ⁻ o
    ... | oc , oκ , rκ , _ with lt a (regTm κ) | lt≡ (≺⪯-trans p (Ω₁⪯R oκ rκ))
    ...   | true | _ = Any-++⁺ˡ (⊗⁺ (KR-∅ oa p κ oκ) (K-∅ oa p c oc))

    KR-∅ : ∀ {a} → OT a → a ≺ Ω₁ → ∀ κ → OT (regTm κ) → Any (All A) (KR a κ)
    KR-∅ oa p IR     o = here []
    KR-∅ oa p (ΩR b) o with OT-Ω⁻ o
    ... | ob , _ = Any-++⁺ˡ (K-∅ oa p b ob)

  C-Ω₁ : ∀ {a} → OT a → a ≺ Ω₁ → C a A ≅ OT
  C-Ω₁ oa p = C⊆OT , (λ {y} o → c! o (K-∅ oa p y o))
```

## 4. Lemma 4.9

- (a) `A ⊆ M(A)，b ⪯ a ⟹ τ^A(a) ∩ b ⊆ τ^A(b)`
- (b) `A ⊆ M(A)，b ⪯ a，b̃ = ã ⟹ τ^A(b) ≅ τ^A(a) ∩ b`
- (c) `a ≺ Ω₁ ⟹ τ^A(a) ≅ a`
- (d) `0, I ∈ M(A)`（`Base.0∈M`、`I∈M`）
- (e) `A ⊆ M(A)`，b, c ∈ (A ∩ ã) ∪ (M(A) ∖ ã)，a =NF b + c ∨ φ b c ∨ Ω b ⟹ a ∈ M(A)

```agda
-- Side A a b：b ∈ (A ∩ ã) ∪ (M(A) ∖ ã)
Side : Pred ℓ → Tm → Tm → Set ℓ
Side A a b = (A b × b ≺ tilde a) ⊎ (M A b × tilde a ⪯ b)

module _ {A : Pred ℓ} (h : A ⊆ M A) where

  τ-anti : ∀ {a b} → OT a → OT b → b ⪯ a → (τ A a ∩ ↓ b) ⊆ τ A b
  τ-anti oa ob p ((c , _) , (_ , x≺b)) = C-anti h ob oa p c , x≺b

  τ-tilde : ∀ {a b} → OT a → OT b → b ⪯ a → tilde b ≡ tilde a → τ A b ≅ (τ A a ∩ ↓ b)
  τ-tilde {a} {b} oa ob p e = to , from
    where
      to : τ A b ⊆ (τ A a ∩ ↓ b)
      to {x} (c , x≺b) =
        (proj₂ (C-tilde h oa) (subst (λ z → C z A x) e (proj₁ (C-tilde h ob) c))
         , ≺⪯-trans x≺b p)
        , (C⊆OT c , x≺b)
      from : (τ A a ∩ ↓ b) ⊆ τ A b
      from ((c , _) , (_ , x≺b)) = C-anti h ob oa p c , x≺b

  Side⇒C : ∀ {a b} → OT a → OT b → b ⪯ a → Side A a b → C a A b
  Side⇒C oa ob p (inj₁ (b∈A , b≺ã)) = proj₂ (C-tilde h oa) (A∩a⊆C (b∈A , ob , b≺ã))
  Side⇒C {a} {b} oa ob p (inj₂ (mb , ã⪯b)) =
    proj₂ (C-tilde h oa)
      (subst (λ z → C z A b) (tilde-between oa ob ã⪯b p) (proj₁ (C-tilde h ob) mb))

  M-+ : ∀ {b q p} → OT (b ▹ q ▹ p)
      → Side A (b ▹ q ▹ p) (b ▹ q) → Side A (b ▹ q ▹ p) ⟨ p ⟩ → M A (b ▹ q ▹ p)
  M-+ o sb sc with OT-+⁻ o
  ... | ob , oc , _ = C-+⁺ tt o (Side⇒C o ob (⪯-+ˡ o) sb) (Side⇒C o oc (⪯-+ʳ o) sc)

  M-φ : ∀ {b c} → OT ⟨ phi b c ⟩
      → Side A ⟨ phi b c ⟩ b → Side A ⟨ phi b c ⟩ c → M A ⟨ phi b c ⟩
  M-φ o sb sc with OT-φ⁻ o
  ... | ob , oc , _ = C-φ⁺ o (Side⇒C o ob (⪯-φˡ o) sb) (Side⇒C o oc (⪯-φʳ o) sc)

  M-Ω : ∀ {b} → OT ⟨ Om b ⟩ → Side A ⟨ Om b ⟩ b → M A ⟨ Om b ⟩
  M-Ω o sb with OT-Ω⁻ o
  ... | ob , _ = C-Ω⁺ o (Side⇒C o ob (⪯-Ω o) sb)

τ-Ω₁ : ∀ {a} → OT a → a ≺ Ω₁ → τ A a ≅ ↓ a
τ-Ω₁ oa p = (λ (c , x≺a) → C⊆OT c , x≺a)
          , (λ (o , x≺a) → proj₂ (C-Ω₁ oa p) o , x≺a)
```
