# Definition 4.39、Lemma 4.40、Theorem 4.41：良序到每个 ψ_{Ω₁}Ω_{I+n}

Setzer [Se98] §4.7。`W₀ := 𝕎 ∩ I`，`W_{S i} := W(W_i) ∩ Ω_{I+S i}`——一列**突出类**，含 I、Ω_{I+1}、Ω_{I+2}、…。Lemma 4.40 对 i 归纳（原文说"meta induction"；这里 `Wi : ℕ → Pred` 由 ℕ 递归定义——ℕ 到宇宙上一层的大消去——所以是 Agda 里一个真正的归纳，**对 n 一致**，ROADMAP B4 的推测成立）。Theorem 4.41：`∀ n. Prog(X) → ∀ y ≺ ψ_{Ω₁}Ω_{I+n}. X y`。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Main (F : OTFacts) where

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
open import Mahlo.Inacc.WO.Lemma47 F
open import Mahlo.Inacc.WO.Lemma413 F
open import Mahlo.Inacc.WO.Dist F
open import Mahlo.Inacc.WO.Closed F
open import Mahlo.Inacc.WO.Closed2 F
open import Mahlo.Inacc.WO.Lemma417b F
open import Mahlo.Inacc.WO.Lemma423 F
open import Mahlo.Inacc.WO.Union F
open import Mahlo.Inacc.WO.Lemma431 F
open import Mahlo.Inacc.WO.Gamma2 F

open import Level using (Level; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _++_)
open import Data.Nat.Base using (ℕ; zero; _<_) renaming (suc to sucℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

private variable
  ℓ : Level
```

## 0. I + n、Ω_{I+n}、端点

```agda
I+ : ℕ → Tm
I+ zero     = I′
I+ (sucℕ n) = I+ n + one

-- I + (n+1) = (I + n) ▹ 1；I + n ≠ 0；I + n ∈ OT
mutual
  I+-OT : ∀ n → OT (I+ n)
  I+-OT zero     = OT-I
  I+-OT (sucℕ n) = +-OT (I+-OT n) OT-one

I+-NZ : ∀ n → NZ (I+ n)
I+-NZ zero     = tt
I+-NZ (sucℕ n) = subst NZ (sym (+one (I+ n) (I+-NZ n) (I+-OT n))) tt

I+suc : ∀ n → I+ (sucℕ n) ≡ I+ n ▹ phi zer zer
I+suc n = +one (I+ n) (I+-NZ n) (I+-OT n)

-- Ω_{I+n}：n = 0 时是 I（Ω_I = I），n ≥ 1 时是 Ω′_{I+n}
ΩI+ : ℕ → Tm
ΩI+ zero     = I′
ΩI+ (sucℕ n) = ⟨ Om (I+ (sucℕ n)) ⟩

ΩI+-OT : ∀ n → OT (ΩI+ n)
-- I + (n+1) 的两个布尔性质（经 I+suc 搬运，不用 rewrite：等式两边归约后同形）
I+suc-Fi : ∀ n → isFiT (I+ (sucℕ n)) ≡ false
I+suc-Fi n = subst (λ t → isFiT t ≡ false) (sym (I+suc n)) (isFiT-▹1 (I+ n) (I+-NZ n))

I+suc-Z : ∀ n → isZero (I+ (sucℕ n)) ≡ false
I+suc-Z n = subst (λ t → isZero t ≡ false) (sym (I+suc n)) refl

ΩI+-OT zero     = OT-I
ΩI+-OT (sucℕ n) = OT-Ω⁺ (I+-OT (sucℕ n)) (I+suc-Fi n) (I+suc-Z n)

ΩI+-Car : ∀ n → isCarT (ΩI+ n) ≡ true
ΩI+-Car zero     = refl
ΩI+-Car (sucℕ n) = refl

-- (Ω_{I+n})⁺ = Ω_{I+n+1}
Ω-I+suc : ∀ n → Ω (I+ (sucℕ n)) ≡ ⟨ Om (I+ (sucℕ n)) ⟩
Ω-I+suc n =
  trans (if-false {x = zer} {y = if isFiT (I+ (sucℕ n)) then I+ (sucℕ n) else ⟨ Om (I+ (sucℕ n)) ⟩} (I+suc-Z n))
        (if-false {x = I+ (sucℕ n)} {y = ⟨ Om (I+ (sucℕ n)) ⟩} (I+suc-Fi n))

plus-ΩI+ : ∀ n → plus (ΩI+ n) ≡ ΩI+ (sucℕ n)
plus-ΩI+ zero     = Ω-I+suc 0
plus-ΩI+ (sucℕ n) = Ω-I+suc (sucℕ n)

ΩI+≺suc : ∀ n → ΩI+ n ≺ ΩI+ (sucℕ n)
ΩI+≺suc n = subst (λ t → ΩI+ n ≺ t) (plus-ΩI+ n) (≺plus (ΩI+-OT n))

-- 端点 ψ_{Ω₁}(Ω_{I+n})（n ≥ 1；n = 0 给 ψ_{Ω₁} I）
endpt : ℕ → Tm
endpt n = ⟨ psi (ΩR one) (ΩI+ n) ⟩

-- G_{Ω₁}(I + n) = ∅，故端点 ∈ OT
G-I+ : ∀ n → G (ΩR one) (I+ n) ≡ []
G-I+ zero     = refl
G-I+ (sucℕ n) = trans (cong (G (ΩR one)) (I+suc n)) (cong (_++ (G (ΩR one) zer ++ G (ΩR one) zer)) (G-I+ n))

endpt-OT : ∀ n → OT (endpt n)
endpt-OT zero     = ot! refl
endpt-OT (sucℕ n) = OT-ψ⁺ (ΩI+-OT (sucℕ n)) (ot! refl) refl g
  where
    g : allLt (G (ΩR one) ⟨ Om (I+ (sucℕ n)) ⟩) ⟨ Om (I+ (sucℕ n)) ⟩ ≡ true
    g = subst (λ l → allLt l ⟨ Om (I+ (sucℕ n)) ⟩ ≡ true) (sym (G-I+ (sucℕ n))) refl
```

## 1. τ^A(κ) ⊆ W(A)（4.40 两步共用）

`A ⊆ M(A)`，κ ∈ Car′，I ⪯ κ，`A ∩ κ ≅ W(A) ∩ κ` ⟹ `τ^A(κ) ⊆ W(A)`：按 size 归纳；原子 ∈ A ∩ κ ⊆ W(A)；和／φ／Ω 由 Lemma 4.17 (b)；ψ_π b 只能是原子（κ ≺ π 时 ψ_π b ⪰ π⁻ ⪰ κ；π = I 时 K^κ 走原子支，因为 I ⪯ κ）。

```agda
-- I + n ∈ C^a(A)（任何 a、A）
C-I+ : ∀ {ℓ} {A : Pred ℓ} {a} n → C a A (I+ n)
C-I+ zero     = c! OT-I (here [])
C-I+ {A = A} {a} (sucℕ n) =
  subst (C a A) (sym (I+suc n))
    (C-+⁺ (I+-NZ n) (subst OT (I+suc n) (I+-OT (sucℕ n))) (C-I+ n) (C-φ⁺ OT-one c0 c0))
  where c0 = c! OT-0 (here [])

module τκ {A : Pred ℓ} (h : A ⊆ M A) {κ : Tm} (oκ : OT κ) (cκ : isCarT κ ≡ true) (I⪯κ : I′ ⪯ κ)
          (E : (A ∩ ↓ κ) ≅ (𝒲 A ∩ ↓ κ)) where

  open L417b h oκ E

  τκ⊆W : τ A κ ⊆ 𝒲 A
  τκ⊆W {x = x₀} t₀ = go x₀ t₀
    where
      go : ∀ x → τ A κ x → 𝒲 A x
      go = sizeRec (λ x → τ A κ x → 𝒲 A x) step
        where
          wC : WDC (C κ A)
          wC = CaWDC oκ (≺plus oκ)
          step : ∀ x → (∀ y → size y < size x → τ A κ y → 𝒲 A y) → τ A κ x → 𝒲 A x
          step zer       ih t = 0∈𝒲
          step (zer ▹ I) ih (cx , x≺κ) = W-I (≺-trans x≺κ (≺plus oκ))
          step (a ▹ r ▹ p) ih (cx , x≺κ) =
            let (c₁ , c₂) = wdc-+ wC tt (C⊆OT cx) cx
                x≺κ⁺ = ≺-trans x≺κ (≺plus oκ)
            in W-+ (ih (a ▹ r) (size-▹ˡ (a ▹ r) p) (c₁ , ≺-trans (≺-+ˡ tt (C⊆OT cx)) x≺κ))
                   (≺-trans (≺-+ˡ tt (C⊆OT cx)) x≺κ⁺)
                   (ih ⟨ p ⟩ (size-▹ʳ (a ▹ r) p tt) (c₂ , ≺-trans (≺-+ʳ tt (C⊆OT cx)) x≺κ))
                   tt (C⊆OT cx) x≺κ⁺
          step (zer ▹ phi a b) ih (cx , x≺κ) =
            let (c₁ , c₂) = wdc-φ wC (C⊆OT cx) cx
            in W-φ (ih a (size-φˡ a b) (c₁ , ≺-trans (≺-φˡ (C⊆OT cx)) x≺κ))
                   (ih b (size-φʳ a b) (c₂ , ≺-trans (≺-φʳ (C⊆OT cx)) x≺κ))
                   (C⊆OT cx) (≺-trans x≺κ (≺plus oκ))
          step (zer ▹ Om a) ih (cx , x≺κ) =
            W-Ω (ih a (size-Ω a) (wdc-Ω wC (C⊆OT cx) cx , ≺-trans (≺-Ω (C⊆OT cx)) x≺κ))
                (C⊆OT cx) (≺-trans x≺κ (≺plus oκ))
          step (zer ▹ psi π b) ih (cx , x≺κ) = fromC π cx x≺κ (C-ψ⁻ cx)
            where
              fromC : ∀ π → C κ A ⟨ psi π b ⟩ → ⟨ psi π b ⟩ ≺ κ
                    → (A ⟨ psi π b ⟩ × ⟨ psi π b ⟩ ≺ κ) ⊎ (κ ≺ regTm π × C κ A (regTm π) × C κ A b)
                    → 𝒲 A ⟨ psi π b ⟩
              fromC π cx x≺κ (inj₁ (ax , _)) = proj₁ (proj₁ E (ax , C⊆OT cx , x≺κ))
              fromC IR     cx x≺κ (inj₂ (κ≺I , _)) = ⊥-elim (≺⇒¬⪯ κ≺I I⪯κ)
              fromC (ΩR z) cx x≺κ (inj₂ (κ≺π , _)) =
                ⊥-elim (≺⇒¬⪯ x≺κ
                  (⪯-trans (Car≺κ⇒⪯κ⁻ oκ cκ (proj₁ (proj₂ (proj₂ (OT-ψ⁻ (C⊆OT cx)))))
                                       (proj₁ (proj₂ (OT-ψ⁻ (C⊆OT cx)))) κ≺π)
                           (≺⇒⪯ (κ⁻≺ψ (C⊆OT cx)))))
```

## 2. Definition 4.39：突出类 W_i

```agda
Wi : ℕ → Pred (suc 0ℓ)
Wi zero     = 𝕎 ∩ ↓ I′
Wi (sucℕ i) = 𝒲 (Wi i) ∩ ↓ (ΩI+ (sucℕ i))

-- I ⪯ Ω_{I+n}
I⪯ΩI+ : ∀ n → I′ ⪯ ΩI+ n
I⪯ΩI+ zero     = ⪯-refl
I⪯ΩI+ (sucℕ n) = ⪯-trans (I⪯I+ (sucℕ n)) (⪯-Ω (ΩI+-OT (sucℕ n)))
  where
    I⪯I+ : ∀ n → I′ ⪯ I+ n
    I⪯I+ zero     = ⪯-refl
    I⪯I+ (sucℕ n) = ⪯-trans (I⪯I+ n) (subst (λ t → I+ n ⪯ t) (sym (I+suc n)) (⪯-prefix {y = I+ n} {z = one} tt (subst OT (I+suc n) (I+-OT (sucℕ n)))))
```

## 3. Lemma 4.40

```agda
record L440 (i : ℕ) : Set (suc 0ℓ) where
  field
    agW : Ag (Wi i)
    Ω∈W : Wi (sucℕ i) (ΩI+ i)
    W≅  : Wi i ≅ (Wi (sucℕ i) ∩ ↓ (ΩI+ i))
open L440

l440 : ∀ i → L440 i
-- i = 0：由 Lemma 4.38 (c)
l440 zero = record { agW = agW₀ ; Ω∈W = I∈W₁ ; W≅ = W≅₀ }
  where
    W₀ : Pred (suc 0ℓ)
    W₀ = Wi zero
    hW₀ : W₀ ⊆ M W₀
    hW₀ (w , o , x≺I) = C-mono (λ z≺x p → p , 𝕎⊆OT p , ≺-trans z≺x x≺I) (𝕎⊆M w)
    f : ∀ {z} → z ≺ I′ → 𝕎 z → W₀ z
    f z≺I p = p , 𝕎⊆OT p , z≺I
    g : ∀ {z} → z ≺ I′ → W₀ z → 𝕎 z
    g _ = proj₁
    E₀ : W₀ ≅ (𝒲 W₀ ∩ ↓ I′)
    E₀ = (λ (w , o , x≺I) → 𝒲-cong-⪯ 𝕎⊆M hW₀ OT-I f g (≺⇒⪯ x≺I) (𝕎⊆𝒲𝕎 w) , o , x≺I)
       , (λ (w , o , x≺I) → L4-38c (𝒲-cong-⪯ hW₀ 𝕎⊆M OT-I g f (≺⇒⪯ x≺I) w) x≺I , o , x≺I)
    E₀′ : (W₀ ∩ ↓ I′) ≅ (𝒲 W₀ ∩ ↓ I′)
    E₀′ = (λ (p , _) → proj₁ E₀ p) , (λ q → proj₂ E₀ q , proj₁ (proj₂ (proj₂ E₀ q)) , proj₂ (proj₂ (proj₂ E₀ q)))
    agW₀ : Ag W₀
    agW₀ = ≅𝒲∩⇒Ag E₀
    W≅₀ : W₀ ≅ (Wi 1 ∩ ↓ I′)
    W≅₀ = (λ p → let (w , o , x≺I) = proj₁ E₀ p in (w , o , ≺-trans x≺I (ΩI+≺suc 0)) , o , x≺I)
        , (λ ((w , o , _) , _ , x≺I) → proj₂ E₀ (w , o , x≺I))
    I∈W₁ : Wi 1 I′
    I∈W₁ = sup I∈M (τκ.τκ⊆W hW₀ OT-I refl ⪯-refl E₀′) , OT-I , ΩI+≺suc 0
-- i = j + 1
l440 (sucℕ j) = record { agW = agW′ ; Ω∈W = Ω∈W′ ; W≅ = W≅′ }
  where
    ih : L440 j
    ih = l440 j
    Wj Wj+1 : Pred (suc 0ℓ)
    Wj   = Wi j
    Wj+1 = Wi (sucℕ j)
    hWj : Wj ⊆ M Wj
    hWj p = 𝒲-M (Ag⇒A⊆𝒲 (agW ih) p)
    Wj⊆Wj+1 : Wj ⊆ Wj+1
    Wj⊆Wj+1 p = proj₁ (proj₁ (W≅ ih) p)
    hWj+1 : Wj+1 ⊆ M Wj+1
    hWj+1 (w , _ , _) = C-mono (λ _ → Wj⊆Wj+1) (𝒲-M w)
    -- W_j 与 W_{j+1} 在 Ω_{I+j} 以下一致
    f : ∀ {z} → z ≺ ΩI+ j → Wj z → Wj+1 z
    f _ = Wj⊆Wj+1
    g : ∀ {z} → z ≺ ΩI+ j → Wj+1 z → Wj z
    g z≺ p = proj₂ (W≅ ih) (p , oz p , z≺)
      where
        oz : ∀ {z} → Wj+1 z → OT z
        oz (_ , o , _) = o
    -- Lemma 4.13 (b)：y ≺ Ω_{I+j+1} 时 W(W_j) 与 W(W_{j+1}) 一致
    cong→ : ∀ {y} → y ≺ ΩI+ (sucℕ j) → 𝒲 Wj y → 𝒲 Wj+1 y
    cong→ y≺ w = 𝒲-cong-plus hWj hWj+1 (ΩI+-OT j) f g (subst (λ t → _ ≺ t) (sym (plus-ΩI+ j)) y≺) w
    cong← : ∀ {y} → y ≺ ΩI+ (sucℕ j) → 𝒲 Wj+1 y → 𝒲 Wj y
    cong← y≺ w = 𝒲-cong-plus hWj+1 hWj (ΩI+-OT j) g f (subst (λ t → _ ≺ t) (sym (plus-ΩI+ j)) y≺) w
    E′ : (Wj+1 ∩ ↓ (ΩI+ (sucℕ j))) ≅ (𝒲 Wj+1 ∩ ↓ (ΩI+ (sucℕ j)))
    E′ = (λ ((w , o , y≺) , _) → cong→ y≺ w , o , y≺)
       , (λ (w′ , o , y≺) → (cong← y≺ w′ , o , y≺) , o , y≺)
    E″ : Wj+1 ≅ (𝒲 Wj+1 ∩ ↓ (ΩI+ (sucℕ j)))
    E″ = (λ p → proj₁ E′ (p , proj₁ (proj₂ p) , proj₂ (proj₂ p))) , (λ q → proj₁ (proj₂ E′ q))
    agW′ : Ag Wj+1
    agW′ = ≅𝒲∩⇒Ag E″
    W≅′ : Wj+1 ≅ (Wi (sucℕ (sucℕ j)) ∩ ↓ (ΩI+ (sucℕ j)))
    W≅′ = (λ p → let (w′ , o , y≺) = proj₁ E″ p in (w′ , o , ≺-trans y≺ (ΩI+≺suc (sucℕ j))) , o , y≺)
        , (λ ((w′ , o , _) , _ , y≺) → proj₂ E″ (w′ , o , y≺))
    Ω∈W′ : Wi (sucℕ (sucℕ j)) (ΩI+ (sucℕ j))
    Ω∈W′ = sup mΩ (τκ.τκ⊆W hWj+1 (ΩI+-OT (sucℕ j)) (ΩI+-Car (sucℕ j)) (I⪯ΩI+ (sucℕ j)) E′)
           , ΩI+-OT (sucℕ j) , ΩI+≺suc (sucℕ j)
      where
        mΩ : M Wj+1 (ΩI+ (sucℕ j))
        mΩ = C-Ω⁺ (ΩI+-OT (sucℕ j)) (C-I+ (sucℕ j))
```

## 4. Theorem 4.41

```agda
Wi⊆suc : ∀ i → Wi i ⊆ Wi (sucℕ i)
Wi⊆suc i p = proj₁ (proj₁ (W≅ (l440 i)) p)

W₀⊆Wi : ∀ i → Wi zero ⊆ Wi i
W₀⊆Wi zero     p = p
W₀⊆Wi (sucℕ i) p = Wi⊆suc i (W₀⊆Wi i p)

Ω₁≺I : Ω₁ ≺ I′
Ω₁≺I with ⪯⇒≺⊎≡ (Ω₁⪯R {IR} OT-I refl)
... | inj₁ q = q
... | inj₂ ()

Ω₁∈𝕎 : 𝕎 Ω₁
Ω₁∈𝕎 = 𝕎-plus 0∈𝕎

thm441 : ∀ n {X : Pred ℓ} → Prog₁ X → ∀ {y} → OT y → y ≺ endpt n → X y
thm441 n {X} prog {y} oy y≺ψ =
  Ag-Prog₁ agS prog (proj₁ (⊑← (Ag-Ω₁⊑OT agS) (ψ∈S , endpt-OT n , ψ≺Ω₁) oy (≺⇒⪯ y≺ψ))
                    , oy , ≺-trans y≺ψ ψ≺Ω₁)
  where
    S : Pred (suc 0ℓ)
    S = Wi (sucℕ n)
    agS : Ag S
    agS = agW (l440 (sucℕ n))
    Ω₁∈S : S Ω₁
    Ω₁∈S = W₀⊆Wi (sucℕ n) (Ω₁∈𝕎 , 𝕎⊆OT Ω₁∈𝕎 , Ω₁≺I)
    Ωn∈S : S (ΩI+ n)
    Ωn∈S = Ω∈W (l440 n)
    ψ∈S : S (endpt n)
    ψ∈S = Ag423.Ag-ψ agS Ω₁∈S Ωn∈S (endpt-OT n)
    ψ≺Ω₁ : endpt n ≺ Ω₁
    ψ≺Ω₁ = ψ≺κ (endpt-OT n)
```

## 5. 可达性证书

`Acc y`：y 以下（OT 中）的每个元素可达。`Prog(Ω₁, Acc)` 是 `acc` 构造子本身；Theorem 4.41 给出端点以下全部可达——这就是 [../../DECISION.md](../../DECISION.md) 里「名字 + 证书」的证书。

```agda
data Acc (y : Tm) : Set where
  acc : (∀ {z} → OT z → z ≺ y → Acc z) → Acc y

Prog₁-Acc : Prog₁ Acc
Prog₁-Acc (ox , x≺Ω₁) ih = acc (λ oz z≺x → ih ((oz , ≺-trans z≺x x≺Ω₁) , oz , z≺x))

Acc-endpt : ∀ n {y} → OT y → y ≺ endpt n → Acc y
Acc-endpt n = thm441 n Prog₁-Acc
```

`endpt (sucℕ n) = ψ_{Ω₁}(Ω′_{I+n+1})`（`Syntax.endpoint` 是 n = ω 那一个形状的固定项，这里的 `endpt n` 是一族）；`Acc-endpt` 对每个 n 给出 ψ_{Ω₁}Ω_{I+n} 以下的可达性，合起来就是 |ML₁W| = ψ_{Ω₁}Ω_{I+ω} 的良序（下界）。
