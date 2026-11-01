# Lemma 4.31：𝕎 对 Ω 封闭（I 以下）；ψ_I 0 与 ψ_I(x+1)

Setzer [Se98] Lemma 4.31。

- (a) `∀x ∈ 𝕎 ∩ I. Ω_x ∈ 𝕎`：对 a ∈ 𝕎 归纳（Ag(𝕎)）。a ∈ Fi′ 时 Ω_a = a；否则 Ω′_a ∈ M(𝕎)，取 B := {(Ω_y)⁺ | y ∈ τ^𝕎(a)}（由归纳假设与 𝕎 对 ⁺ 封闭，B ⊆ 𝕎|Ω′_a），τ^𝕎(Ω′_a) 的每个 y 有 ỹ = Ω_c、c ∈ τ^𝕎(a)、y ≺ (Ω_c)⁺，Lemma 4.30 收尾。
- (b) `ψ_I 0 ∈ 𝕎`；`ψ_I x ∈ 𝕎 ⟹ ψ_I(x+1) ∈ 𝕎`：同样用 4.30，B := {Ωⁿ_{c+1} | n}（c := 0 或 ψ_I x），由 (a) 与 Fi′ 元素对 Ω、+1 封闭得 B ⊆ 𝕎|d；Remark 2.14 (i) 给 τ^𝕎(d) ⪯ B。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Lemma431 (F : OTFacts) where

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
open import Mahlo.Inacc.WO.CTilde F
open import Mahlo.Inacc.WO.Lemma47ef F
open import Mahlo.Inacc.WO.Lemma423 F
open import Mahlo.Inacc.WO.Union F
open import Mahlo.Inacc.WO.Lemma430 F

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
```

## 工具

```agda
-- 基数的形状：Ω′_c、ψ_I e、I
data CarView : Tm → Set where
  car-Ω  : ∀ c → CarView ⟨ Om c ⟩
  car-ψ  : ∀ e → CarView ⟨ psi IR e ⟩
  car-I  : CarView I′

carView : ∀ x → isCarT x ≡ true → CarView x
carView (zer ▹ Om c)     _ = car-Ω c
carView (zer ▹ psi IR e) _ = car-ψ e
carView (zer ▹ I)        _ = car-I
carView (zer ▹ psi (ΩR _) _) ()
carView (zer ▹ phi _ _) ()
carView zer ()
carView (_ ▹ _ ▹ _) ()

-- Ω y ⪯ Ω′_a（y ≺ a），故 (Ω y)⁺ ⪯ Ω′_a
Ωy⁺⪯Ω′ : ∀ {y a} → OT y → OT ⟨ Om a ⟩ → y ≺ a → plus (Ω y) ⪯ ⟨ Om a ⟩
Ωy⁺⪯Ω′ oy oa y≺a = plus-least (Ω-OT oy) oa refl (Ω≺Ω′ oy oa y≺a)

-- W(𝕎)|b 落回 𝕎（b ∈ 𝕎）
W→𝕎 : ∀ {b z} → 𝕎 b → 𝒲 𝕎 z → z ⪯ b → 𝕎 z
W→𝕎 b∈𝕎 w t = ⊑← (proj₂ Ag𝕎) b∈𝕎 w t

τ𝕎⊆𝕎 : ∀ {b} → 𝕎 b → τ 𝕎 b ⊆ 𝕎
τ𝕎⊆𝕎 b∈𝕎 t = W→𝕎 b∈𝕎 (𝒲-τ (𝕎⊆𝒲𝕎 b∈𝕎) t) (≺⇒⪯ (proj₂ t))
```

## (a)

```agda
𝕎-Ω : ∀ {a} → 𝕎 a → a ≺ I′ → 𝕎 (Ω a)
𝕎-Ω {a} a∈𝕎 a≺I = Ag-ind Ag𝕎 prog a∈𝕎 a≺I
  where
    prog : Prog 𝕎 (λ a → a ≺ I′ → 𝕎 (Ω a))
    prog {x = a} a∈𝕎 ih a≺I with Ω-view a
    ... | Ω-0 _ e      = subst 𝕎 (sym e) (0∈A a∈𝕎)
      where 0∈A = Ag423.0∈A Ag𝕎
    ... | Ω-Fi _ e     = subst 𝕎 (sym e) a∈𝕎
    ... | Ω-Om e₀ e₁ e = subst 𝕎 (sym e) (L430.L4-30 mΩ Ω≺I B cover B⊆)
      where
        oa : OT a
        oa = 𝕎⊆OT a∈𝕎
        oΩ : OT ⟨ Om a ⟩
        oΩ = OT-Ω⁺ oa e₁ e₀
        Ω≺I : ⟨ Om a ⟩ ≺ I′
        Ω≺I = subst (λ t → t ≺ I′) e (Fi-closed-Ω refl OT-I oa a≺I)
        a⪯Ω : a ⪯ ⟨ Om a ⟩
        a⪯Ω = ⪯-Ω oΩ
        -- Ω′_a ∈ M(𝕎)
        mΩ : M 𝕎 ⟨ Om a ⟩
        mΩ = C-Ω⁺ oΩ (A∩a⊆C (a∈𝕎 , oa , ≺-Ω oΩ))
        -- 见证集 A ∋ a；τ^𝕎(a) ≅ τ^A(a)（A 与 𝕎 在 a 以下一致），B 用 τ^A(a) 才是集合
        A : Pred 0ℓ
        A = proj₁ a∈𝕎
        agA : Ag A
        agA = proj₁ (proj₂ a∈𝕎)
        a∈A : A a
        a∈A = proj₂ (proj₂ a∈𝕎)
        A⊑𝕎 : A ⊑ 𝕎
        A⊑𝕎 = Ag⇒⊑𝕎 A agA
        CaA≅ : C a A ≅ C a 𝕎
        CaA≅ = C-cong (λ z≺a q → ⊑→ A⊑𝕎 a∈A q (≺⇒⪯ z≺a)) (λ z≺a w → ⊑← A⊑𝕎 a∈A w (≺⇒⪯ z≺a))
        -- B := {(Ω y)⁺ | y ∈ τ^A(a)}
        B : Pred 0ℓ
        B x = ∃ λ y → τ A a y × x ≡ plus (Ω y)
        B⊆ : B ⊆ (𝕎 ∣ ⟨ Om a ⟩)
        B⊆ (y , (cy , y≺a) , refl) =
          𝕎-plus (ih (τ𝕎⊆𝕎 a∈𝕎 (proj₁ CaA≅ cy , y≺a) , C⊆OT cy , y≺a) (≺-trans y≺a a≺I))
          , Ωy⁺⪯Ω′ (C⊆OT cy) oΩ y≺a
        -- τ^𝕎(Ω′_a) ⪯ B
        cover : ∀ {y} → τ 𝕎 ⟨ Om a ⟩ y → ∃ λ b → B b × y ⪯ b
        cover {y} t@(cy , y≺Ω) = plus (Ω c) , (c , (proj₂ CaA≅ cc , c≺a) , refl) , ≺⇒⪯ y≺Ωc⁺
          where
            oy : OT y
            oy = C⊆OT cy
            -- ỹ ∈ τ^𝕎(Ω′_a)
            tỹ : τ 𝕎 ⟨ Om a ⟩ (tilde y)
            tỹ = dc-tilde (Rem4-15.DC′ (τ-WDC′ (C-WDC-tilde 𝕎⊆M oΩ (WDC-∩↓ (Ag423.Ag-WDC Ag𝕎) _)))
                                       τ-WUC ≺a-mono proj₂)
                          oy t
            -- ỹ = Ω_c，c ∈ τ^𝕎(a)：按 ỹ ∈ Car′ ∪ {0} 的形状
            nz-a : NZ a
            nz-a = nz-of e₀
              where
                nz-of : ∀ {b} → isZero b ≡ false → NZ b
                nz-of {b = _ ▹ _} _ = tt
            0≺a : zer ≺ a
            0≺a = ⪯-sub⇒≺ (size-NZ a nz-a) (0⪯ a)
            -- τ^𝕎(Ω′_a) 的元素落进 C^a(𝕎)
            toCa : ∀ {z} → τ 𝕎 ⟨ Om a ⟩ z → C a 𝕎 z
            toCa (cz , _) = C-anti 𝕎⊆M oa oΩ a⪯Ω cz
            pick : ∃ λ c → C a 𝕎 c × c ≺ a × Ω c ≡ tilde y
            pick with tilde y in eỹ | tilde-Car oy | tỹ
            ... | ỹ | inj₂ e0 | _ = zer , c! OT-0 (here []) , 0≺a , sym e0
            ... | ỹ | inj₁ ca | tỹ′ = byCar (carView ỹ ca) tỹ′
              where
                -- Fi′ 的元素 ≺ Ω′_a ⟹ ⪯ a，且 ≠ a（a ∉ Fi′）
                fi≺a : ∀ {z} → isFiT z ≡ true → OT z → z ≺ ⟨ Om a ⟩ → z ≺ a
                fi≺a {z} fz oz z≺Ω with ⪯⇒≺⊎≡ (Fi≺Ω⇒⪯ fz oz oΩ z≺Ω)
                ... | inj₁ q = q
                ... | inj₂ refl = ⊥-elim (true≢false (trans (sym fz) e₁))
                byCar : ∀ {ỹ} → CarView ỹ → τ 𝕎 ⟨ Om a ⟩ ỹ → ∃ λ c → C a 𝕎 c × c ≺ a × Ω c ≡ ỹ
                byCar (car-Ω c) t@(cỹ , ỹ≺Ω) =
                  c , toCa tc , Ω-mono⁻ (C⊆OT cỹ) oΩ ỹ≺Ω , eqΩ
                  where
                    tc : τ 𝕎 ⟨ Om a ⟩ c
                    tc = wdc-Ω (τ-WDC′ (C-WDC-tilde 𝕎⊆M oΩ (WDC-∩↓ (Ag423.Ag-WDC Ag𝕎) _))) (C⊆OT cỹ) t
                    eqΩ : Ω c ≡ ⟨ Om c ⟩
                    eqΩ = trans (if-false (proj₂ (proj₂ (OT-Ω⁻ (C⊆OT cỹ))))) (if-false (proj₁ (proj₂ (OT-Ω⁻ (C⊆OT cỹ)))))
                byCar (car-ψ e) t@(cỹ , ỹ≺Ω) =
                  ⟨ psi IR e ⟩ , toCa t , fi≺a refl (C⊆OT cỹ) ỹ≺Ω , refl
                byCar car-I t@(cỹ , ỹ≺Ω) =
                  I′ , toCa t , fi≺a refl OT-I ỹ≺Ω , refl
            c = proj₁ pick
            cc = proj₁ (proj₂ pick)
            c≺a = proj₁ (proj₂ (proj₂ pick))
            y≺Ωc⁺ : y ≺ plus (Ω c)
            y≺Ωc⁺ = subst (λ t → y ≺ t) (cong plus (sym (proj₂ (proj₂ (proj₂ pick))))) (x≺plus-tilde oy)
```

## (b)

```agda
-- 0 + 1 = 1
0+1 : zer + one ≡ one
0+1 = refl

-- B := {Ωⁿ_{c+1} | n : ℕ}
Bω : Tm → Pred 0ℓ
Bω c x = ∃ λ n → x ≡ Ωⁿ (c + one) n

-- Ωⁿ_{c+1} ≺ f（f ∈ Fi′，c ≺ f）
Ωⁿ≺Fi : ∀ {f c} → isFiT f ≡ true → OT f → OT c → c ≺ f → ∀ n → Ωⁿ (c + one) n ≺ f
Ωⁿ≺Fi {f} {c} ff of oc c≺f zero    = Car-closed-+1 (Fi⊆Car {f} ff) of oc c≺f
  where
    Fi⊆Car : ∀ {f} → isFiT f ≡ true → isCarT f ≡ true
    Fi⊆Car {zer ▹ psi IR _} _ = refl
    Fi⊆Car {zer ▹ I} _ = refl
Ωⁿ≺Fi {f} {c} ff of oc c≺f (Data.Nat.Base.suc n) =
  Fi-closed-Ω ff of (Ωⁿ-OT n (+-OT oc OT-one)) (Ωⁿ≺Fi ff of oc c≺f n)

one∈𝕎 : ∀ {c} → 𝕎 c → 𝕎 one
one∈𝕎 {c} c∈𝕎 = wuc-φ (wuc 𝕎-UC) OT-one (plus c , 𝕎-plus c∈𝕎 , one≺c⁺) 0∈𝕎 0∈𝕎
  where
    0∈𝕎 = Ag423.0∈A Ag𝕎 c∈𝕎
    one≺c⁺ : one ≺ plus c
    one≺c⁺ = Car-closed-+1 (plus-Car (𝕎⊆OT c∈𝕎)) (plus-OT (𝕎⊆OT c∈𝕎)) OT-0 (0≺Car (plus-Car (𝕎⊆OT c∈𝕎)))
      where
        0≺Car : ∀ {κ} → isCarT κ ≡ true → zer ≺ κ
        0≺Car {κ} cκ with carView κ cκ
        ... | car-Ω c = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)
        ... | car-ψ e = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)
        ... | car-I   = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)

-- Ωⁿ_{c+1} ∈ 𝕎（c ∈ 𝕎，c ≺ I）
Ωⁿ∈𝕎 : ∀ {c} → 𝕎 c → c ≺ I′ → ∀ n → 𝕎 (Ωⁿ (c + one) n)
Ωⁿ∈𝕎 {c} c∈𝕎 c≺I zero =
  uc-+ 𝕎-UC oc OT-one (+-OT oc OT-one)
       (plus c , 𝕎-plus c∈𝕎 , Car-closed-+1 (plus-Car oc) (plus-OT oc) oc (≺plus oc)) c∈𝕎 (one∈𝕎 c∈𝕎)
  where oc = 𝕎⊆OT c∈𝕎
Ωⁿ∈𝕎 {c} c∈𝕎 c≺I (Data.Nat.Base.suc n) =
  𝕎-Ω (Ωⁿ∈𝕎 c∈𝕎 c≺I n) (Ωⁿ≺Fi refl OT-I (𝕎⊆OT c∈𝕎) c≺I n)

-- 0 ∈ 𝕎：{0} 是突出集
0∈𝕎 : 𝕎 zer
0∈𝕎 = Z , agZ , refl
  where
    Z : Pred 0ℓ
    Z x = x ≡ zer
    agZ : Ag Z
    agZ = (λ { refl → OT-0 }) , (λ { refl → OT-0 })
        , λ { refl → (λ { (refl , t) → 0∈𝒲 , t }) , (λ (w , t) → ⪯0⇒≡0 t , t) }

-- x + 1 的两种形状
x+1-view : ∀ x → OT x → (x ≡ zer × x + one ≡ one) ⊎ (NZ x × x + one ≡ x ▹ phi zer zer)
x+1-view zer     _  = inj₁ (refl , refl)
x+1-view (a ▹ p) ox = inj₂ (tt , +one (a ▹ p) tt ox)

x≺x+1 : ∀ {x} → OT x → x ≺ x + one
x≺x+1 {x} ox with x+1-view x ox
... | inj₁ (refl , e) = subst (λ t → zer ≺ t) (sym e) (⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ one))
... | inj₂ (nz , e)   = subst (λ t → x ≺ t) (sym e) (≺-+ˡ nz (subst OT e (+-OT ox OT-one)))

-- 4.30 的公共部分：d = ψ_I e，c ≺ d，B := {Ωⁿ_{c+1}}
module ψI (c e : Tm) (c∈𝕎 : 𝕎 c) (c≺I : c ≺ I′) (od : OT ⟨ psi IR e ⟩) (c≺d : c ≺ ⟨ psi IR e ⟩)
          (mFi⪯c : ∀ {y} → OT y → y ≺ ⟨ psi IR e ⟩ → mFi y ⪯ c)
          (ce : C ⟨ psi IR e ⟩ 𝕎 e) where

  oc : OT c
  oc = 𝕎⊆OT c∈𝕎
  d≺I : ⟨ psi IR e ⟩ ≺ I′
  d≺I = ψ≺κ od
  md : M 𝕎 ⟨ psi IR e ⟩
  md = C-ψ⁺ od d≺I (c! OT-I (here [])) ce
  B⊆ : Bω c ⊆ (𝕎 ∣ ⟨ psi IR e ⟩)
  B⊆ (n , refl) = Ωⁿ∈𝕎 c∈𝕎 c≺I n , ≺⇒⪯ (Ωⁿ≺Fi refl od oc c≺d n)
  cover : ∀ {y} → τ 𝕎 ⟨ psi IR e ⟩ y → ∃ λ b → Bω c b × y ⪯ b
  cover {y} (cy , y≺d) =
    let (n , y≺Ωⁿ) = Ωⁿ-bound oy (≺-trans y≺d d≺I)
    in Ωⁿ (c + one) n , (n , refl)
       , ≺⇒⪯ (≺⪯-trans y≺Ωⁿ (Ωⁿ-mono n (+-OT (mFi-OT oy) OT-one) (+-OT oc OT-one)
                                          (+1-mono (mFi-OT oy) oc (mFi⪯c oy y≺d))))
    where
      oy : OT y
      oy = C⊆OT cy
  result : 𝕎 ⟨ psi IR e ⟩
  result = L430.L4-30 md d≺I (Bω c) cover B⊆

𝕎-ψI0 : 𝕎 ⟨ psi IR zer ⟩
𝕎-ψI0 = ψI.result zer zer 0∈𝕎 (0≺reg IR) (ot! refl) 0≺ψI0 mFi⪯0 (c! OT-0 (here []))
  where
    0≺ψI0 : zer ≺ ⟨ psi IR zer ⟩
    0≺ψI0 = ⪯-sub⇒≺ (Data.Nat.Base.s≤s (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)) (0⪯ _)
    mFi⪯0 : ∀ {y} → OT y → y ≺ ⟨ psi IR zer ⟩ → mFi y ⪯ zer
    mFi⪯0 oy y≺ψ with mFi-Fi oy
    ... | inj₂ e  = ≡⇒⪯ e
    ... | inj₁ fi = ⊥-elim (≺⇒¬⪯ y≺ψ (⪯-trans (ψI0-least fi (mFi-OT oy)) (mFi⪯ oy)))

𝕎-ψI+1 : ∀ {x} → OT ⟨ psi IR (x + one) ⟩ → 𝕎 ⟨ psi IR x ⟩ → 𝕎 ⟨ psi IR (x + one) ⟩
𝕎-ψI+1 {x} od+ w = ψI.result ⟨ psi IR x ⟩ (x + one) w (ψ≺κ ox) od+ ψx≺ψx+1 mFi⪯ψx ce
  where
    ox : OT ⟨ psi IR x ⟩
    ox = 𝕎⊆OT w
    ox′ : OT x
    ox′ = proj₁ (OT-ψ⁻ ox)
    ψx≺ψx+1 : ⟨ psi IR x ⟩ ≺ ⟨ psi IR (x + one) ⟩
    ψx≺ψx+1 = ψI-mono ox od+ (x≺x+1 ox′)
    mFi⪯ψx : ∀ {y} → OT y → y ≺ ⟨ psi IR (x + one) ⟩ → mFi y ⪯ ⟨ psi IR x ⟩
    mFi⪯ψx oy y≺d with mFi-Fi oy
    ... | inj₂ e  = subst (λ t → t ⪯ ⟨ psi IR x ⟩) (sym e) (0⪯ _)
    ... | inj₁ fi = Fi≺ψI+1⇒⪯ fi (mFi-OT oy) od+ (⪯≺-trans (mFi⪯ oy) y≺d)
    -- x ∈ C^{ψ_I x}(𝕎)
    cx : C ⟨ psi IR x ⟩ 𝕎 x
    cx with C-ψ⁻ (𝕎⊆M w)
    ... | inj₁ (_ , ψ≺ψ)    = ⊥-elim (≺-irrefl ψ≺ψ)
    ... | inj₂ (_ , _ , cx′) = cx′
    c0 : C ⟨ psi IR x ⟩ 𝕎 zer
    c0 = c! OT-0 (here [])
    c1 : C ⟨ psi IR x ⟩ 𝕎 one
    c1 = C-φ⁺ OT-one c0 c0
    -- x + 1 ∈ C^{ψ_I x}(𝕎)，x + 1 ∈ C̃_I(x)
    cx+1 : C ⟨ psi IR x ⟩ 𝕎 (x + one)
    cx+1 with x+1-view x ox′
    ... | inj₁ (refl , e) = subst (C ⟨ psi IR zer ⟩ 𝕎) (sym e) c1
    ... | inj₂ (nz , e)   = subst (C ⟨ psi IR x ⟩ 𝕎) (sym e) (C-+⁺ nz (subst OT e (+-OT ox′ OT-one)) cx c1)
    gx+1 : inC̃ IR x (x + one) ≡ true
    gx+1 with x+1-view x ox′
    ... | inj₁ (refl , e) = subst (λ t → inC̃ IR zer t ≡ true) (sym e) refl
    ... | inj₂ (nz , e)   =
      subst (λ t → inC̃ IR x t ≡ true) (sym e) (allLt-++⁺ (G IR x) (proj₂ (proj₂ (proj₂ (OT-ψ⁻ ox)))) refl)
    ce : C ⟨ psi IR (x + one) ⟩ 𝕎 (x + one)
    ce = L4-7e ox ox od+ ⪯-refl (ψ≺κ ox) (≺⇒⪯ ψx≺ψx+1) (ψ≺κ od+) (x + one) gx+1 cx+1
```
