# Lemma 4.7 (e)(f)：C^a(A) 在 ψ_I 之下的稳定性

Setzer [Se98] Lemma 4.7 (e)：`ψ_I a ⪯ b ≺ I`，`ψ_I a ⪯ c ≺ I`，`a ∈ C_I(a)` ⟹ `C^b(A) ∩ C_I(a) ≅ C^c(A) ∩ C_I(a)`。要点：C̃_I(a) ∩ I 恰是 ψ_I a 以下的项（Remark 2.15 (c)），所以 `A ∩ b` 与 `A ∩ c` 对 C̃_I(a) 的元素无区别；ψ_κ u₁ ∈ C̃_I(a) 时若 κ ≺ I 则 κ ⪯ ψ_I a ⪯ b, c（(≺′6)），K 只看 {{u}}；若 I ⪯ κ 则 κ、u₁ 也在 C̃_I(a)。

(f)（只证 ⟹，且只在 `d ≺ ã` 的情形；`ã ⪯ d` 时就是 Lemma 5.5 (d) 经 C^a ≅ C^ã）：`a ≺ κ`，`d = ψ_κ c ∈ C^a(A)`，`d ≺ ã` ⟹ `κ = I` 且（`d ∈ A ∩ ã` 或 `c ∈ C^d(A)`）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Lemma47ef (F : OTFacts) where

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
open import Mahlo.Inacc.WO.Closed2 F using (sizeRec)
open import Mahlo.Inacc.WO.CTilde F

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

private variable
  ℓ : Level
  A : Pred ℓ

Car-ψI : ∀ a → isCarT ⟨ psi IR a ⟩ ≡ true
Car-ψI a = refl
```

## (e)

```agda
L4-7e : ∀ {a b c} → OT ⟨ psi IR a ⟩ → OT b → OT c
      → ⟨ psi IR a ⟩ ⪯ b → b ≺ I′ → ⟨ psi IR a ⟩ ⪯ c → c ≺ I′
      → ∀ u → inC̃ IR a u ≡ true → C b A u → C c A u
L4-7e {A = A} {a} {b} {c} oψ ob oc ψ⪯b b≺I ψ⪯c c≺I =
  sizeRec (λ u → inC̃ IR a u ≡ true → C b A u → C c A u) step
  where
    -- u ∈ A ∩ b，u ∈ C̃_I(a)，u ≺ I ⟹ u ≺ ψ_I a ⪯ c
    viaA : ∀ {u} → OT u → inC̃ IR a u ≡ true → A u → u ≺ b → C c A u
    viaA ou g au u≺b = A∩a⊆C (au , ou , ≺⪯-trans (C̃⇒≺ψ oψ ou (≺-trans u≺b b≺I) g) ψ⪯c)

    step : ∀ u → (∀ v → size v < size u → inC̃ IR a v ≡ true → C b A v → C c A v)
         → inC̃ IR a u ≡ true → C b A u → C c A u
    step zer        ih g cu = c! OT-0 (here [])
    step (zer ▹ I)  ih g cu = c! OT-I (here [])
    step (u₁ ▹ q ▹ p) ih g cu with C-+⁻ tt cu
    ... | inj₁ (au , u≺b) = viaA (C⊆OT cu) g au u≺b
    ... | inj₂ (c₁ , c₂) =
      let (g₁ , g₂) = inC̃-▹ IR a (u₁ ▹ q) p g
      in C-+⁺ tt (C⊆OT cu) (ih (u₁ ▹ q) (size-▹ˡ (u₁ ▹ q) p) g₁ c₁) (ih ⟨ p ⟩ (size-▹ʳ (u₁ ▹ q) p tt) g₂ c₂)
    step (zer ▹ phi u₁ u₂) ih g cu with C-φ⁻ cu
    ... | inj₁ (au , u≺b) = viaA (C⊆OT cu) g au u≺b
    ... | inj₂ (c₁ , c₂) =
      let (g₁ , g₂) = inC̃-φ IR a u₁ u₂ g
      in C-φ⁺ (C⊆OT cu) (ih u₁ (size-φˡ u₁ u₂) g₁ c₁) (ih u₂ (size-φʳ u₁ u₂) g₂ c₂)
    step (zer ▹ Om u₁) ih g cu with C-Ω⁻ cu
    ... | inj₁ (au , u≺b) = viaA (C⊆OT cu) g au u≺b
    ... | inj₂ c₁ = C-Ω⁺ (C⊆OT cu) (ih u₁ (size-Ω u₁) (inC̃-Ω IR a u₁ g) c₁)
    step (zer ▹ psi IR u₁) ih g cu with C-ψ⁻ cu
    ... | inj₁ (au , u≺b) = viaA (C⊆OT cu) g au u≺b
    ... | inj₂ (_ , _ , c₁) =
      let (g₁ , _) = inC̃-ψII a u₁ g
      in C-ψ⁺ (C⊆OT cu) c≺I (c! OT-I (here [])) (ih u₁ (size-ψc IR u₁) g₁ c₁)
    step (zer ▹ psi (ΩR z) u₁) ih g cu with C-ψ⁻ cu
    ... | inj₁ (au , u≺b) = viaA (C⊆OT cu) g au u≺b
    ... | inj₂ (b≺κ , cκ , c₁) = byI (≺-or-⪰ ⟨ Om z ⟩ I′)
      where
        ou : OT ⟨ psi (ΩR z) u₁ ⟩
        ou = C⊆OT cu
        oκ : OT ⟨ Om z ⟩
        oκ = proj₁ (proj₂ (OT-ψ⁻ ou))
        byI : ⟨ Om z ⟩ ≺ I′ ⊎ I′ ⪯ ⟨ Om z ⟩ → C c A ⟨ psi (ΩR z) u₁ ⟩
        byI (inj₁ κ≺I) =
          -- u ≺ κ ≺ I ⟹ u ≺ ψ_I a ⟹ κ ⪯ ψ_I a ⪯ b，与 b ≺ κ 矛盾
          ⊥-elim (≺⇒¬⪯ b≺κ
            (⪯-trans (ψ≺Car⇒κ⪯ (Car-ψI a) ou oψ
                        (C̃⇒≺ψ oψ ou (≺-trans (ψ≺κ ou) κ≺I) g))
                     ψ⪯b))
        byI (inj₂ I⪯κ) =
          let (gκ , g₁ , _) = inC̃-ψIΩ a z u₁ I⪯κ g
          in C-ψ⁺ ou (≺⪯-trans c≺I I⪯κ)
                  (ih ⟨ Om z ⟩ (size-ψκ z u₁) gκ cκ) (ih u₁ (size-ψc (ΩR z) u₁) g₁ c₁)

L4-7e≅ : ∀ {a b c} → OT ⟨ psi IR a ⟩ → OT b → OT c
       → ⟨ psi IR a ⟩ ⪯ b → b ≺ I′ → ⟨ psi IR a ⟩ ⪯ c → c ≺ I′
       → ∀ u → inC̃ IR a u ≡ true → (C b A u → C c A u) × (C c A u → C b A u)
L4-7e≅ oψ ob oc ψ⪯b b≺I ψ⪯c c≺I u g =
  L4-7e oψ ob oc ψ⪯b b≺I ψ⪯c c≺I u g , L4-7e oψ oc ob ψ⪯c c≺I ψ⪯b b≺I u g
```

## (f)：`d = ψ_κ c ≺ ã`，`a ≺ κ` 的情形

`κ ≠ I` 不可能（ã ≺ κ 给 ã ⪯ κ⁻ ⪯ d）。`κ = I`：`d ∈ C^a(A) ≅ C^ã(A)`，K^ã(ψ_I c) 分两支：`d ∈ A ∩ ã`，或 `c ∈ C^ã(A)`，而后者由 (e)（b := ã，c := d）等价于 `c ∈ C^d(A)`。

```agda
L4-7f : A ⊆ M A → ∀ {a κ c} → OT a → OT ⟨ psi κ c ⟩ → a ≺ regTm κ → ⟨ psi κ c ⟩ ≺ tilde a
      → C a A ⟨ psi κ c ⟩
      → (A ⟨ psi κ c ⟩ × ⟨ psi κ c ⟩ ≺ tilde a) ⊎ (κ ≡ IR × C ⟨ psi κ c ⟩ A c)
L4-7f h {a} {κ = ΩR z} {c} oa od a≺κ d≺ã cd = ⊥-elim (impossible (tilde-Car oa))
  where
    impossible : isCarT (tilde a) ≡ true ⊎ tilde a ≡ zer → ⊥
    impossible (inj₂ e) = ¬≺0′ (subst (λ t → ⟨ psi (ΩR z) c ⟩ ≺ t) e d≺ã)
      where ¬≺0′ : ∀ {x} → x ≺ zer → ⊥
            ¬≺0′ {x} p = ≺⇒¬⪯ p (0⪯ x)
    impossible (inj₁ ca) =
      ≺⇒¬⪯ d≺ã
        (⪯-trans (Car≺κ⇒⪯κ⁻ (tilde-OT oa) ca (proj₁ (proj₂ (proj₂ (OT-ψ⁻ od))))
                              (proj₁ (proj₂ (OT-ψ⁻ od))) (⪯≺-trans (tilde⪯ oa) a≺κ))
                 (≺⇒⪯ (κ⁻≺ψ od)))
L4-7f h {a} {κ = IR} {c} oa od a≺κ d≺ã cd = split (C-ψ⁻ (proj₁ (C-tilde h oa) cd))
  where
    split : (A ⟨ psi IR c ⟩ × ⟨ psi IR c ⟩ ≺ tilde a)
          ⊎ (tilde a ≺ I′ × C (tilde a) A I′ × C (tilde a) A c)
          → (A ⟨ psi IR c ⟩ × ⟨ psi IR c ⟩ ≺ tilde a) ⊎ (IR ≡ IR × C ⟨ psi IR c ⟩ A c)
    split (inj₁ p) = inj₁ p
    split (inj₂ (ã≺I , _ , cc)) =
      inj₂ (refl , L4-7e od (tilde-OT oa) od (≺⇒⪯ d≺ã) ã≺I ⪯-refl (ψ≺κ od) c
                          (proj₂ (proj₂ (proj₂ (OT-ψ⁻ od)))) cc)
```

## (g)：`C^d(A) ∩ (⪯ d̃) ⊆ C^a(A)`（d ≺ a ≺ I）

Setzer 的 (g) 是 `b̃ ⪯ c`，`b^{−I} = c^{−I}` 下的等价；这里只证 Lemma 4.30 用到的方向，前提简化为 `d ≺ a ≺ I`。按 x 的 size 归纳：x ∈ A ∩ d ⊆ A ∩ a；x = ψ_κ x₀ 且 d ≺ κ 时 κ = I（否则 d̃ ⪯ κ⁻ ⪯ x ⪯ d̃ 给 x = d̃ ∈ Car′，形状矛盾），x₀ ∈ C^a(A) 由 (e)。

```agda
L4-7g : A ⊆ M A → ∀ {d a} → OT d → OT a → d ≺ a → a ≺ I′
      → ∀ x → OT x → x ⪯ tilde d → C d A x → C a A x
L4-7g {A = A} h {d} {a} od oa d≺a a≺I =
  sizeRec (λ x → OT x → x ⪯ tilde d → C d A x → C a A x) step
  where
    d≺I : d ≺ I′
    d≺I = ≺-trans d≺a a≺I
    -- x ∈ A ∩ d ⟹ x ∈ C^a(A)
    viaA : ∀ {x} → OT x → A x → x ≺ d → C a A x
    viaA ox ax x≺d = A∩a⊆C (ax , ox , ≺-trans x≺d d≺a)
    -- 子项 ⪯ d̃
    sub : ∀ {y x} → y ≺ x → x ⪯ tilde d → y ⪯ tilde d
    sub y≺x x⪯d̃ = ⪯-trans (≺⇒⪯ y≺x) x⪯d̃

    step : ∀ x → (∀ y → size y < size x → OT y → y ⪯ tilde d → C d A y → C a A y)
         → OT x → x ⪯ tilde d → C d A x → C a A x
    step zer       ih ox x⪯ cx = c! OT-0 (here [])
    step (zer ▹ I) ih ox x⪯ cx = c! OT-I (here [])
    step (x₁ ▹ q ▹ p) ih ox x⪯ cx with C-+⁻ tt cx
    ... | inj₁ (ax , x≺d) = viaA ox ax x≺d
    ... | inj₂ (c₁ , c₂) =
      C-+⁺ tt ox (ih (x₁ ▹ q) (size-▹ˡ (x₁ ▹ q) p) (C⊆OT c₁) (sub (≺-+ˡ tt ox) x⪯) c₁)
                 (ih ⟨ p ⟩ (size-▹ʳ (x₁ ▹ q) p tt) (C⊆OT c₂) (sub (≺-+ʳ tt ox) x⪯) c₂)
    step (zer ▹ phi x₁ x₂) ih ox x⪯ cx with C-φ⁻ cx
    ... | inj₁ (ax , x≺d) = viaA ox ax x≺d
    ... | inj₂ (c₁ , c₂) =
      C-φ⁺ ox (ih x₁ (size-φˡ x₁ x₂) (C⊆OT c₁) (sub (≺-φˡ ox) x⪯) c₁)
              (ih x₂ (size-φʳ x₁ x₂) (C⊆OT c₂) (sub (≺-φʳ ox) x⪯) c₂)
    step (zer ▹ Om x₁) ih ox x⪯ cx with C-Ω⁻ cx
    ... | inj₁ (ax , x≺d) = viaA ox ax x≺d
    ... | inj₂ c₁ = C-Ω⁺ ox (ih x₁ (size-Ω x₁) (C⊆OT c₁) (sub (≺-Ω ox) x⪯) c₁)
    step (zer ▹ psi κ x₀) ih ox x⪯ cx with C-ψ⁻ cx
    ... | inj₁ (ax , x≺d) = viaA ox ax x≺d
    ... | inj₂ (d≺κ , cκ , c₀) = byκ κ ox x⪯ cx d≺κ cκ c₀
      where
        byκ : ∀ κ → OT ⟨ psi κ x₀ ⟩ → ⟨ psi κ x₀ ⟩ ⪯ tilde d → C d A ⟨ psi κ x₀ ⟩
            → d ≺ regTm κ → C d A (regTm κ) → C d A x₀ → C a A ⟨ psi κ x₀ ⟩
        -- κ = I：x₀ ∈ C^a(A) 由 (e)（b := d，c := a）
        byκ IR ox x⪯ cx d≺I′ cκ c₀ =
          C-ψ⁺ ox a≺I (c! OT-I (here []))
            (L4-7e ox od oa (⪯-trans x⪯ (tilde⪯ od)) d≺I (⪯-trans (⪯-trans x⪯ (tilde⪯ od)) (≺⇒⪯ d≺a)) a≺I
                   x₀ (proj₂ (proj₂ (proj₂ (OT-ψ⁻ ox)))) c₀)
        -- κ = Ω′_z：d̃ ⪯ κ⁻ ⪯ x ⪯ d̃ ⟹ x = d̃ ∈ Car′ ∪ {0}，形状矛盾
        byκ (ΩR z) ox x⪯ cx d≺κ cκ c₀ = ⊥-elim (bad (tilde-Car od))
          where
            rκ : isRR (ΩR z) ≡ true
            rκ = proj₁ (proj₂ (proj₂ (OT-ψ⁻ ox)))
            oκ : OT ⟨ Om z ⟩
            oκ = proj₁ (proj₂ (OT-ψ⁻ ox))
            bad : isCarT (tilde d) ≡ true ⊎ tilde d ≡ zer → ⊥
            bad (inj₂ e0) = ¬0 (⪯0⇒≡0 (subst (λ t → ⟨ psi (ΩR z) x₀ ⟩ ⪯ t) e0 x⪯))
              where
                ¬0 : ⟨ psi (ΩR z) x₀ ⟩ ≡ zer → ⊥
                ¬0 ()
            bad (inj₁ ca) = ¬Car (subst (λ t → isCarT t ≡ true) (sym x≡d̃) ca)
              where
                d̃⪯x : tilde d ⪯ ⟨ psi (ΩR z) x₀ ⟩
                d̃⪯x = ⪯-trans (Car≺κ⇒⪯κ⁻ (tilde-OT od) ca rκ oκ (⪯≺-trans (tilde⪯ od) d≺κ))
                               (≺⇒⪯ (κ⁻≺ψ ox))
                x≡d̃ : ⟨ psi (ΩR z) x₀ ⟩ ≡ tilde d
                x≡d̃ = ⪯-antisym x⪯ d̃⪯x
                ¬Car : isCarT ⟨ psi (ΩR z) x₀ ⟩ ≡ true → ⊥
                ¬Car ()
```
