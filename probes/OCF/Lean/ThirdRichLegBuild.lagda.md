# Third 全种类富合法化：底与塔互递归

沿原 `Sb` 和 `Tw` 的种类结构寻找产生该种类的 `step`。
`Sb (suc n)` 的组件进入第 n 个底的塔；塔在零高度回到该底。
不读 `Pos`，不判层号，不洗坐标，也不将任何非指标分支改成常值。
这里只构造新的合法化，不改旧 `ThirdLeg` 与旧闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLegBuild where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; FX)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; pw; lgpw)
open import OCF.Lean.ThirdRichLegIf

module _ {T : KS} where
  θS : ∀ n (c : Ctx T (Sb n)) (κ : K (Sb n)) → (E (Sb n) κ → HB T) → E (Sb n) κ → HB T
  θT : ∀ n m (c : Ctx T (Tw (Sb n) m)) (κ : K (Tw (Sb n) m)) →
    (E (Tw (Sb n) m) κ → HB T) → E (Tw (Sb n) m) κ → HB T
  θS zero c () g d
  θS (suc n) c (inj₁ _ , inj₂ _) g d = New.θ (viaL {F = FX (Sb n)} c (inj₁ tt)) g d
  θS (suc n) c (inj₁ _ , inj₁ κ) g d = θS n (viaS (viaL {F = FX (Sb n)} c (inj₁ tt))) κ g d
  θS (suc n) c (inj₂ e , κ) g d = θT n (hs e) (viaL {F = FX (Sb n)} c (inj₂ e)) κ g d
  θT n hz c κ g d = θS n c κ g d
  θT n (hs m) c (inj₂ _) g d = New.θ c g d
  θT n (hs m) c (inj₁ κ) g d = θT n m (viaS c) κ g d
  θT n (hl f) c (i , κ) g d = θT n (f i) (viaL c i) κ g d
  θT n (hΩ κ₀ h) c (e , κ) g d = θT n (h e) (viaL c e) κ g d

  θS-⊲ : ∀ n (c : Ctx T (Sb n)) κ g {W d d′} → Pr (Sb n) κ (pw c W) d d′ → θS n c κ g d ⊲[ W ] θS n c κ g d′
  θT-⊲ : ∀ n m (c : Ctx T (Tw (Sb n) m)) κ g {W d d′} → Pr (Tw (Sb n) m) κ (pw c W) d d′ → θT n m c κ g d ⊲[ W ] θT n m c κ g d′
  θS-⊲ zero c () g p
  θS-⊲ (suc n) c (inj₁ _ , inj₂ _) g p = New.θ-⊲ (viaL {F = FX (Sb n)} c (inj₁ tt)) g p
  θS-⊲ (suc n) c (inj₁ _ , inj₁ κ) g p = θS-⊲ n (viaS (viaL {F = FX (Sb n)} c (inj₁ tt))) κ g p
  θS-⊲ (suc n) c (inj₂ e , κ) g p = θT-⊲ n (hs e) (viaL {F = FX (Sb n)} c (inj₂ e)) κ g p
  θT-⊲ n hz c κ g p = θS-⊲ n c κ g p
  θT-⊲ n (hs m) c (inj₂ _) g p = New.θ-⊲ c g p
  θT-⊲ n (hs m) c (inj₁ κ) g p = θT-⊲ n m (viaS c) κ g p
  θT-⊲ n (hl f) c (i , κ) g p = θT-⊲ n (f i) (viaL c i) κ g p
  θT-⊲ n (hΩ κ₀ h) c (e , κ) g p = θT-⊲ n (h e) (viaL c e) κ g p

  Lg-θS : ∀ n (c : Ctx T (Sb n)) κ g → (∀ d → LgB (g d)) → ∀ {W d} → LgW T W → Bd (Sb n) κ d (pw c W) → LgB (θS n c κ g d)
  Lg-θT : ∀ n m (c : Ctx T (Tw (Sb n) m)) κ g → (∀ d → LgB (g d)) → ∀ {W d} → LgW T W → Bd (Tw (Sb n) m) κ d (pw c W) → LgB (θT n m c κ g d)
  Lg-θS zero c () g lg lw b
  Lg-θS (suc n) c (inj₁ _ , inj₂ _) g lg {d = d} lw b =
    New.Lg-θ (viaL {F = FX (Sb n)} c (inj₁ tt)) g lg d
      (lgB⊲ b (proj₁ (lgpw (viaL {F = FX (Sb n)} c (inj₁ tt)) lw)) (proj₂ (lgpw (viaL {F = FX (Sb n)} c (inj₁ tt)) lw)))
  Lg-θS (suc n) c (inj₁ _ , inj₁ κ) g lg lw b = Lg-θS n (viaS (viaL {F = FX (Sb n)} c (inj₁ tt))) κ g lg lw b
  Lg-θS (suc n) c (inj₂ e , κ) g lg lw b = Lg-θT n (hs e) (viaL {F = FX (Sb n)} c (inj₂ e)) κ g lg lw b
  Lg-θT n hz c κ g lg lw b = Lg-θS n c κ g lg lw b
  Lg-θT n (hs m) c (inj₂ _) g lg {d = d} lw b = New.Lg-θ c g lg d (lgB⊲ b (proj₁ (lgpw c lw)) (proj₂ (lgpw c lw)))
  Lg-θT n (hs m) c (inj₁ κ) g lg lw b = Lg-θT n m (viaS c) κ g lg lw b
  Lg-θT n (hl f) c (i , κ) g lg lw b = Lg-θT n (f i) (viaL c i) κ g lg lw b
  Lg-θT n (hΩ κ₀ h) c (e , κ) g lg lw b = Lg-θT n (h e) (viaL c e) κ g lg lw b

allS : ∀ n → AllKinds (Sb n)
allS n = record { θK = θS n ; position = θS-⊲ n ; legal = Lg-θS n }

allT : ∀ n m → AllKinds (Tw (Sb n) m)
allT n m = record { θK = θT n m ; position = θT-⊲ n m ; legal = Lg-θT n m }

module Complete {S : KS} (A : AllKinds S) where
  open AllKinds A
  partial : (ℕ → HB S) → ℕ → HB S
  partial f zero = f zero
  partial f (suc n) = partial f n ⊞ f (suc n)

  leg : HB S → HB S
  leg hz = hz
  leg (hs a) = hs (leg a)
  leg (hl f) = hl (partial (λ n → leg (f n)))
  leg (hΩ κ g) = hΩ κ (θK here κ (λ e → leg (g e)))

  legal-leg : ∀ a → LgB (leg a)
  legal-partial : ∀ f n → LgB (partial (λ m → leg (f m)) n)
  legal-leg hz = tt
  legal-leg (hs a) = legal-leg a
  legal-leg (hl f) = (λ n → ⊞-fst _ (leg (f (suc n)))) , legal-partial f
  legal-leg (hΩ κ g) =
    (λ lw b b′ p → position here κ (λ e → leg (g e)) p) ,
    (λ lw b → legal here κ (λ e → leg (g e)) (λ e → legal-leg (g e)) lw b)
  legal-partial f zero = legal-leg (f zero)
  legal-partial f (suc n) = Lg-⊞ _ _ (legal-partial f n) (legal-leg (f (suc n)))

legS : ∀ n → HB (Sb n) → HB (Sb n)
legS n = Complete.leg (allS n)
Lg-legS : ∀ n a → LgB (legS n a)
Lg-legS n = Complete.legal-leg (allS n)

legT : ∀ n m → HB (Tw (Sb n) m) → HB (Tw (Sb n) m)
legT n m = Complete.leg (allT n m)
Lg-legT : ∀ n m a → LgB (legT n m a)
Lg-legT n m = Complete.legal-leg (allT n m)
```

`allS/allT` 实填全部种类；`legS/legT` 的合法性不要求输入合法。
所增加的后继项是否给全域值不缩，另由值侧验收；这里没有把合法性
作为强度证据，也没有把新合法化偷偷代入旧闭项。
