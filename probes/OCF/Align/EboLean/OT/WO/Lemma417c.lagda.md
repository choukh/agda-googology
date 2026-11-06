# Lemma 4.17 (c)：W(A) 对 ψ 封闭

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Lemma417c` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] Lemma 4.17 (c)。设 `A ⊆ M(A)`，θ ∈ Car ∩ W(A)，`W(A) ∩ θ ≅ A ∩ θ`。对 y ∈ W(A) 作 W-归纳证：

> y ≺ θ⁺，κ ∈ R，(κ = I 或 κ⁻ ∈ W(A)|θ)，ψ_κ y ∈ OT（含 y ∈ C_κ(y)），ψ_κ y ≺ θ⁺ ⟹ ψ_κ y ∈ W(A)。

核心是 (∗)：`∀u ∈ C̃_κ(y) ∩ C^{ψ_κ y}(A) ∩ θ⁺. u ∈ W(A)`，按 u 的 size 归纳；和／φ／Ω 由 Lemma 4.17 (b)；`u = ψ_π u′` 按 u 与 ã := (ψ_κ y)~ 的三分：

- u ≺ ã：K^ã(u) 若走原子支则 u ∈ A ∩ θ ⊆ W(A)；若走 (π, u′) 支则 π = I（Lemma 4.7 (f) 的分析）：κ ≠ I 时 u ≺ κ⁻ ∈ W(A) 且 u ∈ τ^A(κ⁻)；κ = I 时 u′ ≺ y，u′ ∈ C^{ψ_I y}(A)（这里 ã = ψ_I y，比原文经 Lemma 4.7 (e) 直接），归纳假设给 u′ ∈ W(A)，主归纳假设给 ψ_I u′ ∈ W(A)。
- u = ã：κ ≠ I（ψ_I y ∉ C̃_I(y)），u = κ⁻ ∈ W(A)。
- ã ≺ u：Remark 2.15 (d)(e) 给 π, u′ ∈ C̃_κ(y)、u′ ≺ y；π, u′ ∈ C^{ψ_κ y}(A)（若 u ∈ A ∩ a 则经 u ∈ M(A) 与 C^u ≅ C^ã）；π 的侧条件：π ⪯ θ⁺，π ≺ θ⁺ 时由归纳假设 π ∈ W(A)、π⁻ ∈ W(A)（W(A) ∩ θ⁺ 向下封闭），π = θ⁺ 时 π⁻ = θ；主归纳假设给 ψ_π u′ ∈ W(A)。

最后 ψ_κ y ∈ M(A)：y ∈ C^{ψ_κ y}(A)（y ≺ ã 时 y ∈ A，否则 y ∈ M(A) 且 C^y ⊆ C^ã）；κ ∈ C^{ψ_κ y}(A)（κ = I 直接；否则 κ⁻ ∈ W(A) ⊆ M(A) 给 κ⁻ ∈ C^ã(A)，再搭出 κ = Ω′_{w+1}）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Lemma417c (F : OTFacts) where

open OTFacts F

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.WO.K
open import OCF.Align.EboLean.OT.WO.Base
open import OCF.Align.EboLean.OT.WO.CLemmas
open import OCF.Align.EboLean.OT.WO.OrderLemmas F
open import OCF.Align.EboLean.OT.WO.Lemma47 F
open import OCF.Align.EboLean.OT.WO.Lemma413 F
open import OCF.Align.EboLean.OT.WO.Dist F
open import OCF.Align.EboLean.OT.WO.Closed F
open import OCF.Align.EboLean.OT.WO.Closed2 F
open import OCF.Align.EboLean.OT.WO.CTilde F
open import OCF.Align.EboLean.OT.WO.Lemma47ef F
open import OCF.Align.EboLean.OT.WO.Lemma417b F

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ : Level
```

## 0. 假设与工具

```agda
module L417c {A : Pred ℓ} (h : A ⊆ M A) {θ : Tm} (oτ : OT θ) (cτ : isCarT θ ≡ true)
             (wτ : 𝒲 A θ) (E : (𝒲 A ∩ ↓ θ) ≅ (A ∩ ↓ θ)) where

  open L417b h oτ (≅-sym E)

  -- 「κ = I 或 κ⁻ ∈ W(A)|θ」
  KSide : Reg → Set ℓ
  KSide κ = κ ≡ IR ⊎ (𝒲 A (κ⁻ κ) × κ⁻ κ ⪯ θ)

  Q : Pred ℓ
  Q y = y ≺ K⁺ → ∀ κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → 𝒲 A ⟨ psi κ y ⟩

  -- u′ ∈ W(A)，u′ ≺ y ≺ τ⁺ ⟹ u′ ∈ τ^A(y)：u′ ≺ θ 时 u′ ∈ A ∩ y ⊆ C^y(A)；否则 ũ′ = θ = ỹ
  toτ : ∀ {y u′} → OT y → y ≺ K⁺ → 𝒲 A u′ → u′ ≺ y → τ A y u′
  toτ {y} {u′} oy y≺τ⁺ wu′ u′≺y with ≺-or-⪰ u′ θ
  ... | inj₁ u′≺τ = A∩a⊆C (W→A wu′ u′≺τ , 𝒲⊆OT wu′ , u′≺y) , u′≺y
  ... | inj₂ θ⪯u′ =
    proj₂ (C-tilde h oy) (subst (λ t → C t A u′) eq (proj₁ (C-tilde h (𝒲⊆OT wu′)) (𝒲-M wu′))) , u′≺y
    where
      ou′ : OT u′
      ou′ = 𝒲⊆OT wu′
      ũ′≡τ : tilde u′ ≡ θ
      ũ′≡τ = ⪯-antisym (≺plus⇒tilde⪯ ou′ oτ (≺-trans u′≺y y≺τ⁺)) (tilde-max ou′ oτ cτ θ⪯u′)
      ỹ≡τ : tilde y ≡ θ
      ỹ≡τ = ⪯-antisym (≺plus⇒tilde⪯ oy oτ y≺τ⁺) (tilde-max oy oτ cτ (⪯-trans θ⪯u′ (≺⇒⪯ u′≺y)))
      eq : tilde u′ ≡ tilde y
      eq = trans ũ′≡τ (sym ỹ≡τ)

  -- ã ⪯ u ⪯ a ⟹ C^u(A) ⊆ C^a(A)
  Cu⊆Ca : ∀ {a u} → OT a → OT u → tilde a ⪯ u → u ⪯ a → C u A ⊆ C a A
  Cu⊆Ca {a} {u} oa ou ã⪯u u⪯a {x} c =
    proj₂ (C-tilde h oa) (subst (λ t → C t A x) (tilde-between oa ou ã⪯u u⪯a) (proj₁ (C-tilde h ou) c))

  -- κ = Ω′_{w+1} ∈ C^a(A) 从 κ⁻ = Ω_w ∈ C^a(A)
  Cκ-from-κ⁻ : ∀ {a} → OT a → WDC (C a A) → ∀ z → isRR (ΩR z) ≡ true → OT ⟨ Om z ⟩
             → C a A (κ⁻ (ΩR z)) → C a A ⟨ Om z ⟩
  Cκ-from-κ⁻ {a} oa w z rz oz cκ⁻ with regView (ΩR z) rz
  ... | succ zer     = C-Ω⁺ oz (C-φ⁺ OT-one c0 c0)
    where c0 = c! OT-0 (here [])
  ... | succ (w′ ▹ r) = C-Ω⁺ oz (C-+⁺ tt (proj₁ (OT-Ω⁻ oz)) cw (C-φ⁺ OT-one c0 c0))
    where
      c0 = c! OT-0 (here [])
      ow : OT (w′ ▹ r)
      ow = proj₁ (OT-▹⁻ tt (proj₁ (OT-Ω⁻ oz)))
      cw : C a A (w′ ▹ r)
      cw with Ω-view (w′ ▹ r)
      ... | Ω-0 () _
      ... | Ω-Fi _ e     = subst (C a A) e cκ⁻
      ... | Ω-Om e₀ e₁ e = wdc-Ω w (OT-Ω⁺ ow e₁ e₀) (subst (C a A) e cκ⁻)
```

## 1. ψ_κ y ∈ M(A)

```agda
  Cκ : ∀ {y} κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → C ⟨ psi κ y ⟩ A (regTm κ)
  Cκ IR     _                o _    = c! OT-I (here [])
  Cκ (ΩR z) (inj₁ ())        o _
  Cκ (ΩR z) (inj₂ (wκ⁻ , _)) o a≺τ⁺ =
    Cκ-from-κ⁻ o (CaWDC o a≺τ⁺) z (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o)))) (proj₁ (proj₂ (OT-ψ⁻ o)))
      (proj₂ (C-tilde h o) (𝒲-M wκ⁻))

  Ma : ∀ {y} → 𝒲 A y → y ≺ K⁺ → ∀ κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → M A ⟨ psi κ y ⟩
  Ma {y} wy y≺τ⁺ κ ks o a≺τ⁺ = C-ψ⁺ o (ψ≺κ o) (Cκ κ ks o a≺τ⁺) cy
    where
      oy : OT y
      oy = proj₁ (OT-ψ⁻ o)
      cy : C ⟨ psi κ y ⟩ A y
      cy with ≺-or-⪰ y (tilde ⟨ psi κ y ⟩)
      ... | inj₁ y≺ã = proj₂ (C-tilde h o) (A∩a⊆C (W→A wy (≺⪯-trans y≺ã (ã⪯κ o a≺τ⁺)) , oy , y≺ã))
      ... | inj₂ ã⪯y = proj₂ (C-tilde h o) (C-anti h (tilde-OT o) (tilde-OT oy) ã⪯ỹ (proj₁ (C-tilde h oy) (𝒲-M wy)))
        where
          ã⪯ỹ : tilde ⟨ psi κ y ⟩ ⪯ tilde y
          ã⪯ỹ with tilde-Car o
          ... | inj₁ ca = tilde-max oy (tilde-OT o) ca ã⪯y
          ... | inj₂ e0 = subst (λ t → t ⪯ tilde y) (sym e0) (0⪯ (tilde y))
```

## 2. (∗) 的 ψ 情形

```agda
  -- 归纳假设的形状
  IH : Tm → Reg → Tm → Set ℓ
  IH y κ u = ∀ v → size v < size u → OT v → inC̃ κ y v ≡ true → C ⟨ psi κ y ⟩ A v → v ≺ K⁺ → 𝒲 A v

  -- u ≺ ã
  belowã : ∀ {y} κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → 𝒲 A y → y ≺ K⁺ → τ A y ⊆ Q
         → ∀ π u′ → OT ⟨ psi π u′ ⟩ → inC̃ κ y ⟨ psi π u′ ⟩ ≡ true → C ⟨ psi κ y ⟩ A ⟨ psi π u′ ⟩
         → ⟨ psi π u′ ⟩ ≺ K⁺ → ⟨ psi π u′ ⟩ ≺ tilde ⟨ psi κ y ⟩ → IH y κ ⟨ psi π u′ ⟩
         → 𝒲 A ⟨ psi π u′ ⟩
  belowã {y} κ ks o a≺τ⁺ wy y≺τ⁺ ihy π u′ ou g cu u≺τ⁺ u≺ã ih with C-ψ⁻ (proj₁ (C-tilde h o) cu)
  ... | inj₁ (au , _) = proj₁ (proj₂ E (au , ou , ≺⪯-trans u≺ã (ã⪯κ o a≺τ⁺)))
  ... | inj₂ (ã≺π , cπ , cu′) = byπ π κ ks o ou g cu cu′ u≺ã ã≺π u≺τ⁺ ih
    where
      -- π ≠ I 不可能：ã ⪯ π⁻ ⪯ u
      byπ : ∀ π κ → KSide κ → OT ⟨ psi κ y ⟩ → OT ⟨ psi π u′ ⟩ → inC̃ κ y ⟨ psi π u′ ⟩ ≡ true
          → C ⟨ psi κ y ⟩ A ⟨ psi π u′ ⟩ → C (tilde ⟨ psi κ y ⟩) A u′
          → ⟨ psi π u′ ⟩ ≺ tilde ⟨ psi κ y ⟩ → tilde ⟨ psi κ y ⟩ ≺ regTm π
          → ⟨ psi π u′ ⟩ ≺ K⁺ → IH y κ ⟨ psi π u′ ⟩
          → 𝒲 A ⟨ psi π u′ ⟩
      byπ (ΩR z′) κ ks o ou g cu cu′ u≺ã ã≺π u≺τ⁺ ih = ⊥-elim (bad (tilde-Car o))
        where
          bad : isCarT (tilde ⟨ psi κ y ⟩) ≡ true ⊎ tilde ⟨ psi κ y ⟩ ≡ zer → ⊥
          bad (inj₂ e0) = ¬≺0 (subst (λ t → ⟨ psi (ΩR z′) u′ ⟩ ≺ t) e0 u≺ã)
          bad (inj₁ ca) =
            ≺⇒¬⪯ u≺ã (⪯-trans (Car≺κ⇒⪯κ⁻ (tilde-OT o) ca (proj₁ (proj₂ (proj₂ (OT-ψ⁻ ou))))
                                             (proj₁ (proj₂ (OT-ψ⁻ ou))) ã≺π)
                               (≺⇒⪯ (κ⁻≺ψ ou)))
      -- π = I，κ = I：u′ ≺ y，u′ ∈ C^{ψ_I y}(A)，归纳假设，再主归纳假设
      byπ IR IR ks o ou g cu cu′ u≺ã ã≺π u≺τ⁺ ih =
        ihy (toτ oy y≺τ⁺ wu′ u′≺y) u′≺τ⁺ IR (inj₁ refl) ou u≺τ⁺
        where
          oy : OT y
          oy = proj₁ (OT-ψ⁻ o)
          u′≺y : u′ ≺ y
          u′≺y = ψI-cmp ou o u≺ã
          u′≺τ⁺ : u′ ≺ K⁺
          u′≺τ⁺ = ≺-trans u′≺y y≺τ⁺
          wu′ : 𝒲 A u′
          wu′ = ih u′ (size-ψc IR u′) (proj₁ (OT-ψ⁻ ou)) (proj₁ (inC̃-ψII y u′ g)) cu′ u′≺τ⁺
      -- π = I，κ = Ω′_z：u ≺ κ⁻ ∈ W(A)，u ∈ τ^A(κ⁻)
      byπ IR (ΩR z) (inj₁ ()) o ou g cu cu′ u≺ã ã≺π u≺τ⁺ ih
      byπ IR (ΩR z) (inj₂ (wκ⁻ , _)) o ou g cu cu′ u≺ã ã≺π u≺τ⁺ ih =
        𝒲-τ wκ⁻ (C-anti h (tilde-OT o) o (κ⁻⪯ψ o) cu , u≺ã)

  -- u = ã
  atã : ∀ {y} κ → KSide κ → OT ⟨ psi κ y ⟩ → ∀ π u′ → inC̃ κ y ⟨ psi π u′ ⟩ ≡ true
      → ⟨ psi π u′ ⟩ ≡ tilde ⟨ psi κ y ⟩ → 𝒲 A ⟨ psi π u′ ⟩
  atã {y} IR ks o π u′ g e =
    ⊥-elim (true≢false (trans (sym (subst (λ t → inC̃ IR y t ≡ true) e g)) (ψ∉C̃ y)))
  atã (ΩR z) (inj₁ ())        o π u′ g e
  atã (ΩR z) (inj₂ (wκ⁻ , _)) o π u′ g e = subst (𝒲 A) (sym e) wκ⁻

  -- ã ≺ u：Remark 2.15 (d)(e) 的分解
  decomp : ∀ {y} κ → OT ⟨ psi κ y ⟩ → ∀ {π u′} → OT ⟨ psi π u′ ⟩ → inC̃ κ y ⟨ psi π u′ ⟩ ≡ true
         → tilde ⟨ psi κ y ⟩ ≺ ⟨ psi π u′ ⟩
         → inC̃ κ y (regTm π) ≡ true × inC̃ κ y u′ ≡ true × u′ ≺ y
  decomp IR     o ou g ã≺u with C̃-ψ-I ou o g
  ... | inj₁ u≺ψ = ⊥-elim (≺-asym u≺ψ ã≺u)
  ... | inj₂ r   = r
  decomp (ΩR z) o ou g ã≺u with C̃-ψ-Ω ou o g
  ... | inj₁ u⪯κ⁻ = ⊥-elim (≺⇒¬⪯ ã≺u u⪯κ⁻)
  ... | inj₂ r    = r

  -- ã ≺ u
  aboveã : ∀ {y} κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → 𝒲 A y → y ≺ K⁺ → τ A y ⊆ Q
         → ∀ π u′ → OT ⟨ psi π u′ ⟩ → inC̃ κ y ⟨ psi π u′ ⟩ ≡ true → C ⟨ psi κ y ⟩ A ⟨ psi π u′ ⟩
         → ⟨ psi π u′ ⟩ ≺ K⁺ → tilde ⟨ psi κ y ⟩ ≺ ⟨ psi π u′ ⟩ → IH y κ ⟨ psi π u′ ⟩
         → inC̃ κ y (regTm π) ≡ true × inC̃ κ y u′ ≡ true × u′ ≺ y
         → 𝒲 A ⟨ psi π u′ ⟩
  aboveã {y} κ ks o a≺τ⁺ wy y≺τ⁺ ihy π u′ ou g cu u≺τ⁺ ã≺u ih (gπ , gu′ , u′≺y) =
    ihy (toτ oy y≺τ⁺ wu′ u′≺y) u′≺τ⁺ π (πside π ou u≺τ⁺ ih gπ (proj₁ πu′∈Ca)) ou u≺τ⁺
    where
      a : Tm
      a = ⟨ psi κ y ⟩
      oy : OT y
      oy = proj₁ (OT-ψ⁻ o)
      ou′ : OT u′
      ou′ = proj₁ (OT-ψ⁻ ou)
      u′≺τ⁺ : u′ ≺ K⁺
      u′≺τ⁺ = ≺-trans u′≺y y≺τ⁺
      -- π, u′ ∈ C^a(A)
      πu′∈Ca : C a A (regTm π) × C a A u′
      πu′∈Ca with C-ψ⁻ cu
      ... | inj₂ (_ , cπ , cu′) = cπ , cu′
      ... | inj₁ (au , u≺a) = fromM (C-ψ⁻ (h au))
        where
          fromM : (A ⟨ psi π u′ ⟩ × ⟨ psi π u′ ⟩ ≺ ⟨ psi π u′ ⟩)
                ⊎ (⟨ psi π u′ ⟩ ≺ regTm π × C ⟨ psi π u′ ⟩ A (regTm π) × C ⟨ psi π u′ ⟩ A u′)
                → C a A (regTm π) × C a A u′
          fromM (inj₁ (_ , u≺u)) = ⊥-elim (≺-irrefl u≺u)
          fromM (inj₂ (_ , cπ , cu′)) =
            Cu⊆Ca o ou (≺⇒⪯ ã≺u) (≺⇒⪯ u≺a) cπ , Cu⊆Ca o ou (≺⇒⪯ ã≺u) (≺⇒⪯ u≺a) cu′
      wu′ : 𝒲 A u′
      wu′ = ih u′ (size-ψc π u′) ou′ gu′ (proj₂ πu′∈Ca) u′≺τ⁺
      -- π 的侧条件
      πside : ∀ π → OT ⟨ psi π u′ ⟩ → ⟨ psi π u′ ⟩ ≺ K⁺ → IH y κ ⟨ psi π u′ ⟩
            → inC̃ κ y (regTm π) ≡ true → C a A (regTm π) → KSide π
      πside IR _ _ _ _ _ = inj₁ refl
      πside (ΩR z′) ou u≺τ⁺ ih gπ cπ = byτ⁺ (⪯⇒≺⊎≡ π⪯τ⁺)
        where
          oπ : OT ⟨ Om z′ ⟩
          oπ = proj₁ (proj₂ (OT-ψ⁻ ou))
          rπ : isRR (ΩR z′) ≡ true
          rπ = proj₁ (proj₂ (proj₂ (OT-ψ⁻ ou)))
          π⁻⪯τ : κ⁻ (ΩR z′) ⪯ θ
          π⁻⪯τ = ≺plus⇒tilde⪯ ou oτ u≺τ⁺
          π⪯τ⁺ : ⟨ Om z′ ⟩ ⪯ K⁺
          π⪯τ⁺ = subst (λ t → t ⪯ K⁺) (plus-κ⁻ rπ oπ)
                   (plus-least (tilde-OT ou) (plus-OT oτ) (plus-Car oτ) (⪯≺-trans π⁻⪯τ (≺plus oτ)))
          byτ⁺ : ⟨ Om z′ ⟩ ≺ K⁺ ⊎ ⟨ Om z′ ⟩ ≡ K⁺ → KSide (ΩR z′)
          byτ⁺ (inj₁ π≺τ⁺) =
            inj₂ (proj₁ (dc-κ⁻ W⁺-DC rπ oπ (ih ⟨ Om z′ ⟩ (size-ψκ z′ u′) oπ gπ cπ π≺τ⁺ , oπ , π≺τ⁺)) , π⁻⪯τ)
          byτ⁺ (inj₂ e) = inj₂ (subst (𝒲 A) (sym eq) wτ , ≡⇒⪯ eq)
            where
              eq : κ⁻ (ΩR z′) ≡ θ
              eq = κ⁻∘plus cτ oτ (sym e)
```

## 3. (∗) 与主归纳

```agda
  star : ∀ {y} κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺ → 𝒲 A y → y ≺ K⁺ → τ A y ⊆ Q
       → ∀ u → OT u → inC̃ κ y u ≡ true → C ⟨ psi κ y ⟩ A u → u ≺ K⁺ → 𝒲 A u
  star {y} κ ks o a≺τ⁺ wy y≺τ⁺ ihy =
    sizeRec (λ u → OT u → inC̃ κ y u ≡ true → C ⟨ psi κ y ⟩ A u → u ≺ K⁺ → 𝒲 A u) stepu
    where
      a : Tm
      a = ⟨ psi κ y ⟩
      wC : WDC (C a A)
      wC = CaWDC o a≺τ⁺
      stepu : ∀ u → IH y κ u → OT u → inC̃ κ y u ≡ true → C a A u → u ≺ K⁺ → 𝒲 A u
      stepu zer           ih ou g cu u≺τ⁺ = 0∈𝒲
      stepu (zer ▹ I)     ih ou g cu u≺τ⁺ = W-I u≺τ⁺
      stepu (u₁ ▹ q ▹ p)  ih ou g cu u≺τ⁺ =
        let (g₁ , g₂) = inC̃-▹ κ y (u₁ ▹ q) p g
            (c₁ , c₂) = wdc-+ wC tt ou cu
            (o₁ , o₂ , _) = OT-+⁻ ou
            u₁≺τ⁺ = ≺-trans (≺-+ˡ tt ou) u≺τ⁺
        in W-+ (ih (u₁ ▹ q) (size-▹ˡ (u₁ ▹ q) p) o₁ g₁ c₁ u₁≺τ⁺) u₁≺τ⁺
               (ih ⟨ p ⟩ (size-▹ʳ (u₁ ▹ q) p tt) o₂ g₂ c₂ (≺-trans (≺-+ʳ tt ou) u≺τ⁺)) tt ou u≺τ⁺
      stepu (zer ▹ phi u₁ u₂) ih ou g cu u≺τ⁺ =
        let (g₁ , g₂) = inC̃-φ κ y u₁ u₂ g
            (c₁ , c₂) = wdc-φ wC ou cu
            (o₁ , o₂ , _ , _) = OT-φ⁻ ou
        in W-φ (ih u₁ (size-φˡ u₁ u₂) o₁ g₁ c₁ (≺-trans (≺-φˡ ou) u≺τ⁺))
               (ih u₂ (size-φʳ u₁ u₂) o₂ g₂ c₂ (≺-trans (≺-φʳ ou) u≺τ⁺)) ou u≺τ⁺
      stepu (zer ▹ Om u₁) ih ou g cu u≺τ⁺ =
        W-Ω (ih u₁ (size-Ω u₁) (proj₁ (OT-Ω⁻ ou)) (inC̃-Ω κ y u₁ g) (wdc-Ω wC ou cu) (≺-trans (≺-Ω ou) u≺τ⁺))
            ou u≺τ⁺
      stepu (zer ▹ psi π u′) ih ou g cu u≺τ⁺ with ≺-trich ⟨ psi π u′ ⟩ (tilde a)
      ... | inj₁ u≺ã        = belowã κ ks o a≺τ⁺ wy y≺τ⁺ ihy π u′ ou g cu u≺τ⁺ u≺ã ih
      ... | inj₂ (inj₁ e)   = atã κ ks o π u′ g e
      ... | inj₂ (inj₂ ã≺u) =
        aboveã κ ks o a≺τ⁺ wy y≺τ⁺ ihy π u′ ou g cu u≺τ⁺ ã≺u ih (decomp κ o ou g ã≺u)

  main : 𝒲 A ⊆ Q
  main = 𝒲-ind {B = Q} step
    where
      step : (𝒜 A Q ∩ 𝒲 A) ⊆ Q
      step {x = y} ((my , ihy) , wy) y≺τ⁺ κ ks o a≺τ⁺ =
        sup (Ma wy y≺τ⁺ κ ks o a≺τ⁺)
            (λ {u} (cu , u≺a) →
               star κ ks o a≺τ⁺ wy y≺τ⁺ ihy u (C⊆OT cu) (≺ψ⇒C̃ o (C⊆OT cu) u≺a) cu (≺-trans u≺a a≺τ⁺))

  -- Lemma 4.17 (c)
  L4-17c : ∀ {y} → 𝒲 A y → y ≺ K⁺ → ∀ κ → KSide κ → OT ⟨ psi κ y ⟩ → ⟨ psi κ y ⟩ ≺ K⁺
         → 𝒲 A ⟨ psi κ y ⟩
  L4-17c wy = main wy
```
