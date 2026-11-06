# Lemma 4.17 (b)：W(A) ∩ κ⁺ 对 +、φ、Ω、I 封闭

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Lemma417b` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] Lemma 4.17 (b)：若 `A ∩ κ ≅ W(A) ∩ κ`，`A ⊆ M(A)`，则 `W(A) ∩ κ⁺` 向下封闭、向上封闭以 κ⁺ 为界。

证明结构（原文 (i)–(v)）：

- (i) 0 ∈ W(A)（`0∈𝒲`）。
- (ii) `b ∈ W(A) ∩ κ⁺` 时 `∀c ∈ W(A). a =NF b + c → a ∈ W(A)`，对 c 作 W-归纳：τ^A(a) 的元素 d 或 ⪯ b（落在 τ^A(b) ∪ {b}），或 d = b + d′ 且 d′ ∈ τ^A(c)，用归纳假设。
- (iii) φ：对 b、c 双重 W-归纳，再对 d ∈ τ^A(a) 按 size 归纳：d ⪯ max{b,c} 直接；否则 d ∉ G′，d 是和（(ii)）或 φ′_{d₁} d₂（Veblen 比较三支）。
- (iv) Ω：对 b W-归纳，d ∈ τ^A(a) 按 size 归纳：d ⪯ b 直接；b ≺ d ≺ Ω′_b 时 d ∉ Fi′，d 是和／φ／Ω′_{d₁}（d₁ ≺ b）／ψ_κ' d₁（κ' ⪯ a，故 d ∈ A ∩ a ⊆ W(A)）。
- (v) I ≺ κ⁺ → I ∈ W(A)：τ^A(I) 按 size 归纳，同 (iv)。

然后由 Lemma 4.16 (a)（弱向下封闭）与 Remark 4.15 得完整封闭性。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Lemma417b (F : OTFacts) where

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

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ : Level

Car-Ω : ∀ b → isCarT ⟨ Om b ⟩ ≡ true
Car-Ω b = refl

Car-I : isCarT I′ ≡ true
Car-I = refl
```

## 0. 假设与公共工具

```agda
module L417b {A : Pred ℓ} (h : A ⊆ M A) {κ : Tm} (oκ : OT κ) (E : (A ∩ ↓ κ) ≅ (𝒲 A ∩ ↓ κ)) where

  K⁺ : Tm
  K⁺ = plus κ

  -- W(A) ∩ κ ⊆ A
  W→A : ∀ {y} → 𝒲 A y → y ≺ κ → A y
  W→A wy y≺κ = proj₁ (proj₂ E (wy , 𝒲⊆OT wy , y≺κ))

  -- A ∩ κ 弱向下封闭（Lemma 4.16 (b)）
  segκ : (A ∩ ↓ κ) ⊑ 𝒲 A
  segκ = (λ (_ , o , _) → o)
       , λ {x} (ax , ox , x≺κ) →
           (λ ((ay , oy , y≺κ) , y⪯x) → proj₁ (proj₁ E (ay , oy , y≺κ)) , y⪯x)
         , (λ (wy , y⪯x) → (W→A wy (⪯≺-trans y⪯x x≺κ) , 𝒲⊆OT wy , ⪯≺-trans y⪯x x≺κ) , y⪯x)

  wκ : WDC (A ∩ ↓ κ)
  wκ = L4-16b segκ

  -- 对 a ≺ κ⁺：ã ⪯ κ，A ∩ ã 弱向下封闭，C^a(A)、τ^A(a) 弱向下封闭且向下封闭
  ã⪯κ : ∀ {a} → OT a → a ≺ K⁺ → tilde a ⪯ κ
  ã⪯κ oa a≺κ⁺ = ≺plus⇒tilde⪯ oa oκ a≺κ⁺

  wã : ∀ {a} → OT a → a ≺ K⁺ → WDC (A ∩ ↓ (tilde a))
  wã oa a≺κ⁺ = WDC-restrict (ã⪯κ oa a≺κ⁺) wκ

  CaWDC : ∀ {a} → OT a → a ≺ K⁺ → WDC (C a A)
  CaWDC oa a≺κ⁺ = C-WDC-tilde h oa (wã oa a≺κ⁺)

  τaWDC : ∀ {a} → OT a → a ≺ K⁺ → WDC (τ A a)
  τaWDC oa a≺κ⁺ = τ-WDC′ (CaWDC oa a≺κ⁺)

  CaDC : ∀ {a} → OT a → a ≺ K⁺ → DC (C a A)
  CaDC oa a≺κ⁺ = Rem4-15.DC′ (CaWDC oa a≺κ⁺) C-WUC (λ _ _ → tt) (λ _ → tt)

  -- b ∈ W(A) 相对 a ≺ κ⁺ 的 Side（Lemma 4.9 (e) 的前提）
  side : ∀ {a b} → OT a → a ≺ K⁺ → 𝒲 A b → Side A a b
  side {a} {b} oa a≺κ⁺ wb with ≺-or-⪰ b (tilde a)
  ... | inj₁ b≺ã = inj₁ (W→A wb (≺⪯-trans b≺ã (ã⪯κ oa a≺κ⁺)) , b≺ã)
  ... | inj₂ ã⪯b = inj₂ (𝒲-M wb , ã⪯b)

  -- d ∈ τ^A(a)，d ≺ b ⪯ a，b ∈ W(A) ⟹ d ∈ W(A)
  viaτ : ∀ {a b d} → OT a → 𝒲 A b → b ⪯ a → C a A d → d ≺ b → 𝒲 A d
  viaτ oa wb b⪯a cd d≺b =
    𝒲-τ wb (τ-anti h oa (𝒲⊆OT wb) b⪯a ((cd , ≺⪯-trans d≺b b⪯a) , (C⊆OT cd , d≺b)))

  -- d ∈ C^a(A)，d ⪯ b ⪯ a，b ∈ W(A) ⟹ d ∈ W(A)
```

## (ii) 和

```agda
  Q+ : Pred ℓ
  Q+ c = ∀ {b} → 𝒲 A b → b ≺ K⁺ → NZ b → NZ c → OT (app b c) → app b c ≺ K⁺ → 𝒲 A (app b c)

  L-ii : 𝒲 A ⊆ Q+
  L-ii = 𝒲-ind {B = Q+} step
    where
      step : (𝒜 A Q+ ∩ 𝒲 A) ⊆ Q+
      step {x = c} ((mc , ih) , wc) {b} wb b≺κ⁺ nzb nzc oa a≺κ⁺ = sup ma τ⊆W
        where
          ob : OT b
          ob = OT-prefixes c oa
          oc : OT c
          oc = OT-suffix c nzb oa
          b⪯a : b ⪯ app b c
          b⪯a = ⪯-prefix nzc oa
          c⪯a : c ⪯ app b c
          c⪯a = ⪯-app nzb nzc oa
          ma : M A (app b c)
          ma = proj₂ (C-tilde h oa)
                 (uc-app (C-UC (wã oa a≺κ⁺)) nzc oa tt
                   (proj₁ (C-tilde h oa) (Side⇒C h oa ob b⪯a (side oa a≺κ⁺ wb)))
                   (proj₁ (C-tilde h oa) (Side⇒C h oa oc c⪯a (side oa a≺κ⁺ wc))))
          τ⊆W : τ A (app b c) ⊆ 𝒲 A
          τ⊆W {x = d} (cd , d≺a) with ≺-or-⪰ d b
          ... | inj₁ d≺b = viaτ oa wb b⪯a cd d≺b
          ... | inj₂ b⪯d with ⪯⇒≺⊎≡ b⪯d
          ...   | inj₂ refl = wb
          ...   | inj₁ b≺d with between-app nzb nzc oa (C⊆OT cd) b≺d d≺a
          ...     | d′ , refl , nzd′ , d′≺c =
                    ih (C-anti h oc oa c⪯a (proj₂ (dc-split (CaDC oa a≺κ⁺) nzb nzd′ (C⊆OT cd) cd)) , d′≺c)
                       wb b≺κ⁺ nzb nzd′ (C⊆OT cd) (≺-trans d≺a a≺κ⁺)

  -- 末分量形式
  W-+ : ∀ {b p} → 𝒲 A b → b ≺ K⁺ → 𝒲 A ⟨ p ⟩ → NZ b → OT (b ▹ p) → (b ▹ p) ≺ K⁺ → 𝒲 A (b ▹ p)
  W-+ {b} {p} wb b≺κ⁺ wp nzb o x≺κ⁺ = L-ii wp wb b≺κ⁺ nzb tt o x≺κ⁺
```

## (iii) φ

```agda
  Qφ : Pred ℓ
  Qφ b = ∀ {c} → 𝒲 A c → OT ⟨ phi b c ⟩ → ⟨ phi b c ⟩ ≺ K⁺ → 𝒲 A ⟨ phi b c ⟩

  L-iii : 𝒲 A ⊆ Qφ
  L-iii = 𝒲-ind {B = Qφ} stepb
    where
      stepb : (𝒜 A Qφ ∩ 𝒲 A) ⊆ Qφ
      stepb {x = b} ((mb , ihb) , wb) {c} wc = 𝒲-ind {B = Qφ′} stepc wc
        where
          Qφ′ : Pred ℓ
          Qφ′ c = OT ⟨ phi b c ⟩ → ⟨ phi b c ⟩ ≺ K⁺ → 𝒲 A ⟨ phi b c ⟩

          stepc : (𝒜 A Qφ′ ∩ 𝒲 A) ⊆ Qφ′
          stepc {x = c} ((mc , ihc) , wc) oa a≺κ⁺ = sup ma (λ {d} t → go d t)
            where
              a : Tm
              a = ⟨ phi b c ⟩
              ob : OT b
              ob = proj₁ (OT-φ⁻ oa)
              oc : OT c
              oc = proj₁ (proj₂ (OT-φ⁻ oa))
              b⪯a : b ⪯ a
              b⪯a = ⪯-φˡ oa
              c⪯a : c ⪯ a
              c⪯a = ⪯-φʳ oa
              ma : M A a
              ma = M-φ h oa (side oa a≺κ⁺ wb) (side oa a≺κ⁺ wc)
              wτ : WDC (τ A a)
              wτ = τaWDC oa a≺κ⁺

              -- b ≺ d、c ≺ d 之后按 d 的形状
              above : ∀ d → (∀ y → size y < size d → τ A a y → 𝒲 A y)
                    → τ A a d → b ≺ d → c ≺ d → 𝒲 A d
              above zer ih t b≺d c≺d = ⊥-elim (¬≺0 b≺d)
              above (d₁ ▹ q ▹ p) ih t@(cd , d≺a) b≺d c≺d =
                let (t₁ , t₂) = wdc-+ wτ tt (C⊆OT cd) t
                in W-+ (ih (d₁ ▹ q) (size-▹ˡ (d₁ ▹ q) p) t₁) (≺-trans (≺-+ˡ tt (C⊆OT cd)) (≺-trans d≺a a≺κ⁺))
                       (ih ⟨ p ⟩ (size-▹ʳ (d₁ ▹ q) p tt) t₂) tt (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
              above (zer ▹ phi d₁ d₂) ih t@(cd , d≺a) b≺d c≺d = veb (φ-cmp oa (C⊆OT cd) d≺a)
                where
                  t₁t₂ = wdc-φ wτ (C⊆OT cd) t
                  veb : (d₁ ≺ b × d₂ ≺ ⟨ phi b c ⟩) ⊎ (d₁ ≡ b × d₂ ≺ c) ⊎ (b ≺ d₁ × ⟨ phi d₁ d₂ ⟩ ⪯ c)
                      → 𝒲 A ⟨ phi d₁ d₂ ⟩
                  veb (inj₁ (d₁≺b , d₂≺a)) =
                    ihb (C-anti h ob oa b⪯a (proj₁ (proj₁ t₁t₂)) , d₁≺b)
                        (ih d₂ (size-φʳ d₁ d₂) (proj₂ t₁t₂)) (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
                  veb (inj₂ (inj₁ (refl , d₂≺c))) =
                    ihc (C-anti h oc oa c⪯a (proj₁ (proj₂ t₁t₂)) , d₂≺c) (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
                  veb (inj₂ (inj₂ (_ , d⪯c))) = ⊥-elim (≺⇒¬⪯ c≺d d⪯c)
              above (zer ▹ psi κ′ d₁) ih (cd , d≺a) b≺d c≺d =
                ⊥-elim (≺-asym d≺a (φ≺G refl (C⊆OT cd) oa b≺d c≺d))
              above (zer ▹ Om d₁) ih (cd , d≺a) b≺d c≺d =
                ⊥-elim (≺-asym d≺a (φ≺G refl (C⊆OT cd) oa b≺d c≺d))
              above (zer ▹ I) ih (cd , d≺a) b≺d c≺d =
                ⊥-elim (≺-asym d≺a (φ≺G refl (C⊆OT cd) oa b≺d c≺d))

              go : ∀ d → τ A a d → 𝒲 A d
              go = sizeRec (λ d → τ A a d → 𝒲 A d) stepd
                where
                  stepd : ∀ d → (∀ y → size y < size d → τ A a y → 𝒲 A y) → τ A a d → 𝒲 A d
                  stepd d ih t@(cd , d≺a) with ≺-or-⪰ d b
                  ... | inj₁ d≺b = viaτ oa wb b⪯a cd d≺b
                  ... | inj₂ b⪯d with ⪯⇒≺⊎≡ b⪯d
                  ...   | inj₂ refl = wb
                  ...   | inj₁ b≺d with ≺-or-⪰ d c
                  ...     | inj₁ d≺c = viaτ oa wc c⪯a cd d≺c
                  ...     | inj₂ c⪯d with ⪯⇒≺⊎≡ c⪯d
                  ...       | inj₂ refl = wc
                  ...       | inj₁ c≺d = above d ih t b≺d c≺d

  W-φ : ∀ {b c} → 𝒲 A b → 𝒲 A c → OT ⟨ phi b c ⟩ → ⟨ phi b c ⟩ ≺ K⁺ → 𝒲 A ⟨ phi b c ⟩
  W-φ wb wc o x≺κ⁺ = L-iii wb wc o x≺κ⁺
```

## (iv) Ω

```agda
  QΩ : Pred ℓ
  QΩ b = OT ⟨ Om b ⟩ → ⟨ Om b ⟩ ≺ K⁺ → 𝒲 A ⟨ Om b ⟩

  L-iv : 𝒲 A ⊆ QΩ
  L-iv = 𝒲-ind {B = QΩ} stepb
    where
      stepb : (𝒜 A QΩ ∩ 𝒲 A) ⊆ QΩ
      stepb {x = b} ((mb , ihb) , wb) oa a≺κ⁺ = sup ma (λ {d} t → go d t)
        where
          a : Tm
          a = ⟨ Om b ⟩
          ob : OT b
          ob = proj₁ (OT-Ω⁻ oa)
          b⪯a : b ⪯ a
          b⪯a = ⪯-Ω oa
          a⪯κ : a ⪯ κ
          a⪯κ = Car≺plus⇒⪯ oa oκ (Car-Ω b) a≺κ⁺
          ma : M A a
          ma = M-Ω h oa (side oa a≺κ⁺ wb)
          wτ : WDC (τ A a)
          wτ = τaWDC oa a≺κ⁺

          above : ∀ d → (∀ y → size y < size d → τ A a y → 𝒲 A y) → τ A a d → b ≺ d → 𝒲 A d
          above zer ih t b≺d = ⊥-elim (¬≺0 b≺d)
          above (d₁ ▹ q ▹ p) ih t@(cd , d≺a) b≺d =
            let (t₁ , t₂) = wdc-+ wτ tt (C⊆OT cd) t
            in W-+ (ih (d₁ ▹ q) (size-▹ˡ (d₁ ▹ q) p) t₁) (≺-trans (≺-+ˡ tt (C⊆OT cd)) (≺-trans d≺a a≺κ⁺))
                   (ih ⟨ p ⟩ (size-▹ʳ (d₁ ▹ q) p tt) t₂) tt (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
          above (zer ▹ phi d₁ d₂) ih t@(cd , d≺a) b≺d =
            let (t₁ , t₂) = wdc-φ wτ (C⊆OT cd) t
            in W-φ (ih d₁ (size-φˡ d₁ d₂) t₁) (ih d₂ (size-φʳ d₁ d₂) t₂) (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
          above (zer ▹ Om d₁) ih t@(cd , d≺a) b≺d =
            ihb (C-anti h ob oa b⪯a (wdc-Ω wτ (C⊆OT cd) t .proj₁) , Ω-mono⁻ (C⊆OT cd) oa d≺a)
                (C⊆OT cd) (≺-trans d≺a a≺κ⁺)
          above (zer ▹ psi (ΩR z) d₁) ih t@(cd , d≺a) b≺d = fromA (C-ψ⁻ cd)
            where
              κ′⪯a : ⟨ Om z ⟩ ⪯ a
              κ′⪯a = ψ≺Car⇒κ⪯ (Car-Ω b) (C⊆OT cd) oa d≺a
              fromA : (A ⟨ psi (ΩR z) d₁ ⟩ × ⟨ psi (ΩR z) d₁ ⟩ ≺ a)
                    ⊎ (a ≺ ⟨ Om z ⟩ × C a A ⟨ Om z ⟩ × C a A d₁) → 𝒲 A ⟨ psi (ΩR z) d₁ ⟩
              fromA (inj₁ (d∈A , _)) = proj₁ (proj₁ E (d∈A , C⊆OT cd , ≺⪯-trans d≺a a⪯κ))
              fromA (inj₂ (a≺κ′ , _)) = ⊥-elim (≺⇒¬⪯ a≺κ′ κ′⪯a)
          above (zer ▹ psi IR d₁) ih (cd , d≺a) b≺d =
            ⊥-elim (≺⇒¬⪯ b≺d (Fi≺Ω⇒⪯ refl (C⊆OT cd) oa d≺a))
          above (zer ▹ I) ih (cd , d≺a) b≺d =
            ⊥-elim (≺⇒¬⪯ b≺d (Fi≺Ω⇒⪯ refl (C⊆OT cd) oa d≺a))

          go : ∀ d → τ A a d → 𝒲 A d
          go = sizeRec (λ d → τ A a d → 𝒲 A d) stepd
            where
              stepd : ∀ d → (∀ y → size y < size d → τ A a y → 𝒲 A y) → τ A a d → 𝒲 A d
              stepd d ih t@(cd , d≺a) with ≺-or-⪰ d b
              ... | inj₁ d≺b = viaτ oa wb b⪯a cd d≺b
              ... | inj₂ b⪯d with ⪯⇒≺⊎≡ b⪯d
              ...   | inj₂ refl = wb
              ...   | inj₁ b≺d = above d ih t b≺d

  W-Ω : ∀ {b} → 𝒲 A b → OT ⟨ Om b ⟩ → ⟨ Om b ⟩ ≺ K⁺ → 𝒲 A ⟨ Om b ⟩
  W-Ω wb o x≺κ⁺ = L-iv wb o x≺κ⁺
```

## (v) I

```agda
  W-I : I′ ≺ K⁺ → 𝒲 A I′
  W-I I≺κ⁺ = sup I∈M (λ {d} t → go d t)
    where
      I⪯κ : I′ ⪯ κ
      I⪯κ = Car≺plus⇒⪯ OT-I oκ Car-I I≺κ⁺
      wτ : WDC (τ A I′)
      wτ = τaWDC OT-I I≺κ⁺

      go : ∀ d → τ A I′ d → 𝒲 A d
      go = sizeRec (λ d → τ A I′ d → 𝒲 A d) stepd
        where
          stepd : ∀ d → (∀ y → size y < size d → τ A I′ y → 𝒲 A y) → τ A I′ d → 𝒲 A d
          stepd zer ih t = 0∈𝒲
          stepd (d₁ ▹ q ▹ p) ih t@(cd , d≺I) =
            let (t₁ , t₂) = wdc-+ wτ tt (C⊆OT cd) t
            in W-+ (ih (d₁ ▹ q) (size-▹ˡ (d₁ ▹ q) p) t₁) (≺-trans (≺-+ˡ tt (C⊆OT cd)) (≺-trans d≺I I≺κ⁺))
                   (ih ⟨ p ⟩ (size-▹ʳ (d₁ ▹ q) p tt) t₂) tt (C⊆OT cd) (≺-trans d≺I I≺κ⁺)
          stepd (zer ▹ phi d₁ d₂) ih t@(cd , d≺I) =
            let (t₁ , t₂) = wdc-φ wτ (C⊆OT cd) t
            in W-φ (ih d₁ (size-φˡ d₁ d₂) t₁) (ih d₂ (size-φʳ d₁ d₂) t₂) (C⊆OT cd) (≺-trans d≺I I≺κ⁺)
          stepd (zer ▹ Om d₁) ih t@(cd , d≺I) =
            W-Ω (ih d₁ (size-Ω d₁) (wdc-Ω wτ (C⊆OT cd) t)) (C⊆OT cd) (≺-trans d≺I I≺κ⁺)
          stepd (zer ▹ psi (ΩR z) d₁) ih t@(cd , d≺I) = fromA (C-ψ⁻ cd)
            where
              κ′⪯I : ⟨ Om z ⟩ ⪯ I′
              κ′⪯I = ψ≺Car⇒κ⪯ Car-I (C⊆OT cd) OT-I d≺I
              fromA : (A ⟨ psi (ΩR z) d₁ ⟩ × ⟨ psi (ΩR z) d₁ ⟩ ≺ I′)
                    ⊎ (I′ ≺ ⟨ Om z ⟩ × C I′ A ⟨ Om z ⟩ × C I′ A d₁) → 𝒲 A ⟨ psi (ΩR z) d₁ ⟩
              fromA (inj₁ (d∈A , _)) = proj₁ (proj₁ E (d∈A , C⊆OT cd , ≺⪯-trans d≺I I⪯κ))
              fromA (inj₂ (I≺κ′ , _)) = ⊥-elim (≺⇒¬⪯ I≺κ′ κ′⪯I)
          stepd (zer ▹ psi IR d₁) ih t@(cd , d≺I) = fromA (C-ψ⁻ cd)
            where
              fromA : (A ⟨ psi IR d₁ ⟩ × ⟨ psi IR d₁ ⟩ ≺ I′)
                    ⊎ (I′ ≺ I′ × C I′ A I′ × C I′ A d₁) → 𝒲 A ⟨ psi IR d₁ ⟩
              fromA (inj₁ (d∈A , _)) = proj₁ (proj₁ E (d∈A , C⊆OT cd , ≺⪯-trans d≺I I⪯κ))
              fromA (inj₂ (I≺I , _)) = ⊥-elim (≺-irrefl I≺I)
          stepd (zer ▹ I) ih (cd , I≺I) = ⊥-elim (≺-irrefl I≺I)
```

## 结论：W(A) ∩ κ⁺ 弱向上封闭以 κ⁺ 为界；向下封闭；向上封闭

```agda
  W⁺ : Pred ℓ
  W⁺ = 𝒲 A ∩ ↓ K⁺

  W⁺-WUC : WUC W⁺ (λ z → z ≺ K⁺)
  W⁺-WUC = record
    { wuc-+ = λ {b} {p} nz o g (wb , _ , b≺κ⁺) (wp , _ , _) → W-+ wb b≺κ⁺ wp nz o g , o , g
    ; wuc-φ = λ o g (wb , _ , _) (wc , _ , _) → W-φ wb wc o g , o , g
    ; wuc-Ω = λ o g (wb , _ , _) → W-Ω wb o g , o , g
    ; wuc-0 = λ g → 0∈𝒲 , OT-0 , g
    ; wuc-I = λ g → W-I g , OT-I , g
    }

  W⁺-WDC : WDC W⁺
  W⁺-WDC = 𝒲∩-WDC h oκ (WDC-restrict (tilde⪯ oκ) wκ)

  W⁺-DC : DC W⁺
  W⁺-DC = Rem4-15.DC′ W⁺-WDC W⁺-WUC ≺a-mono (λ (_ , _ , g) → g)

  W⁺-UC : UC W⁺ (λ z → z ≺ K⁺)
  W⁺-UC = Rem4-15.UC′ W⁺-WDC W⁺-WUC ≺a-mono (λ (_ , _ , g) → g)
```
