# Γ 迭代：Definitions 4.32–4.36, 5.8；Lemmas 4.34, 4.35, 4.37, 4.38

Setzer [Se98] §4.6。目标 4.38 (c)：`𝕎 ∩ I ≅ W(𝕎) ∩ I`。关键是 (a)：`ψ_I c ∈ 𝒜^𝕎(𝕎) ⟹ ψ_I c ∈ 𝕎`，为此要把类 `C^𝕎_I(c) := C̃_I(c) ∩ C^{ψ_I c}(𝕎)` 表示成**集合** Γ^ω = ⋃ₙ Γⁿ（Lemma 4.37），再用 Lemma 4.30。

- 原文先定义算子 Γ_c 于类（Def 4.32），再说明限制到 C^𝕎_I(c) 的子集上可换成集合版 Γ′（Lemma 4.35：把 `𝕎 ∩ ψ_I 0`、`𝕎 ∩ ψ_I(b+1)` 换成含 ψ_I 0、ψ_I(b+1) 的突出**集**），最后对 n 同时递归定义 Γⁿ 与证明 Γⁿ ⊆ C^𝕎_I(c)（Def 5.8）。这里**直接**定义集合版 `ΓStep X p`（一个归纳类型，参数 X 是集合、p : X ⊆ C^𝕎_I(c)），Def 5.8 的同时递归就是 `ΓP : ℕ → Σ (Pred 0ℓ) (_⊆ C^𝕎_I(c))`。这是 N 到宇宙的大消去。
- 见证集来自 `𝕎` 的 Σ 投影（Lemma 4.31 (b) 给 ψ_I 0 ∈ 𝕎，ψ_I b ∈ 𝕎 ⟹ ψ_I(b+1) ∈ 𝕎）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Gamma (F : OTFacts) where

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
open import Mahlo.Inacc.WO.Lemma431 F

open import Level using (Level; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; _<_; _≤_; s≤s; z≤n) renaming (suc to sucℕ; _+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm; ≤-trans; <⇒≤; ≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
```

## 0. 工具

```agda
-- ψ_I b ∈ OT ⟹ ψ_I (b+1) ∈ OT
OT-ψIb+1 : ∀ {b} → OT ⟨ psi IR b ⟩ → OT ⟨ psi IR (b + one) ⟩
OT-ψIb+1 {b} o = OT-ψ⁺ (+-OT ob OT-one) OT-I refl g
  where
    ob : OT b
    ob = proj₁ (OT-ψ⁻ o)
    gbb : inC̃ IR b b ≡ true
    gbb = proj₂ (proj₂ (proj₂ (OT-ψ⁻ o)))
    g : inC̃ IR (b + one) (b + one) ≡ true
    g with x+1-view b ob
    ... | inj₁ (refl , e) = subst (λ t → inC̃ IR t t ≡ true) (sym e) refl
    ... | inj₂ (nz , e)   =
      subst (λ t → inC̃ IR t t ≡ true) (sym e)
        (inC̃-▹1 IR (b ▹ phi zer zer) b (allLt-mono (G IR b) gbb (subst (λ t → b ≺ t) e (x≺x+1 ob))))

-- 两个含 ψ 的见证集在 ψ 以下一致
A-swap : ∀ {ψ} (w₁ w₂ : 𝕎 ψ) {x} → proj₁ w₁ x → x ≺ ψ → proj₁ w₂ x
A-swap (A₁ , ag₁ , p₁) (A₂ , ag₂ , p₂) ax x≺ψ =
  ⊑← (Ag⇒⊑𝕎 A₂ ag₂) p₂ (⊑⇒⊆ (Ag⇒⊑𝕎 A₁ ag₁) ax) (≺⇒⪯ x≺ψ)

CψWDC : ∀ {a} → OT a → WDC (C a 𝕎)
CψWDC oa = C-WDC-tilde 𝕎⊆M oa (WDC-∩↓ (Ag423.Ag-WDC Ag𝕎) _)

CψDC : ∀ {a} → OT a → DC (C a 𝕎)
CψDC oa = Rem4-15.DC′ (CψWDC oa) C-WUC (λ _ _ → tt) (λ _ → tt)
```

## 1. 固定 c：C^𝕎_I(c)、见证集、ΓStep

```agda
module Γ-block (c : Tm) (oψc : OT ⟨ psi IR c ⟩) (q : τ 𝕎 ⟨ psi IR c ⟩ ⊆ 𝕎) where

  ψc : Tm
  ψc = ⟨ psi IR c ⟩
  ψc≺I : ψc ≺ I′
  ψc≺I = ψ≺κ oψc
  oc : OT c
  oc = proj₁ (OT-ψ⁻ oψc)

  CWI : Pred (suc 0ℓ)
  CWI x = inC̃ IR c x ≡ true × C ψc 𝕎 x

  τ→CWI : ∀ {x} → τ 𝕎 ψc x → CWI x
  τ→CWI (cx , x≺ψc) = ≺ψ⇒C̃ oψc (C⊆OT cx) x≺ψc , cx

  CWI∩I→τ : ∀ {x} → CWI x → x ≺ I′ → τ 𝕎 ψc x
  CWI∩I→τ (gx , cx) x≺I = cx , C̃⇒≺ψ oψc (C⊆OT cx) x≺I gx

  CWI∩I→𝕎 : ∀ {x} → CWI x → x ≺ I′ → 𝕎 x
  CWI∩I→𝕎 w x≺I = q (CWI∩I→τ w x≺I)

  -- ψ_I 0 的见证集
  A₀ : Pred 0ℓ
  A₀ = proj₁ 𝕎-ψI0
  agA₀ : Ag A₀
  agA₀ = proj₁ (proj₂ 𝕎-ψI0)
  ψI0∈A₀ : A₀ ⟨ psi IR zer ⟩
  ψI0∈A₀ = proj₂ (proj₂ 𝕎-ψI0)

  ψI0⪯ψc : ⟨ psi IR zer ⟩ ⪯ ψc
  ψI0⪯ψc with ≺-or-⪰ zer c
  ... | inj₁ 0≺c = ≺⇒⪯ (ψI-mono (ot! refl) oψc 0≺c)
  ... | inj₂ c⪯0 = ≡⇒⪯ (cong (λ t → ⟨ psi IR t ⟩) (sym (⪯0⇒≡0 c⪯0)))

  -- b ∈ C^𝕎_I(c)，b ∈ C̃_I(b)，b ≺ c ⟹ ψ_I b ∈ τ^𝕎(ψ_I c) ⊆ 𝕎，ψ_I(b+1) ∈ 𝕎
  ψIb∈𝕎 : ∀ {b} → CWI b → inC̃ IR b b ≡ true → b ≺ c → 𝕎 ⟨ psi IR b ⟩
  ψIb∈𝕎 {b} (gb , cb) gbb b≺c =
    q (C-ψ⁺ oψb ψc≺I (c! OT-I (here [])) cb , ψI-mono oψb oψc b≺c)
    where
      oψb : OT ⟨ psi IR b ⟩
      oψb = OT-ψ⁺ (C⊆OT cb) OT-I refl gbb

  ψIb+1∈𝕎 : ∀ {b} → CWI b → inC̃ IR b b ≡ true → b ≺ c → 𝕎 ⟨ psi IR (b + one) ⟩
  ψIb+1∈𝕎 {b} w gbb b≺c = 𝕎-ψI+1 (OT-ψIb+1 (𝕎⊆OT (ψIb∈𝕎 w gbb b≺c))) (ψIb∈𝕎 w gbb b≺c)

  ψIb+1⪯ψc : ∀ {b} → OT b → OT ⟨ psi IR (b + one) ⟩ → b ≺ c → ⟨ psi IR (b + one) ⟩ ⪯ ψc
  ψIb+1⪯ψc {b} ob oψb+1 b≺c with ⪯⇒≺⊎≡ (+1-least ob oc b≺c)
  ... | inj₁ b+1≺c = ≺⇒⪯ (ψI-mono oψb+1 oψc b+1≺c)
  ... | inj₂ e     = ≡⇒⪯ (cong (λ t → ⟨ psi IR t ⟩) e)
```

Γ′（Def 4.32 的集合版）：

```agda
  data ΓStep (X : Pred 0ℓ) (p : X ⊆ CWI) : Tm → Set where
    Γ0  : ΓStep X p zer
    ΓI  : ΓStep X p I′
    Γ+  : ∀ {a r} → NZ a → OT (a ▹ r) → X a → X ⟨ r ⟩ → ΓStep X p (a ▹ r)
    Γφ  : ∀ {a b} → OT ⟨ phi a b ⟩ → X a → X b → ΓStep X p ⟨ phi a b ⟩
    ΓΩ  : ∀ {a} → OT ⟨ Om a ⟩ → X a → ΓStep X p ⟨ Om a ⟩
    Γψ  : ∀ {z b} → OT ⟨ psi (ΩR z) b ⟩ → I′ ≺ ⟨ Om z ⟩ → X ⟨ Om z ⟩ → X b → b ≺ c
        → ΓStep X p ⟨ psi (ΩR z) b ⟩
    Γ↓0 : ∀ {x} → A₀ x → x ≺ ⟨ psi IR zer ⟩ → ΓStep X p x
    Γ↓  : ∀ {x b} (xb : X b) (gbb : inC̃ IR b b ≡ true) (b≺c : b ≺ c)
        → proj₁ (ψIb+1∈𝕎 (p xb) gbb b≺c) x → x ≺ ⟨ psi IR (b + one) ⟩ → ΓStep X p x
```

Lemma 4.34 (b)（集合版）：`ΓStep X p ⊆ C^𝕎_I(c)`。

```agda
  Γstep⊆CWI : ∀ X (p : X ⊆ CWI) → ΓStep X p ⊆ CWI
  Γstep⊆CWI X p Γ0 = refl , c! OT-0 (here [])
  Γstep⊆CWI X p ΓI = refl , c! OT-I (here [])
  Γstep⊆CWI X p (Γ+ {a} {r} nz o xa xr) =
    let (g₁ , c₁) = p xa ; (g₂ , c₂) = p xr
    in allLt-++⁺ (G IR a) g₁ g₂ , C-+⁺ nz o c₁ c₂
  Γstep⊆CWI X p (Γφ {a} {b} o xa xb) =
    let (g₁ , c₁) = p xa ; (g₂ , c₂) = p xb
    in allLt-++⁺ (G IR a) g₁ g₂ , C-φ⁺ o c₁ c₂
  Γstep⊆CWI X p (ΓΩ o xa) = let (g₁ , c₁) = p xa in g₁ , C-Ω⁺ o c₁
  Γstep⊆CWI X p (Γψ {z} {b} o I≺κ xκ xb b≺c) =
    let (gκ , cκ) = p xκ ; (gb , cb) = p xb
    in inC̃-ψIΩ⁺ c z b (≺⇒⪯ I≺κ) gκ gb b≺c , C-ψ⁺ o (≺-trans ψc≺I I≺κ) cκ cb
  Γstep⊆CWI X p (Γ↓0 {x} ax x≺ψ0) =
    τ→CWI (A∩a⊆C (⊑⇒⊆ (Ag⇒⊑𝕎 A₀ agA₀) ax , proj₁ agA₀ ax , x≺ψc) , x≺ψc)
    where
      x≺ψc : x ≺ ψc
      x≺ψc = ≺⪯-trans x≺ψ0 ψI0⪯ψc
  Γstep⊆CWI X p (Γ↓ {x} {b} xb gbb b≺c ax x≺ψb+1) =
    τ→CWI (A∩a⊆C (x∈𝕎 , 𝕎⊆OT x∈𝕎 , x≺ψc) , x≺ψc)
    where
      w : 𝕎 ⟨ psi IR (b + one) ⟩
      w = ψIb+1∈𝕎 (p xb) gbb b≺c
      x∈𝕎 : 𝕎 x
      x∈𝕎 = ⊑⇒⊆ (Ag⇒⊑𝕎 (proj₁ w) (proj₁ (proj₂ w))) ax
      x≺ψc : x ≺ ψc
      x≺ψc = ≺⪯-trans x≺ψb+1 (ψIb+1⪯ψc (C⊆OT (proj₂ (p xb))) (𝕎⊆OT w) b≺c)
```

Def 5.8：Γⁿ 与 Γⁿ ⊆ C^𝕎_I(c) 同时递归；Γ^ω。

```agda
  ΓP : ℕ → Σ (Pred 0ℓ) (λ X → X ⊆ CWI)
  ΓP zero      = (λ _ → ⊥) , (λ ())
  ΓP (sucℕ n)  = ΓStep (proj₁ (ΓP n)) (λ q → proj₂ (ΓP n) q) , Γstep⊆CWI (proj₁ (ΓP n)) (λ q → proj₂ (ΓP n) q)

  Γ : ℕ → Pred 0ℓ
  Γ n = proj₁ (ΓP n)

  Γ⊆CWI : ∀ n → Γ n ⊆ CWI
  Γ⊆CWI n = proj₂ (ΓP n)

  Γω : Pred 0ℓ
  Γω x = ∃ λ n → Γ n x

  Γω⊆CWI : Γω ⊆ CWI
  Γω⊆CWI (n , Γx) = Γ⊆CWI n Γx
```

单调性：`X ⊆ Y ⟹ ΓStep X ⊆ ΓStep Y`（Γ↓ 的见证集换掉，用 `A-swap`）；`Γ n ⊆ Γ (n +ℕ k)`。

```agda
  Γ-mono : ∀ {X Y : Pred 0ℓ} {p : X ⊆ CWI} {p′ : Y ⊆ CWI} → X ⊆ Y → ΓStep X p ⊆ ΓStep Y p′
  Γ-mono f Γ0 = Γ0
  Γ-mono f ΓI = ΓI
  Γ-mono f (Γ+ nz o xa xr) = Γ+ nz o (f xa) (f xr)
  Γ-mono f (Γφ o xa xb) = Γφ o (f xa) (f xb)
  Γ-mono f (ΓΩ o xa) = ΓΩ o (f xa)
  Γ-mono f (Γψ o I≺κ xκ xb b≺c) = Γψ o I≺κ (f xκ) (f xb) b≺c
  Γ-mono f (Γ↓0 ax x≺) = Γ↓0 ax x≺
  Γ-mono {p = p} {p′ = p′} f (Γ↓ xb gbb b≺c ax x≺) =
    Γ↓ (f xb) gbb b≺c (A-swap (ψIb+1∈𝕎 (p xb) gbb b≺c) (ψIb+1∈𝕎 (p′ (f xb)) gbb b≺c) ax x≺) x≺

  Γ⊆suc : ∀ n → Γ n ⊆ Γ (sucℕ n)
  Γ⊆suc zero     ()
  Γ⊆suc (sucℕ n) = Γ-mono (λ q → Γ⊆suc n q)

  Γ+k : ∀ n k → Γ n ⊆ Γ (n +ℕ k)
  Γ+k n zero     = subst (λ m → Γ n ⊆ Γ m) (sym (+-comm n 0)) (λ x → x)
  Γ+k n (sucℕ k) = subst (λ m → Γ n ⊆ Γ m) (sym (+-comm n (sucℕ k)))
                     (λ {x} q → Γ⊆suc (k +ℕ n) (subst (λ m → Γ m x) (+-comm n k) (Γ+k n k q)))

  -- 两个层次合并到 m + n
  join : ∀ m n {x y} → Γ m x → Γ n y → Γ (m +ℕ n) x × Γ (m +ℕ n) y
  join m n {x} {y} Γx Γy = Γ+k m n Γx , subst (λ k → Γ k y) (+-comm n m) (Γ+k n m Γy)
```

Lemma 4.37 ⊇：`C^𝕎_I(c) ⊆ Γ^ω`，按 size 归纳。

```agda
  CWI⊆Γω : ∀ x → CWI x → Γω x
  CWI⊆Γω = sizeRec (λ x → CWI x → Γω x) step
    where
      step : ∀ x → (∀ y → size y < size x → CWI y → Γω y) → CWI x → Γω x
      step zer       ih _ = 1 , Γ0
      step (zer ▹ I) ih _ = 1 , ΓI
      step (a ▹ r ▹ p′) ih (gx , cx) =
        let (g₁ , g₂) = inC̃-▹ IR c (a ▹ r) p′ gx
            (c₁ , c₂) = wdc-+ (CψWDC oψc) tt (C⊆OT cx) cx
            (n₁ , Γa) = ih (a ▹ r) (size-▹ˡ (a ▹ r) p′) (g₁ , c₁)
            (n₂ , Γr) = ih ⟨ p′ ⟩ (size-▹ʳ (a ▹ r) p′ tt) (g₂ , c₂)
            (Γa′ , Γr′) = join n₁ n₂ Γa Γr
        in sucℕ (n₁ +ℕ n₂) , Γ+ tt (C⊆OT cx) Γa′ Γr′
      step (zer ▹ phi a b) ih (gx , cx) =
        let (g₁ , g₂) = inC̃-φ IR c a b gx
            (c₁ , c₂) = wdc-φ (CψWDC oψc) (C⊆OT cx) cx
            (n₁ , Γa) = ih a (size-φˡ a b) (g₁ , c₁)
            (n₂ , Γb) = ih b (size-φʳ a b) (g₂ , c₂)
            (Γa′ , Γb′) = join n₁ n₂ Γa Γb
        in sucℕ (n₁ +ℕ n₂) , Γφ (C⊆OT cx) Γa′ Γb′
      step (zer ▹ Om a) ih (gx , cx) =
        let (n₁ , Γa) = ih a (size-Ω a) (inC̃-Ω IR c a gx , wdc-Ω (CψWDC oψc) (C⊆OT cx) cx)
        in sucℕ n₁ , ΓΩ (C⊆OT cx) Γa
      step (zer ▹ psi κ b) ih w@(gx , cx) with ≺-or-⪰ I′ (regTm κ)
      ... | inj₁ I≺κ = aboveI κ I≺κ w ih
        where
          aboveI : ∀ κ → I′ ≺ regTm κ → CWI ⟨ psi κ b ⟩
                 → (∀ y → size y < size ⟨ psi κ b ⟩ → CWI y → Γω y) → Γω ⟨ psi κ b ⟩
          aboveI IR I≺I _ _ = ⊥-elim (≺-irrefl I≺I)
          aboveI (ΩR z) I≺κ (gx′ , cx′) ih′ = fromC (C-ψ⁻ cx′)
            where
              ox′ : OT ⟨ psi (ΩR z) b ⟩
              ox′ = C⊆OT cx′
              oκ : OT ⟨ Om z ⟩
              oκ = proj₁ (proj₂ (OT-ψ⁻ ox′))
              rκ : isRR (ΩR z) ≡ true
              rκ = proj₁ (proj₂ (proj₂ (OT-ψ⁻ ox′)))
              gs : inC̃ IR c ⟨ Om z ⟩ ≡ true × inC̃ IR c b ≡ true × b ≺ c
              gs = inC̃-ψIΩ c z b (≺⇒⪯ I≺κ) gx′
              fromC : (𝕎 ⟨ psi (ΩR z) b ⟩ × ⟨ psi (ΩR z) b ⟩ ≺ ψc)
                    ⊎ (ψc ≺ ⟨ Om z ⟩ × C ψc 𝕎 ⟨ Om z ⟩ × C ψc 𝕎 b) → Γω ⟨ psi (ΩR z) b ⟩
              fromC (inj₁ (_ , x≺ψc)) =
                -- x ⪰ κ⁻ ⪰ I ≻ ψ_I c ≻ x
                ⊥-elim (≺-irrefl (≺⪯-trans (≺-trans x≺ψc ψc≺I)
                          (⪯-trans (Car≺κ⇒⪯κ⁻ OT-I refl rκ oκ I≺κ) (≺⇒⪯ (κ⁻≺ψ ox′)))))
              fromC (inj₂ (_ , cκ , cb)) =
                let (n₁ , Γκ) = ih′ ⟨ Om z ⟩ (size-ψκ z b) (proj₁ gs , cκ)
                    (n₂ , Γb) = ih′ b (size-ψc (ΩR z) b) (proj₁ (proj₂ gs) , cb)
                    (Γκ′ , Γb′) = join n₁ n₂ Γκ Γb
                in sucℕ (n₁ +ℕ n₂) , Γψ ox′ I≺κ Γκ′ Γb′ (proj₂ (proj₂ gs))
      ... | inj₂ κ⪯I = belowI (≺-or-⪰ ⟨ psi κ b ⟩ ⟨ psi IR zer ⟩)
        where
          ox : OT ⟨ psi κ b ⟩
          ox = C⊆OT cx
          x≺I : ⟨ psi κ b ⟩ ≺ I′
          x≺I = ≺⪯-trans (ψ≺κ ox) κ⪯I
          x∈𝕎 : 𝕎 ⟨ psi κ b ⟩
          x∈𝕎 = CWI∩I→𝕎 w x≺I
          x≺ψc : ⟨ psi κ b ⟩ ≺ ψc
          x≺ψc = proj₂ (CWI∩I→τ w x≺I)
          belowI : ⟨ psi κ b ⟩ ≺ ⟨ psi IR zer ⟩ ⊎ ⟨ psi IR zer ⟩ ⪯ ⟨ psi κ b ⟩ → Γω ⟨ psi κ b ⟩
          belowI (inj₁ x≺ψ0) =
            1 , Γ↓0 (⊑← (Ag⇒⊑𝕎 A₀ agA₀) ψI0∈A₀ x∈𝕎 (≺⇒⪯ x≺ψ0)) x≺ψ0
          belowI (inj₂ ψ0⪯x) = fromForm (Fi-form ox ψ0⪯x x≺I)
            where
              fromForm : (∃ λ b′ → OT ⟨ psi IR b′ ⟩ × mFi ⟨ psi κ b ⟩ ≡ ⟨ psi IR b′ ⟩
                                  × pFi ⟨ psi κ b ⟩ ≡ ⟨ psi IR (b′ + one) ⟩ × ⟨ psi κ b ⟩ ≺ ⟨ psi IR (b′ + one) ⟩)
                       → Γω ⟨ psi κ b ⟩
              fromForm (b′ , oψb′ , eM , eP , x≺ψb′+1) =
                let (n , Γb′) = ih b′ b′<x (gb′ , cb′)
                    wb′ = ψIb+1∈𝕎 (Γ⊆CWI n Γb′) gb′b′ b′≺c
                in sucℕ n , Γ↓ Γb′ gb′b′ b′≺c
                              (⊑← (Ag⇒⊑𝕎 (proj₁ wb′) (proj₁ (proj₂ wb′))) (proj₂ (proj₂ wb′)) x∈𝕎 (≺⇒⪯ x≺ψb′+1))
                              x≺ψb′+1
                where
                  ob′ : OT b′
                  ob′ = proj₁ (OT-ψ⁻ oψb′)
                  gb′b′ : inC̃ IR b′ b′ ≡ true
                  gb′b′ = proj₂ (proj₂ (proj₂ (OT-ψ⁻ oψb′)))
                  -- ψ_I b′ = x^{−Fi} ⪯ x ≺ ψ_I c
                  ψb′⪯x : ⟨ psi IR b′ ⟩ ⪯ ⟨ psi κ b ⟩
                  ψb′⪯x = subst (λ t → t ⪯ ⟨ psi κ b ⟩) eM (mFi⪯ ox)
                  ψb′≺ψc : ⟨ psi IR b′ ⟩ ≺ ψc
                  ψb′≺ψc = ⪯≺-trans ψb′⪯x x≺ψc
                  b′≺c : b′ ≺ c
                  b′≺c = ψI-cmp oψb′ oψc ψb′≺ψc
                  gb′ : inC̃ IR c b′ ≡ true
                  gb′ = allLt-mono (G IR b′) gb′b′ b′≺c
                  -- ψ_I b′ ∈ C^{ψ_I c}(𝕎) ∩ ψ_I c ⊆ 𝕎，故 b′ ∈ C^{ψ_I b′}(𝕎) ⊆ C^{ψ_I c}(𝕎)（4.7 (e)）
                  cψb′ : C ψc 𝕎 ⟨ psi IR b′ ⟩
                  cψb′ = subst (C ψc 𝕎) eM (dc-mFi (CψDC oψc) ox cx)
                  ψb′∈𝕎 : 𝕎 ⟨ psi IR b′ ⟩
                  ψb′∈𝕎 = q (cψb′ , ψb′≺ψc)
                  -- 不用 with：对 `C-ψ⁻ (𝕎⊆M ψb′∈𝕎)` 做 with-抽象会让 Agda 规范化这个巨大的项（实测超时）
                  cb″ : C ⟨ psi IR b′ ⟩ 𝕎 b′
                  cb″ = fromM (C-ψ⁻ (𝕎⊆M ψb′∈𝕎))
                    where
                      fromM : (𝕎 ⟨ psi IR b′ ⟩ × ⟨ psi IR b′ ⟩ ≺ ⟨ psi IR b′ ⟩)
                            ⊎ (⟨ psi IR b′ ⟩ ≺ I′ × C ⟨ psi IR b′ ⟩ 𝕎 I′ × C ⟨ psi IR b′ ⟩ 𝕎 b′)
                            → C ⟨ psi IR b′ ⟩ 𝕎 b′
                      fromM (inj₁ (_ , ψ≺ψ)) = ⊥-elim (≺-irrefl ψ≺ψ)
                      fromM (inj₂ (_ , _ , r)) = r
                  cb′ : C ψc 𝕎 b′
                  cb′ = L4-7e oψb′ oψb′ oψc ⪯-refl (ψ≺κ oψb′) (≺⇒⪯ ψb′≺ψc) ψc≺I b′ gb′b′ cb″
                  b′<x : size b′ < size ⟨ psi κ b ⟩
                  b′<x = ≤-trans (size-ψc IR b′) (subst (λ t → size t ≤ size ⟨ psi κ b ⟩) eM (size-mFi≤ ⟨ psi κ b ⟩))
```

Lemma 4.38 (a)：`ψ_I c ∈ M(𝕎)`（连同模块前提 τ^𝕎(ψ_I c) ⊆ 𝕎，即 ψ_I c ∈ 𝒜^𝕎(𝕎)）⟹ `ψ_I c ∈ 𝕎`。用 Lemma 4.30，B := Γ^ω ∩ I。

```agda
  L4-38a : M 𝕎 ψc → 𝕎 ψc
  L4-38a mψ = L430.L4-30 mψ ψc≺I B cover B⊆
    where
      B : Pred 0ℓ
      B x = Γω x × x ≺ I′
      cover : ∀ {y} → τ 𝕎 ψc y → ∃ λ b → B b × y ⪯ b
      cover {y} t = y , (CWI⊆Γω y (τ→CWI t) , ≺-trans (proj₂ t) ψc≺I) , ⪯-refl
      B⊆ : B ⊆ (𝕎 ∣ ψc)
      B⊆ (Γx , x≺I) = CWI∩I→𝕎 (Γω⊆CWI Γx) x≺I , ≺⇒⪯ (proj₂ (CWI∩I→τ (Γω⊆CWI Γx) x≺I))
```

