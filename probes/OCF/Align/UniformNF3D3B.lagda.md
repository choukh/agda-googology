# 一切深度 (八): 反柯里化的树与原来的树互模拟

> 接 [UniformNF3D3T](UniformNF3D3T.lagda.md). 结论先说:
>
> 1. **`Cor d X X′`: 柯里化的 `A d` 与反柯里化的 `Fr d` 的对应.** 相关的脊上, 值互模拟 (`≈ᴿ` 不看环境).
> 2. **`foldC`: 折叠保持 `Cor`**, `fold-≅U` 的克隆. 各行引理 `limS`, `limᵢS`, `ĉS`, `ŝS`, `cloS` 对 $d$ 递归, 每一步只把一个参数搬进脊.
> 3. **`CΘf n : Cor (suc n) (Ω̂A n) (Θf n)`.** 所以 `Ω̂A n (Ω̂A (n-1)) … (Ω̂A 0) ∅ᴿ` 与塔 `T n` 互模拟.
> 4. **地板的结合律 `≃ᶠ`:** `bound` 按中序读地板, 两边的地板只差结合与 `fz`, 所以界相同.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3B where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; _≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; kd-≅; ≅→Rˢ; flo-∼; tf; toZ-≅; Ωˢ-≅; _≈ᴿ_; limR; limᵢR; ĉR; ŝR; fold-≅0)
open import OCF.Align.Uniform3Base using (Sym; ∅ᵀ; _⊕_; Ψ; ψᵀ; Flr; fz; fk; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; flo; cvFlo; toFlo; repA; fold; cloA; Ω̂A; ∅ᴿ; Top; Bd; accT; top₀; bound; accM; _∼ᶠ_; ∼ᶠ-refl; fk∼; fz∼; ⊔∼)
open import OCF.Align.UniformNF3D3O using (Fr; Sp; sf; fold1; repU; rowU)
open import OCF.Align.UniformNF3D3T using (Θ₀; Θ; Θf; Ω̂U; nzB; ∅U; ws; T)
open import OCF.Align.UniformNF3D3C using (NZ)
open import OCF.Align.UniformNF3D3W using (WSp; er)
```

## §1 地板的结合律

```agda
_≃ᶠ_ : Flr → Flr → Set
a ≃ᶠ b = ∀ {i i′ ℓ ℓ′ φ φ′} (t : Top i ℓ φ) (t′ : Top i′ ℓ′ φ′) (ev : Ev ℓ a) (ev′ : Ev ℓ′ b) → Bd t ≅ᴵ Bd t′ → Bd (accT t a ev) ≅ᴵ Bd (accT t′ b ev′)

∼→≃ : ∀ {a b} → a ∼ᶠ b → a ≃ᶠ b
∼→≃ s t t′ ev ev′ h = accM t t′ s ev ev′ h

≃-refl : ∀ a → a ≃ᶠ a
≃-refl a = ∼→≃ (∼ᶠ-refl a)

≃⊔ : ∀ {a a′ b b′} → a ≃ᶠ a′ → b ≃ᶠ b′ → (a ⊔ b) ≃ᶠ (a′ ⊔ b′)
≃⊔ {a} {a′} sa sb t t′ (x , y) (x′ , y′) h = sb (accT t a x) (accT t′ a′ x′) y y′ (sa t t′ x x′ h)

≃-unitl : ∀ {a b} → a ≃ᶠ b → (fz ⊔ a) ≃ᶠ b
≃-unitl s t t′ (_ , x) x′ h = s _ t′ x x′ h

≃-unitl′ : ∀ {a b} → a ≃ᶠ b → a ≃ᶠ (fz ⊔ b)
≃-unitl′ s t t′ x (_ , x′) h = s t _ x x′ h

≃-unitr : ∀ {a b} → a ≃ᶠ b → (a ⊔ fz) ≃ᶠ b
≃-unitr s t t′ (x , _) x′ h = s t t′ x x′ h

≃-assoc′ : ∀ {a b c d} → a ≃ᶠ (b ⊔ (c ⊔ d)) → a ≃ᶠ ((b ⊔ c) ⊔ d)
≃-assoc′ {b = b} {c} {d} s t t′ x ((y , z) , w) h =
  ≅ᴵ-trans (s t t′ x (y , (z , w)) h) (accM (accT (accT t′ b y) c z) (accT t′ (b ⊔ c) (y , z)) (∼ᶠ-refl d) w w (≅ᴵ-refl _))
```

## §2 脊与 `Cor`

```agda
CA : ℕ → Set
CA zero    = ⊤
CA (suc d) = Σ Flr λ fl → A d fl × CA d

capF : ∀ {d : ℕ} → CA d → Flr → Flr
capF {d = zero}  _ φ = φ
capF {d = suc d} (fl , P , c) φ = capF c (fl ⊔ φ)

capp : ∀ {d : ℕ} {φ} (c : CA d) → A d φ → Run (capF c φ)
capp {d = zero}  _ X = X
capp {d = suc d} (fl , P , c) X = capp c (X P)

mutual
  CorS : ∀ {d : ℕ} → CA d → Sp d → Set
  CorS {d = zero}  _ _ = ⊤
  CorS {d = suc d} (fl , P , c) (fl′ , P′ , s) = (fl ≃ᶠ fl′) × (Cor d P P′ × CorS c s)

  Cor : ∀ (d : ℕ) {φ ψ} → A d φ → Fr d ψ → Set
  Cor d X X′ = ∀ {c s} → CorS c s → capp c X ≈ᴿ X′ s

capF≃ : ∀ {d : ℕ} {c : CA d} {s : Sp d} {φ φ′} → CorS c s → φ ≃ᶠ φ′ → capF c φ ≃ᶠ (sf s ⊔ φ′)
capF≃ {d = zero} _ h = ≃-unitl′ h
capF≃ {d = suc d} (sφ , _ , cs) h = ≃-assoc′ (capF≃ cs (≃⊔ sφ h))
```

## §3 行引理

每一条对 $d$ 递归: `capp` 把一个参数搬进 $c$.

```agda
wkS : ∀ {d : ℕ} {φ ψ χ} (c : CA d) {X : A d φ} {le : ∀ {L} → Ev L ψ → Ev L φ} {Z : Run χ} → capp c X ≈ᴿ Z → capp c (wk d le X) ≈ᴿ Z
wkS {d = zero} c h ev p ev′ p′ ei = h _ p ev′ p′ ei
wkS {d = suc d} (fl , P , c) h = wkS c h

limS : ∀ {d : ℕ} {φ χ} (c : CA d) {F : ℕ → A d φ} {Z : ℕ → Run χ} → (∀ m → capp c (F m) ≈ᴿ Z m) → capp c (limA d F) ≈ᴿ limA 0 Z
limS {d = zero} c h = limR h
limS {d = suc d} (fl , P , c) h = limS c h

limᵢS : ∀ {d : ℕ} {φ χ j j′} (c : CA d) {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L χ → j′ <ᴵ L} {H : Ordˢ j → A d φ} {H′ : Ordˢ j′ → Run χ} →
        j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → capp c (H x) ≈ᴿ H′ y) → capp c (limᵢA d ac H) ≈ᴿ limᵢA 0 ac′ H′
limᵢS {d = zero} c e h = limᵢR e h
limᵢS {d = suc d} (fl , P , c) e h = limᵢS c e h

ĉS : ∀ {d : ℕ} {φ χ c₀ c₁ t₀ t₁} (c : CA d) {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z}
     {O₀ : A d φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} {O₀′ : Run χ} {O′ : (η : Ordᴵ) → c₁ ⊑ᴵ η → Run χ} →
     c₀ ≅ᴵ c₁ → t₀ ≅ᶻ t₁ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
     capp c O₀ ≈ᴿ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → capp c (O η e) ≈ᴿ O′ η′ e′) → capp c (ĉA d c₀ t₀ g O₀ O) ≈ᴿ ĉA 0 c₁ t₁ g′ O₀′ O′
ĉS {d = zero} c ec dt dg h₀ h = ĉR ec dt dg h₀ h
ĉS {d = suc d} (fl , P , c) ec dt dg h₀ h = ĉS c ec dt dg h₀ h

ŝS : ∀ {d : ℕ} {φ χ c₀ c₁} (c : CA d) {T₀ : A d φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} {T₀′ : Run χ} {G′ : (η : Ordᴵ) → c₁ ⊑ᴵ η → Run χ} →
     c₀ ≅ᴵ c₁ → capp c T₀ ≈ᴿ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → capp c (G η e) ≈ᴿ G′ η′ e′) → capp c (ŝA d c₀ T₀ G) ≈ᴿ ŝA 0 c₁ T₀′ G′
ŝS {d = zero} c ec h₀ h = ŝR ec h₀ h
ŝS {d = suc d} (fl , P , c) ec h₀ h = ŝS c ec h₀ h

cloS : ∀ {d : ℕ} {φ ψ} (c : CA d) {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)} {t′ : Run (ψ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (ψ ⊔ fk η)} →
       capF c φ ≃ᶠ ψ → capp c t ≈ᴿ t′ → (∀ η η′ → η ≅ᴵ η′ → NZ η → capp c (g η) ≈ᴿ g′ η′) → capp c (cloA d t g) ≈ᴿ cloA 0 t′ g′
cloS {d = zero} {φ} {ψ} c sh ht hg ev p ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (≃⊔ sh (∼→≃ (fk∼ z≅)) (top₀ p) (top₀ p′) ev ev′ (s≅ ei)) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη (nzB (bound (φ ⊔ fk zero) ev p) e) _ _ _ _ ei)
cloS {d = suc d} {φ} (fl , P , c) {t} {g} sh ht hg =
  wkS c (cloS {φ = fl ⊔ φ} c sh (wkS c ht) (λ η η′ eη nz → wkS c (hg η η′ eη nz)))
```

## §4 副本与折叠

```agda
repC : ∀ {d : ℕ} {fl fl′ ψ ψ′} {Q : A d fl} {Q′ : Fr d fl′} {fr : A (suc d) ψ} {fr′ : Fr (suc d) ψ′} →
       fl ≃ᶠ fl′ → ψ ≃ᶠ ψ′ → Cor d Q Q′ → Cor (suc d) fr fr′ → ∀ m → Cor d (repA d Q fr m) (repU Q′ fr′ m)
repC sf₁ sψ cQ cF zero {c} cs ev p ev′ p′ ei = wkS c (cQ cs) ev p _ p′ ei
repC sf₁ sψ cQ cF (suc zero) cs ev p ev′ p′ ei = cF (sf₁ , cQ , cs) ev p _ p′ ei
repC sf₁ sψ cQ cF (suc (suc m)) {c} cs ev p ev′ p′ ei =
  wkS c (cF (≃⊔ sf₁ sψ , repC sf₁ sψ cQ cF (suc m) , cs)) ev p _ p′ ei

foldC : ∀ {d : ℕ} {flE flE′ k₁ k₂} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L}
        {E : A (suc d) flE} {E′ : Fr (suc d) flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
        flE ≃ᶠ flE′ → Cor (suc d) E E′ → a ≅ˢ b → Cor (suc d) (fold (suc d) (flo k₁) cv E a) (fold1 (flo k₂) cv′ E′ b)
foldC sE cE z≅ {fl , P , c} cs ev p ev′ p′ ei = wkS c (cE cs) ev p _ p′ ei
foldC sE cE (s≅ le e) {fl , P , c} {fl′ , P′ , s} (sφ , cP , cs) ev p ev′ p′ ei =
  limS c (λ m → repC sφ (≃⊔ sE (∼→≃ (flo-∼ le))) cP (foldC sE cE e) m cs) ev p (proj₁ (proj₁ ev′) , (proj₂ (proj₁ ev′) , proj₂ ev′)) p′ ei
foldC sE cE (l≅ h) {fl , P , c} cs = limS c (λ n → foldC sE cE (h n) cs)
foldC sE cE (lᵢ≅ {p = q} e h) {fl , P , c} cs = limᵢS c e (λ x y d → foldC sE cE (h x y (≅→Rˢ (<→◃ q) d)) cs)
foldC {k₁ = suc k′} sE cE (upˡ {r = zero} e) {fl , P , c} cs ev p ev′ p′ ei =
  wkS c (foldC {cv = cvFlo k′} sE cE e cs) ev p _ p′ ei
foldC {k₁ = lim f t} sE cE (upˡ {r = self n} e) {fl , P , c} cs ev p ev′ p′ ei =
  wkS c (foldC {cv = cvFlo (f n)} sE cE e cs) ev p _ p′ ei
foldC {k₂ = suc k′} sE cE (upʳ {r = zero} e) cs ev p ev′ p′ ei =
  foldC {cv′ = cvFlo k′} sE cE e cs ev p _ p′ ei
foldC {k₂ = lim f t} sE cE (upʳ {r = self n} e) cs ev p ev′ p′ ei =
  foldC {cv′ = cvFlo (f n)} sE cE e cs ev p _ p′ ei
foldC {k₁ = zero} {k₂ = zero} sE cE (ŝ≅ k ec et eg) {fl , P , c} cs =
  ĉS c ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (foldC sE cE et cs) (λ η e η′ e′ eη → foldC sE cE (eg η e η′ e′ eη) cs)
foldC {k₁ = zero} {k₂ = suc _}   sE cE (ŝ≅ k ec et eg) cs = ⊥-elim (tf k)
foldC {k₁ = zero} {k₂ = lim _ _} sE cE (ŝ≅ k ec et eg) cs = ⊥-elim (tf k)
foldC {k₁ = suc _}   {k₂ = zero} sE cE (ŝ≅ k ec et eg) cs = ⊥-elim (tf (sym k))
foldC {k₁ = lim _ _} {k₂ = zero} sE cE (ŝ≅ k ec et eg) cs = ⊥-elim (tf (sym k))
foldC {k₁ = suc _} {k₂ = suc _} sE cE (ŝ≅ k ec et eg) {fl , P , c} cs =
  ŝS c ec (foldC sE cE et cs) (λ η e η′ e′ eη → foldC sE cE (eg η e η′ e′ eη) cs)
foldC {k₁ = suc _} {k₂ = lim _ _} sE cE (ŝ≅ k ec et eg) {fl , P , c} cs =
  ŝS c ec (foldC sE cE et cs) (λ η e η′ e′ eη → foldC sE cE (eg η e η′ e′ eη) cs)
foldC {k₁ = lim _ _} {k₂ = suc _} sE cE (ŝ≅ k ec et eg) {fl , P , c} cs =
  ŝS c ec (foldC sE cE et cs) (λ η e η′ e′ eη → foldC sE cE (eg η e η′ e′ eη) cs)
foldC {k₁ = lim _ _} {k₂ = lim _ _} sE cE (ŝ≅ k ec et eg) {fl , P , c} cs =
  ŝS c ec (foldC sE cE et cs) (λ η e η′ e′ eη → foldC sE cE (eg η e η′ e′ eη) cs)
foldC sE cE (ĉ≅ ec dt dg eo eO) {fl , P , c} cs =
  ĉS c ec dt dg (foldC sE cE eo cs) (λ η e η′ e′ eη → foldC sE cE (eO η e η′ e′ eη) cs)
```

## §5 闭包算子对应

```agda
module ΩC {m : ℕ} {fl fl′} {E : A (suc m) fl} {E′ : Fr (suc m) fl′} {c : CA (suc m)} {s : Sp (suc m)} (sE : fl ≃ᶠ fl′) (cE : Cor (suc m) E E′) (cs : CorS c s) where
  Gg : ∀ η′ → Run ((sf s ⊔ fl′) ⊔ fk η′)
  Gg η′ e q = fold1 (fk η′) (λ e′ q′ → e′ (suc q′)) E′ (Ωˢ η′) s (proj₁ (proj₁ e) , (proj₂ (proj₁ e) , proj₂ e)) q

  ΩS : ∀ η η′ → η ≅ᴵ η′ → NZ η → capp c (fold (suc m) (fk η) (λ e q → e (suc q)) E (Ωˢ η)) ≈ᴿ Gg η′
  ΩS (suc j) (suc j′) (s≅ e) nz ev p ev′ p′ ei =
    limᵢS c {ac′ = λ e₁ → proj₂ (proj₂ e₁) (suc zero)} {H′ = λ x → fold1 (fk (suc j′)) (λ e′ q′ → e′ (suc q′)) E′ (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) s} e
      (λ x y d ev₁ p₁ ev₁′ p₁′ ei₁ → wkS c (foldC {cv = cvFlo j} {cv′ = cvFlo j′} sE cE d cs) ev₁ p₁ _ p₁′ ei₁)
      ev p (proj₁ (proj₁ ev′) , (proj₂ (proj₁ ev′) , proj₂ ev′)) p′ ei
  ΩS (lim f a) (lim g b) (l≅ h) nz ev p ev′ p′ ei =
    limS c {Z = λ n → fold1 (fk (lim g b)) (λ e′ q′ → e′ (suc q′)) E′ (Ord₊ˢ.up (self n) (Ωˢ (g n))) s}
      (λ n ev₁ p₁ ev₁′ p₁′ ei₁ → wkS c (foldC {cv = cvFlo (f n)} {cv′ = cvFlo (g n)} sE cE (Ωˢ-≅ (h n)) cs) ev₁ p₁ _ p₁′ ei₁)
      ev p (proj₁ (proj₁ ev′) , (proj₂ (proj₁ ev′) , proj₂ ev′)) p′ ei

CΘ : ∀ m → Cor (suc (suc m)) (Ω̂A (suc m)) (Θ m)
CΘ m {fl , E , c} {fl′ , E′ , s} (sE , cE , cs) =
  cloS {d = suc m} {φ = fl} {ψ = sf s ⊔ fl′} c
    {t′ = λ e q → fold1 (fk zero) (λ e′ → e′) E′ (Ωˢ (suc zero)) s (proj₁ (proj₁ e) , (proj₂ (proj₁ e) , proj₂ e)) q}
    {g′ = λ η e q → fold1 (fk η) (λ e′ q′ → e′ (suc q′)) E′ (Ωˢ η) s (proj₁ (proj₁ e) , (proj₂ (proj₁ e) , proj₂ e)) q}
    (capF≃ cs sE)
    (λ ev p ev′ p′ ei → foldC {cv = cvFlo (suc zero)} {cv′ = cvFlo (suc zero)} sE cE (Ωˢ-≅ (≅ᴵ-refl (suc zero))) cs ev p _ p′ ei)
    (ΩC.ΩS sE cE cs)

CΘ₀ : Cor 1 (Ω̂A 0) Θ₀
CΘ₀ {fl , P , _} {fl′ , P′ , _} (sφ , cP , _) =
  cloS {d = zero} {φ = fl} {ψ = fz ⊔ fl′} tt
    {t′ = fold 0 (fk zero) (λ e → e) (P′ tt) (Ωˢ (suc zero))}
    {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) (P′ tt) (Ωˢ η)}
    (≃-unitl′ sφ)
    (fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} (cP {tt} {tt} tt) (Ωˢ-≅ (≅ᴵ-refl (suc zero))))
    (λ η η′ eη _ → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = λ e q → e (suc q)} {cv′ = λ e q → e (suc q)} (cP {tt} {tt} tt) (Ωˢ-≅ eη))

CΘf : ∀ n → Cor (suc n) (Ω̂A n) (Θf n)
CΘf zero    = CΘ₀
CΘf (suc n) = CΘ n
```

## §6 塔与替身

`cw n`: 柯里化一侧的脊 $\hat\Omega_{n-1},\dots,\hat\Omega_0,\emptyset$. `OP`: 与 [Uniform3OmegaPlus1](Uniform3OmegaPlus1.lagda.md) `OmegaPlus` 同文, 那个文件读记号, 所以这里抄一份树的定义; 验收处定义性地等同.

```agda
cw : ∀ n → CA (suc n)
cw zero    = fz , ∅ᴿ , tt
cw (suc n) = fk zero , Ω̂A n , cw n

csw : ∀ n → CorS (cw n) (er (ws n))
csw zero    = ≃-refl fz , (λ _ ev p ev′ p′ ei → Ωˢ-≅ ei) , tt
csw (suc n) = ≃-refl (fk zero) , CΘf n , csw n

T′ : ∀ j → Run (sf (er (ws j)) ⊔ fk zero)
T′ j = Θf j (er (ws j))

module OP where
  ΓF : ℕ → Flr
  ΓF zero    = fz ⊔ (fk zero ⊔ fz)
  ΓF (suc n) = fz ⊔ (fk zero ⊔ ΓF n)

  ΓS : ∀ n → Sym (ΓF n)
  ΓS zero    = ∅ᵀ ⊕ Ψ ∅ᵀ
  ΓS (suc n) = ∅ᵀ ⊕ Ψ (ΓS n)

  evΓ : ∀ n {ℓ} → Ev ℓ (fz ⊔ fk zero) → Ev ℓ (ΓF n)
  evΓ zero    e = proj₁ e , (proj₂ e , tt)
  evΓ (suc n) e = proj₁ e , (proj₂ e , evΓ n e)

  leΓ : ∀ n {fl ℓ} → Ev ℓ (fl ⊔ (fz ⊔ fk zero)) → Ev ℓ (fl ⊔ ΓF n)
  leΓ n e = proj₁ e , evΓ n (proj₂ e)

  Ω⁺ : Sym (fz ⊔ fk zero)
  Ω⁺ d P = limA d (λ n → wk d (leΓ n) (ΓS n d P))

open OP

plus : ℕ → ℕ → ℕ
plus zero    m = m
plus (suc n) m = plus n (suc m)

plus-suc : ∀ n m → plus n (suc m) ≡ suc (plus n m)
plus-suc zero    m = refl
plus-suc (suc n) m = plus-suc n (suc m)

corΓ : ∀ n m (c : CA (suc m)) → CorS c (er (ws m)) → capp c (ΓS n m) ≈ᴿ T′ (plus n m)
corΓ zero m (fl , P , c) (sφ , cP , cs) =
  wkS c (wkS c (CΘf m {fl ⊔ fz , wk m proj₁ P , c} {er (ws m)} (≃-unitr sφ , (λ {c′} cs′ → wkS c′ (cP cs′)) , cs)))
corΓ (suc n) m (fl , P , c) (sφ , cP , cs) =
  wkS c (corΓ n (suc m) (fk zero , Ω̂A m , fl ⊔ fz , wk m proj₁ P , c)
    (≃-refl (fk zero) , CΘf m , ≃-unitr sφ , (λ {c′} cs′ → wkS c′ (cP cs′)) , cs))

pt≈ : ∀ n → ΓS n 0 ∅ᴿ ≈ᴿ T′ (plus n 0)
pt≈ n = corΓ n 0 (cw 0) (csw 0)

Ψ3≈ : ψᵀ (Ψ (Ψ (Ψ ∅ᵀ))) ≈ᴿ T′ 2
Ψ3≈ ev p ev′ p′ ei = CΘf 2 {cw 2} {er (ws 2)} (csw 2) _ p ev′ p′ ei
```
