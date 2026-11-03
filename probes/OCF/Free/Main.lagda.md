# 无记号主线 (二十): 闭包定理

> **`GᴺΩ̇ η`: $\psi_0(\Omega_{\Omega+\eta})$, 对一切 $\eta:$ `Ordᴵ`. `GᴺTΩ·2`: $\psi_0(\Omega_{\Omega\cdot2})$.** 强度的说法是验收的结论 ([Bridge](Bridge.lagda.md)); 这里只说证书存在.
> 脚本从 [UniformNF5Main](../Align/UniformNF5Main.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
> 对一切 $\psi$, $\iota$, 后继, $\oplus$ 的闭包: `good-ψ`, `good-ι`, `good-os`, `good-⊕`. 闭项在 [Closed](Closed.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Free.Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; toZ-≅; _≈ᴿ_; ≅ˢ-sym; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; Run; InF; inl; inr; ink; Dem; _∼ᶠ_; ∼ᶠ-refl; ⊔∼; flo; cvFlo; limA; wk; cloA; Top; bound; FB; liftEv; Bd; Fc; evF; iF; FM; ubd)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Force using (Goodᴺ-tr)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Tree
open import OCF.Free.Base
open import OCF.Free.Rules
open import OCF.Free.Strict
open import OCF.Free.Class
open import OCF.Free.ClassF
open import OCF.Free.Good
open import OCF.Free.Add
open import OCF.Free.Psi
open import OCF.Free.Eval
open import OCF.Free.Tail
open import OCF.Free.Omega 
```

```agda
open EvalM Ω̇G public using (T̄)
open PsiM Ω̇G public using (Psi)

Gᴺof : ∀ {c φ ℓ} {x : O c φ} → Gᵀ c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ x ev z))
Gᴺof g ev z = Good→N refl (T̄ {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺΩ̇ : ∀ η {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ η) ev z))
GᴺΩ̇ η = Gᴺof (Ω̇G η)
```

## §1 ℕ 的实例, 加法与塔

```agda
Gᴺfin : ∀ n {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ (natᴵ n)) ev z))
Gᴺfin n = GᴺΩ̇ (natᴵ n)

Gᴺω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ ωᴵ) ev z))
Gᴺω = GᴺΩ̇ ωᴵ

wfΩ̇ : ∀ c → WFl (Ω̇ c)
wfΩ̇ c = wfl (RΩ̇ (≅ᴵ-refl c)) (𝟏⊑Ω̇ c)

hoΩ̇ : ∀ c {C} → 𝓥 C → HonT (Ω̇ c) C
hoΩ̇ c x G (inr ink) = inj₂ z≅

Ω·2ᵒ : ∀ c → O c (Fl ⊔ Fl)
Ω·2ᵒ c = Ω̇ c ⊕ Ω̇ c

gΩ2 : ∀ c → Gᵀ c 𝓥 (Ω·2ᵒ c)
gΩ2 c = AddT.Add {𝓐 = 𝓥} (Ω̇G c) (wfΩ̇ c) (λ x o _ → x) (λ _ f → cxoᵀ f) (λ x → x) (hoΩ̇ c)
                 {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → wfΩ̇ c , x) (Ω̇G c)

GᴺΩ2 : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω·2ᵒ c) ev z))
GᴺΩ2 c = Gᴺof (gΩ2 c)

tsqᵒ : O zero (Fl ⊔ Fl)
tsqᵒ = ψᵒ zero (ι zero (Ω̇ zero))

gsq : Gᵀ zero 𝓥 tsqᵒ
gsq = Psi zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Iota zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Ω̇G zero))

Gᴺsq : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ tsqᵒ ev z))
Gᴺsq = Gᴺof gsq

Z₀ : Flr → Set
Z₀ φ = ∀ {K} (q : InF K φ) {X : Ordᴵ} → Dem X q

Z-Fl : Z₀ Fl
Z-Fl (inr ink) = inj₂ z≅

Z-⊔ : ∀ {a b} → Z₀ a → Z₀ b → Z₀ (a ⊔ b)
Z-⊔ za zb (inl q) = za q
Z-⊔ za zb (inr q) = zb q

good-ψ : ∀ {c t φ} (q : t <ᴵ c) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ t 𝓥 (ψᵒ q x)
good-ψ q = Psi q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-ι : ∀ {c d φ} (q : c ◃ d) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ d 𝓥 (ι q x)
good-ι q = Iota q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-os : ∀ {c φ} {a : O c φ} → Z₀ φ → Gᵀ c 𝓥 a → Gᵀ c 𝓥 (os a)
good-os z g = gs 𝓥 (λ x → x) g (λ _ f → cxoᵀ f) (λ x _ _ → x) (λ _ G q → z q)

good-⊕ : ∀ {c α φ} {W : O c α} {y : O c φ} → Z₀ α → WFl W → Gᵀ c 𝓥 W → Gᵀ c 𝓥 y → Gᵀ c 𝓥 (W ⊕ y)
good-⊕ {φ = φ} z w gW g = AddT.Add {𝓐 = 𝓥} gW w (λ x _ _ → x) (λ _ f → cxoᵀ f) (λ x → x) (λ _ G q → z q)
                                {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → w , x) g

Flᶠ : ℕ → Flr
Flᶠ zero    = Fl
Flᶠ (suc n) = Fl ⊔ Flᶠ n

tow : ∀ n → O zero (Flᶠ n)
tow zero    = Ω̇ zero
tow (suc n) = ψᵒ zero (os (ι zero (tow n)))

Z-tow : ∀ n → Z₀ (Flᶠ n)
Z-tow zero    = Z-Fl
Z-tow (suc n) = Z-⊔ Z-Fl (Z-tow n)

gtow : ∀ n → Gᵀ zero 𝓥 (tow n)
gtow zero    = Ω̇G zero
gtow (suc n) = good-ψ zero (good-os (Z-tow n) (good-ι zero (gtow n)))

Gᴺtow : ∀ n {ℓ} (ev : Ev ℓ (Flᶠ n)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (tow n) ev z))
Gᴺtow n = Gᴺof (gtow n)
```

## §2 值层的单调性

```agda
⊑ᵒ-≅ˡ : ∀ {k k′} {x x′ : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x′ → x′ ⊑ᵒ y → x ⊑ᵒ y
⊑ᵒ-≅ˡ e h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ d G (Goodᴺ-tr d G))) (h o (Goodᴺ-tr d G) G′)
  where d = toZ-≅ (run-≅ (≈ᵒ-reflˡ o) e)

module _ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} where
  Vstep : ∀ {k₀ b} {x : Ordˢ k₀} → x ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′ → x ⊑ᴱ ψ̄ (Ω̇ (suc b)) ev′ p′
  Vstep {b = b} h = lim-rᴱ 0 (⊑ᴱ-≅ʳ h (R→≈ (rwkʳ {le′ = proj₁} (R-ιʳ zero (rwkʳ {le′ = λ e → e} (RΩ̇ (≅ᴵ-refl b))))) ev′ p′ (ev′ , ev′) p′ (≅ᴵ-refl i)))

  Vlim : ∀ {k₀ g s} n {x : Ordˢ k₀} → x ⊑ᴱ ψ̄ (Ω̇ (g n)) ev′ p′ → x ⊑ᴱ ψ̄ (Ω̇ (lim g s)) ev′ p′
  Vlim n h = lim-rᴱ n (⊑ᴱ-≅ʳ h (R→≈ (R-ιʳ (self n) (RΩ̇ (≅ᴵ-refl _))) ev′ p′ ev′ p′ (≅ᴵ-refl i)))

Vz : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} b → ψ̄ (Ω̇ zero) ev p ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′
Vz {i} {ev = ev} {ev′} {p} {p′} zero = ≅→⊑ᴱ (R→≈ (RΩ̇ z≅) ev p ev′ p′ (≅ᴵ-refl i))
Vz {i} {ev = ev} {ev′} {p} {p′} (suc b) = Vstep {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} (Vz b)
Vz {i} {ev = ev} {ev′} {p} {p′} (lim g s) = Vlim {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} 0 (Vz (g 0))

Vs : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {a₀ a″ b} → a₀ ≅ᴵ a″ → a″ <ᴵ b → ψ̄ (Ω̇ (suc a₀)) ev p ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′
Vs {i} {ev = ev} {ev′} {p} {p′} e zero = ≅→⊑ᴱ (R→≈ (RΩ̇ (s≅ e)) ev p ev′ p′ (≅ᴵ-refl i))
Vs {ev = ev} {ev′} {p} {p′} e (suc q) = Vstep {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} (Vs e q)
Vs {ev = ev} {ev′} {p} {p′} e (lim n q) = Vlim {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} n (Vs e q)

Vm : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {a b} → a ⊑ᴵ b → ψ̄ (Ω̇ a) ev p ⊑ᵒ ψ̄ (Ω̇ b) ev′ p′
Vm {i} {ev = ev} {p = p} {b = b} z⊑ = ⊑ᴱ→ᵒ (R→≈ (RΩ̇ z≅) ev p ev p (≅ᴵ-refl i)) (Vz b)
Vm {i} {ev = ev} {p = p} (s⊑ e q) = ⊑ᴱ→ᵒ (R→≈ (RΩ̇ (≅ᴵ-refl _)) ev p ev p (≅ᴵ-refl i)) (Vs e q)
Vm {i} {ev = ev} {ev′} {p} {p′} (l⊑ k) = lim-l (λ n → ⊑ᵒ-≅ˡ (R→≈ (R-ιˡ (self n) (RΩ̇ (≅ᴵ-refl _))) ev p ev p (≅ᴵ-refl i)) (Vm {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} (k n)))
```

## §3 $\psi_0(\Omega_{\Omega\cdot2})$: 外层闭包定理

```agda
module TopClo (c : Ordᴵ → Ordᴵ) (F : ∀ η → O (c η) Fl) (gF : ∀ η → Gᵀ (c η) 𝓥 (F η))
              (rF : ∀ {η η′} → η ≅ᴵ η′ → Rᵒ (c η) (c η′) (F η) (F η′))
              (mF : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {η η′} → η ⊑ᴵ η′ → ψ̄ (F η) ev p ⊑ᵒ ψ̄ (F η′) ev′ p′) where

  Tᶜ : Run (Fl ⊔ fk zero)
  Tᶜ = cloA 0 {Fl} (wk 0 proj₁ (ψ̄ (F (suc zero)))) (λ η → wk 0 proj₁ (ψ̄ (F η)))

  rT : Tᶜ ≈ᴿ Tᶜ
  rT = cloR {t = wk 0 proj₁ (ψ̄ (F (suc zero)))} {g = λ η → wk 0 proj₁ (ψ̄ (F η))} {t′ = wk 0 proj₁ (ψ̄ (F (suc zero)))} {g′ = λ η → wk 0 proj₁ (ψ̄ (F η))}
            (∼ᶠ-refl Fl) (wkR proj₁ proj₁ (R→≈ (rF (≅ᴵ-refl _)))) (λ η η′ d → wkR proj₁ proj₁ (R→≈ (rF d)))

  module At {i ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (p : i <ᴵ ℓ) where
    B : Top i ℓ (Fl ⊔ fk zero)
    B = bound (Fl ⊔ fk zero) ev p

    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e = Mlev (Fc B) (suc η) (FB B e)

    evη : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) Fl
    evη η e = liftEv Fl (λ q → lim 0 q) (proj₁ (evF B))

    tg : ∀ η (e : Bd B ⊑ᴵ η) → i <ᴵ Lη η e
    tg η e = lim 0 (iF B)

    one⊑η : ∀ η → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
    one⊑η η e = ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)

    bd⊑ : ∀ {O : Obs i} {X : Ordˢ i} (G : Goodᴺ (toZ (run O X))) → suc i ⊑ᴵ lvG G → Bd B ⊑ᴵ lvG G
    bd⊑ G (s⊑ e q) = ubd B (via e q) (λ { (inl (inr ink)) → inj₂ z≅ ; (inr ink) → inj₂ z≅ })

    GoodT : Wit i (VT i) → Good true (VT i) (Tᶜ ev p)
    GoodT w =
      bŝ (λ _ _ → ⊤) (λ _ _ → tt)
         (T̄ {ev = proj₁ ev} {p = p} {𝓖 = 𝓥} {𝓖′ = VT i} (cxT i) (λ x → x) w (gF (suc zero)))
         (λ η e w′ → T̄ {ev = evη η e} {p = tg η e} {𝓖 = 𝓥} {𝓖′ = VT i ∧ (λ _ → ⊤)} (λ (x , _) → cxT i x) proj₁ w′ (gF η))
         (R→≈ (rF (≅ᴵ-refl _)) (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))
         (λ η e η′ e′ d → R→≈ (rF d) (evη η e) (tg η e) (evη η′ e′) (tg η′ e′) (≅ᴵ-refl i))
         (λ η e → mF (one⊑η η e))
         (λ η e η′ e′ u → mF u)
         (λ c₁ G → bd⊑ G (readT _ c₁ (R→≈ (rF (≅ᴵ-refl _)) (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i)) (F0ᵀ (rF (≅ᴵ-refl _))) G))
         (λ η e c₁ _ G → bd⊑ G (readT _ c₁ (R→≈ (rF (≅ᴵ-refl η)) (evη η e) (tg η e) (evη η e) (tg η e) (≅ᴵ-refl i)) (F0ᵀ (rF (≅ᴵ-refl η))) G))
         (λ _ _ → tt)
         (λ _ _ _ _ _ → tt)

  GᴺT : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᶜ ev z))
  GᴺT ev z = Good→N refl (At.GoodT ev z refl)

open TopClo (λ η → η) Ω̇ Ω̇G (λ e → RΩ̇ e) (λ u → Vm u) public using () renaming (GᴺT to GᴺTΩ·2; rT to RTΩ·2)

GoodTΩ·2 : ∀ {i ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (p : i <ᴵ ℓ) → Wit i (VT i) → Good true (VT i) (TΩ·2 ev p)
GoodTΩ·2 ev p = TopClo.At.GoodT (λ η → η) Ω̇ Ω̇G (λ e → RΩ̇ e) (λ u → Vm u) ev p
```

## §4 判据
