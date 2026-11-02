# 统一折叠上的三层遗传好树 (三): 前缀 $P$ 的折叠定理

> 接 [UniformPendingGoodZ](UniformPendingGoodZ.lagda.md). 本文是 PendingBase §6–§7 的 `Fold.P-ψ1`/`V-ψ1`/`F₀` 在统一折叠上的移植, **对任意前缀 $P$ 参数化**: 唯一的外部数据是 $P$ 的自互模拟、地板与它的值在三个模式下的好性 (`vP`/`vV`/`v0`). `PopCov` 只出现在实例 (下一篇) 的 `vP`/`vV` 里.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPendingGoodF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Uˢ; Ordˢ; intoˢ; out-intoˢ; toZ; tr⁻ˢ; Goodᶻ)
open import OCF.Align.UniformS using (⊑ᴵ-≅ˡ; _≅ˢ_; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ĉ-refl₀; ĉ-reflg; self-tr⁻ˢ)
open import OCF.Align.Uniform2Base using (Flr; _⊔_; Ev; Run; flo; cvFlo; toFlo; fold; _≈ᴿ_; fold-≅0; chainA)
open import OCF.Align.UniformNFBase using (_⊑ᵒ_; fold-cong; tr⁻-cong; rule4ᵒ; FlR; FlΛ-fold; dom-cov; col; Ω-monoᵒ)
open import OCF.Align.UniformNFDepth0 using (NZ)
open import OCF.Align.UniformPendingGoodBase
open import OCF.Align.UniformPendingGoodZ using (chain-≅; chain-st; NZ-≺; NZ-≅; <→⊑; module ZFold)

module PFold {fl} (P : Run fl) (rP : P ≈ᴿ P) (fP : FlR P) (Tg : Ordᴵ → Set) {ℓ : Ordᴵ}
             (vP : ∀ {K i} (ev₀ : Ev ℓ fl) (p : i <ᴵ ℓ) → Tg i → NZ i → i ⊑ᴵ K → GoodP.Good P rP mP K (P ev₀ p))
             (vV : ∀ {a} (ev₀ : Ev ℓ fl) (p : a <ᴵ ℓ) → Tg a → NZ a → GoodP.Good P rP mV a (P ev₀ p))
             (v0 : ∀ (K′ : Ordᴵ) (ev₀ : Ev ℓ fl) (p : zero <ᴵ ℓ) → GoodP.Good P rP mV K′ (P ev₀ p)) where
  open GoodP P rP
  open ZFold P rP using (mkĉ; inb)

  P-g : ∀ {K φ k i} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} → Tg i → (∀ {j} → j <ᴵ k → Tg j) → NZ i → i ⊑ᴵ K → Good mP K x → x ≅ˢ x → Good mP K (fold 0 φ cv P x ev p)
  V-g : ∀ {K φ k i} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} → Tg i → (∀ {j} → j <ᴵ k → Tg j) → NZ i → K ⊑ᴵ i → Good mP K x → x ≅ˢ x → Good mV i (fold 0 φ cv P x ev p)
  chain1P : ∀ {K a φ k j} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → (∀ {j′} → j′ <ᴵ k → Tg j′) → NZ j → j ⊑ᴵ a → K ⊑ᴵ a →
            (∀ a′ → K ⊑ᴵ a′ → ∀ (y : Ordˢ j) → y ≅ˢ y → Gd mP a′ j (<→◃ q) (intoˢ (<→◃ q) y) → Good mP a′ (f (intoˢ (<→◃ q) y))) →
            Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP a (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n)
  F₀ : ∀ {K} (K′ : Ordᴵ) {φ k} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : zero <ᴵ ℓ} {x : Ordˢ k} → (∀ {j} → j <ᴵ k → Tg j) → Good mV K x → x ≅ˢ x → Good mV K′ (fold 0 φ cv P x ev p)
  chain1V : ∀ {κ φ k j} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → (∀ {j′} → j′ <ᴵ k → Tg j′) → j ⊑ᴵ κ →
            (∀ (y : Ordˢ j) → y ≅ˢ y → Gd mP κ j (<→◃ q) (intoˢ (<→◃ q) y) → (κ ⊑ᴵ j → Gd mV κ j (<→◃ q) (intoˢ (<→◃ q) y)) → Good mV κ (f (intoˢ (<→◃ q) y))) →
            Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP κ (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n) × (κ ⊑ᴵ j → Good mV κ (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n))

  chain1P {j = j} tk nj ja h tr e zero = Good-Ωᴾ j ja
  chain1P {a = a} {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} tk nj ja h tr ex (suc n) =
    P-g {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (tk q) tk nj ja (tr a h _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (chain1P {φ = φ} {cv = cv} {ev = ev} tk nj ja h tr ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n))

  P-g {ev = ev} {p = p} ti tk nz ik bz ex = vP (proj₁ ev) p ti nz ik
  P-g {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bs g) ex = bl (Good-iter tt nz (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g ea) eψ′) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP ea ev p ev p (≅ᴵ-refl i)
  P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bl hg st) ex = bl (λ n → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (hg n) (l-invˢ ex n)) (λ n → fold-cong rP (st n))
  P-g {k = suc k′} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bu {r = zero} g) ex = P-g {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} ti (λ j< → tk (suc j<)) nz ik g (u-reflˢ zero ex)
  P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bu {r = self n} g) ex = P-g {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} ti (λ j< → tk (lim n j<)) nz ik g (u-reflˢ (self n) ex)
  P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik go (ĉ-refl₀ ex)) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong rP (mo η e)) (λ η e η′ e′ hh → fold-cong rP (mO η e η′ e′ hh))
  P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (biP {K} {p = q} {f = f} j₀ tr hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biP (⊑ᴵ-≅ˡ e j₀) (λ a h y ey g → subst (λ u → Good _ _ (fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) y)) (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz (⊑ᴵ-trans ik h) (tr a h (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong rP (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (tr K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (chain1P {φ = φ} {cv = cv} {ev = ev} tk (NZ-≺ c) j₀ ⊑ᴵ-refl tr ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  ... | injᶜ c = bl (λ n → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (tr K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (chain1P {φ = φ} {cv = cv} {ev = ev} tk (NZ-≅ nz c) j₀ ⊑ᴵ-refl tr ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  P-g {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g0 et) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
  P-g {φ = φ} {k = suc _} {i = suc _} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g0 et) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       (cvd , tt)
  P-g {φ = φ} {k = lim _ _} {i = suc _} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g0 et) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       (cvd , tt)
  P-g {φ = φ} {k = suc _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g0 et) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       (cvd , tt)
  P-g {φ = φ} {k = lim _ _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} ti tk nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik g0 et) (λ η e → P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       (cvd , tt)

  V-g {ev = ev} {p = p} ti tk nz h bz ex = vV (proj₁ ev) p ti nz
  V-g {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} ti tk nz h (bs {a = y} g) ex =
    bl (λ n → proj₁ (V-iter nz (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g ea) (λ h′ → FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP h′ y ea) eψ′ n)) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP ea ev p ev p (≅ᴵ-refl i)
  V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (bl hg st) ex = bl (λ n → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (hg n) (l-invˢ ex n)) (λ n → fold-cong rP (st n))
  V-g {k = suc k′} {cv = cv} {ev = ev} {p = p} ti tk nz h (bu {r = zero} g) ex = V-g {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} ti (λ j< → tk (suc j<)) nz h g (u-reflˢ zero ex)
  V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (bu {r = self n} g) ex = V-g {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} ti (λ j< → tk (lim n j<)) nz h g (u-reflˢ (self n) ex)
  V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h go (ĉ-refl₀ ex)) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong rP (mo η e)) (λ η e η′ e′ hh → fold-cong rP (mO η e η′ e′ hh))
  V-g {φ = φ} {i = a₀} {cv = cv} {ev = ev} {p = p} ti tk nz h (biP {K} {p = q} {f = f} j₀ tr hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
    (λ a k₁ y ey g → subst (λ u → Good _ _ (fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) y)) (P-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz k₁ (tr a (⊑ᴵ-trans h k₁) (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (λ y ey gp gv → subst (λ u → Good _ _ (fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) y)) (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ⊑ᴵ-refl (tr a₀ h (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv P (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong rP (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ⊑ᴵ-refl (tr a₀ h _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (chain1P {φ = φ} {cv = cv} {ev = ev} tk (NZ-≺ c) (⊑ᴵ-trans j₀ h) h tr ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  ... | injᶜ c = bl (λ n → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz ⊑ᴵ-refl (tr a₀ h _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (chain1P {φ = φ} {cv = cv} {ev = ev} tk (NZ-≅ nz c) (⊑ᴵ-trans j₀ h) h tr ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  V-g {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} ti tk nz h (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g0 et) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
  V-g {φ = φ} {k = suc _} {i = suc _} {cv = cv} {ev = ev} {p = p} ti tk nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g0 et) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-g {φ = φ} {k = lim _ _} {i = suc _} {cv = cv} {ev = ev} {p = p} ti tk nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g0 et) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-g {φ = φ} {k = suc _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} ti tk nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g0 et) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-g {φ = φ} {k = lim _ _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} ti tk nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h g0 et) (λ η e → V-g {φ = φ} {cv = cv} {ev = ev} {p = p} ti tk nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} rP fP (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)

  chain1V {j = j} tk jκ ab e zero = Good-Ωᴾ j jκ , λ _ → Good-Ωⱽ j jκ
  chain1V {κ} {φ = φ} {j = zero} {cv = cv} {ev = ev} {q = q} {f = f} tk jκ ab ex (suc n) =
    V→P (F₀ κ {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} tk (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n))) ,
    λ _ → F₀ κ {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} tk (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n))
  chain1V {κ} {φ = φ} {j = suc _} {cv = cv} {ev = ev} {q = q} {f = f} tk jκ ab ex (suc n) =
    P-g {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (tk q) tk tt jκ (V→P (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h)))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)) ,
    λ κj → Good-mono jκ (V-g {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (tk q) tk tt κj (V→P (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h)))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
  chain1V {κ} {φ = φ} {j = lim _ _} {cv = cv} {ev = ev} {q = q} {f = f} tk jκ ab ex (suc n) =
    P-g {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (tk q) tk tt jκ (V→P (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h)))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)) ,
    λ κj → Good-mono jκ (V-g {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (tk q) tk tt κj (V→P (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h)))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))

  F₀ K′ {ev = ev} {p = p} tk bz ex = v0 K′ (proj₁ ev) p
  F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (bs g) ex = bl (Good-iter₀ (F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk g ea) eψ′) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP ea ev p ev p (≅ᴵ-refl zero)
  F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (bl hg st) ex = bl (λ n → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (hg n) (l-invˢ ex n)) (λ n → fold-cong rP (st n))
  F₀ K′ {k = suc k′} {cv = cv} {ev = ev} {p = p} tk (bu {r = zero} g) ex = F₀ K′ {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} (λ j< → tk (suc j<)) g (u-reflˢ zero ex)
  F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (bu {r = self n} g) ex = F₀ K′ {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} (λ j< → tk (lim n j<)) g (u-reflˢ (self n) ex)
  F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk go (ĉ-refl₀ ex)) (λ η e → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong rP (mo η e)) (λ η e η′ e′ hh → fold-cong rP (mO η e η′ e′ hh))
  F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (biV {p = q} {f = f} j₀ κ jκ κK tr ab hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e ())
  ... | injᵇ c = bl (λ n → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  ... | injᶜ c = bl (λ n → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (ab _ (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V {φ = φ} {cv = cv} {ev = ev} tk jκ ab ex n) h))) (i-respˢ ex (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} rP ex n)))
                    (λ n → fold-cong rP (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} rP fP ex hm n)))
  F₀ K′ {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} tk (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk g0 et) (λ η e → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
  F₀ K′ {φ = φ} {k = suc _} {cv = cv} {ev = ev} {p = p} tk (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (_ , c₀ , cg)) ex =
    bŝ (F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk g0 et) (λ η e → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((λ G → c₀ (col {φ = φ} {cv = cv} {ev = ev} {z = p}) G) , (λ η e G → cg η e (col {φ = φ} {cv = cv} {ev = ev} {z = p}) G))
  F₀ K′ {φ = φ} {k = lim _ _} {cv = cv} {ev = ev} {p = p} tk (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (_ , c₀ , cg)) ex =
    bŝ (F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk g0 et) (λ η e → F₀ K′ {φ = φ} {cv = cv} {ev = ev} {p = p} tk (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} rP (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong rP (m η e)) (λ η e η′ e′ hh → fold-cong rP (mm η e η′ e′ hh))
       ((λ G → c₀ (col {φ = φ} {cv = cv} {ev = ev} {z = p}) G) , (λ η e G → cg η e (col {φ = φ} {cv = cv} {ev = ev} {z = p}) G))
```
