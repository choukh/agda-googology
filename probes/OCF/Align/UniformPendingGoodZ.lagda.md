# 统一折叠上的三层遗传好树 (二): 空前缀的折叠

> 接 [UniformPendingGoodBase](UniformPendingGoodBase.lagda.md). 本文是 PendingBase §5 的 `C-ψ0`/`P-ψ0`/`V-ψ0` 在统一折叠上的移植, 对相对前缀 $P$ 参数化. 目标 0 的 `Z-ψ0` 不移植: 它只用在 $\Omega$ 尾巴上, 下一篇由 Depth0 的 `good∅` 转换得到.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformPendingGoodZ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; tr⁻ˢ; Ωˢ; _+ˢ_; Goodᶻ; force; force-HS)
open import OCF.Align.UniformS using (⊑ᴵ-≅ˡ; _≅ˢ_; ≅ˢ-reflˡ; s≅; l≅; Ωˢ-refl; self-tr⁻ˢ; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ĉ-refl₀; ĉ-reflg)
open import OCF.Align.Uniform2Base using (Flr; fz; fk; _⊔_; Ev; Run; flo; cvFlo; toFlo; fold; ∅ᴿ; _≈ᴿ_; fold-≅0; chainA)
open import OCF.Align.UniformNFBase using (_⊑ᵒ_; idO; fold-cong; tr⁻-cong; rule4ᵒ; FlΛ; FlR; FlΛ-fold; FlR-∅; r∅; B1; dom-cov)
open import OCF.Align.UniformNFDepth0 using (NZ)
open import OCF.Align.UniformPendingGoodBase
```

## §1 链

`chain-≅`, `chain-st`: 对任意前缀 (Depth0 的 `chain-sim`/`chain-step` 的模块外版本). 对折叠的目标没有条件.

```agda
chain-≅ : ∀ {fl φ k j ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
          P ≈ᴿ P → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
          ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n ≅ˢ
                chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n
chain-≅ {j = j} r e zero = Ωˢ-refl j
chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} {q = q} r e (suc n) =
  fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = P} {P′ = P} r (i-respˢ e (chain-≅ {φ = φ} {P = P} {cv = cv} {ev = ev} r e n)) ev _ ev _ (≅ᴵ-refl _)

chain-st : ∀ {fl φ k j ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
           P ≈ᴿ P → FlR P → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f →
           (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
           ∀ n → chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev n ⊑ᵒ
                 chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))) ev (suc n)
chain-st {φ = φ} {j = j} {P = P} {cv = cv} {ev = ev} {q = q} {f = f} r fP e hm zero =
  B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} {x = Ωˢ j} r (fP (proj₁ ev) (cv (proj₂ ev) q) ⊑ᴵ-refl)
     (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} r fP e hm (suc n) = fold-cong r (hm (chain-st {φ = φ} {P = P} {cv = cv} {ev = ev} r fP e hm n))

NZ-≺ : ∀ {i j} → i ≺ᴵ j → NZ j
NZ-≺ {j = suc _}   _ = tt
NZ-≺ {j = lim _ _} _ = tt
NZ-≺ {j = zero} (via e ())

NZ-≅ : ∀ {i j} → NZ i → j ≅ᴵ i → NZ j
NZ-≅ {j = suc _}   nz e = tt
NZ-≅ {j = lim _ _} nz e = tt
NZ-≅ {j = zero} () z≅

<→⊑ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ {a} r = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ (via (≅ᴵ-refl a) r))
```

## §2 空前缀

```agda
module ZFold {fl} (P : Run fl) (rP : P ≈ᴿ P) where
  open GoodP P rP

  mkĉ : ∀ {m K m′ K′ ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
        Good m′ K′ t₀ → (∀ η e → Good m′ K′ (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
        Dom m′ K′ zero c t₀ g → Good m K o₀ → (∀ η e → Good m K (o η e)) →
        (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
        Good m K (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
  mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
    bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
       (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
       go gO mo mO
    where
    G₀ = Good→Goodᶻ g0
    Gg = λ η e → Good→Goodᶻ (gg η e)

  inb : ∀ {m m′ K j b k k′} (cvt : ∀ {ℓ} {x : Ordˢ ℓ} → Good m K x → Good m′ K x) {q : j <ᴵ k} {r : b <ᴵ k′} (e : j ≅ᴵ b) {z : Ordˢ b} →
        Gd m K b (<→◃ r) (intoˢ (<→◃ r) z) → Gd m′ K j (<→◃ q) (intoˢ (<→◃ q) (tr⁻ˢ e z))
  inb cvt {q} {r} e g = Good→Gd (<→◃ q) (cvt (Good-tr⁻ e (Gd→Good (<→◃ r) g)))

  C-f : ∀ {K φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} → NZ i → Good mC K x → x ≅ˢ x → Good mC K (fold 0 φ cv ∅ᴿ x ev p)
  P-f : ∀ {K φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} → NZ i → i ⊑ᴵ K → Good mC K x → x ≅ˢ x → Good mP K (fold 0 φ cv ∅ᴿ x ev p)
  V-f : ∀ {K φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k} → NZ i → K ⊑ᴵ i → Good mC K x → x ≅ˢ x → Good mV i (fold 0 φ cv ∅ᴿ x ev p)
  chainH : ∀ {K a φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → NZ j → K ⊑ᴵ a →
           (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mC a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
           Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mC a (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)
  chainL : ∀ {K a φ k j ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → NZ j → j ⊑ᴵ a → K ⊑ᴵ a →
           (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mP a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
           Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP a (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)

  chainH {a = a} {j = j} nj h hb e zero = Good-Ωᶜ j a
  chainH {a = a} {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} nj h hb ex (suc n) =
    C-f {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} nj (hb a h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} nj h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n))
  chainL {j = j} nj ja h hb e zero = Good-Ωᴾ j ja
  chainL {a = a} {φ = φ} {j = j} {cv = cv} {ev = ev} {q = q} {f = f} nj ja h hb ex (suc n) =
    P-f {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} nj ja (hb a h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} nj ja h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n))

  C-f {K} {i = i} nz bz ex = Good-Ωᶜ i K
  C-f {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} nz (bs g) ex = bl (Good-iter tt nz (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g ea) eψ′) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ ea ev p ev p (≅ᴵ-refl i)
  C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (bl hg st) ex = bl (λ n → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hg n) (l-invˢ ex n)) (λ n → fold-cong r∅ (st n))
  C-f {k = suc k′} {cv = cv} {ev = ev} {p = p} nz (bu {r = zero} g) ex = C-f {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} nz g (u-reflˢ zero ex)
  C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (bu {r = self n} g) ex = C-f {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} nz g (u-reflˢ (self n) ex)
  C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz go (ĉ-refl₀ ex)) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong r∅ (mo η e)) (λ η e η′ e′ hh → fold-cong r∅ (mO η e η′ e′ hh))
  C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biH (λ a h z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (biL {K} {p = q} {f = f} j₀ hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biL (⊑ᴵ-≅ˡ e j₀) (λ a h z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) j₀ ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) j₀ ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  C-f {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} nz (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g0 et) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
  C-f {φ = φ} {k = suc _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g0 et) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  C-f {φ = φ} {k = lim _ _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g0 et) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  C-f {φ = φ} {k = suc _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g0 et) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  C-f {φ = φ} {k = lim _ _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz g0 et) (λ η e → C-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)

  P-f {i = i} nz ik bz ex = Good-Ωᴾ i ik
  P-f {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} nz ik (bs g) ex = bl (Good-iter tt nz (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g ea) eψ′) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ ea ev p ev p (≅ᴵ-refl i)
  P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (bl hg st) ex = bl (λ n → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (hg n) (l-invˢ ex n)) (λ n → fold-cong r∅ (st n))
  P-f {k = suc k′} {cv = cv} {ev = ev} {p = p} nz ik (bu {r = zero} g) ex = P-f {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} nz ik g (u-reflˢ zero ex)
  P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (bu {r = self n} g) ex = P-f {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} nz ik g (u-reflˢ (self n) ex)
  P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik go (ĉ-refl₀ ex)) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong r∅ (mo η e)) (λ η e η′ e′ hh → fold-cong r∅ (mO η e η′ e′ hh))
  P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biP (⊑ᴵ-trans (<→⊑ r) ik) (λ a h z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (⊑ᴵ-trans ik h) (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (biL {K} {p = q} {f = f} j₀ hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biP (⊑ᴵ-≅ˡ e j₀) (λ a h z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz (⊑ᴵ-trans ik h) (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) j₀ ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (hb K ⊑ᴵ-refl _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) j₀ ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  P-f {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} nz ik (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g0 et) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
  P-f {φ = φ} {k = suc _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g0 et) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  P-f {φ = φ} {k = lim _ _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g0 et) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  P-f {φ = φ} {k = suc _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g0 et) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)
  P-f {φ = φ} {k = lim _ _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm (cvd , _)) ex =
    bŝ (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik g0 et) (λ η e → P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       (cvd , tt)

  V-f {i = i} nz h bz ex = Good-Ωⱽ i ⊑ᴵ-refl
  V-f {φ = φ} {i = i} {cv = cv} {ev = ev} {p = p} nz h (bs {a = y} g) ex =
    bl (λ n → proj₁ (V-iter nz (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g ea) (λ h′ → FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ h′ y ea) eψ′ n)) (rule4ᵒ eψ′)
    where ea = s-invˢ ex
          eψ′ = fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ ea ev p ev p (≅ᴵ-refl i)
  V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (bl hg st) ex = bl (λ n → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (hg n) (l-invˢ ex n)) (λ n → fold-cong r∅ (st n))
  V-f {k = suc k′} {cv = cv} {ev = ev} {p = p} nz h (bu {r = zero} g) ex = V-f {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (cv (proj₂ ev))} {p = p} nz h g (u-reflˢ zero ex)
  V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (bu {r = self n} g) ex = V-f {φ = φ} {cv = λ e q → cv e (lim n q)} {ev = ev} {p = p} nz h g (u-reflˢ (self n) ex)
  V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex = bĉ G₀ Gg d₀ dE m₀ mE (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h go (ĉ-refl₀ ex)) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gO η e) (ĉ-reflg ex η e)) (λ η e → fold-cong r∅ (mo η e)) (λ η e η′ e′ hh → fold-cong r∅ (mO η e η′ e′ hh))
  V-f {φ = φ} {i = a₀} {cv = cv} {ev = ev} {p = p} nz h (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
    (λ a k₁ z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz k₁ (hb a (⊑ᴵ-trans h k₁) (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ z ez gp gv → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainH {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  V-f {φ = φ} {i = a₀} {cv = cv} {ev = ev} {p = p} nz h (biL {K} {p = q} {f = f} j₀ hb hm) ex with <ᴵ-dec (cv (proj₂ ev) q) p
  ... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
    (λ a k₁ z ez g → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (P-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz k₁ (hb a (⊑ᴵ-trans h k₁) (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ z ez gp gv → subst (λ u → Good _ _ (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ r) z)) (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ez))))
    (λ {z} {z′} h₀ → subst₂ (λ u v → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p ⊑ᵒ fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))) ev p) (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (fold-cong r∅ (hm (tr⁻-cong h₀))))
  ... | injᵇ c = bl (λ n → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≺ c) (⊑ᴵ-trans j₀ h) h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  ... | injᶜ c = bl (λ n → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz ⊑ᴵ-refl (hb a₀ h _ (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n) (Good→Gd (<→◃ q) (chainL {φ = φ} {cv = cv} {ev = ev} (NZ-≅ nz c) (⊑ᴵ-trans j₀ h) h hb ex n))) (i-respˢ ex (chain-≅ {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ ex n)))
                    (λ n → fold-cong r∅ (hm (chain-st {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} r∅ FlR-∅ ex hm n)))
  V-f {φ = φ} {k = zero} {cv = cv} {ev = ev} {p = p} nz h (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g0 et) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
  V-f {φ = φ} {k = suc _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g0 et) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-f {φ = φ} {k = lim _ _} {i = suc _} {cv = cv} {ev = ev} {p = p} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g0 et) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-f {φ = φ} {k = suc _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g0 et) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
  V-f {φ = φ} {k = lim _ _} {i = lim _ _} {cv = cv} {ev = ev} {p = p} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((ψ , cvd , ψK) , _)) ex =
    bŝ (V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h g0 et) (λ η e → V-f {φ = φ} {cv = cv} {ev = ev} {p = p} nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ et ev p ev p (≅ᴵ-refl _))
       (λ η e η′ e′ eη → fold-≅0 {φ = φ} {φ′ = φ} {cv = cv} {cv′ = cv} {P = ∅ᴿ} {P′ = ∅ᴿ} r∅ (eg η e η′ e′ eη) ev p ev p (≅ᴵ-refl _))
       (λ η e → fold-cong r∅ (m η e)) (λ η e η′ e′ hh → fold-cong r∅ (mm η e η′ e′ hh))
       ((ψ , cvd , ⊑ᴵ-trans ψK h) , dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) t₀ et) cvd , λ η e → dom-cov rP (FlΛ-fold {φ = φ} {P = ∅ᴿ} {cv = cv} {ev = ev} {p = p} r∅ FlR-∅ (⊑ᴵ-trans ψK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cvd)
```
