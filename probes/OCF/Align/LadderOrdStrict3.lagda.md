# 序数高度: 节点的严格增长

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfStrict3](LadderInfStrict3.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 对高度结构 `HtB` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFStrict3](LadderNFStrict3.lagda.md) 生成, 下面的说明是原文件的. `ClimbΩ`, `Climb↓`: $x\prec$ `qΩ`, $x\prec$ `qΩ↓`, 只要 $x$ 严格低于每个严格高于 $\dot\Omega_k$ 的 $h(z)$. `Ω↓≺`: 经 `ι↓` 看, $\dot\Omega_a\prec\dot\Omega_{a+1}$. 这是高度 $n$ 的闭包守卫增长所需的全部严格性. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdStrict3 (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Free.Floor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; bound)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdRules3 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import Data.Bool using (Bool; true; false)
open import OCF.Free.Eq using (backˢ-≅; back⁻ˢ-≅; ≅ˢ-trans)
open import OCF.Align.LadderOrdStrict2 𝕊

open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

## §1 辅助

```agda
≺-≅ˡ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₃} {a : Ordᶜ ℓ₂} → c′ ≅ c → c ≺ a → c′ ≺ a
≺-≅ˡ e (≺z e₀) = ≺z (≅-trans e e₀)
≺-≅ˡ e (≺s h) = ≺s (≺-≅ˡ e h)
≺-≅ˡ e (≺l n h) = ≺l n (≺-≅ˡ e h)
≺-≅ˡ e (≺i x ex h) = ≺i x ex (≺-≅ˡ e h)
≺-≅ˡ e (≺u h) = ≺u (≺-≅ˡ e h)

nbW : ∀ {m c φ χ ψ ρ} b {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} (C : Cx m c ψ ρ) → NdB b C → NdB b (wkC le lc C)
nbW true C n = tt
nbW false C n = Nd-wk C n

Ls-wk : ∀ {m c φ₀ χ₀ φ χ ψ ρ} b {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {x : Q m c φ₀ χ₀} {y : Q m c φ χ} → Ls b x y → Ls b x (qwk le lc y)
Ls-wk b {le} {lc} {y = y} h {C} {C′} o c nd G′ = proj₁ K , proj₂ L (proj₂ K)
  where
  L = pull≡ (run-wkC le lc C′ y) G′
  K = h (≈ᶜ-wkʳ le lc o) (Ctx-wkC C′ c) (nbW b C′ nd) (proj₁ L)

Ls-lim : ∀ {m c φ₀ χ₀ φ χ} b {x : Q m c φ₀ χ₀} {F : ℕ → Q m c φ χ} n → Rq m c c (F n) (F n) → Ls b x (F n) → Ls b x (ql F)
Ls-lim b {F = F} n rF h o c nd G′ = proj₁ K , proj₂ J (proj₂ K)
  where
  J = lim-rᵀ {x = F n} {F = F} n (R→⊑ᵀ rF) (≈ᶜ-reflʳ o) G′
  K = h o c nd (proj₁ J)

Sz : ∀ m k {ξ ζ} → Q m k ξ ζ → Set
Sz m k z = Ls true (Ω̇ m k) z

Sψ : ∀ {m c t φ χ} (q : t <ᴵ c) {y : Q m c φ χ} → One y → Sz m t (ψᵠ q y)
Sψ {m} {t = t} {φ} {χ} q {y} hy {C} {C′} o c _ G′ = proj₁ K , proj₂ J₁ (proj₂ J₂ (proj₂ K))
  where
  le₁ : ∀ {L} → Ev L Fl → Ev L (Fl ⊔ fz)
  le₁ e = e , tt
  lc₁ : Sub m (κ Fl) (Z* (κ fz))
  lc₁ i r e = e , tt
  C₁ = wkC le₁ lc₁ C
  o₁ : C₁ ≈ᶜ C′
  o₁ = ≈ᶜ-wkˡ le₁ lc₁ o
  J₁ = hy {C₀ = pψ q C₁} (pψ o₁) tt G′
  X : Q m t (Fl ⊔ fz) (Z* (κ fz))
  X = ψᵠ q q0
  rX : Rq m t t X X
  rX = R-ψᵠ q q (≅ᴵ-refl t) rz
  le₂ : ∀ {L} → Ev L (Fl ⊔ fz) → Ev L ((Fl ⊔ fz) ⊔ fz)
  le₂ e = e , tt
  lc₂ : Sub m (Z* (κ fz)) (Z* (κ fz) ∪ κ fz)
  lc₂ i r e = e , tt
  J₂ = subst (λ w → Σ (Goodᴺ (toZ (runᶜ (wkC le₂ lc₂ C₁) w))) λ G → forceᴺ _ G ⊑ forceᴺ _ (proj₁ J₁)) (⊞𝟏 t X)
         (lim-rᵀ {x = X ⊞ 𝟏q t} {F = repᵠ X} 2 (wk-rᵀ (⊞-cong rX (wk-rᵀ (𝟏⊑Ω̇ m t)))) (≈ᶜ-wkˡ le₂ lc₂ (≈ᶜ-reflˡ o₁)) (proj₁ J₁))
  K = Sᵀ {a = Ω̇ m t} {a′ = qwk proj₁ (λ i r → proj₁) X} o (≈ᶜ-wkʳ le₂ lc₂ (≈ᶜ-sym o₁)) (rwkʳ (rwkʳ (RΩ̇ m (≅ᴵ-refl t)))) (rwk rX) (proj₁ J₂)

SΨ : ∀ {H m c t φ χ w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) {y : Q m c φ χ} → One y → Sz H t (Ψ qH ok e p y)
SΨ {H} {m} {t = t} {φ} {χ} {w} qH ok e p {y} hy {C} {C′} o c _ G′ = proj₁ K , proj₂ J₁ (proj₂ J₂ (proj₂ K))
  where
  le₁ : ∀ {L} → Ev L Fl → Ev L (Fl ⊔ fz)
  le₁ e₁ = e₁ , tt
  lc₁ : Sub H (κ Fl) (Z* (κ fz))
  lc₁ i r e₁ = e₁ , tt
  C₁ = wkC le₁ lc₁ C
  o₁ : C₁ ≈ᶜ C′
  o₁ = ≈ᶜ-wkˡ le₁ lc₁ o
  e₀ : Eh H m w (κ fz)
  e₀ i h r = tt
  J₁ = hy {C₀ = pΨ qH ok e₀ p C₁} (pΨ {qH = qH} {ok = ok} {ok′ = ok} {e = e₀} {e′ = e} {p = p} {p′ = p} o₁) tt G′
  X : Q H t (Fl ⊔ fz) (Z* (κ fz))
  X = qwk proj₁ fc* (Ω̇ H t)
  rX : Rq H t t X X
  rX = rwk (RΩ̇ H (≅ᴵ-refl t))
  le₂ : ∀ {L} → Ev L (Fl ⊔ fz) → Ev L ((Fl ⊔ fz) ⊔ fz)
  le₂ e₁ = e₁ , tt
  lc₂ : Sub H (Z* (κ fz)) (Z* (κ fz) ∪ κ fz)
  lc₂ i r e₁ = e₁ , tt
  J₂ = subst (λ w₁ → Σ (Goodᴺ (toZ (runᶜ (wkC le₂ lc₂ C₁) w₁))) λ G → forceᴺ _ G ⊑ forceᴺ _ (proj₁ J₁)) (⊞𝟏 t X)
         (lim-rᵀ {x = X ⊞ 𝟏q t} {F = repᵠ X} 2 (wk-rᵀ (⊞-cong rX (wk-rᵀ (𝟏⊑Ω̇ H t)))) (≈ᶜ-wkˡ le₂ lc₂ (≈ᶜ-reflˡ o₁)) (proj₁ J₁))
  K = Sᵀ {a = Ω̇ H t} {a′ = qwk proj₁ (λ i r → proj₁) X} o (≈ᶜ-wkʳ le₂ lc₂ (≈ᶜ-sym o₁)) (rwkʳ (rwkʳ (RΩ̇ H (≅ᴵ-refl t)))) (rwk rX) (proj₁ J₂)

Sz-tr⁻ : ∀ {m a b ξ ζ} (e : a ≅ᴵ b) {z : Q m b ξ ζ} → Sz m b z → Sz m a (tr⁻Q e z)
Sz-tr⁻ {m} {a} {b} e {z} h {C} {C′} o c _ G′ = Goodᴺ-tr d (proj₁ K) , ≺-≅ˡ (forceᴺ-≅ (≅ᶻ-sym d) (Goodᴺ-tr d (proj₁ K)) (proj₁ K)) (proj₂ K)
  where
  K = h (ptr⁻ {e = e} {e′ = e} o) c tt G′
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) (R-tr⁻ˡ e (RΩ̇ m (≅ᴵ-sym e))))

Sz-tr : ∀ {m a b ξ ζ} (e : a ≅ᴵ b) {z : Q m a ξ ζ} → Sz m a z → Sz m b (trQ e z)
Sz-tr {m} {a} {b} e {z} h {C} {C′} o c _ G′ = Goodᴺ-tr d (proj₁ K) , ≺-≅ˡ (forceᴺ-≅ (≅ᶻ-sym d) (Goodᴺ-tr d (proj₁ K)) (proj₁ K)) (proj₂ K)
  where
  K = h (ptr {e = e} {e′ = e} o) c tt G′
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) (R-trˡ e (RΩ̇ m e)))

Sz-back : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : Q m (repQ (resQ q e)) ξ ζ} → Sz m _ z → Sz m j (backQ (resQ q e) z)
Sz-back zero      (s≅ e) f = Sz-tr⁻ e f
Sz-back (suc q)   (s≅ e) f = Sz-back q e f
Sz-back (lim n q) (l≅ f) g = Sz-back q (f n) g

Sz-back⁻ : ∀ {m j a b ξ ζ} (q : j <ᴵ a) (e : b ≅ᴵ a) {z : Q m (repQ (res⁻Q q e)) ξ ζ} → Sz m _ z → Sz m j (backQ (res⁻Q q e) z)
Sz-back⁻ zero      (s≅ e) f = Sz-tr e f
Sz-back⁻ (suc q)   (s≅ e) f = Sz-back⁻ q e f
Sz-back⁻ (lim n q) (l≅ f) g = Sz-back⁻ q (f n) g

Pos-tr : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {y : Q m a φ χ} → Pos p y → Pos p (trQ e y)
Pos-tr true e h = 𝟏-tr e h
Pos-tr false e h = One-tr e h

Pos-tr⁻ : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {y : Q m b φ χ} → Pos p y → Pos p (tr⁻Q e y)
Pos-tr⁻ true e h = 𝟏-tr⁻ e h
Pos-tr⁻ false e h = One-tr⁻ e h

nbP : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {C : Cx m b φ χ} → NdB p (ptr e C) → NdB p C
nbP true e n = tt
nbP false e n = n

nbQ : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {C : Cx m b φ χ} → NdB p C → NdB p (ptr e C)
nbQ true e n = tt
nbQ false e n = n

nbP⁻ : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {C : Cx m a φ χ} → NdB p (ptr⁻ e C) → NdB p C
nbP⁻ true e n = tt
nbP⁻ false e n = n

nbQ⁻ : ∀ {m a b φ χ} p (e : a ≅ᴵ b) {C : Cx m a φ χ} → NdB p C → NdB p (ptr⁻ e C)
nbQ⁻ true e n = tt
nbQ⁻ false e n = n
```

## §2 链的第一步严格高于 $\dot\Omega_k$

```agda
RfΩ : ∀ m c k (r : k <ᴵ c) φ χ → (∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)) → Set
RfΩ m c k r φ χ h = ∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k ξ′ ζ′) → Rq m k k z z′ → Rq m c c (h ξ ζ (intoU (<→◃ r) z)) (h ξ′ ζ′ (intoU (<→◃ r) z′))

RfV : ∀ m c n k (q : n <ᴸ m) φ χ → (∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)) → Set
RfV m c n k q φ χ h = ∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k ξ′ ζ′) → Rq n k k z z′ → Rq m c c (h ξ ζ (intoV q z)) (h ξ′ ζ′ (intoV q z′))

ΩCh : ∀ {m c φ χ k} b {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} ξ ζ (fe′ : ∀ {L} → Ev L ξ → Ev L Fl) (lc₀ : Sub m ζ (κ Fl))
      {le : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {lc : Sub m ζ (Z* (lo m ζ ∪ χ))} → RfΩ m c k r φ χ h →
      (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → FlΩ̇ m k z → Pos b (h ξ ζ (intoU (<→◃ r) z))) →
      Rq m k k (qwk le lc (ψᵠ r (h ξ ζ (intoU (<→◃ r) (qwk fe′ lc₀ (Ω̇ m k)))))) (qwk le lc (ψᵠ r (h ξ ζ (intoU (<→◃ r) (qwk fe′ lc₀ (Ω̇ m k)))))) ×
      Sz m k (qwk le lc (ψᵠ r (h ξ ζ (intoU (<→◃ r) (qwk fe′ lc₀ (Ω̇ m k))))))
ΩCh {m} {k = k} b {r = r} {h = h} ξ ζ fe′ lc₀ rf h1 =
  rwk (R-ψᵠ r r (≅ᴵ-refl k) (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ rz₀)) ,
  Ls-wk true (Sψ r (Pos→One b (h1 ξ ζ _ rz₀ (λ _ h₁ → wk-rᵀ h₁))))
  where rz₀ = rwk (RΩ̇ m (≅ᴵ-refl k))

VCh : ∀ {m c φ χ n k w} b {q : n <ᴸ m} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)} ξ ζ (fe′ : ∀ {L} → Ev L ξ → Ev L Fl) (lc₀ : Sub n ζ (κ Fl))
      (ok : Ok w) (E : Eh n m w (lo n ζ ∪ χ)) (P : k <ᴵ w n)
      {le : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {lc : Sub n ζ (Z* (lo n ζ ∪ χ))} → RfV m c n k q φ χ h →
      (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → FlΩ̇ n k z → Pos b (h ξ ζ (intoV q z))) →
      Rq n k k (qwk le lc (Ψ q ok E P (h ξ ζ (intoV q (qwk fe′ lc₀ (Ω̇ n k)))))) (qwk le lc (Ψ q ok E P (h ξ ζ (intoV q (qwk fe′ lc₀ (Ω̇ n k)))))) ×
      Sz n k (qwk le lc (Ψ q ok E P (h ξ ζ (intoV q (qwk fe′ lc₀ (Ω̇ n k))))))
VCh {n = n} {k = k} b {q = q} {h = h} ξ ζ fe′ lc₀ ok E P rf h1 =
  rwk (R-Ψ q ok E P ok E P (≅ᴵ-refl k) (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ rz₀)) ,
  Ls-wk true (SΨ q ok E P (Pos→One b (h1 ξ ζ _ rz₀ (λ _ h₁ → wk-rᵀ h₁))))
  where rz₀ = rwk (RΩ̇ n (≅ᴵ-refl k))

ClimbΩψ : ∀ {m c φ₀ χ₀ φ χ k t} b {x : Q m c φ₀ χ₀} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} (q : t <ᴵ c) →
          RfΩ m c k r φ χ h →
          (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → FlΩ̇ m k z → Pos b (h ξ ζ (intoU (<→◃ r) z))) →
          (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → Sz m k z → Ls b x (h ξ ζ (intoU (<→◃ r) z))) →
          ∀ {C : Cx m t (Fl ⊔ φ₀) (Z* χ₀)} {C′ : Cx m t (Fl ⊔ φ) (Z* χ)} → C ≈ᶜ C′ → Ctxᶜ C′ →
          (G′ : Goodᴺ (toZ (runᶜ C′ (ql (λ i → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i))))))))) →
          Σ (Goodᴺ (toZ (runᶜ C (ψᵠ q x)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
ClimbΩψ {m} {φ = φ} {χ = χ} {t = t} b {x = x} {r = r} {h = h} q rf h1 h2 o c G′ =
  Ls-lim true {x = ψᵠ q x} {F = λ i → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i))))} 1
    (rwk (R-ψᵠ q q (≅ᴵ-refl t) (rf (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) _ _ (proj₁ P))))
    (Ls-wk true (λ o′ c′ _ G → h2 (Fl ⊔ φ) (Z* χ) _ (proj₁ P) (proj₂ P) (pψ {q = q} o′) c′ (nb b tt) G))
    o c tt G′
  where P = ΩCh b {r = r} {h = h} (Fl ⊔ φ) (Z* χ) proj₁ fc* {le = dupr2} {lc = ⇑ (cv* _)} rf h1

Climb↓Ψ : ∀ {H m c φ₀ χ₀ φ χ n k t w w₀} b {x : Q m c φ₀ χ₀} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)}
          (qH : H <ᴸ m) (ok₀ : Ok w₀) (e₀ : Eh H m w₀ χ₀) (p₀ : t <ᴵ w₀ H) (ok : Ok w) (E : Eh H m w (lo n (Z* χ) ∪ χ)) (pt : t <ᴵ w H) (E′ : Eh n m w (lo n (Z* χ) ∪ χ)) (P₁ : k <ᴵ w n) →
          RfV m c n k q φ χ h →
          (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → FlΩ̇ n k z → Pos b (h ξ ζ (intoV q z))) →
          (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → Sz n k z → Ls b x (h ξ ζ (intoV q z))) →
          ∀ {C : Cx H t (Fl ⊔ φ₀) (Z* χ₀)} {C′ : Cx H t (Fl ⊔ φ) (Z* χ)} → C ≈ᶜ C′ → Ctxᶜ C′ →
          (G′ : Goodᴺ (toZ (runᶜ C′ (ql (λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok E pt (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok E′ P₁ (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))))))) →
          Σ (Goodᴺ (toZ (runᶜ C (Ψ qH ok₀ e₀ p₀ x)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Climb↓Ψ {H} {φ = φ} {χ = χ} {n = n} {t = t} b {x = x} {q = q} {h = h} qH ok₀ e₀ p₀ ok E pt E′ P₁ rf h1 h2 o c G′ =
  Ls-lim true {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok E pt (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok E′ P₁ (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 1
    (rwk (R-Ψ qH ok E pt ok E pt (≅ᴵ-refl t) (rf (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) _ _ (proj₁ P))))
    (Ls-wk true (λ o′ c′ _ G → h2 (Fl ⊔ φ) (Z* χ) _ (proj₁ P) (proj₂ P) (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = E} {p = p₀} {p′ = pt} o′) c′ (nb b tt) G))
    o c tt G′
  where P = VCh b {q = q} {h = h} (Fl ⊔ φ) (Z* χ) proj₁ fc* ok E′ P₁ {le = dupr2} {lc = ⇑ (cv* n)} rf h1
```

## §3 攀登

```agda
ClimbΩ : ∀ {m c φ₀ χ₀ φ χ k} b {x : Q m c φ₀ χ₀} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} →
         RfΩ m c k r φ χ h →
         (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → FlΩ̇ m k z → Pos b (h ξ ζ (intoU (<→◃ r) z))) →
         (∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → Sz m k z → Ls b x (h ξ ζ (intoU (<→◃ r) z))) →
         Ls b x (qΩ fe r h)
Climb↓ : ∀ {m c φ₀ χ₀ φ χ n k} b {x : Q m c φ₀ χ₀} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)} →
         RfV m c n k q φ χ h →
         (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → FlΩ̇ n k z → Pos b (h ξ ζ (intoV q z))) →
         (∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → Sz n k z → Ls b x (h ξ ζ (intoV q z))) →
         Ls b x (qΩ↓ q fe ac h)

ClimbΩ {m} {φ = φ} {χ = χ} {k = k} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) c nd G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  P = ΩCh b {r = r} {h = h} φ (Z* χ) fe fc* {le = λ v → fe v , (v , v)} {lc = ⇑ (cv* m)} rf h1
  z₁ = qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) (qwk fe fc* (Ω̇ m k)))))
  ey₁ = R→≈ᵠ (rf φ φ (Z* χ) (Z* χ) (∼ᶠ-refl φ) (Sim∼-refl (Z* χ)) z₁ z₁ (proj₁ P)) ok′ (e⁺ m ok′ e′) ok′ (e⁺ m ok′ e′) (ev′ , ev′) p′ (ev′ , ev′) p′ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ n → ψ̄ᵠ ok′ (e⁺ m ok′ e′) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) n))) (ev′ , ev′) p′} 1 (≅→⊑ᴱ ey₁) (≈ᵒ-reflʳ o) G′
  S = h2 φ (Z* χ) z₁ (proj₁ P) (proj₂ P) (top {ev = ev} {ev′ = ev′ , ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e⁺ m ok′ e′} o) c (nb b tt) (proj₁ L)
ClimbΩ b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pa {a = α} {b = β} {W = W} rW o) (w , c) nd G′ =
  ClimbΩ true {x = W ⊞ x} {fe = λ e → fe (proj₂ e)} {r = r} {h = λ ξ ζ z → qwk swp (λ i q → swp) (W ⊞ h ξ ζ z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → wk-rᵀ (B1ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) z z rz₁) (WFl.oneW w)))
    (λ ξ ζ z rz₁ sz → Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pa rW o′) (w , c′) (nb b tt) G))
    o c tt G′
ClimbΩ {m} {c = c₀} {k = k} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pψ {t = t} {q = q} o) c nd G′ with <ᴵ-dec r q
... | injᵃ (via e s) =
  ClimbΩ true {x = ψᵠ q x} {fe = proj₁} {r = s} {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e (outU (<→◃ s) z)))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m t t (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e w))))) (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ′ ζ′ (intoU (<→◃ r) (tr⁻Q e w′)))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
        (rwk (R-ψᵠ q q (≅ᴵ-refl t) (rf ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻ˡ e (R-tr⁻ʳ e l))))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos true (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e w)))))) (sym (out-intoU (<→◃ s) z))
        (wk-rᵀ (P0ᵀ {q = q} (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ (R-tr⁻ˡ e (R-tr⁻ʳ e rz₁))) (𝟏⊑Ω̇ m t))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls true (ψᵠ q x) (qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e w)))))) (sym (out-intoU (<→◃ s) z))
        (Ls-wk true (λ o′ c′ _ G → h2 ξ ζ (tr⁻Q e z) (R-tr⁻ˡ e (R-tr⁻ʳ e rz₁)) (Sz-tr⁻ e sz) (pψ {q = q} o′) c′ (nb b tt) G)))
    o c tt G′
... | injᵇ _ = ClimbΩψ {m} {k = k} b {x = x} {fe = fe} {r = r} {h = h} q rf h1 h2 o c G′
... | injᶜ _ = ClimbΩψ {m} {k = k} b {x = x} {fe = fe} {r = r} {h = h} q rf h1 h2 o c G′
ClimbΩ {m} {φ = φ} {χ = χ} {k = k} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pΨ {H = H} {t = t} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) c nd G′ =
  Ls-lim true {x = Ψ qH ok₀ e₀ p₀ x} {F = λ i → qwk dupr2 (⇑ (cv* m)) (Ψ qH ok (e⁺ m ok e) pt (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i))))} 1
    (rwk (R-Ψ qH ok (e⁺ m ok e) pt ok (e⁺ m ok e) pt (≅ᴵ-refl t) (rf (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) _ _ (proj₁ P))))
    (Ls-wk true (λ o′ c′ _ G → h2 (Fl ⊔ φ) (Z* χ) _ (proj₁ P) (proj₂ P) (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e⁺ m ok e} {p = p₀} {p′ = pt} o′) c′ (nb b tt) G))
    o c tt G′
  where P = ΩCh b {r = r} {h = h} (Fl ⊔ φ) (Z* χ) proj₁ fc* {le = dupr2} {lc = ⇑ (cv* m)} rf h1
ClimbΩ {m} {c = c₀} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pι {q = q} o) (n₁ , c) nd G′ =
  ClimbΩ false {x = ι q x} {fe = fe} {r = <◃ r q} {h = λ ξ ζ z → ι q (h ξ ζ (intoU (<→◃ r) (outU (<→◃ (<◃ r q)) z)))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m _ _ (ι q (h ξ ζ (intoU (<→◃ r) w))) (ι q (h ξ′ ζ′ (intoU (<→◃ r) w′)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ r q)) z′)) (R-ι q q (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → subst (λ w → One (ι q (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (One-ι q (Pos→One b (h1 ξ ζ z rz₁ f))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls false (ι q x) (ι q (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (λ o′ c′ n₂ G → h2 ξ ζ z rz₁ sz (pι {q = q} o′) (n₂ , c′) (nb b tt) G))
    o c n₁ G′
ClimbΩ {m} {c = c₀} {χ = χ} true {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pD {q = qd} o) c nd G′ =
  Climb↓ true {x = ι↓ {α = zero} qd x} {q = qd} {fe = fe} {ac = λ e → cvFlo c₀ (subst (Ev _) (cap-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) (outV qd z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq _ zero zero (ι↓ qd (h ξ ζ (intoU (<→◃ r) w))) (ι↓ qd (h ξ′ ζ′ (intoU (<→◃ r) w′)))) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    (λ ξ ζ z rz₁ f → wk-rᵀ (subst (λ w → Pos true (ι↓ {α = zero} qd (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoV qd z)) (𝟏-D {qd = qd} (h1 ξ ζ z rz₁ f))))
    (λ ξ ζ z rz₁ sz → Ls-wk true (subst (λ w → Ls true (ι↓ {α = zero} qd x) (ι↓ {α = zero} qd (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoV qd z)) (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G)))
    o c tt G′
ClimbΩ false rf h1 h2 (pD o) c () G′
ClimbΩ {m} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (ptr {e = e₀} {e′ = ε} o) c nd G′ =
  ClimbΩ b {x = trQ e₀ x} {fe = fe} {r = ltQ (resQ r ε)} {h = λ ξ ζ z → trQ ε (h ξ ζ (intoU (<→◃ r) (backQ (resQ r ε) (outU (<→◃ (ltQ (resQ r ε))) z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m _ _ (trQ ε (h ξ ζ (intoU (<→◃ r) (backQ (resQ r ε) w)))) (trQ ε (h ξ′ ζ′ (intoU (<→◃ r) (backQ (resQ r ε) w′))))) (sym (out-intoU (<→◃ (ltQ (resQ r ε))) z)) (sym (out-intoU (<→◃ (ltQ (resQ r ε))) z′))
        (R-tr₂ ε ε (rf ξ ξ′ ζ ζ′ d dc _ _ (R-back r ε l))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos b (trQ ε (h ξ ζ (intoU (<→◃ r) (backQ (resQ r ε) w))))) (sym (out-intoU (<→◃ (ltQ (resQ r ε))) z)) (Pos-tr b ε (h1 ξ ζ _ (R-back r ε rz₁) (Fl-back r ε f))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls b (trQ e₀ x) (trQ ε (h ξ ζ (intoU (<→◃ r) (backQ (resQ r ε) w))))) (sym (out-intoU (<→◃ (ltQ (resQ r ε))) z))
        (λ o′ c′ n₂ G → h2 ξ ζ _ (R-back r ε rz₁) (Sz-back r ε sz) (ptr {e = e₀} {e′ = ε} o′) c′ (nbQ b ε n₂) G))
    o c (nbP b ε nd) G′
ClimbΩ {m} b {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (ptr⁻ {e = e₀} {e′ = ε} o) c nd G′ =
  ClimbΩ b {x = tr⁻Q e₀ x} {fe = fe} {r = ltQ (res⁻Q r ε)} {h = λ ξ ζ z → tr⁻Q ε (h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r ε) (outU (<→◃ (ltQ (res⁻Q r ε))) z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m _ _ (tr⁻Q ε (h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r ε) w)))) (tr⁻Q ε (h ξ′ ζ′ (intoU (<→◃ r) (backQ (res⁻Q r ε) w′))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q r ε))) z)) (sym (out-intoU (<→◃ (ltQ (res⁻Q r ε))) z′))
        (R-tr⁻₂ ε ε (rf ξ ξ′ ζ ζ′ d dc _ _ (R-back⁻ r ε l))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos b (tr⁻Q ε (h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r ε) w))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q r ε))) z)) (Pos-tr⁻ b ε (h1 ξ ζ _ (R-back⁻ r ε rz₁) (Fl-back⁻ r ε f))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls b (tr⁻Q e₀ x) (tr⁻Q ε (h ξ ζ (intoU (<→◃ r) (backQ (res⁻Q r ε) w))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q r ε))) z))
        (λ o′ c′ n₂ G → h2 ξ ζ _ (R-back⁻ r ε rz₁) (Sz-back⁻ r ε sz) (ptr⁻ {e = e₀} {e′ = ε} o′) c′ (nbQ⁻ b ε n₂) G))
    o c (nbP⁻ b ε nd) G′

Climb↓ {φ = φ} {χ = χ} {n = n} {k = k} b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) c nd G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  E₁ = e⁺ n ok′ (e↓ e′)
  P₁ = ac (e↓ e′ n (inj₁ refl) q)
  P = VCh b {q = q} {h = h} φ (Z* χ) fe fc* ok′ E₁ P₁ {le = λ v → fe v , (v , v)} {lc = ⇑ (cv* n)} rf h1
  z₁ = qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok′ E₁ P₁ (h φ (Z* χ) (intoV q (qwk fe fc* (Ω̇ n k)))))
  ey₁ = R→≈ᵠ (rf φ φ (Z* χ) (Z* χ) (∼ᶠ-refl φ) (Sim∼-refl (Z* χ)) z₁ z₁ (proj₁ P)) ok′ (e⁺ n ok′ e′) ok′ (e⁺ n ok′ e′) (ev′ , ev′) p′ (ev′ , ev′) p′ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ i → ψ̄ᵠ ok′ (e⁺ n ok′ e′) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok′ E₁ P₁ (h φ (Z* χ) (intoV q z)))) i))) (ev′ , ev′) p′} 1 (≅→⊑ᴱ ey₁) (≈ᵒ-reflʳ o) G′
  S = h2 φ (Z* χ) z₁ (proj₁ P) (proj₂ P) (top {ev = ev} {ev′ = ev′ , ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e⁺ n ok′ e′} o) c (nb b tt) (proj₁ L)
Climb↓ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pa {a = α} {b = β} {W = W} rW o) (w , c) nd G′ =
  Climb↓ true {x = W ⊞ x} {q = q} {fe = λ e → fe (proj₂ e)} {ac = λ e → ac (proj₂ e)} {h = λ ξ ζ z → qwk swp (λ i q₁ → swp) (W ⊞ h ξ ζ z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → wk-rᵀ (B1ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) z z rz₁) (WFl.oneW w)))
    (λ ξ ζ z rz₁ sz → Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pa rW o′) (w , c′) (nb b tt) G))
    o c tt G′
Climb↓ {m} b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pψ {t = t} {q = q₁} o) c nd G′ =
  Climb↓ true {x = ψᵠ q₁ x} {q = q} {fe = proj₁} {ac = λ e → ac (proj₂ e)} {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q₁ (h ξ ζ z))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ψᵠ q₁ q₁ (≅ᴵ-refl t) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → wk-rᵀ (P0ᵀ {q = q₁} (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) z z rz₁) (𝟏⊑Ω̇ m t)))
    (λ ξ ζ z rz₁ sz → Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pψ {q = q₁} o′) c′ (nb b tt) G))
    o c tt G′
Climb↓ {m} {φ = φ} {χ = χ} {n = n} {k = k} b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pΨ {H = H₀} {t = t} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) c nd G′ with tri n H₀
... | tlt l =
  Climb↓ true {x = Ψ qH ok₀ e₀ p₀ x} {q = l} {fe = proj₁} {ac = λ u → ac (proj₂ u)} {h = λ ξ ζ z → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) pt (h ξ ζ (intoV q (outV l z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l₁ → subst₂ (λ w w′ → Rq H₀ t t (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) pt (h ξ ζ (intoV q w)))) (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ′ (inj₂ l) e) pt (h ξ′ ζ′ (intoV q w′))))) (sym (out-intoV l z)) (sym (out-intoV l z′))
        (rwk (R-Ψ qH ok (e-lo ζ (inj₂ l) e) pt ok (e-lo ζ′ (inj₂ l) e) pt (≅ᴵ-refl t) (rf ξ ξ′ ζ ζ′ d dc z z′ l₁))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos true (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) pt (h ξ ζ (intoV q w))))) (sym (out-intoV l z))
        (wk-rᵀ (H0ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) z z rz₁) (𝟏⊑Ω̇ H₀ t))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls true (Ψ qH ok₀ e₀ p₀ x) (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) pt (h ξ ζ (intoV q w))))) (sym (out-intoV l z))
        (Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e-lo ζ (inj₂ l) e} {p = p₀} {p′ = pt} o′) c′ (nb b tt) G)))
    o c tt G′
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) pt
...   | injᵃ (via d s) =
  ClimbΩ true {x = Ψ qH ok₀ e₀ p₀ x} {fe = proj₁} {r = s} {h = λ ξ ζ y → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) pt (h ξ ζ (intoV q (tr⁻Q d (outU (<→◃ s) y)))))}
    (λ ξ ξ′ ζ ζ′ d₁ dc z z′ l₁ → subst₂ (λ w w′ → Rq H₀ t t (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) pt (h ξ ζ (intoV q (tr⁻Q d w))))) (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ′ (inj₁ refl) e) pt (h ξ′ ζ′ (intoV q (tr⁻Q d w′)))))) (sym (out-intoU (<→◃ s) z)) (sym (out-intoU (<→◃ s) z′))
        (rwk (R-Ψ qH ok (e-lo ζ (inj₁ refl) e) pt ok (e-lo ζ′ (inj₁ refl) e) pt (≅ᴵ-refl t) (rf ξ ξ′ ζ ζ′ d₁ dc _ _ (R-tr⁻ˡ d (R-tr⁻ʳ d l₁))))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos true (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) pt (h ξ ζ (intoV q (tr⁻Q d w)))))) (sym (out-intoU (<→◃ s) z))
        (wk-rᵀ (H0ᵀ (rf ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) _ _ (R-tr⁻ˡ d (R-tr⁻ʳ d rz₁))) (𝟏⊑Ω̇ H₀ t))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls true (Ψ qH ok₀ e₀ p₀ x) (qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) pt (h ξ ζ (intoV q (tr⁻Q d w)))))) (sym (out-intoU (<→◃ s) z))
        (Ls-wk true (λ o′ c′ _ G → h2 ξ ζ (tr⁻Q d z) (R-tr⁻ˡ d (R-tr⁻ʳ d rz₁)) (Sz-tr⁻ d sz) (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e-lo ζ (inj₁ refl) e} {p = p₀} {p′ = pt} o′) c′ (nb b tt) G)))
    o c tt G′
...   | injᵇ _ = Climb↓Ψ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} qH ok₀ e₀ p₀ ok (e⁺ n ok e) pt (e⁺ n ok e) (ac (e n (inj₁ refl) q)) rf h1 h2 o c G′
...   | injᶜ _ = Climb↓Ψ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} qH ok₀ e₀ p₀ ok (e⁺ n ok e) pt (e⁺ n ok e) (ac (e n (inj₁ refl) q)) rf h1 h2 o c G′
Climb↓ {m} {φ = φ} {χ = χ} {n = n} {k = k} b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pΨ {H = H₀} {t = t} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) c nd G′ | tgt l =
  Climb↓Ψ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} qH ok₀ e₀ p₀ ok (e⁺ n ok e) pt (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) rf h1 h2 o c G′
Climb↓ {m} b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pι {q = q₁} o) (n₁ , c) nd G′ =
  Climb↓ false {x = ι q₁ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → ι q₁ (h ξ ζ z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-ι q₁ q₁ (rf ξ ξ′ ζ ζ′ d dc z z′ l))
    (λ ξ ζ z rz₁ f → One-ι q₁ (Pos→One b (h1 ξ ζ z rz₁ f)))
    (λ ξ ζ z rz₁ sz o′ c′ n₂ G → h2 ξ ζ z rz₁ sz (pι {q = q₁} o′) (n₂ , c′) (nb b tt) G)
    o c n₁ G′
Climb↓ {c = c₀} {χ = χ} {n = j} true {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (pD {q = qd} o) c nd G′ =
  Climb↓ true {x = ι↓ {α = zero} qd x} {q = tr< q qd} {fe = fe} {ac = λ e → ac (subst (Ev _) (cap-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoV q (outV (tr< q qd) z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq _ zero zero (ι↓ qd (h ξ ζ (intoV q w))) (ι↓ qd (h ξ′ ζ′ (intoV q w′)))) (sym (out-intoV (tr< q qd) z)) (sym (out-intoV (tr< q qd) z′)) (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    (λ ξ ζ z rz₁ f → wk-rᵀ (subst (λ w → Pos true (ι↓ {α = zero} qd (h ξ ζ (intoV q w)))) (sym (out-intoV (tr< q qd) z)) (𝟏-D {qd = qd} (h1 ξ ζ z rz₁ f))))
    (λ ξ ζ z rz₁ sz → Ls-wk true (subst (λ w → Ls true (ι↓ {α = zero} qd x) (ι↓ {α = zero} qd (h ξ ζ (intoV q w)))) (sym (out-intoV (tr< q qd) z)) (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G)))
    o c tt G′
Climb↓ false rf h1 h2 (pD o) c () G′
Climb↓ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (ptr {e = e₀} {e′ = ε} o) c nd G′ =
  Climb↓ b {x = trQ e₀ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → trQ ε (h ξ ζ z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-tr₂ ε ε (rf ξ ξ′ ζ ζ′ d dc z z′ l))
    (λ ξ ζ z rz₁ f → Pos-tr b ε (h1 ξ ζ z rz₁ f))
    (λ ξ ζ z rz₁ sz o′ c′ n₂ G → h2 ξ ζ z rz₁ sz (ptr {e = e₀} {e′ = ε} o′) c′ (nbQ b ε n₂) G)
    o c (nbP b ε nd) G′
Climb↓ b {x = x} {q = q} {fe = fe} {ac = ac} {h = h} rf h1 h2 (ptr⁻ {e = e₀} {e′ = ε} o) c nd G′ =
  Climb↓ b {x = tr⁻Q e₀ x} {q = q} {fe = fe} {ac = ac} {h = λ ξ ζ z → tr⁻Q ε (h ξ ζ z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-tr⁻₂ ε ε (rf ξ ξ′ ζ ζ′ d dc z z′ l))
    (λ ξ ζ z rz₁ f → Pos-tr⁻ b ε (h1 ξ ζ z rz₁ f))
    (λ ξ ζ z rz₁ sz o′ c′ n₂ G → h2 ξ ζ z rz₁ sz (ptr⁻ {e = e₀} {e′ = ε} o′) c′ (nbQ⁻ b ε n₂) G)
    o c (nbP⁻ b ε nd) G′
```

## §4 $\dot\Omega_a\prec\dot\Omega_{a+1}$ 经 $\downarrow$

```agda
Ω↓≺ : ∀ {n m} (qd : n <ᴸ m) a → Ls true (ι↓ {α = zero} qd (Ω̇ n a)) (ι↓ {α = zero} qd (Ω̇ n (suc a)))
Ω↓≺ {n} {m} qd a =
  Climb↓ true {x = ι↓ {α = zero} qd (Ω̇ n a)} {q = qd}
    {h = λ ξ ζ z → Hι qd a ξ ζ (outV qd z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (Hι qd a ξ ζ w) (Hι qd a ξ′ ζ′ w′)) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (rwk (rwk (rwk (R-ι↓ qd (≅ᴵ-refl a) l)))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos true (Hι qd a ξ ζ w)) (sym (out-intoV qd z)) (wk-rᵀ (wk-rᵀ (wk-rᵀ (𝟏-D {qd = qd} (f (R𝟏 a) (𝟏⊑Ω̇ n a)))))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls true (ι↓ {α = zero} qd (Ω̇ n a)) (Hι qd a ξ ζ w)) (sym (out-intoV qd z)) (Ls-wk true (Ls-wk true (Ls-wk true (λ o c _ G → sz (pD {q = qd} o) c tt G)))))

```
