# 值验收: 塔上的相对值, 对 `HtB`

> **机械改写.** 由 [ValueJudgeLadder](ValueJudgeLadder.lagda.md) 经 `Survey/scripts/vallab/mk_ladder.py` 生成: 只把 `HtS`, `LadderInf*` 换成 `HtB`, `LadderOrd*`. 入口 [ValLab](ValLab.lagda.md). 不含记号. 这里把折叠的行读成**值的方程**: `T m a` 是证书的计值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.ValLabLadder (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; <◃)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import OCF.Align.LadderOrdStrict2 𝕊
open import OCF.Align.LadderOrdStrict3 𝕊
open import OCF.Align.LadderOrdMono 𝕊 using (R-ιι; R-ιι′; ◃-tr; Ωs↓)
open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
open import OCF.Align.LadderOrdDn 𝕊 using (D→≈ᵠ)
open import OCF.Align.LadderOrdDnSelf 𝕊 using (D-self)
open import OCF.Align.ValueJudgeBase
open import Data.Bool using (Bool; true; false)
open import OCF.Free.Force using (gl; gz; gs; gc)
```

## §1 单侧的 `ι`

`R-ι` 两边都过 `ι`. 这里要的是: 一边是 $\iota_\downarrow$ 或 `tl` 的像, 另一边再过一次 `ι`. 这些像里没有 `omk` (`ι↓` 读掉第一格), 也没有顶层的 `qΩ`, 所以 `Rq` 够用.

```agda
R-tl-ι : ∀ {c d c′ k₁ k₂ χ ρ} (r : c′ ◃ d) {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
         a ≅ˢ b → Rq h₀ c d (tl {χ = χ} (flo k₁) cv a) (ι r (tl {c = c′} {χ = ρ} (flo k₂) cv′ b))
R-tl-ι r z≅ = rz
R-tl-ι r (s≅ le e) = rs (flo-∼ le) (λ i q → ⊥-elim (no< q)) (R-tl-ι r e)
R-tl-ι r (l≅ h) = rl (λ n → R-tl-ι r (h n))
R-tl-ι r (lᵢ≅ {p = q} e h) = ri e (λ x y dd → R-tl-ι r (h x y (≅→Rˢ (<→◃ q) dd)))
R-tl-ι {k₁ = suc k′} r (upˡ {r = zero} d) = rwkˡ (R-tl-ι r d)
R-tl-ι {k₁ = lim f s} r (upˡ {r = self n} d) = rwkˡ (R-tl-ι r d)
R-tl-ι {k₂ = suc k′} r (upʳ {r = zero} d) = rwkʳ (R-tl-ι r d)
R-tl-ι {k₂ = lim f s} r (upʳ {r = self n} d) = rwkʳ (R-tl-ι r d)
R-tl-ι {k₁ = zero} {k₂ = zero} r (ŝ≅ k ec et eg) =
  rĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (R-tl-ι r et) (λ η e η′ e′ eη → R-tl-ι r (eg η e η′ e′ eη))
R-tl-ι {k₁ = zero} {k₂ = suc _} r   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl-ι {k₁ = zero} {k₂ = lim _ _} r (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl-ι {k₁ = suc _} {k₂ = zero} r (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl-ι {k₁ = lim _ _} {k₂ = zero} r (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl-ι {k₁ = suc _} {k₂ = suc _} r (ŝ≅ k ec et eg) = rŝ ec (R-tl-ι r et) (λ η e η′ e′ eη → R-tl-ι r (eg η e η′ e′ eη))
R-tl-ι {k₁ = suc _} {k₂ = lim _ _} r (ŝ≅ k ec et eg) = rŝ ec (R-tl-ι r et) (λ η e η′ e′ eη → R-tl-ι r (eg η e η′ e′ eη))
R-tl-ι {k₁ = lim _ _} {k₂ = suc _} r (ŝ≅ k ec et eg) = rŝ ec (R-tl-ι r et) (λ η e η′ e′ eη → R-tl-ι r (eg η e η′ e′ eη))
R-tl-ι {k₁ = lim _ _} {k₂ = lim _ _} r (ŝ≅ k ec et eg) = rŝ ec (R-tl-ι r et) (λ η e η′ e′ eη → R-tl-ι r (eg η e η′ e′ eη))
R-tl-ι r (ĉ≅ ec dt dg eo eO) = rĉ ec dt dg (R-tl-ι r eo) (λ η e η′ e′ eη → R-tl-ι r (eO η e η′ e′ eη))

R-tlΩ-ι : ∀ {c d c′ η η′ φ φ′ χ ρ} (r : c′ ◃ d) {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ →
          Rq h₀ c d (tl {χ = χ} φ cv (Ωˢ η)) (ι r (tl {c = c′} {χ = ρ} φ′ cv′ (Ωˢ η′)))
R-tlΩ-ι r z≅ s = rs s (λ i q → ⊥-elim (no< q)) rz
R-tlΩ-ι r (s≅ e) s = ri e (λ x y d → rwk (R-tl-ι r d))
R-tlΩ-ι r (l≅ h) s = rl (λ n → rwk (R-tl-ι r (Ωˢ-≅ (h n))))

R-ι↓-ι : ∀ {n m k k′ α α′ β φ ψ χ ρ} (dq : n <ᴸ m) (r₀ : α′ ◃ β) → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Rq m α β (ι↓ dq x) (ι r₀ (ι↓ {α = α′} dq x′))
R-ι↓-ι dq r₀ ek rz = rz
R-ι↓-ι {n = n} dq r₀ ek (rs sa sb r) = rs sa (cap∼ n sb (flo-∼ ek)) (R-ι↓-ι dq r₀ ek r)
R-ι↓-ι dq r₀ ek (rl h) = rl (λ n → R-ι↓-ι dq r₀ ek (h n))
R-ι↓-ι dq r₀ ek (ri e h) = ri e (λ x y d → R-ι↓-ι dq r₀ ek (h x y d))
R-ι↓-ι dq r₀ ek (rŝ e r h) = rŝ e (R-ι↓-ι dq r₀ ek r) (λ η ee η′ e′ d → R-ι↓-ι dq r₀ ek (h η ee η′ e′ d))
R-ι↓-ι dq r₀ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓-ι dq r₀ ek r) (λ η ee η′ e′ d → R-ι↓-ι dq r₀ ek (h η ee η′ e′ d))
R-ι↓-ι dq r₀ ek (rclo s r h) = rclo s (R-ι↓-ι dq r₀ ek r) (λ η η′ d → R-ι↓-ι dq r₀ ek (h η η′ d))
R-ι↓-ι dq r₀ ek (rcl {q = q} same s r h) = rcl {q = tr< q dq} same s (R-ι↓-ι dq r₀ ek r) (λ η η′ d → rwk (R-ι↓-ι dq r₀ ek (h η η′ d)))
R-ι↓-ι dq r₀ ek (rwkˡ r) = rwkˡ (R-ι↓-ι dq r₀ ek r)
R-ι↓-ι dq r₀ ek (rwkʳ r) = rwkʳ (R-ι↓-ι dq r₀ ek r)
R-ι↓-ι {n = n} {m = m} {α = α} {α′ = α′} {β = β} dq r₀ ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c f) =
  rΩ↓ {q = tr< q dq} same ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk
    (subst₂ (λ u v → Rq m α β (ι↓ dq (h ξ ζ (intoV q u))) (ι r₀ (ι↓ {α = α′} dq (h′ ξ′ ζ′ (intoV q v))))) (sym (out-intoV (tr< q dq) z)) (sym (out-intoV (tr< q dq) z′))
      (R-ι↓-ι dq r₀ ek (f ξ ξ′ ζ ζ′ d dc dc′ _ _ (intoVq q (outVq (tr< q dq) l))))))
R-ι↓-ι {n = n} {m = m} {α = α} {α′ = α′} {β = β} dq r₀ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  rΩ↓ {q = dq} same ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk
    (subst₂ (λ u v → Rq m α β (ι↓ dq (h ξ ζ (intoU (<→◃ r) u))) (ι r₀ (ι↓ {α = α′} dq (h′ ξ′ ζ′ (intoU (<→◃ r′) v))))) (sym (out-intoV dq z)) (sym (out-intoV dq z′))
      (R-ι↓-ι dq r₀ ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (outVq dq l))))))
R-ι↓-ι dq r₀ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓-ι dq r₀ ea l)
R-ι↓-ι dq r₀ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓-ι dq r₀ ea l)
```

第 0 行与它的 `ι` 同值. 不看 `view` 的具体取值.

```agda
R-row-ι : ∀ m {d} (r : zero ◃ d) (v : View _<ᴸ_ h₀ m) → Rq m zero d (rowV m (ΩI m) v) (ι r (rowV m (ΩI m) v))
R-row-ι _ r base = rclo (∼ᶠ-refl fz)
  (R-tlΩ-ι r (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ-ι r eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
R-row-ι m {d} r (clos {n = n} q) = subst (λ X → Rq m zero d (rowC q X) (ι r (rowC q X))) (sym (ΩI≡ q))
  (rcl {q = q} same fz∼ (rwk (R-ι↓-ι q r (s≅ z≅) (RΩ̇ n (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓-ι q r eη (RΩ̇ n eη))))
R-row-ι m {d} r (chain F qs₁) = rl go
  where
  go : ∀ i → Rq m zero d (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i) (ι r (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i))
  go zero = rwk (rs fz∼ (λ i q → fz∼) rz)
  go (suc i) = subst (λ X → Rq m zero d (stepL (qs₁ i) X) (ι r (stepL (qs₁ i) X))) (sym (ΩI≡ (qs₁ i)))
    (rwk (R-ι↓-ι (qs₁ i) r z≅ (RΩ̇ (F i) z≅)))
```

**`ι-top`: 折叠不看 `ι`.** 对一切 $a$, `ψ̄ᵠ` 在 $\dot\Omega_m a$ 与它的 `ι` 上同值. 后继和极限都不要归纳: 这两种节点的输出本来就是 `ι` 的像, 用 `R-ιι`. 后继要对链归纳.

```agda
Hs : ∀ m a ξ ζ → Q m a ξ ζ → Q m (suc a) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)
Hs m a ξ ζ z = qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z))

Zκ : Fv
Zκ = Z* (κ Fl)

Hr : ∀ m a {c} (r : suc a ◃ c) ξ ζ → Q m a ξ ζ → Q m c (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)
Hr m a r ξ ζ z = ι r (Hs m a ξ ζ (outU (<→◃ (<◃ zero r)) (intoU (<→◃ (<◃ zero r)) z)))

chL : ∀ m a → ℕ → Q m a Fl Zκ
chL m a = chainᵠ (λ e → e) fc* (λ z → qwk (λ v → v , (v , v)) (⇑ (cv* m)) (ψᵠ zero (Hs m a Fl Zκ z)))

chR : ∀ m a {c} (r : suc a ◃ c) → ℕ → Q m a Fl Zκ
chR m a r = chainᵠ (λ e → e) fc* (λ z → qwk (λ v → v , (v , v)) (⇑ (cv* m)) (ψᵠ (<◃ zero r) (Hr m a r Fl Zκ z)))

chain-≅ : ∀ {m a c} (r : suc a ◃ c) i → Rq m a a (chL m a i) (chR m a r i)
chain-≅ {m} {a} r zero = rwk (RΩ̇ m (≅ᴵ-refl a))
chain-≅ {m} {a} r (suc i) =
  subst (λ u → Rq m a a (chL m a (suc i)) (qwk (λ v → v , (v , v)) (⇑ (cv* m)) (ψᵠ (<◃ zero r) (ι r (Hs m a Fl Zκ u)))))
        (sym (out-intoU (<→◃ (<◃ zero r)) (chR m a r i)))
        (rwk (rwk (R-ψᵠ zero (<◃ zero r) (≅ᴵ-refl a) (R-ιι zero zero r (chain-≅ r i)))))

ι-term : ∀ {m a c w w′} (r : suc a ◃ c) (ok : Ok w) (E : Eh h₀ m w (lo m Zκ ∪ κ Fl)) (ok′ : Ok w′) (E′ : Eh h₀ m w′ (lo m Zκ ∪ κ Fl)) i →
         ψ̄ᵠ ok E (Hs m a Fl Zκ (chL m a i)) ≈ᴿ ψ̄ᵠ ok′ E′ (Hr m a r Fl Zκ (chR m a r i))
ι-term {m} {a} r ok E ok′ E′ i =
  subst (λ u → ψ̄ᵠ ok E (Hs m a Fl Zκ (chL m a i)) ≈ᴿ ψ̄ᵠ ok′ E′ (ι r (Hs m a Fl Zκ u)))
        (sym (out-intoU (<→◃ (<◃ zero r)) (chR m a r i)))
        (wkR proj₁ proj₁ (R→≈ᵠ (R-ιι zero zero r (chain-≅ r i)) ok _ ok′ _))

ι-top : ∀ m a {c} (r : a ◃ c) {w w′} (ok : Ok w) (e : Eh h₀ m w (κ Fl)) (ok′ : Ok w′) (e′ : Eh h₀ m w′ (κ Fl)) → ψ̄ᵠ ok e (Ω̇ m a) ≈ᴿ ψ̄ᵠ ok′ e′ (ι r (Ω̇ m a))
ι-top m zero r ok e ok′ e′ = R→≈ᵠ (R-row-ι m r (view m)) ok e ok′ e′
ι-top m (lim f s) r ok e ok′ e′ = limR (λ n → R→≈ᵠ (R-ιι (self n) (self n) r (RΩ̇ m (≅ᴵ-refl (f n)))) ok e ok′ e′)
ι-top m (suc a) {c} r ok e ok′ e′ =
  limR {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ m ok e) (Hs m a Fl Zκ (chL m a i)))}
       {G = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok′ (e⁺ m ok′ e′) (Hr m a r Fl Zκ (chR m a r i)))}
       (λ i → wkR (λ v → v , v) (λ v → v , v) (ι-term r ok (e⁺ m ok e) ok′ (e⁺ m ok′ e′) i))
```

## §2 严格递增与极限行

`Ω≺`: 只在 `Nd` 上下文: $\iota(\dot\Omega_m a)\prec\dot\Omega_m(a+1)$. 用 `ClimbΩ`, 与 `Ω↓≺` 同一个论证.

```agda
One-wk : ∀ {m c φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {y : Q m c φ χ} → One y → One (qwk le lc y)
One-wk {le = le} {lc} {y} h {C₀} {C′} o n G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = pull≡ (run-wkC le lc C′ y) G′
  K = h (≈ᶜ-wkʳ le lc o) (Nd-wk C′ n) (proj₁ J)

private
  eq-omk : ∀ {m a φ χ} (C′ : Cx m (suc a) φ χ) → Nd C′ → (z : Q m a φ χ) → runᶜ C′ (ι zero z) ≡ runᶜ C′ (omk zero z (ι zero z))
  eq-omk C′ n z = sym (nd-omk zero C′ n z (ι zero z))

One-omk : ∀ {m a φ χ} {z : Q m a φ χ} → One (ι zero z) → One (omk zero z (ι zero z))
One-omk {z = z} h {C₀} {C′} o n G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = pull≡ (eq-omk C′ n z) G′
  K = h o n (proj₁ J)

Ls-omk : ∀ {m a φ₀ χ₀ φ χ} {x : Q m (suc a) φ₀ χ₀} {z : Q m a φ χ} → (∀ {C C′} → C ≈ᶜ C′ → Ctxᶜ C′ → Nd C′ → (G′ : Goodᴺ (toZ (runᶜ C′ (ι zero z)))) → Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′) →
         Ls false x (omk zero z (ι zero z))
Ls-omk {z = z} h {C} {C′} o c n G′ = proj₁ K , proj₂ J (proj₂ K)
  where
  J = pull≡ (eq-omk C′ n z) G′
  K = h o c n (proj₁ J)

Ω≺ : ∀ m a → Ls false (ι zero (Ω̇ m a)) (Ω̇ m (suc a))
Ω≺ m a = ClimbΩ false {x = ι zero (Ω̇ m a)} {fe = λ e → e} {r = zero} {h = Hs m a}
  (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} (≅ᴵ-refl a) l (R-ι zero zero l)))
  (λ ξ ζ z rz f → One-wk (One-omk (One-ι zero (⊑→One (f (R𝟏 a) (𝟏⊑Ω̇ m a))))))
  (λ ξ ζ z rz sz → Ls-wk false (Ls-omk (λ o c n G′ → sz (pι {q = zero} o) (n , c) tt G′)))
```

**闭项.** `V m a` 是 `Tᵠ m a` 的计值. 证书的选择无关 (`forceᴺ-≅`), 所以下面都对 `GᴺTᵠ` 写.

```agda
ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

e₀ : ∀ {m} → Eh h₀ m w₀ (κ Fl)
e₀ i h r = ok₀ i

GV : ∀ m a → Goodᴺ (toZ (Tᵠ m a ev₀ zero))
GV m a = GᴺTᵠ m a ev₀ zero

-- 不透明: 检查器不去展开证书 (展开 `forceᴺ` 要算证书的范式, 内存爆掉).
opaque
  V : Ht → Ordᴵ → Ordᶜ zero
  V m a = forceᴺ _ (GV m a)

  -- 任意证书的计值就是 V
  V-G : ∀ m a (G : Goodᴺ (toZ (Tᵠ m a ev₀ zero))) → forceᴺ _ G ≅ V m a
  V-G m a G = forceᴺ-≅ (toZ-≅ (R→≈ᵠ (RΩ̇ m (≅ᴵ-refl a)) ok₀ e₀ ok₀ e₀ ev₀ zero ev₀ zero z≅)) G (GV m a)

-- 同上, 证据也任意: 接到别的文件里的闭项
V-G′ : ∀ m a (ev : Ev (suc zero) Fl) (G : Goodᴺ (toZ (Tᵠ m a ev zero))) → forceᴺ _ G ≅ V m a
V-G′ m a ev G = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (RΩ̇ m (≅ᴵ-refl a)) ok₀ e₀ ok₀ e₀ ev zero ev₀ zero z≅)) G (GV m a)) (V-G m a (GV m a))

V-≅ : ∀ m {a b} → a ≅ᴵ b → V m a ≅ V m b
V-≅ m {a} {b} e = ≅-trans (≅-sym (V-G m a (GV m a))) (≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (RΩ̇ m e) ok₀ e₀ ok₀ e₀ ev₀ zero ev₀ zero z≅)) (GV m a) (GV m b)) (V-G m b (GV m b)))

V-≺ : ∀ m a → V m a ≺ V m (suc a)
V-≺ m a = ≺-respʳ (≺-≅ˡ (≅-trans (≅-sym (V-G m a (GV m a))) (forceᴺ-≅ d (GV m a) (proj₁ K))) (proj₂ K)) (V-G m (suc a) (GV m (suc a)))
  where
  K = Ω≺ m a {C = top idO ev₀ zero ok₀ e₀} {C′ = top idO ev₀ zero ok₀ e₀} (top idO) tt tt (GV m (suc a))
  d = toZ-≅ (ι-top m a zero ok₀ e₀ ok₀ e₀ ev₀ zero ev₀ zero z≅)

V-lim : ∀ m f s → V m (lim f s) ≅ lim (λ n → V m (f n))
V-lim m f s = ≅-trans (≅-sym (V-G m (lim f s) (GV m (lim f s)))) (go (GV m (lim f s)))
  where
  go : (G : Goodᴺ (Z.lim (λ n → toZ (ψ̄ᵠ ok₀ e₀ (ι (self n) (Ω̇ m (f n))) ev₀ zero)))) → forceᴺ _ G ≅ lim (λ n → V m (f n))
  go (gl Gs st) = l≅ (λ n → ≅-trans (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ (ι-top m (f n) (self n) ok₀ e₀ ok₀ e₀ ev₀ zero ev₀ zero z≅))) (Gs n) (GV m (f n))) (V-G m (f n) (GV m (f n))))
```

**单调.** 对层号的 $\sqsubseteq^\mathsf{I}$: 不要字面公共上界 (`no-join` 不挡): 只走 `V-≺` 与 `V-lim`.

```agda
V-z≼ : ∀ m b → V m zero ≼ V m b
V-z≼ m zero = ≼-refl _
V-z≼ m (suc b) = ≼-trans (V-z≼ m b) (≺→≼ (≺→s≼ (V-≺ m b)))
V-z≼ m (lim f s) = ≼-trans (≼l 0 (V-z≼ m (f 0))) (≅→≼ (≅-sym (V-lim m f s)))

V-<≼ : ∀ m {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → V m (suc a) ≼ V m b
V-<≼ m e zero = ≅→≼ (V-≅ m (s≅ e))
V-<≼ m e (suc q) = ≼-trans (V-<≼ m e q) (≺→≼ (≺→s≼ (V-≺ m _)))
V-<≼ m e (lim {f} {s} n q) = ≼-trans (≼l n (V-<≼ m e q)) (≅→≼ (≅-sym (V-lim m f s)))

V-≼ : ∀ m {a b} → a ⊑ᴵ b → V m a ≼ V m b
V-≼ m {b = b} z⊑ = V-z≼ m b
V-≼ m (s⊑ e q) = V-<≼ m e q
V-≼ m {a = lim g s} (l⊑ k) = ≼-trans (≅→≼ (V-lim m g s)) (l≼ (λ n → V-≼ m (k n)))

-- 严格: 层号严格小, 值严格小
V-≺≺ : ∀ m {a b} → a ≺ᴵ b → V m a ≺ᵛ V m b
V-≺≺ m (via e q) = ≼-trans (s≼s (≅→≼ (V-≅ m e))) (≼-trans (≺→s≼ (V-≺ m _)) (V-<≼ m (≅ᴵ-refl _) q))
```

## §3 高度的行

`Good-≡`: 证书沿 $\dot\Omega$ 的展开搬运. `D-val`: $\iota_\downarrow(\dot\Omega_n 0)$ 与 $\dot\Omega_n 0$ 同值 (`D-self`).

```agda
Good-≡ : ∀ {m c w} {ok : Ok w} {e : Eh h₀ m w (κ Fl)} {x y : Q m c Fl (κ Fl)} → x ≡ y → Goodᴺ (toZ (ψ̄ᵠ ok e x ev₀ zero)) → Goodᴺ (toZ (ψ̄ᵠ ok e y ev₀ zero))
Good-≡ refl G = G

Good-≡-≅ : ∀ {m c w} {ok : Ok w} {e : Eh h₀ m w (κ Fl)} {x y : Q m c Fl (κ Fl)} (eq : x ≡ y) (rx : Rq m c c x x) (G : Goodᴺ (toZ (ψ̄ᵠ ok e x ev₀ zero))) → forceᴺ _ G ≅ forceᴺ _ (Good-≡ eq G)
Good-≡-≅ {ok = ok} {e} refl rx G = forceᴺ-≅ (toZ-≅ (R→≈ᵠ rx ok e ok e ev₀ zero ev₀ zero z≅)) G G

D-val : ∀ {n m} (q : n <ᴸ m) {w} (ok : Ok w) (e : Eh h₀ m w (cap (κ Fl) n fz)) → ψ̄ᵠ ok₀ e₀ (Ω̇ n zero) ≈ᴿ ψ̄ᵠ ok e (ι↓ {α = zero} q (Ω̇ n zero))
D-val q ok e = D→≈ᵠ (D-self q) ok₀ e₀ ok e
```

**链行.** `view m = chain F qs`: $V_m0$ 是 $V_{F i}0$ 的上确界 (外加第 0 项, 它不超过 $V_{F 0}0$). 这是 `anchor` ([LadderInfAgree](LadderInfAgree.lagda.md)) 对一切结构的版本.

```agda
V-chain : ∀ m F (qq : ∀ i → F i <ᴸ m) → view m ≡ chain F qq → V m zero ≈ᵛ lim (λ i → V (F i) zero)
V-chain m F qq ev = sub , sup
  where
  eq : Ω̇ m zero ≡ ql (rowL F qq (λ i → ΩI m (qq i)))
  eq = cong (rowV m (ΩI m)) ev

  R0 : Rq m zero zero (Ω̇ m zero) (Ω̇ m zero)
  R0 = RΩ̇ m z≅

  G₀ : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (ql (rowL F qq (λ i → ΩI m (qq i)))) ev₀ zero))
  G₀ = Good-≡ eq (GV m zero)

  e₁ : ∀ i → V m zero ≅ forceᴺ _ G₀
  e₁ i = ≅-trans (≅-sym (V-G m zero (GV m zero))) (Good-≡-≅ eq R0 (GV m zero))

  -- 第 i+1 项
  term : ∀ i (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (rowL F qq (λ j → ΩI m (qq j)) (suc i)) ev₀ zero))) → forceᴺ _ G ≅ V (F i) zero
  term i G = ≅-trans (forceᴺ-≅ (≅ᶻ-sym (d (ΩI m (qq i)) (ΩI≡ (qq i)))) G (GV (F i) zero)) (V-G (F i) zero (GV (F i) zero))
    where
    d : ∀ (X : XΩ (F i)) → X ≡ Ω̇ (F i) → toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ (F i) zero) ev₀ zero) ≅ᶻ toZ (ψ̄ᵠ ok₀ e₀ (stepL (qq i) X) ev₀ zero)
    d _ refl = toZ-≅ (D-val (qq i) ok₀ (λ j h r → κ-cap (F i) (λ _ → tt) j (ok₀ j)) ev₀ zero ev₀ zero z≅)

  go : (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (ql (rowL F qq (λ i → ΩI m (qq i)))) ev₀ zero))) → (forceᴺ _ G ≼ lim (λ i → V (F i) zero)) × (lim (λ i → V (F i) zero) ≼ forceᴺ _ G)
  go (gl Gs st) =
    l≼ (λ { zero → ≼l 0 (≼-trans (⊑→≼ _ (st 0)) (≅→≼ (term 0 (Gs 1)))) ; (suc i) → ≼l i (≅→≼ (term i (Gs (suc i)))) }) ,
    l≼ (λ i → ≼l (suc i) (≅→≼ (≅-sym (term i (Gs (suc i))))))

  sub : V m zero ≼ lim (λ i → V (F i) zero)
  sub = ≼-trans (≅→≼ (e₁ 0)) (proj₁ (go G₀))

  sup : lim (λ i → V (F i) zero) ≼ V m zero
  sup = ≼-trans (proj₂ (go G₀)) (≅→≼ (≅-sym (e₁ 0)))
```

**闭包行.** `view m = clos r`: $V_m0$ 是链 `ys` 的上确界, `ys 0` 是 $\iota_\downarrow(\dot\Omega_n1)$ 的值, `ys (k+1)` 是 $\iota_\downarrow(\dot\Omega_n\,\mathrm{lv}(y_k))$ 的值. 这是 `gc` 的字面读法, 没有用到别的.

`FV r η`: 一个 `Eh` 下 $\iota_\downarrow(\dot\Omega_n\eta)$ 的计值 (任何证书). `Fv-≅`: 与 `Eh` 无关. 所以 `F` 在链点上是良定义的函数.

```agda
Ωd : ∀ {n m} (r : n <ᴸ m) η → Q m zero Fl (cap (κ Fl) n (flo η))
Ωd r η = ι↓ {α = zero} r (Ω̇ n η)
  where n = _

Rd : ∀ {n m} (r : n <ᴸ m) {η η′} → η ≅ᴵ η′ → Rq m zero zero (Ωd r η) (Ωd r η′)
Rd {n} r e = R-ι↓ r e (RΩ̇ n e)

-- 严格: 经 ι↓
Fd-≺ : ∀ {n m w} (r : n <ᴸ m) a (ok : Ok w) (e : Eh h₀ m w (cap (κ Fl) n (flo a))) (e′ : Eh h₀ m w (cap (κ Fl) n (flo (suc a))))
       (G′ : Goodᴺ (toZ (ψ̄ᵠ ok e′ (Ωd r (suc a)) ev₀ zero))) →
       Σ (Goodᴺ (toZ (ψ̄ᵠ ok e (Ωd r a) ev₀ zero))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Fd-≺ r a ok e e′ G′ = Ω↓≺ r a {C = top idO ev₀ zero ok e} {C′ = top idO ev₀ zero ok e′} (top idO) tt tt G′

-- 第 2 层的具体环境
ok₂ : Ok (λ _ → suc (suc (suc zero)))
ok₂ i = tt , (λ { zero → suc (suc zero) })

capE₂ : ∀ {n m} → Eh h₀ m (λ _ → suc (suc (suc zero))) (cap (κ Fl) n (flo (suc (suc zero))))
capE₂ {n} j h r with tri j n
... | tlt _ = ok₂ j
... | teq _ = toFlo (suc (suc zero)) suc
... | tgt _ = tt

record GoodAt {n m} (r : n <ᴸ m) (η : Ordᴵ) : Set where
  constructor goodAt
  field
    {wA} : Ht → Ordᴵ
    okA  : Ok wA
    eA   : Eh h₀ m wA (cap (κ Fl) n (flo η))
    gA   : Goodᴺ (toZ (ψ̄ᵠ okA eA (Ωd r η) ev₀ zero))
open GoodAt public

-- 记号: x 是 ι↓(Ω̇ n η) 的值, 对任何 Eh, 任何证书
IsF : ∀ {n m} (r : n <ᴸ m) → Ordᴵ → Ordᶜ zero → Set
IsF {n} {m} r η x = ∀ {w} (ok : Ok w) (e : Eh h₀ m w (cap (κ Fl) n (flo η))) (G : Goodᴺ (toZ (ψ̄ᵠ ok e (Ωd r η) ev₀ zero))) → forceᴺ _ G ≅ x

record ClosRow {n m} (r : n <ᴸ m) : Set where
  constructor closRow
  field
    ys    : ℕ → Ordᶜ zero
    hy    : ∀ k → HS (ys k)
    first : IsF r (suc zero) (ys 0)
    next  : ∀ k → IsF r (toLevel (ys k) (hy k)) (ys (suc k))
    value : V m zero ≅ lim ys
    Gf    : Goodᴺ (toZ (ψ̄ᵠ ok₀ (λ j h r′ → κ-cap n proj₂ j (ok₀ j)) (Ωd r (suc zero)) ev₀ zero))
    Gn    : ∀ k → GoodAt r (toLevel (ys k) (hy k))
open ClosRow public

rowC-eq : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → Ω̇ m zero ≡ rowC r (Ω̇ n)
rowC-eq {n} {m} r ev = trans (cong (rowV m (ΩI m)) ev) (cong (rowC r) (ΩI≡ r))

clos-row : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → ClosRow r
clos-row {n} {m} r ev = go (Good-≡ (rowC-eq r ev) (GV m zero)) (≅-trans (≅-sym (V-G m zero (GV m zero))) (Good-≡-≅ (rowC-eq r ev) (RΩ̇ m z≅) (GV m zero)))
  where
  go : (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (rowC r (Ω̇ n)) ev₀ zero))) → V m zero ≅ forceᴺ _ G → ClosRow r
  go (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) eG = closRow ys hy
    (λ ok e G → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (Rd r (s≅ z≅)) ok e ok₀ _ ev₀ zero ev₀ zero z≅)) G G₀) l₀)
    (λ k ok e G → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (Rd r (≅ᴵ-refl _)) ok e _ _ ev₀ zero ev₀ zero z≅)) G (Gg k)) (lE k))
    (≅-trans eG (l≅ (λ { zero → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (Rd r (s≅ z≅)) ok₀ _ ok₀ _ ev₀ zero ev₀ zero z≅)) Go₀ G₀) l₀
                       ; (suc k) → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (Rd r (≅ᴵ-refl _)) _ _ _ _ ev₀ zero ev₀ zero z≅)) (Go k) (Gg k)) (lE k) })))
    G₀
    (λ k → goodAt _ _ (Gg k))

ca₀ : ∀ {n m} → Eh h₀ m w₀ (cap (κ Fl) n fz)
ca₀ {n} j h r = κ-cap n (λ _ → tt) j (ok₀ j)

ca₁ : ∀ {n m} → Eh h₀ m w₀ (cap (κ Fl) n (flo (suc zero)))
ca₁ {n} j h r = κ-cap n proj₂ j (ok₀ j)

V-clos-≺ : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → V n zero ≺ᵛ V m zero
V-clos-≺ {n} {m} r ev = go (Good-≡ (rowC-eq r ev) (GV m zero)) (≅-trans (≅-sym (V-G m zero (GV m zero))) (Good-≡-≅ (rowC-eq r ev) (RΩ̇ m z≅) (GV m zero)))
  where
  go : (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (rowC r (Ω̇ n)) ev₀ zero))) → V m zero ≅ forceᴺ _ G → V n zero ≺ᵛ V m zero
  go (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) eG =
    ≼-trans (≺→s≼ (≺-≅ˡ (≅-trans (≅-sym (V-G n zero (GV n zero))) (forceᴺ-≅ (toZ-≅ (D-val r ok₀ ca₀ ev₀ zero ev₀ zero z≅)) (GV n zero) (proj₁ K))) (proj₂ K)))
            (≼-trans (≼l 0 (≼-refl _)) (≅→≼ (≅-sym eG)))
    where K = Fd-≺ r zero ok₀ ca₀ ca₁ Go₀
```

`clos-first≺`: 闭包行的第 0 个链点严格低于整棵树. 第 0 个链点 $\ge2$ (`S1ᵀ`), 所以下一个链点读到的层号 $\succ1$.

```agda
1≺F : ∀ {n m} (r : n <ᴸ m) (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ ca₁ (Ωd r (suc zero)) ev₀ zero))) → suc (zero {zero}) ≺ forceᴺ _ G
1≺F {n} r G = go (S1ᵀ {t = Ωd r (suc zero)} {ok = ok₀} {e = ca₁} {ev = ev₀} {p = zero} (⊑→One (𝟏-D {qd = r} (𝟏⊑Ω̇ n (suc zero)))) idO G)
  where
  go : (Σ (Goodᴺ (toZ (Ord₊ˢ.suc (Ord₊ˢ.suc Ord₊ˢ.zero)))) λ H → forceᴺ _ H ⊑ forceᴺ _ G) → suc (zero {zero}) ≺ forceᴺ _ G
  go (gs (gs gz) , le) = le (≺z (s≅ z≅))

Ωs↓′ : ∀ {n m a b} {qd : n <ᴸ m} → a ≺ᴵ b → ι↓ {α = zero} qd (Ω̇ n (suc a)) ⊑ᵀ ι↓ {α = zero} qd (Ω̇ n b)
Ωs↓′ {qd = qd} (via e q) = Ωs↓ {qd = qd} e q

clos-first≺ : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → ∀ {x} → IsF r (suc zero) x → x ≺ᵛ V m zero
clos-first≺ {n} {m} r ev {x} ix =
  ≼-trans (≺→s≼ (≺-≅ˡ (≅-sym (ix ok₀ ca₁ (proj₁ K₂))) (proj₂ K₁ (proj₂ K₂))))
          (≼-trans (≅→≼ (next CR 0 (okA (Gn CR 0)) (eA (Gn CR 0)) (gA (Gn CR 0)))) (≼-trans (≼l 1 (≼-refl _)) (≅→≼ (≅-sym (value CR)))))
  where
  CR = clos-row r ev
  η = toLevel (ys CR 0) (hy CR 0)
  1≺y : suc (zero {zero}) ≺ ys CR 0
  1≺y = ≺-respʳ (1≺F r (Gf CR)) (first CR ok₀ ca₁ (Gf CR))
  via₁ : suc zero ≺ᴵ η
  via₁ = toLevel-≺ (hs hz) (hy CR 0) 1≺y
  K₁ = Ωs↓′ {qd = r} via₁ {C = top idO ev₀ zero ok₂ capE₂} {C′ = top idO ev₀ zero (okA (Gn CR 0)) (eA (Gn CR 0))} (top idO) (gA (Gn CR 0))
  K₂ = Ω↓≺ r (suc zero) {C = top idO ev₀ zero ok₀ ca₁} {C′ = top idO ev₀ zero ok₂ capE₂} (top idO) tt tt (proj₁ K₁)
```
