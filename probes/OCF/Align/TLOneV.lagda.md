# `tH` 实验 (二): 带高度的树上, $\alpha$ 严格增长

> 入口 [TLOne](TLOne.lagda.md). **判决: HOLDS (对结构 `HtB`, 编译过, 无条件).** 代码是 [ValueJudgeLadder](ValueJudgeLadder.lagda.md) §1, §2 对 `HtS` 证的 `Ω≺`, `V-≺`, `V-lim`, 这里机械改写到 `HtB` (`LadderInf*` 换成 `LadderOrd*`, 别的逐字相同; 机械替换, 脚本没有进仓库). 新增的只有文末的 `dom-α`: **第 $\alpha$ 行的值不低于 $\alpha$.** 这是原则版为什么一下就过了 `T⊤` 的原因: 折叠的 $\alpha$ 字面地进了树, 不必在闭包里. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TLOneV (𝕊 : HtB) where

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
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅; forceᴺ-HS; Goodᴺ-tr; gl; gz; gs; gc)
open import OCF.Free.Class using (lvG)
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
open import OCF.Align.LadderOrdCode using (_≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-trans; ≼-refl)
open import OCF.Align.LadderOrdStr using (≺→s≼; ≅→≼)
open import Data.Bool using (Bool; true; false)
```

## §1 单侧的 `ι`

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

  HV : ∀ m a → HS (V m a)
  HV m a = forceᴺ-HS _ (GV m a)

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

## §3 $\alpha\preceq V_m\alpha$

`Lv m a` 是第 $a$ 行的层号. 对 $a$ 归纳, 后继用 `V-≺`, 极限用 `V-lim`. 这条对一切 `HtB`, 不按阶段.

```agda
⊑ᴵ→≼ : ∀ {a b} → a ⊑ᴵ b → a ≼ b
⊑ᴵ→≼ z⊑ = z≼
⊑ᴵ→≼ (s⊑ e q) = ≺→s≼ (via e q)
⊑ᴵ→≼ (l⊑ h) = l≼ (λ n → ⊑ᴵ→≼ (h n))

Lv : Ht → Ordᴵ → Ordᴵ
Lv m a = toLevel (V m a) (HV m a)

Lv-≺ : ∀ m a → Lv m a ≺ᴵ Lv m (suc a)
Lv-≺ m a = toLevel-≺ (HV m a) (HV m (suc a)) (V-≺ m a)

V-lim⊑ : ∀ m f s n → V m (f n) ⊑⁰ V m (lim f s)
V-lim⊑ m f s n r = ≺-respʳ (≺l n r) (≅-sym (V-lim m f s))

dom-α : ∀ m a → a ≼ Lv m a
dom-α m zero = z≼
dom-α m (suc a) = ≼-trans (s≼ (dom-α m a)) (≺→s≼ (Lv-≺ m a))
dom-α m (lim f s) = l≼ (λ n → ≼-trans (dom-α m (f n)) (⊑ᴵ→≼ (toLevel-⊑ (HV m (f n)) (HV m (lim f s)) (V-lim⊑ m f s n))))

-- 与任意证书的层号的关系
Lv≅lvG : ∀ m a (ev : Ev (suc zero) Fl) (G : Goodᴺ (toZ (Tᵠ m a ev zero))) → lvG G ≅ᴵ Lv m a
Lv≅lvG m a ev G = toLevel-≅ (forceᴺ-HS _ G) (HV m a) (V-G′ m a ev G)
```
