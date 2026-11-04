# 序数高度: 严格比较的底座, 一层上移 `sh`

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfStrict](LadderInfStrict.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 对高度结构 `HtB` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFStrict](LadderNFStrict.lagda.md) 生成, 下面的说明是原文件的. `sh r C`: 把上下文下移一层, 与 `Ordˢ` 的 `sh` 同形. `omk r z x` 在 $C$ 下的值就是 $z$ 在 `sh r C` 下的值 (`sh-run`). `𝟏q k`: 层 $k$ 的 $1$, 带 `omk` 的塔, 所以 `ι↓` 读它时地板是紧的. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdStrict (𝕊 : HtB) where

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
open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

## §1 $1$ 与上下文条件

```agda

σ₀ : ∀ {ℓ} → Simᴵ zero ℓ
σ₀ ()

𝟏 : Ordˢ zero
𝟏 = Ord₊ˢ.suc Ord₊ˢ.zero

Ω1ᴱ : ∀ b → 𝟏 ⊑ᴱ Ωˢ b
Ω1ᴱ zero      = ≅→⊑ᴱ (s≅ z≅ z≅)
Ω1ᴱ (suc b)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ b) (≅ˢ-sym d)))
Ω1ᴱ (lim g s) = lim-rᴱ 0 (up-rᴱ {r = self 0} (Ω1ᴱ (g 0)))


NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤

record AFl {ℓ} (a : Ordˢ ℓ) : Set where
  constructor afl
  field
    ea  : a ≅ˢ a
    one : 𝟏 ⊑ᴱ a
    nzA : NZ ℓ


𝟏q : ∀ {m} k → Q m k fz (κ fz)
𝟏q zero = qs q0
𝟏q (suc k) = omk zero (𝟏q k) (qs q0)
𝟏q (lim f s) = omk (self 0) (𝟏q (f 0)) (qs q0)

record WFl {m c φ χ} (W : Q m c φ χ) : Set where
  constructor wfl
  field
    rW   : Rq m c c W W
    oneW : 𝟏q c ⊑ᵀ W

Nd : ∀ {m c φ χ} → Cx m c φ χ → Set
Nd (pD C)     = ⊥
Nd (ptr e C)  = Nd C
Nd (ptr⁻ e C) = Nd C
Nd (top O ev p ok e) = ⊤
Nd (pa W C)   = ⊤
Nd (pψ q C)   = ⊤
Nd (pΨ qH ok e p C) = ⊤
Nd (pι q C)   = ⊤

Nd-≈ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → Nd C′ → Nd C
Nd-≈ (top o) n = tt
Nd-≈ (pa r o) n = tt
Nd-≈ (pψ o) n = tt
Nd-≈ (pΨ o) n = tt
Nd-≈ (pι o) n = tt
Nd-≈ (pD o) ()
Nd-≈ (ptr o) n = Nd-≈ o n
Nd-≈ (ptr⁻ o) n = Nd-≈ o n

Nd-wk : ∀ {m c φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} (C : Cx m c ψ ρ) → Nd C → Nd (wkC le lc C)
Nd-wk (top O ev p ok e) n = tt
Nd-wk (pa W C) n = tt
Nd-wk (pψ q C) n = tt
Nd-wk (pΨ qH ok e p C) n = tt
Nd-wk (pι q C) n = tt
Nd-wk (pD C) ()
Nd-wk (ptr e C) n = Nd-wk C n
Nd-wk (ptr⁻ e C) n = Nd-wk C n

Ctx  : ∀ {k} → Obs k → Set
Ctxᶜ : ∀ {m c φ χ} → Cx m c φ χ → Set
Ctx idO          = ⊤
Ctx (tlo C)      = Ctxᶜ C
Ctx (addo O a σ) = AFl a × Ctx O
Ctx (tro O e)    = Ctx O
Ctx (tr⁻o O e)   = Ctx O
Ctxᶜ (top O ev p ok e) = Ctx O
Ctxᶜ (pa W C)     = WFl W × Ctxᶜ C
Ctxᶜ (pψ q C)     = Ctxᶜ C
Ctxᶜ (pΨ qH ok e p C) = Ctxᶜ C
Ctxᶜ (pι q C)     = Nd C × Ctxᶜ C
Ctxᶜ (pD C)       = Ctxᶜ C
Ctxᶜ (ptr e C)    = Ctxᶜ C
Ctxᶜ (ptr⁻ e C)   = Ctxᶜ C

ctx-refl  : ∀ {k} (O : Obs k) → Ctx O → O ≈ᵒ O
ctxᶜ-refl : ∀ {m c φ χ} (C : Cx m c φ χ) → Ctxᶜ C → C ≈ᶜ C
ctx-refl idO _ = idO
ctx-refl (tlo C) c = tlo (ctxᶜ-refl C c)
ctx-refl (addo O a σ) (afl e _ _ , c) = addo (ctx-refl O c) (≅ᴵ-refl _) e
ctx-refl (tro O e) c = tro (ctx-refl O c)
ctx-refl (tr⁻o O e) c = tr⁻o (ctx-refl O c)
ctxᶜ-refl (top O ev p ok e) c = top (ctx-refl O c)
ctxᶜ-refl (pa W C) (w , c) = pa (WFl.rW w) (ctxᶜ-refl C c)
ctxᶜ-refl (pψ q C) c = pψ (ctxᶜ-refl C c)
ctxᶜ-refl (pΨ qH ok e p C) c = pΨ (ctxᶜ-refl C c)
ctxᶜ-refl (pι q C) (_ , c) = pι (ctxᶜ-refl C c)
ctxᶜ-refl (pD C) c = pD (ctxᶜ-refl C c)
ctxᶜ-refl (ptr e C) c = ptr (ctxᶜ-refl C c)
ctxᶜ-refl (ptr⁻ e C) c = ptr⁻ (ctxᶜ-refl C c)

Ctx-wkC : ∀ {m c φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} (C : Cx m c ψ ρ) → Ctxᶜ C → Ctxᶜ (wkC le lc C)
Ctx-wkC (top O ev p ok e) c = c
Ctx-wkC (pa W C) (w , c) = w , Ctx-wkC C c
Ctx-wkC (pψ q C) c = Ctx-wkC C c
Ctx-wkC (pΨ qH ok e p C) c = Ctx-wkC C c
Ctx-wkC (pι q C) (n , c) = Nd-wk C n , Ctx-wkC C c
Ctx-wkC (pD C) c = Ctx-wkC C c
Ctx-wkC (ptr e C) c = Ctx-wkC C c
Ctx-wkC (ptr⁻ e C) c = Ctx-wkC C c

⊑ᴱ-≅ˡ : ∀ {k k′} {x x′ : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x′ → x′ ⊑ᴱ y → x ⊑ᴱ y
⊑ᴱ-≅ˡ e h o G′ = proj₁ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′))) ,
                 ⊑-trans (proj₂ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′)))) (proj₂ (h o G′))

suc-iter : ∀ {ℓ} {w : Ordˢ ℓ} → w ≅ˢ w → 𝟏 ⊑ᴱ w → Ord₊ˢ.suc w ⊑ᴱ Ord₊ˢ.lim (iter (w +ˢ_) Ord₊ˢ.zero)
suc-iter {w = w} ew one =
  lim-rᴱ {h = iter (w +ˢ_) Ord₊ˢ.zero} 2
    (add-congᴱ {a = w} {a′ = w} {σ = σ₀} {σ′ = λ q → q} {x = 𝟏} {y = w} (≅ᴵ-refl _) ew one)

```

## §2 下移一层

```agda
tighten : ∀ {k ℓ} → k ◃₁ ℓ → ∀ {L} → Ev L (flo ℓ) → Ev L (flo k)
tighten {k} zero e = toFlo k (λ q → e (suc q))
tighten {k} (self n) e = toFlo k (λ q → e (lim n q))

Dd : ∀ {m c φ χ} → Cx m c φ χ → Set
Dd (pD C)     = ⊤
Dd (ptr e C)  = Dd C
Dd (ptr⁻ e C) = Dd C
Dd (top O ev p ok e) = ⊥
Dd (pa W C)   = ⊥
Dd (pψ q C)   = ⊥
Dd (pΨ qH ok e p C) = ⊥
Dd (pι q C)   = ⊥

dh : ∀ {m c φ χ} (C : Cx m c φ χ) → Nd C ⊎ Dd C
dh (pD C)     = inj₂ tt
dh (ptr e C)  = dh C
dh (ptr⁻ e C) = dh C
dh (top O ev p ok e) = inj₁ tt
dh (pa W C)   = inj₁ tt
dh (pψ q C)   = inj₁ tt
dh (pΨ qH ok e p C) = inj₁ tt
dh (pι q C)   = inj₁ tt

Dd-≈ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → Dd C′ → Dd C
Dd-≈ (pD o) n = tt
Dd-≈ (ptr o) n = Dd-≈ o n
Dd-≈ (ptr⁻ o) n = Dd-≈ o n

Nd∧Dd : ∀ {m c φ χ} (C : Cx m c φ χ) → Nd C → Dd C → ⊥
Nd∧Dd (pD C) () d
Nd∧Dd (ptr e C) n d = Nd∧Dd C n d
Nd∧Dd (ptr⁻ e C) n d = Nd∧Dd C n d

shD : ∀ {m k ℓ φ χ} → k ◃₁ ℓ → (C : Cx m ℓ φ χ) → Dd C → Cx m k φ χ
shD {m = n} r (pD {q = q} C) d = pD {q = q} (wkC (λ e → e) (⇑ (cap-map n (tighten r))) C)
shD zero (ptr (s≅ e) C) d = ptr e (shD zero C d)
shD (self n) (ptr (l≅ h) C) d = ptr (h n) (shD (self n) C d)
shD zero (ptr⁻ (s≅ e) C) d = ptr⁻ e (shD zero C d)
shD (self n) (ptr⁻ (l≅ h) C) d = ptr⁻ (h n) (shD (self n) C d)

shE : ∀ {m k ℓ φ χ} → k ◃₁ ℓ → (C : Cx m ℓ φ χ) → Nd C ⊎ Dd C → Cx m k φ χ
shE r C (inj₁ n) = pι (◃₁→◃ r) C
shE r C (inj₂ d) = shD r C d

sh : ∀ {m k ℓ φ χ} → k ◃₁ ℓ → Cx m ℓ φ χ → Cx m k φ χ
sh r C = shE r C (dh C)

shD-≈ : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → (d : Dd C) (d′ : Dd C′) → shD r C d ≈ᶜ shD r C′ d′
shD-≈ r (pD o) d d′ = pD (wk≈ _ _ _ _ o)
shD-≈ zero (ptr {e = s≅ e} {e′ = s≅ e′} o) d d′ = ptr (shD-≈ zero o d d′)
shD-≈ (self n) (ptr {e = l≅ h} {e′ = l≅ h′} o) d d′ = ptr (shD-≈ (self n) o d d′)
shD-≈ zero (ptr⁻ {e = s≅ e} {e′ = s≅ e′} o) d d′ = ptr⁻ (shD-≈ zero o d d′)
shD-≈ (self n) (ptr⁻ {e = l≅ h} {e′ = l≅ h′} o) d d′ = ptr⁻ (shD-≈ (self n) o d d′)

shE-≈ : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → (u : Nd C ⊎ Dd C) (v : Nd C′ ⊎ Dd C′) → shE r C u ≈ᶜ shE r C′ v
shE-≈ r o (inj₁ n) (inj₁ n′) = pι o
shE-≈ r {C = C} o (inj₁ n) (inj₂ d′) = ⊥-elim (Nd∧Dd C n (Dd-≈ o d′))
shE-≈ r {C′ = C′} o (inj₂ d) (inj₁ n′) = ⊥-elim (Nd∧Dd C′ n′ (Dd-≈ (≈ᶜ-sym o) d))
shE-≈ r o (inj₂ d) (inj₂ d′) = shD-≈ r o d d′

sh-≈ : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → sh r C ≈ᶜ sh r C′
sh-≈ r {C} {C′} o = shE-≈ r o (dh C) (dh C′)

Ctx-shD : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (d : Dd C) → Ctxᶜ C → Ctxᶜ (shD r C d)
Ctx-shD r (pD C) d c = Ctx-wkC C c
Ctx-shD zero (ptr (s≅ e) C) d c = Ctx-shD zero C d c
Ctx-shD (self n) (ptr (l≅ h) C) d c = Ctx-shD (self n) C d c
Ctx-shD zero (ptr⁻ (s≅ e) C) d c = Ctx-shD zero C d c
Ctx-shD (self n) (ptr⁻ (l≅ h) C) d c = Ctx-shD (self n) C d c

Ctx-sh : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) → Ctxᶜ C → Ctxᶜ (sh r C)
Ctx-sh r C c with dh C
... | inj₁ n = n , c
... | inj₂ d = Ctx-shD r C d c

-- Nd 上下文读 omk 的第二格
nd-omk : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) → Nd C → (z : Q m k φ χ) (x : Q m ℓ φ χ) → runᶜ C (omk r (intoU (◃₁→◃ r) z) x) ≡ runᶜ C x
nd-omk r (top O ev p ok e) n z x = refl
nd-omk r (pa W C) n z x = refl
nd-omk r (pψ q C) n z x = refl
nd-omk r (pΨ qH ok e p C) n z x = refl
nd-omk r (pι q C) n z x = refl
nd-omk r (pD C) () z x
nd-omk zero (ptr (s≅ e) C) n z x = nd-omk zero C n (trQ e z) (trQ (s≅ e) x)
nd-omk (self i) (ptr (l≅ h) C) n z x = nd-omk (self i) C n (trQ (h i) z) (trQ (l≅ h) x)
nd-omk zero (ptr⁻ (s≅ e) C) n z x = nd-omk zero C n (tr⁻Q e z) (tr⁻Q (s≅ e) x)
nd-omk (self i) (ptr⁻ (l≅ h) C) n z x = nd-omk (self i) C n (tr⁻Q (h i) z) (tr⁻Q (l≅ h) x)

sh-runD : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → (d : Dd C) {z : Q m k φ χ} {z′ : Q m k ψ ρ} {x : Q m ℓ ψ ρ} → Rq m k k z z′ →
         runᶜ (shD r C d) z ≅ˢ runᶜ C′ (omk r (intoU (◃₁→◃ r) z′) x)
sh-runD {m = n} {k = k} zero {C′ = pD C′} (pD {q = qd} o) d {z = z} {z′ = z′} rr =
  subst (λ v → _ ≅ˢ v) (run-wkC (λ e → e) (⇑ (cap-map n (tighten zero))) C′ (ι↓ qd z′)) (runᶜ-≅ (wk≈ _ _ _ _ o) (R-ι↓ qd (≅ᴵ-refl k) rr))
sh-runD {m = n} {k = k} (self i) {C′ = pD C′} (pD {q = qd} o) d {z = z} {z′ = z′} rr =
  subst (λ v → _ ≅ˢ v) (run-wkC (λ e → e) (⇑ (cap-map n (tighten (self i)))) C′ (ι↓ qd z′)) (runᶜ-≅ (wk≈ _ _ _ _ o) (R-ι↓ qd (≅ᴵ-refl k) rr))
sh-runD zero (ptr {e = s≅ e} {e′ = s≅ e′} o) d rr = sh-runD zero o d (R-trˡ e (R-trʳ e′ rr))
sh-runD (self n) (ptr {e = l≅ h} {e′ = l≅ h′} o) d rr = sh-runD (self n) o d (R-trˡ (h n) (R-trʳ (h′ n) rr))
sh-runD zero (ptr⁻ {e = s≅ e} {e′ = s≅ e′} o) d rr = sh-runD zero o d (R-tr⁻ˡ e (R-tr⁻ʳ e′ rr))
sh-runD (self n) (ptr⁻ {e = l≅ h} {e′ = l≅ h′} o) d rr = sh-runD (self n) o d (R-tr⁻ˡ (h n) (R-tr⁻ʳ (h′ n) rr))

sh-run : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → {z : Q m k φ χ} {z′ : Q m k ψ ρ} {x : Q m ℓ ψ ρ} → Rq m k k z z′ →
         Rq m ℓ ℓ (ι (◃₁→◃ r) z) x → runᶜ (sh r C) z ≅ˢ runᶜ C′ (omk r (intoU (◃₁→◃ r) z′) x)
sh-run r {C} {C′} o {z} {z′} {x} rr H with dh C
... | inj₁ n = subst (λ v → runᶜ C (ι (◃₁→◃ r) z) ≅ˢ v) (sym (nd-omk r C′ (Nd-≈ (≈ᶜ-sym o) n) z′ x)) (runᶜ-≅ o H)
... | inj₂ d = sh-runD r o d rr

-- 字面的上移
Up : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) → Q m k φ χ → Q m ℓ φ χ
Up zero y = omk zero y (ι zero y)
Up (self n) y = omk (self n) y (ι (self n) y)

up-run : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {C : Cx m ℓ φ χ} {C′ : Cx m ℓ ψ ρ} → C ≈ᶜ C′ → {z : Q m k φ χ} {z′ : Q m k ψ ρ} → Rq m k k z z′ → runᶜ (sh r C) z ≅ˢ runᶜ C′ (Up r z′)
up-run zero o rr = sh-run zero o rr (R-ι zero zero rr)
up-run (self n) o rr = sh-run (self n) o rr (R-ι (self n) (self n) rr)

-- omk 的同余: 经 sh 比较
omk-go : ∀ {m k k′ ℓ φ₁ χ₁ φ₂ χ₂} (r : k ◃₁ ℓ) (r′ : k′ ◃₁ ℓ) {a : Q m k φ₁ χ₁} {z : Q m k′ φ₂ χ₂} {x : Q m ℓ φ₁ χ₁} {y : Q m ℓ φ₂ χ₂} →
         Rq m k k a a → Rq m ℓ ℓ (ι (◃₁→◃ r) a) x →
         Rq m k′ k′ z z → Rq m ℓ ℓ (ι (◃₁→◃ r′) z) y →
         (∀ {C : Cx m ℓ φ₁ χ₁} {C′ : Cx m ℓ φ₂ χ₂} → C ≈ᶜ C′ → (G′ : Goodᴺ (toZ (runᶜ (sh r′ C′) z))) → Σ (Goodᴺ (toZ (runᶜ (sh r C) a))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′) →
         omk r (intoU (◃₁→◃ r) a) x ⊑ᵀ omk r′ (intoU (◃₁→◃ r′) z) y
omk-go r r′ {a = a} {z = z} {x = x} {y = y} ra Hx rr Hy h {C} {C′} o G′ =
  Goodᴺ-tr (toZ-≅ dl) (proj₁ J) , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ dl)) (Goodᴺ-tr (toZ-≅ dl) (proj₁ J)) (proj₁ J))) (⊑-trans (proj₂ J) (≅→⊑ (forceᴺ-≅ (toZ-≅ dr) G₁ G′)))
  where
  dr = sh-run r′ (≈ᶜ-reflʳ o) rr Hy
  G₁ = Goodᴺ-tr (≅ᶻ-sym (toZ-≅ dr)) G′
  J = h o G₁
  dl = sh-run r (≈ᶜ-reflˡ o) ra Hx

Up-cong : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {a : Q m k φ χ} {z : Q m k ψ ρ} → Rq m k k a a → Rq m k k z z → a ⊑ᵀ z → Up r a ⊑ᵀ Up r z
Up-cong zero {a} {z} ra rr h = omk-go zero zero ra (R-ι zero zero ra) rr (R-ι zero zero rr) (λ o G′ → h (sh-≈ zero o) G′)
Up-cong (self n) {a} {z} ra rr h = omk-go (self n) (self n) ra (R-ι (self n) (self n) ra) rr (R-ι (self n) (self n) rr) (λ o G′ → h (sh-≈ (self n) o) G′)

ι-𝟏 : ∀ {m} k {d} (q : k ◃ d) → ι q (𝟏q {m} k) ≡ qs q0
ι-𝟏 zero q = refl
ι-𝟏 (suc k) q = refl
ι-𝟏 (lim f s) q = refl

R𝟏 : ∀ {m} k → Rq m k k (𝟏q k) (𝟏q k)
R𝟏 zero = rs fz∼ (λ i q → fz∼) rz
R𝟏 (suc k) = rob {r = zero} {r′ = zero} (≅ᴵ-refl k) (R𝟏 k) (rs fz∼ (λ i q → fz∼) rz)
R𝟏 (lim f s) = rob {r = self 0} {r′ = self 0} (≅ᴵ-refl _) (R𝟏 (f 0)) (rs fz∼ (λ i q → fz∼) rz)

𝟏-up : ∀ {m} k {d} (q′ : k ◃ d) → Rq m d d (ι q′ (𝟏q {m} k)) (qs {φ = fz} {χ = κ fz} q0)
𝟏-up {m} k {d} q′ = subst (λ v → Rq m d d v (qs q0)) (sym (ι-𝟏 k q′)) (rs fz∼ (λ i q → fz∼) rz)
```
