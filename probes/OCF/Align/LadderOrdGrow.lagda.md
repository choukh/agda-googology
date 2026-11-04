# 序数高度: 高度严格增长

> **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 这是 "定理不空" 的证据: 对 `HtB` 的任何 $n<m$, $\dot\Omega_n\,0$ 的计值严格低于 $\dot\Omega_m\,0$ 的计值 (`grow`, 字面的 $\prec$). 所以新的高度确实比下面的都高, 不是退化成同一棵树. 只用闭包定理已有的 `Ω↓≺`, `low⊑`, `D-self`; 对高度归纳, 不按阶段定制.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdGrow (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (≅ᶻ-sym; z≅; toZ-≅)
open import OCF.Free.Floor using (Ev; fz)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import OCF.Align.LadderOrdStrict2 𝕊
open import OCF.Align.LadderOrdStrict3 𝕊
open import OCF.Align.LadderOrdMono 𝕊
open import OCF.Align.LadderOrdOmega 𝕊
open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
open import OCF.Align.LadderOrdDn 𝕊 using (D→≈ᵠ)
open import OCF.Align.LadderOrdDnSelf 𝕊 using (D-self)
```

## §1 $\prec$ 与 $\sqsubseteq$ 的组合

字面的 $\prec$ 只能先 $\prec$ 后 $\sqsubseteq$. 左边只能换 $\cong$ 的.

```agda
Ls-⊑ᵀ : ∀ {m c φ₀ χ₀ φ₁ χ₁ ψ ρ} {x : Q m c φ₀ χ₀} {y : Q m c φ₁ χ₁} {w : Q m c ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ₁) (lc : Sub m ρ χ₁) → Ls true x y → y ⊑ᵀ w → Ls true x w
Ls-⊑ᵀ le lc h i {C} {C′} o c nd G′ = proj₁ K , proj₂ J (proj₂ K)
  where
  J = i (≈ᶜ-wkˡ le lc (≈ᶜ-reflʳ o)) G′
  K = h (≈ᶜ-wkʳ le lc o) (Ctx-wkC C′ c) tt (proj₁ J)

Ls-Rˡ : ∀ {m c φ₀ χ₀ φ₁ χ₁ ψ ρ} {x : Q m c φ₀ χ₀} {y : Q m c φ₁ χ₁} {w : Q m c ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ₁) (lc : Sub m ρ χ₁) → Rq m c c x y → Ls true y w → Ls true x w
Ls-Rˡ le lc e i {C} {C′} o c nd G′ = Goodᴺ-tr (≅ᶻ-sym d) (proj₁ J) , ≺-≅ˡ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) (proj₁ J)) (proj₁ J)) (proj₂ J)
  where
  J = i (≈ᶜ-wkˡ le lc (≈ᶜ-reflʳ o)) c tt G′
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ le lc o) e)

Ls-ι↓ : ∀ {n m k φ χ ψ ρ} {qd : n <ᴸ m} {x : Q n k φ χ} {y : Q n k ψ ρ} → Ls true x y → Ls true (ι↓ {α = zero} qd x) (ι↓ {α = zero} qd y)
Ls-ι↓ {qd = qd} h o c nd G = h (pD {q = qd} o) c tt G

-- 把 ι↓ q (ι↓ r x) 的严格性换成 ι↓ (r;q) x 的
comp≺ : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → Ls true (ι↓ {α = zero} r (Ω̇ n zero)) (Ω̇ n′ zero) → Ls true (ι↓ {α = zero} (tr< r q′) (Ω̇ n zero)) (ι↓ {α = zero} q′ (Ω̇ n′ zero))
comp≺ {n} {n′} r q′ h = Ls-Rˡ (λ u → u) (upd-sub n′ (λ i q u → κ-cap n (λ _ → tt) i u) (λ u → u)) (R-ιι↓ r q′ z≅ (RΩ̇ n z≅)) (Ls-ι↓ h)
```

## §2 严格增长

```agda
XS : Ht → Set
XS m = ∀ {n} (r : n <ᴸ m) → Ls true (ι↓ {α = zero} r (Ω̇ n zero)) (Ω̇ m zero)

ι↓1⊑row : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → ι↓ {α = zero} r (Ω̇ n (suc zero)) ⊑ᵀ Ω̇ m zero
ι↓1⊑row {n} {m} r e = subst (λ X → ι↓ {α = zero} r (Ω̇ n (suc zero)) ⊑ᵀ X) (sym (Ω̇-clos r e)) (cl-rᵀ (wk-rᵀ (R→⊑ᵀ (R-ι↓ r (s≅ z≅) (RΩ̇ n (s≅ z≅))))))

row≺ : ∀ m → (∀ {n} → n <ᴸ m → XS n) → (v : View _<ᴸ_ h₀ m) → ViewOk _<ᴸ_ h₀ m v → view m ≡ v → XS m
row≺ _ I base ok e r = ⊥-elim (no< r)
row≺ m I (clos {n = n′} q) ok e {n} r with ok r
... | inj₁ refl = subst (λ r₀ → Ls true (ι↓ {α = zero} r₀ (Ω̇ n zero)) (Ω̇ m zero)) (<-prop q r)
  (Ls-⊑ᵀ (λ u → u) (⇑ (κ-cap n′ proj₂)) (Ω↓≺ q zero) (ι↓1⊑row q e))
... | inj₂ r₁ = subst (λ r₀ → Ls true (ι↓ {α = zero} r₀ (Ω̇ n zero)) (Ω̇ m zero)) (<-prop (tr< r₁ q) r)
  (Ls-⊑ᵀ (λ u → u) (⇑ (κ-cap n′ (λ _ → tt))) (comp≺ r₁ q (I q r₁)) (ι↓⊑row q e))
row≺ m I (chain F qs₁) (asc , cof) e {n} r with cof r
... | i , inj₁ refl = subst (λ r₀ → Ls true (ι↓ {α = zero} r₀ (Ω̇ n zero)) (Ω̇ m zero)) (<-prop (tr< (asc i) (qs₁ (suc i))) r)
  (Ls-⊑ᵀ (λ u → u) (⇑ (κ-cap (F (suc i)) (λ _ → tt))) (comp≺ (asc i) (qs₁ (suc i)) (I (qs₁ (suc i)) (asc i))) (ι↓⊑chain F qs₁ e (suc i)))
... | i , inj₂ r₁ = subst (λ r₀ → Ls true (ι↓ {α = zero} r₀ (Ω̇ n zero)) (Ω̇ m zero)) (<-prop (tr< (tr< r₁ (asc i)) (qs₁ (suc i))) r)
  (Ls-⊑ᵀ (λ u → u) (⇑ (κ-cap (F (suc i)) (λ _ → tt))) (comp≺ (tr< r₁ (asc i)) (qs₁ (suc i)) (I (qs₁ (suc i)) (tr< r₁ (asc i)))) (ι↓⊑chain F qs₁ e (suc i)))

FS : ∀ m → (∀ {n} → n <ᴸ m → XS n) → XS m
FS m I = row≺ m I (view m) (view-ok m) refl

low≺ : ∀ m → XS m
low≺ m = FS m (Rec XS FS m)
```

## §3 落到计值

```agda
e-low : ∀ {n m} (r : n <ᴸ m) → Eh h₀ m w₀ (cap (κ Fl) n fz)
e-low {n} r j h q = κ-cap n (λ _ → tt) j (ok₀ j)

grow : ∀ {n m} (r : n <ᴸ m) {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (GᴺTᵠ n zero ev z) ≺ forceᴺ _ (GᴺTᵠ m zero ev z)
grow {n} {m} r {ℓ} ev z = ≺-≅ˡ (forceᴺ-≅ d (GᴺTᵠ n zero ev z) (proj₁ L)) (proj₂ L)
  where
  L = low≺ m r {C = top idO ev z ok₀ (e-low r)} {C′ = top idO ev z ok₀ (λ i h q → ok₀ i)} (top idO) tt tt (GᴺTᵠ m zero ev z)
  d = toZ-≅ (D→≈ᵠ (D-self r) ok₀ (λ i h q → ok₀ i) ok₀ (e-low r) ev z ev z (≅ᴵ-refl zero))
```
