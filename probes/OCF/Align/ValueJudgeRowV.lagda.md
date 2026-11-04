# 值判据 (七): 证书的计值满足判据

> **判决: PARTIAL (`V-rows` 无条件; `fix-of-Br` 条件于 `Br`).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 对高度结构 `HtS` 参数化, 不含记号. `V-rows`: 证书的计值 `V` 满足 `Rows`. `V-⊑`: 结构版本的单调. `fix-of-Br`: 给定桥 `Br` ($\iota_\downarrow$ 的值就是 $V$), 闭包行是 `IsFix`. `Br` 对 $\eta=0,1$ 是定理 (`D-self`, [ValueJudgeBridge](ValueJudgeBridge.lagda.md) 的 `V₁-F`), 对 $\eta\ge2$ 是条件. `clos-below`: 不要桥, 在 $\iota_\downarrow$ 的值上: 层号被链爬过的点, 它的值严格低于闭包.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.ValueJudgeRowV (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev; flo; cvFlo; toFlo; fz; fk; _⊔_; ∼ᶠ-refl)
open import OCF.Free.Eq using (toZ-≅; z≅; s≅; l≅)
open import OCF.Free.Prefix using (Ωˢ)
open import OCF.Free.Force using (forceᴺ-≅; gc)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderInfTree 𝕊
open import OCF.Align.LadderInfCx 𝕊
open import OCF.Align.LadderInfRel 𝕊 using (Rq; R→≈ᵠ; R-tlΩ; RΩ̇)
open import OCF.Align.LadderInfRules 𝕊 using (_⊑ᵀ_)
open import OCF.Align.LadderInfStrict2 𝕊 using (Ls)
open import OCF.Align.LadderInfStrict3 𝕊 using (Ω↓≺; ≺-≅ˡ)
open import OCF.Align.LadderInfMono 𝕊 using (Ωs↓)
open import OCF.Free.Tree using (<◃)
open import OCF.Align.ValueJudgeBase
open import OCF.Align.ValueJudgeFix
open import OCF.Align.ValueJudgeRow 𝕊
open import OCF.Align.ValueJudgeLadder 𝕊

V-rows : Rows V
V-rows = record
  { r-cong   = λ m e → ≅→≈ᵛ (V-≅ m e)
  ; r-strict = λ m a → ≺→s≼ (V-≺ m a)
  ; r-limit  = λ m f s → ≅→≈ᵛ (V-lim m f s)
  ; r-chain  = V-chain
  ; r-clos   = V-clos-≺
  }
```

## §1 结构版本的单调

```agda
V-z⊑ : ∀ m b → V m zero ⊑⁰ V m b
V-z⊑ m zero = λ h → h
V-z⊑ m (suc b) = ⊑-trans (V-z⊑ m b) (≺→⊑ (V-≺ m b))
V-z⊑ m (lim f s) = ⊑-trans (⊑-lim 0 (V-z⊑ m (f 0))) (≅→⊑ (≅-sym (V-lim m f s)))

V-<⊑ : ∀ m {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → V m (suc a) ⊑⁰ V m b
V-<⊑ m e zero = ≅→⊑ (V-≅ m (s≅ e))
V-<⊑ m e (suc q) = ⊑-trans (V-<⊑ m e q) (≺→⊑ (V-≺ m _))
V-<⊑ m e (lim {f} {s} n q) = ⊑-trans (⊑-lim n (V-<⊑ m e q)) (≅→⊑ (≅-sym (V-lim m f s)))

V-⊑ : ∀ m {a b} → a ⊑ᴵ b → V m a ⊑⁰ V m b
V-⊑ m {b = b} z⊑ = V-z⊑ m b
V-⊑ m (s⊑ e q) = V-<⊑ m e q
V-⊑ m {a = lim g s} (l⊑ k) = ⊑-trans (≅→⊑ (V-lim m g s)) (λ { (≺l n h) → V-⊑ m (k n) h })
```

## §2 闭包行是 `IsFix`, 条件于桥

**条件 `Br`.** $\iota_\downarrow(\dot\Omega_n\eta)$ 在任何环境下的值都是 $V_n\eta$.

```agda
Br : ∀ {n m} (r : n <ᴸ m) → Set
Br {n} r = ∀ η → IsF r η (V n η)

fix-of-Br : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → Br r → IsFix (V n) (V m zero)
fix-of-Br {n} r ev br = isFix (ys CR) (hy CR)
    (≅-trans (≅-sym (first CR ok₀ _ (Gf CR))) (br (suc zero) ok₀ _ (Gf CR)))
    (λ k → ≅-trans (≅-sym (next CR k (okA (Gn CR k)) (eA (Gn CR k)) (gA (Gn CR k)))) (br _ (okA (Gn CR k)) (eA (Gn CR k)) (gA (Gn CR k))))
    (value CR)
  where CR = clos-row r ev

-- 经 Br 得到的最小性与唯一性
module FixV {n m} (r : n <ᴸ m) (ev : view m ≡ clos r) (br : Br r) where
  open Row (fix-of-Br r ev br) (V-⊑ n) public

  uniq : ∀ {T} → IsFix (V n) T → T ≅ V m zero
  uniq R = fix-uniq (V-≅ n) R (fix-of-Br r ev br)
```

## §3 不要桥: 链爬过的点

`clos-below`: 在 `ι↓` 的值上. $\eta$ 字面地低于链第 $k$ 项的层号, 则 $\iota_\downarrow(\dot\Omega_n\eta)$ 的值严格低于闭包. 这是 `clos-first≺` 的一般形式; 替身正是这种点 (`fix-static` 的前提).

```agda
module Below {n m} (r : n <ᴸ m) (ev : view m ≡ clos r) (k : ℕ) {η : Ordᴵ} (cr : η <ᴵ toLevel (ys (clos-row r ev) k) (hy (clos-row r ev) k)) where
  private
    CR = clos-row r ev
    lv = toLevel (ys CR k) (hy CR k)
    A  = Gn CR k
    w  = wA A n

    σlv : Simᴵ lv w
    σlv = cvFlo lv (subst (Ev _) (cap-self (κ Fl) n _) (eA A n (Hi-0 n) r))

    σ₁ : Simᴵ η w
    σ₁ p = σlv (<◃ p (<→◃ cr))

    σ₂ : Simᴵ (suc η) w
    σ₂ zero    = σlv cr
    σ₂ (suc p) = σ₁ p

    envE : ∀ {x} → Simᴵ x w → Eh h₀ m (wA A) (cap (κ Fl) n (flo x))
    envE {x} σ j h r′ with tri j n
    ... | tlt _ = okA A j
    ... | teq refl = toFlo x σ
    ... | tgt _ = tt

    K₁ = Ωs↓ {qd = r} (≅ᴵ-refl η) cr {C = top idO ev₀ zero (okA A) (envE σ₂)} {C′ = top idO ev₀ zero (okA A) (eA A)} (top idO) (gA A)
    K₂ = Ω↓≺ r η {C = top idO ev₀ zero (okA A) (envE σ₁)} {C′ = top idO ev₀ zero (okA A) (envE σ₂)} (top idO) tt tt (proj₁ K₁)

  clos-below : ∀ {x} → IsF r η x → x ≺ᵛ V m zero
  clos-below ix =
    ≼-trans (≺→s≼ (≺-≅ˡ (≅-sym (ix (okA A) (envE σ₁) (proj₁ K₂))) (proj₂ K₁ (proj₂ K₂))))
            (≼-trans (≅→≼ (next CR k (okA A) (eA A) (gA A))) (≼-trans (≼l (suc k) (≼-refl _)) (≅→≼ (≅-sym (value CR)))))
```

## §4 根层: 第 0 行是链

`view h₀ ≡ base`: $V_{h_0}0$ 也是一条链的上确界. 链点是 $\psi^0(\Omega_\eta)$ 的值: 字面的 `tl` 像, 没有高度. 这是闭包行的根层版本, $\psi_0(\Omega_\Omega)$ 这一项.

```agda
record BaseRow : Set where
  constructor baseRow
  field
    ysᵇ   : ℕ → Ordᶜ zero
    hyᵇ   : ∀ k → HS (ysᵇ k)
    firstᵇ : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (tl {m = h₀} {c = zero} {χ = κ Fl} Fl proj₂ (Ωˢ (suc zero))) ev p))) → forceᴺ _ G ≅ ysᵇ 0
    nextᵇ : ∀ k {ℓ} (ev : Ev ℓ (fz ⊔ fk (toLevel (ysᵇ k) (hyᵇ k)))) (p : zero <ᴵ ℓ)
            (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (tl {m = h₀} {c = zero} {χ = κ Fl} (fz ⊔ fk (toLevel (ysᵇ k) (hyᵇ k))) (λ e q → proj₂ e (suc q)) (Ωˢ (toLevel (ysᵇ k) (hyᵇ k)))) ev p))) → forceᴺ _ G ≅ ysᵇ (suc k)
    valueᵇ : V h₀ zero ≅ lim ysᵇ
open BaseRow public

rowB-eq : view h₀ ≡ base → Ω̇ h₀ zero ≡ rowB {h₀}
rowB-eq ev = cong (rowV h₀ (ΩI h₀)) ev

base-row : view h₀ ≡ base → BaseRow
base-row ev = go (Good-≡ (rowB-eq ev) (GV h₀ zero)) (≅-trans (≅-sym (V-G h₀ zero (GV h₀ zero))) (Good-≡-≅ (rowB-eq ev) (RΩ̇ h₀ z≅) (GV h₀ zero)))
  where
  R₁ : Rq h₀ zero zero (tl {m = h₀} {c = zero} {χ = κ Fl} Fl proj₂ (Ωˢ (suc zero))) (tl {m = h₀} {c = zero} {χ = κ Fl} Fl proj₂ (Ωˢ (suc zero)))
  R₁ = R-tlΩ (≅ᴵ-refl (suc zero)) (∼ᶠ-refl Fl)

  Rη : ∀ η → Rq h₀ zero zero (tl {m = h₀} {c = zero} {χ = κ Fl} (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η)) (tl {m = h₀} {c = zero} {χ = κ Fl} (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
  Rη η = R-tlΩ (≅ᴵ-refl η) (∼ᶠ-refl (fz ⊔ fk η))

  sameη : ∀ η {ℓ ℓ′} (ev : Ev ℓ (fz ⊔ fk η)) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ (fz ⊔ fk η)) (p′ : zero <ᴵ ℓ′)
          (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (tl {m = h₀} {c = zero} {χ = κ Fl} (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η)) ev p)))
          (G′ : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (tl {m = h₀} {c = zero} {χ = κ Fl} (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η)) ev′ p′))) → forceᴺ _ G ≅ forceᴺ _ G′
  sameη η ev p ev′ p′ G G′ = forceᴺ-≅ (toZ-≅ (R→≈ᵠ (Rη η) ok₀ e₀ ok₀ e₀ ev p ev′ p′ z≅)) G G′

  go : (G : Goodᴺ (toZ (ψ̄ᵠ ok₀ e₀ (rowB {h₀}) ev₀ zero))) → V h₀ zero ≅ forceᴺ _ G → BaseRow
  go (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) eG = baseRow ys hy
    (λ evv p G → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ R₁ ok₀ e₀ ok₀ e₀ evv p ev₀ zero z≅)) G G₀) l₀)
    (λ k evv p G → ≅-trans (sameη _ evv p _ _ G (Gg k)) (lE k))
    (≅-trans eG (l≅ (λ { zero → ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ R₁ ok₀ e₀ ok₀ e₀ ev₀ zero ev₀ zero z≅)) Go₀ G₀) l₀
                       ; (suc k) → ≅-trans (sameη _ _ _ _ _ (Go k) (Gg k)) (lE k) })))
```
