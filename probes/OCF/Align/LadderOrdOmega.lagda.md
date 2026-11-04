# 序数高度: 塔上的 $\dot\Omega$

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfOmega](LadderInfOmega.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 这一个模块有手写补丁: 链行的单调 (`low⊑`, `mono-rowL`). 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 对高度结构 `HtB` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFOmega](LadderNFOmega.lagda.md) 生成, 下面的说明是原文件的. `Ω̇G g m k`: 一切 $m$, $k$, `Ω̇ m k` 都是 `Gq`. 高度 $n+1$ 的闭包守卫 `Brq` 与根层的 `Brᵀ` 同形: 读数是 "$\dot\Omega_b$ 之下层号 $\succeq b+1$", 增长由 `Ω↓≺` 给出, 下移由 `InvD` 读出. 无归纳于 $\theta$, $c$; 对 $m$ 的结构递归只是 $\dot\Omega$ 定义本身的结构. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdOmega (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Free.Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdRules3 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import OCF.Align.LadderOrdStrict2 𝕊
open import OCF.Align.LadderOrdClass 𝕊
open import OCF.Align.LadderOrdClassF 𝕊
open import OCF.Align.LadderOrdGood 𝕊
open import OCF.Align.LadderOrdVis 𝕊
open import OCF.Align.LadderOrdIota 𝕊
open import OCF.Align.LadderOrdAdd 𝕊
open import OCF.Align.LadderOrdTr 𝕊
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Force using (forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Eq using (s-invˢ; l-invˢ; i-respˢ; u-reflˢ; tf; ŝ≅; ĉ≅; upˡ; upʳ)
-- (同上)

open import OCF.Align.LadderOrdTail 𝕊
open import OCF.Align.LadderOrdRead 𝕊
open import OCF.Free.Aux using (one⁰)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; Ωˢ-≅; Ωˢ-refl)
open import OCF.Free.Floor using (⊔∼; fk∼; fz∼)
-- (同上)

open import OCF.Align.LadderOrdRoot 𝕊 using (Ω̇G₀; one⊑; zlt; τ; ≺ᴵ-up; NZ-≅₁)
open import OCF.Align.LadderOrdStrict3 𝕊 using (Ω↓≺)
open import OCF.Align.LadderOrdMono 𝕊
open RestrQ
```

## §1 高度 $n$ 的闭包守卫

对一个固定的 `qd : n <ᴸ m`. 原文件是 $m=n+1$.

```agda
lvG≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G₁ → lvG G ≅ᴵ lvG G₁
lvG≡ refl G = G , ≅ᴵ-refl _

module BrM {n m : Ht} (qd : n <ᴸ m) where
  CD : Ordᴵ → Set
  CD k = Cx m zero Fl (cap (κ Fl) n (flo k))

  ι↓₀ : ∀ {k φ χ} → Q n k φ χ → Q m zero φ (cap χ n (flo k))
  ι↓₀ = ι↓ {α = zero} qd

  CQq : ∀ {ψ ρ} → Cx m zero ψ ρ → Ordᴵ → Set
  CQq C b = ∀ {k′} → k′ ≅ᴵ b → {D : CD k′} → D ≈ᶜ C → (G : Goodᴺ (toZ (runᶜ D (ι↓₀ (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G

  record Brq {ψ ρ} (η : Ordᴵ) (C : Cx m zero ψ ρ) : Set where
    constructor br-mk
    field
      cxB : Ctxᶜ C
      br  : ∀ {b} → b ≺ᴵ η → CQq C b
      η₋  : Ordᴵ
      D₋  : CD η₋
      o₋  : D₋ ≈ᶜ C
      G₋  : Goodᴺ (toZ (runᶜ D₋ (ι↓₀ (Ω̇ n η₋))))
      eη  : η ≅ᴵ lvG G₋
      h₋  : η₋ ≺ᴵ η
  open Brq

  Ω↓lt : ∀ {a a′ b} → a ≅ᴵ a′ → (q : a′ <ᴵ b) → ι↓₀ (Ω̇ n a) ⊑ᵀ ι↓₀ (Ω̇ n b)
  Ω↓lt {a} {a′} {b} e q =
    ⊑ᵀ-transʷ (λ u → u) (⇑ (cap-map n (λ u {c} x → cvFlo b u (τ q x))))
      (⊑ᵀ-Rˡʷ (λ u → u) D↑s (R-ι↓ qd e (RΩ̇ n e)) (Ωstep↓ {qd = qd})) (Ωs↓ {qd = qd} (≅ᴵ-refl a′) q)

  Ω↓via : ∀ {a b} → a ≺ᴵ b → ι↓₀ (Ω̇ n a) ⊑ᵀ ι↓₀ (Ω̇ n b)
  Ω↓via (via e q) = Ω↓lt e q

  rdq : ∀ {η₀ k′ b} {D₀ : CD η₀} {D : CD k′} → D₀ ≈ᶜ D → (G₀ : Goodᴺ (toZ (runᶜ D₀ (ι↓₀ (Ω̇ n η₀))))) → b ≺ᴵ lvG G₀ →
        ι↓₀ (Ω̇ n η₀) ⊑ᵀ ι↓₀ (Ω̇ n k′) → (G : Goodᴺ (toZ (runᶜ D (ι↓₀ (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G
  rdq {η₀} o G₀ h fl G =
    s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                           (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
    where
    L = fl o G
    d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) (R-ι↓ qd (≅ᴵ-refl η₀) (RΩ̇ n (≅ᴵ-refl η₀))))

  growT : ∀ {η₋ a η′} {D₋ : CD η₋} {D′ : CD η′} → Ctxᶜ D′ → D₋ ≈ᶜ D′ → η₋ ≅ᴵ a → (q : a <ᴵ η′) →
          (G₋ : Goodᴺ (toZ (runᶜ D₋ (ι↓₀ (Ω̇ n η₋))))) (G′ : Goodᴺ (toZ (runᶜ D′ (ι↓₀ (Ω̇ n η′))))) → lvG G₋ ≺ᴵ lvG G′
  growT {η₋} {a} {η′} {D₋} {D′} cD o e q G₋ G′ =
    ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ S)) e₃)
             (toLevel-≺ (forceᴺ-HS _ (proj₁ S)) (forceᴺ-HS _ G′) (proj₂ L (proj₂ S)))
    where
    lS : Sub m (cap (κ Fl) n (flo η′)) (cap (κ Fl) n (flo (suc a)))
    lS = ⇑ (cap-map n (λ u {c} x → cvFlo η′ u (τ q x)))
    lA : Sub m (cap (κ Fl) n (flo η′)) (cap (κ Fl) n (flo a))
    lA = ⇑ (cap-map n (λ u → toFlo a (λ x → cvFlo η′ u (τ q (suc x)))))
    rD = ≈ᶜ-reflʳ o
    L = Ωs↓ {qd = qd} (≅ᴵ-refl a) q {C = wkC (λ u → u) lS D′} {C′ = D′} (≈ᶜ-wkˡ (λ u → u) lS rD) G′
    S = Ω↓≺ qd a {C = wkC (λ u → u) lA D′} {C′ = wkC (λ u → u) lS D′} (wk≈ (λ u → u) lA (λ u → u) lS rD) (Ctx-wkC D′ cD) tt (proj₁ L)
    e₃ = forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (λ u → u) lA o) (R-ι↓ qd e (RΩ̇ n e)))) G₋ (proj₁ S)

  brZ : ∀ {ψ ρ} {C : Cx m zero ψ ρ} → Ctxᶜ C → CQq C zero
  brZ x {k′} e {D} d G = read1ᵀ D (≈Ctxᶜ d x) (ι↓₀ (Ω̇ n k′)) (R-ι↓ qd (≅ᴵ-refl k′) (RΩ̇ n (≅ᴵ-refl k′))) (𝟏-D {qd = qd} (𝟏⊑Ω̇ n k′)) G

  ω1q : ∀ {k′ x L} → k′ ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ x → ι↓₀ (Ω̇ n (suc zero)) ⊑ᵀ ι↓₀ (Ω̇ n k′)
  ω1q {k′} e q z nx = go (⊑ᴵ-≅ʳ (one⊑ z q nx) (≅ᴵ-sym e))
    where
    go : suc zero ⊑ᴵ k′ → ι↓₀ (Ω̇ n (suc zero)) ⊑ᵀ ι↓₀ (Ω̇ n k′)
    go (s⊑ z≅ r) = Ωs↓ {qd = qd} z≅ r

  ch₀q : ∀ (uₒ : Sub m (κ Fl) (cap (κ Fl) n (flo (suc zero)))) {C : Cx m zero Fl (κ Fl)} → 𝓥 C →
         (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero))))))) →
         ∀ {C′ : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq (lvG G) C′
  ch₀q uₒ {C} x G {C′} x′ o = br-mk x′ brB (suc zero) D₁ (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym o)) G₁ e₁ two
    where
    J = lvG≡ (run-wkC (λ u → u) uₒ C (ι↓₀ (Ω̇ n (suc zero)))) G
    G₁ = proj₁ J
    e₁ = proj₂ J
    D₁ = wkC (λ u → u) uₒ C
    rt₁ : Rq m zero zero (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero)))) (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero))))
    rt₁ = rwk (R-ι↓ qd (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _)))
    one₁ : 𝟏q zero ⊑ᵀ qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero)))
    one₁ = wk-rᵀ (𝟏-D {qd = qd} (𝟏⊑Ω̇ n (suc zero)))
    two : suc zero ≺ᴵ lvG G
    two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (Twᵀ C x rt₁ one₁ G)
    z₁ : zero <ᴵ lvG G
    z₁ = zlt (read1ᵀ C x _ rt₁ one₁ G)
    brB : ∀ {b} → b ≺ᴵ lvG G → CQq C′ b
    brB {b = zero} h e d G′ = brZ x′ e d G′
    brB {b = suc b} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′
    brB {b = lim f s} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′

  LLq : ∀ η → Sub m (upd (κ Fl) n (fz ⊔ fk η)) (cap (κ Fl) n (flo η))
  LLq η = ⇑ (upd-cap n (λ i e → e) (λ e → toFlo η (λ q → proj₂ e (suc q))))

  chSq : ∀ η {C : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk η))} → Brq η C →
         (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) (LLq η) (ι↓₀ (Ω̇ n η)))))) →
         ∀ {C′ : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq (lvG G) C′
  chSq η {C} B G {C′} x′ o = br-mk x′ brN η D₁ (≈ᶜ-wkˡ (λ u → u) (LLq η) (≈ᶜ-sym o)) G₁ e₁ (≺ᴵ-respʳ gr (≅ᴵ-sym e₁))
    where
    J = lvG≡ (run-wkC (λ u → u) (LLq η) C (ι↓₀ (Ω̇ n η))) G
    G₁ = proj₁ J
    e₁ = proj₂ J
    D₁ = wkC (λ u → u) (LLq η) C
    grr : η₋ B ≺ᴵ η → lvG (G₋ B) ≺ᴵ lvG G₁
    grr (via e′ q) = growT (Ctx-wkC C (cxB B)) (≈ᶜ-wkʳ (λ u → u) (LLq η) (o₋ B)) e′ q (G₋ B) G₁
    gr : η ≺ᴵ lvG G₁
    gr = ≺ᴵ-respˡ (eη B) (grr (h₋ B))
    brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQq C′ b′
    brN {b′} h {k′} e {D} d G′ = go gr (≺ᴵ-respʳ h e₁)
      where
      dC : D ≈ᶜ C
      dC = ≈ᶜ-trans d o
      o₁ : D₁ ≈ᶜ D
      o₁ = ≈ᶜ-wkˡ (λ u → u) (LLq η) (≈ᶜ-sym dC)
      go : η ≺ᴵ lvG G₁ → b′ ≺ᴵ lvG G₁ → suc b′ ⊑ᴵ lvG G′
      go (via ex qx) h′@(via eb qb) with <ᴵ-dec qb qx
      ... | injᵃ s = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) e dC G′
      ... | injᵇ s = rdq o₁ G₁ h′ (Ω↓via (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym (≅ᴵ-trans e eb))))) G′
      ... | injᶜ c = rdq o₁ G₁ h′ (R→⊑ᵀ (R-ι↓ qd (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb)))) (RΩ̇ n (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb))))))) G′

  BrCast : ∀ {η η′ ψ ρ ψ′ ρ′} {C : Cx m zero ψ ρ} {C′ : Cx m zero ψ′ ρ′} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → Brq η C → Brq η′ C′
  BrCast eq x′ o B = br-mk x′ (λ h e d → br B (≺ᴵ-respʳ h (≅ᴵ-sym eq)) e (≈ᶜ-trans d o)) (η₋ B) (D₋ B) (≈ᶜ-trans (o₋ B) (≈ᶜ-sym o)) (G₋ B)
                           (≅ᴵ-trans (≅ᴵ-sym eq) (eη B)) (≺ᴵ-respʳ (h₋ B) eq)
```

## §2 下移读出闭包守卫

原文件的 `rt` 把上下文的头读出来再比较. 这里头的 `q` 要记住, 而 `≈ᶜ` 两边的 `q` 一样, 同时对两边模式匹配要用 K. 所以改成一个归纳的不变量 `Inv C₀ X`: $X$ 的头 (穿过搬运) 是 `pD {q = qd} C`, 且 $C\approx C_0$. 这与 `rt`, `rt-≈`, `rtD`, `rtE`, `InvD` 是同一个论证, 只是把它们合成了一个谓词.

```agda
  data Inv {ψ₀ ρ₀} (C₀ : Cx m zero ψ₀ ρ₀) : ∀ {k φ χ} → Cx n k φ χ → Set where
    iD  : ∀ {k φ χ} {C : Cx m zero φ (cap χ n (flo k))} → C ≈ᶜ C₀ → Inv C₀ (pD {q = qd} C)
    iT  : ∀ {a b φ χ} {e : a ≅ᴵ b} {C : Cx n b φ χ} → Inv C₀ C → Inv C₀ (ptr e C)
    iT⁻ : ∀ {a b φ χ} {e : a ≅ᴵ b} {C : Cx n a φ χ} → Inv C₀ C → Inv C₀ (ptr⁻ e C)

  Inv→Dd : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k φ χ} {X : Cx n k φ χ} → Inv C₀ X → Dd X
  Inv→Dd (iD c) = tt
  Inv→Dd (iT i) = Inv→Dd i
  Inv→Dd (iT⁻ i) = Inv→Dd i

  Inv-≈ : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k φ χ ψ ρ} {E : Cx n k φ χ} {X : Cx n k ψ ρ} → E ≈ᶜ X → Inv C₀ X → Inv C₀ E
  Inv-≈ (pD o) (iD c) = iD (≈ᶜ-trans o c)
  Inv-≈ (ptr o) (iT i) = iT (Inv-≈ o i)
  Inv-≈ (ptr⁻ o) (iT⁻ i) = iT⁻ (Inv-≈ o i)

  Inv-shD : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k ℓ φ χ} (r : k ◃₁ ℓ) {X : Cx n ℓ φ χ} (d : Dd X) → Inv C₀ X → Inv C₀ (shD r X d)
  Inv-shD r d (iD c) = iD (≈ᶜ-wkˡ (λ e → e) _ c)
  Inv-shD zero d (iT {e = s≅ e} i) = iT (Inv-shD zero d i)
  Inv-shD (self j) d (iT {e = l≅ h} i) = iT (Inv-shD (self j) d i)
  Inv-shD zero d (iT⁻ {e = s≅ e} i) = iT⁻ (Inv-shD zero d i)
  Inv-shD (self j) d (iT⁻ {e = l≅ h} i) = iT⁻ (Inv-shD (self j) d i)

  Inv-shE : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k ℓ φ χ} (r : k ◃₁ ℓ) (X : Cx n ℓ φ χ) (u : Nd X ⊎ Dd X) → Inv C₀ X → Inv C₀ (shE r X u)
  Inv-shE r X (inj₁ a) i = ⊥-elim (Nd∧Dd X a (Inv→Dd i))
  Inv-shE r X (inj₂ d) i = Inv-shD r d i

  InvD : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k b φ χ s} {X : Cx n k φ χ} {E : Cx n b Fl (κ Fl)} → Inv C₀ X → Sft X s E → Inv C₀ E
  InvD i (sB e) = Inv-≈ e i
  InvD {X = X} i (sS h) = InvD (Inv-shE zero X (dh X) i) h
  InvD {X = X} i (sL j h) = InvD (Inv-shE (self j) X (dh X) i) h
  InvD i (sT e h) = InvD (iT i) h
  InvD i (sT⁻ e h) = InvD (iT⁻ i) h

  inv-val : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k} {E : Cx n k Fl (κ Fl)} → Inv C₀ E → {y : Q n k Fl (κ Fl)} → RΩv n k y →
            Σ Ordᴵ λ k₀ → Σ (CD k₀) λ D → (k₀ ≅ᴵ k) × (D ≈ᶜ C₀) × (runᶜ E y ≅ˢ runᶜ D (ι↓₀ (Ω̇ n k₀)))
  inv-val (iD {k = k} {C = C} c) hy = k , C , ≅ᴵ-refl k , c , hy (pD (≈ᶜ-reflˡ c))
  inv-val (iT {e = e} i) hy =
    let P = inv-val i (RΩv-tr e hy)
    in proj₁ P , proj₁ (proj₂ P) , ≅ᴵ-trans (proj₁ (proj₂ (proj₂ P))) (≅ᴵ-sym e) , proj₁ (proj₂ (proj₂ (proj₂ P))) , proj₂ (proj₂ (proj₂ (proj₂ P)))
  inv-val (iT⁻ {e = e} i) hy =
    let P = inv-val i (RΩv-tr⁻ e hy)
    in proj₁ P , proj₁ (proj₂ P) , ≅ᴵ-trans (proj₁ (proj₂ (proj₂ P))) e , proj₁ (proj₂ (proj₂ (proj₂ P))) , proj₂ (proj₂ (proj₂ (proj₂ P)))

  brVis : ∀ {η ψ ρ} {C₀ : Cx m zero ψ ρ} {Y : CD η} → Ctxᶜ Y → Y ≈ᶜ C₀ → (∀ {b} → b ≺ᴵ η → CQq C₀ b) → VisQ η (pD {q = qd} Y)
  brVis {η} x o br₁ = visQ x (λ {b} {E} h G →
    let P = inv-val (InvD (iD o) h) (RΩv-Ω {n} {b})
    in pull (proj₂ (proj₂ (proj₂ (proj₂ P)))) (λ H → br₁ (Sft-lvT h) (proj₁ (proj₂ (proj₂ P))) (proj₁ (proj₂ (proj₂ (proj₂ P)))) H) G)
  
  -- 闭包行的证书, 对低一层的 Ω̇G
  G-rowC : ∀ w → (∀ w′ → inp w′ ≡ w′ → ∀ k → Gq w′ n k (KQ w′ k) (Ω̇ n k)) → Gq w m zero 𝓥 (rowC qd (Ω̇ n))
  G-rowC w I =
    gcl 𝓥 (λ c → c) (λ η C → Brq η C) BrCast
       (gw (λ E → 𝓥 E × VisQ (suc zero) (pD {q = qd} E))
           (λ {C} c → Ctx-wkC C c , brVis (Ctx-wkC C c) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C c)) (λ { (via z≅ zero) → brZ c ; (via e (suc ())) }))
           (IDM.ID qd proj₂ proj₁ (I g₂ refl (suc zero))))
       (λ η → gw (λ E → 𝓥 E × VisQ η (pD {q = qd} E))
           (λ {C} B → Ctx-wkC C (cxB B) , brVis (Ctx-wkC C (cxB B)) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C (cxB B))) (br B))
           (IDM.ID qd proj₂ proj₁ (I g₂ refl η)))
       (rwk (R-ι↓ qd (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _))))
       (λ η η′ d → rwk (R-ι↓ qd d (RΩ̇ n d)))
       (λ η h → wk-lᵗ (wk-rᵗ (Ωm↓ {qd = qd} h)))
       (λ η η′ h u → wk-lᵗ (wk-rᵗ (Ωm↓ {qd = qd} u)))
       (λ c G ())
       (λ η c G ())
       (ch₀q _)
       chSq

  -- 链行的一项
  G-stepL : ∀ w → (∀ w′ → inp w′ ≡ w′ → ∀ k → Gq w′ n k (KQ w′ k) (Ω̇ n k)) → Gq w m zero 𝓥 (stepL qd (Ω̇ n))
  G-stepL w I =
    gw (λ E → 𝓥 E × VisQ zero (pD {q = qd} E))
       (λ {C} c → Ctx-wkC C c , brVis (Ctx-wkC C c) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C c)) (λ { (via e ()) }))
       (IDM.ID qd proj₂ proj₁ (I g₂ refl zero))
```

## §2′ 跨高度: 两次 `ι↓` 与一次

链行的单调. $\iota_{\downarrow q'}(\iota_{\downarrow r}x)$ 与 $\iota_{\downarrow (r;q')}x$ 互模拟. 中间一层的目标是 $0$, 地板 `flo zero` 是 `fz`, 所以地板一致. 嵌套节点的 $q$ 只差结合律 (`tr-assoc`).

```agda
cap²∼ : ∀ {a b c} {χ ρ : Fv} {x y} → a <ᴸ b → Sim∼ a χ ρ → x ∼ᶠ y → Sim∼ c (cap χ a x) (cap (cap ρ a y) b fz)
cap²∼ {a} {b} {c} {χ} {ρ} {x} {y} x₁ s e i q = case-tri i a
  (λ r → subst₂ _∼ᶠ_ (sym (cap-lt χ x r)) (sym (trans (cap-lt (cap ρ a y) fz (tr< r x₁)) (cap-lt ρ y r))) (s i r))
  (λ { refl → subst₂ _∼ᶠ_ (sym (cap-self χ i x)) (sym (trans (cap-lt (cap ρ i y) fz x₁) (cap-self ρ i y))) e })
  (λ r → case-tri i b
     (λ r′ → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (trans (cap-lt (cap ρ a y) fz r′) (cap-gt ρ y r))) fz∼)
     (λ { refl → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (cap-self (cap ρ a y) i fz)) fz∼ })
     (λ r′ → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (cap-gt (cap ρ a y) fz r′)) fz∼))

R-Ω↓-cast : ∀ {c α α′ j k k′ φ χ ψ ρ} {Q₁ Q₂ : j <ᴸ c} → Q₁ ≡ Q₂ → {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ j) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ j) → k′ <ᴵ L}
            {h₁ : ∀ ξ ζ → Vs c Q₁ k ξ ζ → Q c α (ξ ⊔ φ) (lo j ζ ∪ χ)} {h₂ : ∀ ξ ζ → Vs c Q₂ k′ ξ ζ → Q c α′ (ξ ⊔ ψ) (lo j ζ ∪ ρ)} →
            k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ c χ ρ →
            (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ j ζ ζ′ → (z : Q j k ξ ζ) (z′ : Q j k′ ξ′ ζ′) → Rq j k k′ z z′ → Rq c α α′ (h₁ ξ ζ (intoV Q₁ z)) (h₂ ξ′ ζ′ (intoV Q₂ z′))) →
            Rq c α α′ (qΩ↓ Q₁ fe ac h₁) (qΩ↓ Q₂ fe′ ac′ h₂)
R-Ω↓-cast {Q₁ = Q₁} refl ek s c f = rΩ↓ {q = Q₁} same ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → f ξ ξ′ ζ ζ′ d dc z z′ (outVq Q₁ l))

R-cl-cast : ∀ {c α α′ j φ χ ψ ρ κ₁ κ₂} {Q₁ Q₂ : j <ᴸ c} → Q₁ ≡ Q₂ → {s : ∀ {ℓ} → Ev ℓ (χ j) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ j) → Ev ℓ (κ₂ ⊔ fk zero)}
            {t : Q c α φ χ} {t′ : Q c α′ ψ ρ} {g : (η : Ordᴵ) → Q c α φ (upd χ j (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q c α′ ψ (upd ρ j (κ₂ ⊔ fk η))} →
            κ₁ ∼ᶠ κ₂ → Rq c α α′ t t′ → (∀ η η′ → η ≅ᴵ η′ → Rq c α α′ (g η) (g′ η′)) → Rq c α α′ (qcl Q₁ κ₁ s t g) (qcl Q₂ κ₂ s′ t′ g′)
R-cl-cast {Q₁ = Q₁} refl e r h = rcl {q = Q₁} same e r h

R-ιι↓ : ∀ {a b c k k′ α α′ φ ψ χ ρ} (x₁ : a <ᴸ b) (x₂ : b <ᴸ c) → k ≅ᴵ k′ → {x : Q a k φ χ} {x′ : Q a k′ ψ ρ} → Rq a k k′ x x′ →
        Rq c α α′ (ι↓ (tr< x₁ x₂) x) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ x′))
R-ιι↓ x₁ x₂ ek rz = rz
R-ιι↓ x₁ x₂ ek (rs sa sb r) = rs sa (cap²∼ x₁ sb (flo-∼ ek)) (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ x₁ x₂ ek (rl h) = rl (λ n → R-ιι↓ x₁ x₂ ek (h n))
R-ιι↓ x₁ x₂ ek (ri e h) = ri e (λ x y d → R-ιι↓ x₁ x₂ ek (h x y d))
R-ιι↓ x₁ x₂ ek (rŝ e r h) = rŝ e (R-ιι↓ x₁ x₂ ek r) (λ η ee η′ e′ d → R-ιι↓ x₁ x₂ ek (h η ee η′ e′ d))
R-ιι↓ x₁ x₂ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ιι↓ x₁ x₂ ek r) (λ η ee η′ e′ d → R-ιι↓ x₁ x₂ ek (h η ee η′ e′ d))
R-ιι↓ x₁ x₂ ek (rclo s r h) = rclo s (R-ιι↓ x₁ x₂ ek r) (λ η η′ d → R-ιι↓ x₁ x₂ ek (h η η′ d))
R-ιι↓ x₁ x₂ ek (rcl {q = q} same s r h) =
  R-cl-cast (sym (tr-assoc q x₁ x₂)) s (R-ιι↓ x₁ x₂ ek r) (λ η η′ d → rwkˡ (rwkʳ (rwkʳ (R-ιι↓ x₁ x₂ ek (h η η′ d)))))
R-ιι↓ x₁ x₂ ek (rwkˡ r) = rwkˡ (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ x₁ x₂ ek (rwkʳ r) = rwkʳ (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ {a} {b} {c} {α = α} {α′ = α′} x₁ x₂ ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c′ f) =
  R-Ω↓-cast (sym (tr-assoc q x₁ x₂)) ei s (cap²∼ x₁ c′ (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwkˡ (rwkʳ (rwkʳ
    (subst₂ (λ u v → Rq c α α′ (ι↓ (tr< x₁ x₂) (h ξ ζ (intoV q u))) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ (h′ ξ′ ζ′ (intoV q v)))))
       (sym (out-intoV (tr< q (tr< x₁ x₂)) z))
       (sym (trans (cong (λ w → outV (tr< q x₁) (intoV (tr< q x₁) w)) (out-intoV (tr< (tr< q x₁) x₂) z′)) (out-intoV (tr< q x₁) z′)))
       (R-ιι↓ x₁ x₂ ek (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l)))))))
R-ιι↓ {a} {b} {c} {α = α} {α′ = α′} x₁ x₂ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c′ f) =
  R-Ω↓-cast refl ei s (cap²∼ x₁ c′ (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwkˡ (rwkʳ (rwkʳ
    (subst₂ (λ u v → Rq c α α′ (ι↓ (tr< x₁ x₂) (h ξ ζ (intoU (<→◃ r) u))) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))
       (sym (out-intoV (tr< x₁ x₂) z))
       (sym (trans (cong (λ w → outV x₁ (intoV x₁ w)) (out-intoV (tr< x₁ x₂) z′)) (out-intoV x₁ z′)))
       (R-ιι↓ x₁ x₂ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l)))))))
R-ιι↓ x₁ x₂ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwkˡ (rwkʳ (R-ιι↓ x₁ x₂ ea l))
R-ιι↓ x₁ x₂ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwkˡ (rwkʳ (R-ιι↓ x₁ x₂ ea l))

-- 第 0 行开出来是闭包时, ι↓ (Ω̇ n 0) 在它下面
Ω̇-clos : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → Ω̇ m zero ≡ rowC r (Ω̇ n)
Ω̇-clos {n} {m} r e = trans (cong (rowV m (ΩI m)) e) (cong (rowC r) (ΩI≡ r))

ι↓⊑row : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ m zero
ι↓⊑row {n} {m} r e = subst (λ X → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ X) (sym (Ω̇-clos r e)) (cl-rᵀ (wk-rᵀ (Ωz↓ {qd = r} (suc zero))))

-- 这里是与 LadderOrdOmega 唯一的不同. 原文件靠 view-step: 链的下一项是上一项的闭包, 在 ω² 上是假的.
-- 改成对高度归纳: 一切 n < m 都有 ι↓ (Ω̇ n 0) ⊑ Ω̇ m 0. 闭包行与链行各用 view-ok 把 n 压到写法给的那个高度以下.
comp↓ : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ n′ zero → ι↓ {α = zero} (tr< r q′) (Ω̇ n zero) ⊑ᵀ ι↓ {α = zero} q′ (Ω̇ n′ zero)
comp↓ {n} {n′} r q′ h = ⊑ᵀ-Rˡʷ (λ u → u) (upd-sub n′ (λ i q u → κ-cap n (λ _ → tt) i u) (λ u → u)) (R-ιι↓ r q′ z≅ (RΩ̇ n z≅)) (ιD-cong {qd = q′} h)

XM : Ht → Set
XM m = ∀ {n} (r : n <ᴸ m) → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ m zero

ι↓⊑chain : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → view m ≡ chain F qs₁ → ∀ i → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ Ω̇ m zero
ι↓⊑chain {m} F qs₁ e i = subst (λ X → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ X) (sym (cong (rowV m (ΩI m)) e))
  (lim-rᵀ (suc i) (subst (λ X → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ stepL (qs₁ i) X) (sym (ΩI≡ (qs₁ i))) (wk-rᵀ (R→⊑ᵀ (R-ι↓ (qs₁ i) z≅ (RΩ̇ (F i) z≅))))))

low-row : ∀ m → (∀ {n} → n <ᴸ m → XM n) → (v : View _<ᴸ_ h₀ m) → ViewOk _<ᴸ_ h₀ m v → view m ≡ v → XM m
low-row _ I base ok e r = ⊥-elim (no< r)
low-row m I (clos {n = n′} q) ok e {n} r with ok r
... | inj₁ refl = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop q r) (ι↓⊑row q e)
... | inj₂ r₁ = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (tr< r₁ q) r)
  (⊑ᵀ-transʷ (λ u → u) (⇑ (κ-cap n′ (λ _ → tt))) (comp↓ r₁ q (I q r₁)) (ι↓⊑row q e))
low-row m I (chain F qs₁) (asc , cof) e {n} r with cof r
... | i , inj₁ refl = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (qs₁ i) r) (ι↓⊑chain F qs₁ e i)
... | i , inj₂ r₁ = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (tr< r₁ (qs₁ i)) r)
  (⊑ᵀ-transʷ (λ u → u) (⇑ (κ-cap (F i) (λ _ → tt))) (comp↓ r₁ (qs₁ i) (I (qs₁ i) r₁)) (ι↓⊑chain F qs₁ e i))

FM : ∀ m → (∀ {n} → n <ᴸ m → XM n) → XM m
FM m I = low-row m I (view m) (view-ok m) refl

low⊑ : ∀ m → XM m
low⊑ m = FM m (Rec XM FM m)

step-mono : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → stepL (tr< r q′) (Ω̇ n) ⊑ᵗ stepL q′ (Ω̇ n′)
step-mono {n} {n′} {m} r q′ =
  wk-lᵗ (wk-rᵗ (⊑ᵀ→ᵗ (R-ι↓ (tr< r q′) z≅ (RΩ̇ n z≅)) (comp↓ r q′ (low⊑ n′ r))))
```

## §3 $\dot\Omega$ 全体

```agda
zcOf : ∀ w (A : Set₁) → (w ≡ g₂ → A) → Zc w A
zcOf g₀ A f = tt₁
zcOf g₁ A f = tt₁
zcOf g₂ A f = f refl

KQ-sh : ∀ w {m k φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {C : Cx m (suc k) ψ ρ} → KQ w (suc k) C → KlT w k (sh zero (wkC le lc C))
KQ-sh g₀ {C = C} c = Ctx-sh zero _ (Ctx-wkC C c)
KQ-sh g₁ {le = le} {lc = lc} {C = C} v = Vis-shq (VisQ-≈ (Ctx-wkC C (cxQ v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl C (cxQ v))) v)
KQ-sh g₂ {le = le} {lc = lc} {C = C} v = Vis-shq (VisQ-≈ (Ctx-wkC C (cxQ v)) (≈ᶜ-wkˡ le lc (ctxᶜ-refl C (cxQ v))) v)

Vis-above : ∀ {m k ξ ζ ψ ρ} {D : Cx m k ξ ζ} {C′ : Cx m (suc k) ψ ρ} (E₀ : Cx m k Fl (κ Fl)) → E₀ ≈ᶜ D → VisQT k D → AboveΩ C′ D → (∀ {L} → Ev L ψ → Ev L Fl) → Sub m ρ (κ Fl) → VisQ (suc k) C′
Vis-above {m} {k} {C′ = C′} E₀ o₀ v a le lc = visQ (cxΩ a) (λ {b} {E} h G →
  let L₁ = Sft-lift (ctxᶜ-refl C′ (cxΩ a)) le lc h (Ω̇ m b) (RΩ̇ m (≅ᴵ-refl b))
      Wp = wrapΩ a (proj₁ L₁) (proj₁ (proj₂ L₁))
      u = proj₁ Wp
      fu = proj₁ (proj₂ (proj₂ Wp))
      d = ≅ˢ-trans (proj₂ (proj₂ L₁)) (proj₂ (proj₂ (proj₂ Wp)))
      S = stp (Sft-lvT h)
  in pull d (λ H →
       let J = fu (RΩ̇ m (≅ᴵ-refl k)) (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl k))) o₀ H
       in ⊑ᴵ-trans S (⊑ᴵ-trans (tpQ v (sB o₀) (proj₁ J)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ J)) (forceᴺ-HS _ H) (proj₂ J)))) G)
  where
  stp : ∀ {b} → b ≺ᴵ suc k → suc b ⊑ᴵ suc k
  stp (via e q) = s⊑ e q

KQ-St : ∀ w {m k ξ ζ} {C : Cx m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)} {C′ : Cx m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)} {le : ∀ {L} → Ev L (ξ ⊔ Fl) → Ev L ξ} {lc : Sub m (lo m ζ ∪ κ Fl) ζ} →
        KQ w (suc k) C → AboveΩ C′ (sh zero (wkC le lc C)) → KQ w (suc k) C′
KQ-St g₀ c a = cxΩ a
KQ-St g₁ {m} {C = C} {le = le} {lc = lc} v a =
  Vis-above (sh zero (wkC proj₂ (λ i q → proj₂) C)) (sh-≈ zero (wk≈ proj₂ (λ i q → proj₂) le lc (ctxᶜ-refl C (cxQ v)))) (KQ-sh g₂ v) a proj₂ (λ i q → proj₂)
KQ-St g₂ {m} {C = C} {le = le} {lc = lc} v a =
  Vis-above (sh zero (wkC proj₂ (λ i q → proj₂) C)) (sh-≈ zero (wk≈ proj₂ (λ i q → proj₂) le lc (ctxᶜ-refl C (cxQ v)))) (KQ-sh g₂ v) a proj₂ (λ i q → proj₂)

KQ-ι : ∀ w {m f s φ χ} i {C : Cx m (lim f s) φ χ} → KQ w (lim f s) C → Nd C → KQ w (f i) (pι (self i) C)
KQ-ι g₀ i c n = n , c
KQ-ι g₁ i {C} v n = VisQ-≈ (n , cxQ v) (shE-≈ (self i) (ctxᶜ-refl C (cxQ v)) (inj₁ n) (dh C)) (Vis-shl i v)
KQ-ι g₂ i {C} v n = VisQ-≈ (n , cxQ v) (shE-≈ (self i) (ctxᶜ-refl C (cxQ v)) (inj₁ n) (dh C)) (Vis-shl i v)

-- `omk` 的值是 sh 下的值 (不要求 R)
sh≡D : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (d : Dd C) (z : Q m k φ χ) (x : Q m ℓ φ χ) → runᶜ (shD r C d) z ≡ runᶜ C (omk r (intoU (◃₁→◃ r) z) x)
sh≡D {m = n} zero (pD {q = qd} C) d z x = run-wkC (λ e → e) (⇑ (cap-map n (tighten zero))) C (ι↓ qd z)
sh≡D {m = n} (self i) (pD {q = qd} C) d z x = run-wkC (λ e → e) (⇑ (cap-map n (tighten (self i)))) C (ι↓ qd z)
sh≡D zero (ptr (s≅ e) C) d z x = sh≡D zero C d (trQ e z) (trQ (s≅ e) x)
sh≡D (self i) (ptr (l≅ h) C) d z x = sh≡D (self i) C d (trQ (h i) z) (trQ (l≅ h) x)
sh≡D zero (ptr⁻ (s≅ e) C) d z x = sh≡D zero C d (tr⁻Q e z) (tr⁻Q (s≅ e) x)
sh≡D (self i) (ptr⁻ (l≅ h) C) d z x = sh≡D (self i) C d (tr⁻Q (h i) z) (tr⁻Q (l≅ h) x)

sh≡E : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (u : Nd C ⊎ Dd C) (z : Q m k φ χ) → runᶜ (shE r C u) z ≡ runᶜ C (Up r z)
sh≡E zero C (inj₁ n) z = sym (nd-omk zero C n z (ι zero z))
sh≡E (self i) C (inj₁ n) z = sym (nd-omk (self i) C n z (ι (self i) z))
sh≡E zero C (inj₂ d) z = sh≡D zero C d z (ι zero z)
sh≡E (self i) C (inj₂ d) z = sh≡D (self i) C d z (ι (self i) z)

Up-congᵗ : ∀ {m k ℓ φ χ ψ ρ} (r : k ◃₁ ℓ) {z : Q m k φ χ} {z′ : Q m k ψ ρ} → z ⊑ᵗ z′ → Up r z ⊑ᵗ Up r z′
Up-congᵗ r {z} {z′} h {C} {C′} o G G′ =
  ⊑-trans (proj₂ (proj₂ J)) (⊑-trans (h (sh-≈ r o) (proj₁ J) (proj₁ K)) (proj₁ (proj₂ K)))
  where
  J = pull≅ (sh≡E r C (dh C) z) G
  K = pull≅ (sh≡E r C′ (dh C′) z′) G′

XG′ : Ht → Set₁
XG′ m = ∀ w → inp w ≡ w → ∀ k → Gq w m k (KQ w k) (Ω̇ m k)

-- 链行第 0 项: 1
G-𝟏L : ∀ w {m} → Gq w m zero 𝓥 (𝟏L {m})
G-𝟏L w = gw 𝓥 (λ {C} c → Ctx-wkC C c)
  (gs 𝓥 (λ c → c) g0 (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ _ _ → (λ ()) , (λ i q ())) (λ c → Hq-zero _))

G-rowL : ∀ w {m} F (qs₁ : ∀ i → F i <ᴸ m) → (∀ {n} → n <ᴸ m → XG′ n) → ∀ i → Gq w m zero 𝓥 (rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i)
G-rowL w F qs₁ I zero = G-𝟏L w
G-rowL w {m} F qs₁ I (suc i) = subst (λ X → Gq w m zero 𝓥 (stepL (qs₁ i) X)) (sym (ΩI≡ (qs₁ i))) (BrM.G-stepL (qs₁ i) w (I (qs₁ i)))

mono-rowL : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → (∀ i → F i <ᴸ F (suc i)) → ∀ i → rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i ⊑ᵗ rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) (suc i)
mono-rowL {m} F qs₁ asc zero = subst (λ X → 𝟏L {m} ⊑ᵗ stepL (qs₁ 0) X) (sym (ΩI≡ (qs₁ 0)))
  (⊑ᵀ→ᵗ R-𝟏L (wk-lᵀ (wk-rᵀ (𝟏-D {qd = qs₁ 0} (𝟏⊑Ω̇ (F 0) zero)))))
mono-rowL {m} F qs₁ asc (suc i) = subst₂ (λ X Y → stepL (qs₁ i) X ⊑ᵗ stepL (qs₁ (suc i)) Y) (sym (ΩI≡ (qs₁ i))) (sym (ΩI≡ (qs₁ (suc i))))
  (subst (λ q₀ → stepL q₀ (Ω̇ (F i)) ⊑ᵗ stepL (qs₁ (suc i)) (Ω̇ (F (suc i)))) (<-prop (tr< (asc i) (qs₁ (suc i))) (qs₁ i)) (step-mono (asc i) (qs₁ (suc i))))

rowG : ∀ w m → (∀ {n} → n <ᴸ m → XG′ n) → (v : View _<ᴸ_ h₀ m) → view m ≡ v → Gq w m zero (KQ w zero) (rowV m (ΩI m) v)
rowG w _ I base _ = Gmono (KQ→Ctx w) Ω̇G₀
rowG w m I (clos q) _ = subst (λ X → Gq w m zero (KQ w zero) (rowC q X)) (sym (ΩI≡ q)) (Gmono (KQ→Ctx w) (BrM.G-rowC q w (I q)))
rowG w m I (chain F qs₁) ev = Gmono (KQ→Ctx w) (gl (G-rowL w F qs₁ I) (mono-rowL F qs₁ (proj₁ (subst (ViewOk _<ᴸ_ h₀ m) ev (view-ok m)))))

FG′ : ∀ m → (∀ {n} → n <ᴸ m → XG′ n) → XG′ m
FG′ m I w iw zero = rowG w m I (view m) refl
FG′ m I w iw (suc k) =
  gΩ (λ ξ ζ → KQ w (suc k))
     (λ ξ ζ c x o → KQ-≈ w x o c)
     (λ ξ ζ D → sh zero (wkC proj₁ (Lζ ζ) D))
     (λ ξ ζ {C} c u ru → subst (λ v → runᶜ (sh zero (wkC proj₁ (Lζ ζ) C)) u ≅ˢ v) (run-wkC proj₁ (Lζ ζ) C (Up zero u))
         (up-run zero (ctxᶜ-refl (wkC proj₁ (Lζ ζ) C) (Ctx-wkC C (KQ→Ctx w c))) ru))
     (λ 𝓔 inc″ ξ ζ z rz₁ gz → Hb 𝓔 inc″ ξ ζ z rz₁ (subst (λ g → Gq g m k ((λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ) z) iw gz))
     (λ ξ ζ c → KQ-sh w c)
     (λ ξ ζ c a _ → KQ-St w c a)
     (λ ξ ξ′ ζ ζ′ x o c → KQ-≈ w x o c)
     (λ u → wk-lᵗ (wk-rᵗ (Up-congᵗ zero u)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-Up zero l))
  where
  Lζ : ∀ ζ → Sub m (lo m ζ ∪ κ Fl) ζ
  Lζ ζ i q e = subst (Ev _) (lo-lt ζ q) (proj₁ e)
  Hb : (𝓔 : ∀ ξ ζ → ClT m (suc k) (ξ ⊔ Fl) (lo m ζ ∪ κ Fl)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → KQ w (suc k) C) → ∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z →
       Gq w m k ((λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ) z → Gq w m (suc k) (𝓔 ξ ζ) (qwk proj₁ (Lζ ζ) (omk zero z (ι zero z)))
  Hb 𝓔 inc″ ξ ζ z rz₁ gz =
    gw 𝓖₁ (λ {D} c₁ → Ctx-wkC D (KQ→Ctx w (inc″ ξ ζ c₁)) , D , c₁ , ctxᶜ-refl (wkC proj₁ (Lζ ζ) D) (Ctx-wkC D (KQ→Ctx w (inc″ ξ ζ c₁))))
      (gm {r = zero} {z = z}
         (zcOf w _ (λ { refl → λ 𝓔′ inc → Gmono (λ { (x , C , c , d , o) →
              let P = inc c in x , proj₁ (proj₂ P) , proj₁ (proj₂ (proj₂ P)) , ≈ᶜ-trans o (shE-≈ zero (proj₂ (proj₂ (proj₂ P))) (inj₂ d) (dh _)) }) gz }))
         rz₁
         (Iota zero {𝓖 = λ C → 𝓖₁ C × Nd C} {𝓧 = (λ D → sh zero (wkC proj₁ (Lζ ζ) D)) ⟪ 𝓔 ξ ζ ⟫ᵀ}
            (λ { ((x , D , c₁ , o) , n) → (n , x) , D , c₁ , shE-≈ zero o (inj₁ n) (dh _) })
            (λ { ((x , _) , n) → x , n })
            gz))
    where
    𝓖₁ : ClT m (suc k) ξ ζ
    𝓖₁ E = Ctxᶜ E × (Σ _ λ D → 𝓔 ξ ζ D × (E ≈ᶜ wkC proj₁ (Lζ ζ) D))
FG′ m I w iw (lim f s) =
  gl (λ i → gm {r = self i} {z = Ω̇ m (f i)}
        (zcOf w _ (λ { refl → λ 𝓔′ inc → Gmono (λ { (x , C , c , d , o) →
             VisQ-≈ x (≈ᶜ-trans o (shE-≈ (self i) (ctxᶜ-refl C (cxQ (inc c))) (inj₂ d) (dh C))) (Vis-shl i (inc c)) }) (FG′ m I g₂ refl (f i)) }))
        (RΩ̇ m (≅ᴵ-refl (f i)))
        (Iota (self i) {𝓖 = λ C → KQ w (lim f s) C × Nd C} {𝓧 = KQ w (f i)} (λ { (c , n) → KQ-ι w i c n }) (λ { (c , n) → KQ→Ctx w c , n }) (FG′ m I w iw (f i))))
     (λ i → Up≤ i (suc i) (s i))

Ω̇G′ : ∀ m → XG′ m
Ω̇G′ m = FG′ m (Rec XG′ FG′ m)

Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)
Ω̇G g m k = Ω̇G′ m (inp g) (inp-idem g) k
```
