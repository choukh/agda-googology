# 紧界树比值 (五): 旧地板的树没有证书, 这不是值错

> [TightVal](TightVal.lagda.md) 的第五篇. 对象是 [Uniform2Base](Uniform2Base.lagda.md) 的统一树 `ψᵀ (Ψ (Ψ ∅ᵀ))`. [OmegaSqA](OmegaSqA.lagda.md) 的 `¬TΩ2-label` 否定的是 "带证书且带标签 $\psi_0(\Omega_\Omega^2)$". 这里去掉标签.
>
> **`no-cert`: 对一切环境, 旧地板的统一树没有 `Goodᴺ`.** 不是值小, 是树没有值: 闭包 $\psi_0(\psi_\Omega(\Omega_{L_1}))$ 的后代, 第 2 份副本的 $\Omega_\Omega$ 弹栈界是 $L_1+1$, 而第 0 点 $\psi_0(\Omega_\Omega+\Omega)$ 的层号 $\prec L_1$. `Goodᴺ` 的字段 `dy 0` 就是 $L_1+1\sqsubseteq$ 这个层号, 假.
>
> 证明是 `OmegaSqA.Refute` 换证书: 标签原来由假设给, 这里第 0 点的标签由 `TΩ1-label` 的同类定理与 `pΩ-label` 给, 再由 `forceᴺ-≅` 搬到任意证书. 读记号的只有这一处读标签, 它用来算层号的序. 定理的陈述不提记号.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValFloor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.EBO using (T; fsn; natT; Ωt)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅)
open import OCF.Align.Bachmann using (gt→<)
open import OCF.Align.Stage2Label using (Lab-oc)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.UniformS using (z≅; _≅ᶻ_; toZ-≅)
open import OCF.Align.GoodLBase using (Goodᴸ; forceᴸ)
open import OCF.Align.NotFree using (Goodᴺ; gs; gl; gc; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2Depth1 using (wkL0)
open import OCF.Align.Uniform2 using (LΩ1; nf-pΩ; pΩ-label; Ω̂ᵀ)
open import OCF.Align.OmegaExp using (tΩ1-NF)
open import OCF.Align.OmegaSqBase using ()
open import OCF.Align.RelativeBase using (one)
open import OCF.Align.Relative
open import OCF.Align.OmegaSqABase
open import OCF.Align.OmegaSqA
open GA1ᴴ
```

## §1 闭包的反演

```agda
closureᴺ : ∀ {c t₀ g} → Goodᴺ (toZ (Ord₊ˢ.ŝ c t₀ g)) →
           Σ (Goodᴺ (toZ t₀)) λ G₀ → Σ (Ordᶜ zero) λ Y → Σ (HS Y) λ hY → (forceᴺ _ G₀ ≅ Y) ×
           Σ (c ⊑ᴵ toLevel Y hY) λ e → Goodᴺ (toZ (g (toLevel Y hY) e))
closureᴺ (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = G₀ , ys 0 , hy 0 , l₀ , dy 0 , Go 0

relabel : ∀ {x : Ordˢ zero} {u Y} → toZ x ≅ᶻ toZ x → (G : Goodᴺ (toZ x)) → forceᴺ _ G ≅ Y → Lab₀ x u → Lab Y u
relabel rt G e (G′ , l) = Lab-≅ (≅-trans (≅-sym e) (≅-trans (forceᴺ-≅ rt G (ofL G′)) (ofL-≅ G′))) l
```

## §2 沿路径下降

与 `Refute` 同一条路 $[0,1,0,0,0]$, 假设从 `Lab₀` 换成 `Goodᴺ`.

```agda
module RefuteN (Y₀ : Ordᶜ zero) (hY₀ : HS Y₀) (lY₀ : Lab Y₀ θ₁) where
  open Refute Y₀ hY₀ lY₀ using (L₀; pos)

  Hyp : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ)
        (Y : Ordᶜ zero) (hY : HS Y) (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Set
  Hyp ℓ σ₁ σ₂ p Y hY cv = Goodᴺ (toZ (fold 1 (fk L₀) cv (Ω̂A 0) (Ωˢ (toLevel Y hY)) ∅ᴿ (tt , (σ₁ , σ₂)) p))

  leaf : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y [] →
         (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  leaf ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  leaf ℓ σ₁ σ₂ p Y hY (lω () e h) cv H
  leaf ℓ σ₁ σ₂ p Ord₊.zero hY (l0 c z≅) cv (gl G st) = ≺ᴵ-irrefl (≺ᴵ-trans L≺Z Z≺L)
    where
    Q : Run (fz ⊔ (fk zero ⊔ fk L₀))
    Q = wk 0 (λ { (u , v) → u , proj₁ v }) (Ω̂A 0 ∅ᴿ)
    HQ : Q ≈ᴬ Q
    HQ = wkRᴬ (λ { (u , v) → u , proj₁ v }) (λ { (u , v) → u , proj₁ v }) (selfΩ̂0ᴬ fz∼ ∅ᴿ-ᴬ)
    ev₁ : Ev ℓ ((fz ⊔ (fk zero ⊔ fk L₀)) ⊔ fk zero)
    ev₁ = (tt , (σ₁ , σ₂)) , σ₁
    t₀′ : Ordˢ zero
    t₀′ = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) ev₁ p
    rt : toZ t₀′ ≅ᶻ toZ t₀′
    rt = toZ-≅ (≅ᴬ→≅ˢ₀ (fold-≅0ᴬ {P = Q} {P′ = Q} HQ (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))) ev₁ p ev₁ p z≅))
    info = closureᴺ {c = suc (Mx (bound ((fz ⊔ (fk zero ⊔ fk L₀)) ⊔ fk zero) ev₁ p))} {t₀ = t₀′} (G 2)
    G₀ = proj₁ info
    Zc : Ordᶜ zero
    Zc = proj₁ (proj₂ info)
    hZ : HS Zc
    hZ = proj₁ (proj₂ (proj₂ info))
    eZ : forceᴺ _ G₀ ≅ Zc
    eZ = proj₁ (proj₂ (proj₂ (proj₂ info)))
    dZ : suc (Mx (bound ((fz ⊔ (fk zero ⊔ fk L₀)) ⊔ fk zero) ev₁ p)) ⊑ᴵ toLevel Zc hZ
    dZ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ info))))
    Q₂ : Run (fz ⊔ (fk zero ⊔ fz))
    Q₂ = Ω̂ᵀ 0 ∅ᴿ
    HQ₂ : Q ≈ᴬ Q₂
    HQ₂ = wkRᴬ (λ { (u , v) → u , proj₁ v }) (λ { (u , v) → u , proj₁ v }) (selfΩ̂0ᴬ fz∼ ∅ᴿ-ᴬ)
    evQ₂ : Ev ℓ ((fz ⊔ (fk zero ⊔ fz)) ⊔ fk zero)
    evQ₂ = (tt , (σ₁ , tt)) , σ₁
    evL : Ev ℓ (fz ⊔ ((fk zero ⊔ fz) ⊔ fk zero))
    evL = tt , ((σ₁ , tt) , σ₁)
    LZ₀ = pΩ-label evL p
    rt₂ : toZ t₀′ ≅ᶻ toZ (ψᵀ (Ω̂ᵀ ⊕ tlᵀ (flo (suc zero)) (cvFlo (suc zero)) (Ωˢ (suc zero))) evL p)
    rt₂ = toZ-≅ (≅ᴬ→≅ˢ₀ (fold-≅0ᴬ {P = Q} {P′ = Q₂} HQ₂ (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))) ev₁ p evQ₂ p z≅))
    lZ : Lab Zc (ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1)))
    lZ = Lab-≅ (≅-trans (≅-sym eZ) (≅-trans (forceᴺ-≅ rt₂ G₀ (ofL (proj₁ LZ₀))) (ofL-≅ (proj₁ LZ₀)))) (proj₂ LZ₀)
    Z≺L : toLevel Zc hZ ≺ᴵ L₀
    Z≺L = toLevel-≺ hZ hY₀ (Lab-oc lY₀ tΩ1-NF lZ nf-pΩ (gt→< θ₁ _ refl))
    L≺Z : L₀ ≺ᴵ toLevel Zc hZ
    L≺Z = ≺ᴵ-respˡ (≅ᴵ-sym (subst (λ M → M ≅ᴵ L₀) (sym (MxL tt σ₁ σ₂ σ₁ p (via z≅ pos))) (≅ᴵ-refl L₀)))
                   (sim dZ zero)

  step₄ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn (fsn (fsn θ₁ 0) 1) 0) 0) →
          (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  step₄ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₄ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₄ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv (gl G st) =
    leaf ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (G 0)

  step₃ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn (fsn θ₁ 0) 1) 0) →
          (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  step₃ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₃ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₃ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv (gl G st) =
    step₄ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (G 0)

  step₂ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn θ₁ 0) 1) →
          (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  step₂ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₂ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₂ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv (gl G st) =
    step₃ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (G 0)

  step₁ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn θ₁ 0) →
          (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  step₁ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₁ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₁ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv (gl G st) =
    step₂ ℓ σ₁ σ₂ p (F 1) (hl₁ hY 1) (Lab-≅ (k 1) (h 1)) (λ e q → cv e (lim 1 q)) (G 1)

  step₀ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y θ₁ →
          (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv → ⊥
  step₀ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₀ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₀ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv (gl G st) =
    step₁ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (G 0)

  refuteN : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk L₀))) (p : zero <ᴵ ℓ) → Goodᴺ (toZ (Branch L₀ ∅ᴿ ev p)) → ⊥
  refuteN {ℓ} ev p H = step₀ ℓ (proj₁ (proj₂ ev)) (proj₂ (proj₂ ev)) p Y₀ hY₀ lY₀ (λ e q → e (suc q)) H
```

## §3 统一树

```agda
F1 : GA1ᴴ (fold 1 (fk zero) (λ e → e) (Ω̂A 0) (Ωˢ (suc zero))) ([] ++ Ωt (natT 1))
F1 = Depth1ᴴ.Full₊ goodΩ̂₀ᴴ FP0-z (⊑-suc one) LΩ1 (Ωˢ-≅ᴬ (≅ᴵ-refl _))

no-cert : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z)) → ⊥
no-cert {ℓ} ev z G = RefuteN.refuteN Y₁ hY₁ lY₁ _ _ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ info)))))
  where
  evT : Ev ℓ (fz ⊔ (fk zero ⊔ fk zero))
  evT = proj₁ ev , (proj₁ (proj₂ ev) , proj₁ (proj₂ (proj₂ ev)))
  t₀ : Ordˢ zero
  t₀ = fold 1 (fk zero) (λ e → e) (Ω̂A 0) (Ωˢ (suc zero)) ∅ᴿ evT z
  rt : toZ t₀ ≅ᶻ toZ t₀
  rt = toZ-≅ (≅ᴬ→≅ˢ₀ (gRᴬ (gv1ᴴ F1 ∅ᴿ-good) evT z evT z z≅))
  info = closureᴺ {t₀ = t₀} G
  Y₁ = proj₁ (proj₂ info)
  hY₁ = proj₁ (proj₂ (proj₂ info))
  lY₁ : Lab Y₁ θ₁
  lY₁ = relabel rt (proj₁ info) (proj₁ (proj₂ (proj₂ (proj₂ info)))) (g01ᴴ F1 ∅ᴿ-good evT z tΩ1-NF)
```
