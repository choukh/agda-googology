# 值判据 (二): 第 1 行的桥

> **判决: PARTIAL (只到 $\eta=1$).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 闭包行读的是 $\iota_\downarrow(\dot\Omega_n\eta)$, 不是 $\dot\Omega_n\eta$ 本身. 这里证 $\eta=1$ 时两者同值 (`Br₁`). 条件: `Uq`, `n <ᴸ m` 的证明唯一. 三个实例都满足, 见 [ValueJudgeInst](ValueJudgeInst.lagda.md). $\eta=0$ 是 `D-self`.
>
> 对 $\eta\ge2$ 没有证. 差在 `omk`: 高层的节点是 `omk z (ι z)`, `ι↓` 读第一格, `ψᵠ` 读第二格, `Rq` 不记两格的关系. $\eta=1$ 时链点在 `Q n 0`, 那里没有 `omk` 也没有 `qΩ`, 这个问题不出现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Align.ValueJudgeBridge (𝕊 : HtS) (Uq : ∀ {a b} (p q : HtS._<ᴸ_ 𝕊 a b) → p ≡ q) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; subst; subst₂; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ordˢ; toZ)
open import OCF.Free.Eq using (_≈ᴿ_; limR; wkR; toZ-≅; z≅; s≅; l≅; _≅ˢ_; ≅ˢ-trans)
open import OCF.Free.Floor using (Flr; fz; fk; _⊔_; Ev; wk; flo; cvFlo; toFlo; _∼ᶠ_; fz∼; fk∼; ⊔∼; ∼ᶠ-refl; bound-≅)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅)
open import OCF.Free.Tree using (Fl; dupr2)
open import OCF.Align.LadderInfTree 𝕊
open import OCF.Align.LadderInfRel 𝕊
open import OCF.Align.LadderInfDn 𝕊
open import OCF.Align.ValueJudgeLadder 𝕊
open import OCF.Align.ValueJudgeBase
open import OCF.Align.LadderInfMain 𝕊 using (GᴺTᵠ)
```

## §1 `ι` 与 `ι↓`: 第 0 层的链点

`Sim-c`: $n$ 以下的格不受 `cap` 影响.

```agda
Sim-c : ∀ {n} {χ ρ : Fv} {y} → Sim∼ n χ ρ → Sim∼ n χ (cap ρ n y)
Sim-c {n} {χ} {ρ} {y} s i q = subst (χ i ∼ᶠ_) (sym (cap-lt ρ y q)) (s i q)

Dι : ∀ {n m a α φ ψ χ ρ} (r : n <ᴸ m) (q₀ : zero ◃ a) {x : Q n zero φ χ} {x′ : Q n zero ψ ρ} → Rq n zero zero x x′ → Dn r a α (ι q₀ x) (ι↓ {α = α} r x′)
Dι r q₀ rz = dz
Dι r q₀ (rs sa sb d) = ds sa (Sim-c sb) (Dι r q₀ d)
Dι r q₀ (rl h) = dl (λ n → Dι r q₀ (h n))
Dι r q₀ (ri e h) = di e (λ x y d → Dι r q₀ (h x y d))
Dι r q₀ (rŝ e d h) = dŝ e (Dι r q₀ d) (λ η ee η′ e′ dd → Dι r q₀ (h η ee η′ e′ dd))
Dι r q₀ (rĉ e dz′ dg d h) = dĉ e dz′ dg (Dι r q₀ d) (λ η ee η′ e′ dd → Dι r q₀ (h η ee η′ e′ dd))
Dι r q₀ (rclo s d h) = dclo s (Dι r q₀ d) (λ η η′ dd → Dι r q₀ (h η η′ dd))
Dι r q₀ (rcl {q = q} same s d h) = dcl {q = q} s (Dι r q₀ d) (λ η η′ dd → dwkʳ (Dι r q₀ (h η η′ dd)))
Dι r q₀ (rwkˡ d) = dwkˡ (Dι r q₀ d)
Dι r q₀ (rwkʳ d) = dwkʳ (Dι r q₀ d)
Dι {n} {m} {a} {α} r q₀ (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c f) =
  dΩ↓ {q = q} ei s (Sim-c c) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkʳ
    (subst (λ v → Dn r a α (ι q₀ (h ξ ζ (intoV q z))) (ι↓ {α = α} r (h′ ξ′ ζ′ (intoV q v)))) (sym (out-intoV (tr< q r) z′))
       (Dι r q₀ (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l)))))
Dι r q₀ (rΩ {r = ()} ei s c f)
Dι r q₀ (rob {r = ()} ea l d)
```

## §2 `ψᵠ` 与 `Ψ`

`D-ψΨ`: 字面目标的折叠与高度 $n$ 目标的折叠同值, 在 `Dn` 上. `Dn` 没有顶层的 `qΩ`, 所以没有链的情形. 节点 $j<n$ 只有 `tlt` 一支 (`irr`). 这里用到 `Uq`: `ψᵠ` 保留 $j<n$ 的证明, `Ψ` 用 `tri` 算出的证明.

```agda
D-ψΨ : ∀ {m m′ a b t t′ φ χ ψ ρ w′} (δ : m <ᴸ m′) (q : t <ᴵ a) (ok′ : Ok w′) (e′ : Eh m m′ w′ ρ) (p′ : t′ <ᴵ w′ m) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn δ a b x x′ → Rq m t t′ (ψᵠ q x) (Ψ δ ok′ e′ p′ x′)
D-ψΨ {m} δ q ok′ e′ p′ et dz = rwk (RΩ̇ m et)
D-ψΨ δ q ok′ e′ p′ et (ds sa sb d) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ sb) (D-ψΨ δ q ok′ e′ p′ et d))
D-ψΨ δ q ok′ e′ p′ et (dl h) = rl (λ n → D-ψΨ δ q ok′ e′ p′ et (h n))
D-ψΨ δ q ok′ e′ p′ et (di d h) = ri d (λ x y dd → D-ψΨ δ q ok′ e′ p′ et (h x y dd))
D-ψΨ δ q ok′ e′ p′ et (dŝ d r h) = rŝ d (D-ψΨ δ q ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-ψΨ δ q ok′ e′ p′ et (h η ee η′ e₁ dd))
D-ψΨ δ q ok′ e′ p′ et (dĉ d dz′ dg r h) = rĉ d dz′ dg (D-ψΨ δ q ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-ψΨ δ q ok′ e′ p′ et (h η ee η′ e₁ dd))
D-ψΨ δ q ok′ e′ p′ et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (D-ψΨ δ q ok′ e′ p′ et r)) (λ η η′ d → rwk (D-ψΨ δ q ok′ e′ p′ et (h η η′ d))))
D-ψΨ δ q ok′ e′ p′ et (dwkˡ r) = rwkˡ (D-ψΨ δ q ok′ e′ p′ et r)
D-ψΨ δ q ok′ e′ p′ et (dwkʳ {lc′ = lc′} r) = rwkʳ (D-ψΨ δ q ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
D-ψΨ {m} δ q ok′ e′ p′ et (dcl {n = n} {q = q₀} s r h) with tri n m
... | tlt l with Uq q₀ l
...   | refl = rcl {q = q₀} same (⊔∼ (∼ᶠ-refl Fl) s) (D-ψΨ δ q ok′ e′ p′ et r) (λ η η′ d → rwk (D-ψΨ δ q ok′ _ p′ et (h η η′ d)))
D-ψΨ {m} δ q ok′ e′ p′ et (dcl {n = n} {q = q₀} s r h) | teq refl = ⊥-elim (irr q₀)
D-ψΨ {m} δ q ok′ e′ p′ et (dcl {n = n} {q = q₀} s r h) | tgt l = ⊥-elim (irr (tr< l q₀))
D-ψΨ {m} {t = t} {t′} δ q ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q = q₀} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n m
... | tlt l with Uq q₀ l
...   | refl = rΩ↓ {q = q₀} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c)
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst (λ v → Rq m t t′ (ψᵠ q (h ξ ζ (intoV q₀ z))) (Ψ δ ok′ (e-lo ζ′ (inj₂ q₀) e′) p′ (h′ ξ′ ζ′ (intoV (tr< q₀ δ) v)))) (sym (out-intoV q₀ z′))
         (D-ψΨ δ q ok′ (e-lo ζ′ (inj₂ q₀) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq q₀ lz)))))
D-ψΨ {m} δ q ok′ e′ p′ et (dΩ↓ {q = q₀} ek s c f) | teq refl = ⊥-elim (irr q₀)
D-ψΨ {m} δ q ok′ e′ p′ et (dΩ↓ {q = q₀} ek s c f) | tgt l = ⊥-elim (irr (tr< l q₀))
```

## §3 `Br₁`

```agda
module Br {n m : Ht} (r : n <ᴸ m) {w : Ht → Ordᴵ} (ok : Ok w) (e : Eh h₀ m w (cap (κ Fl) n (flo (suc zero)))) where
  χ₁ : Fv
  χ₁ = cap (κ Fl) n (flo (suc zero))

  ac₁ : ∀ {L} → Ev L (χ₁ n) → zero <ᴵ L
  ac₁ u = cvFlo (suc zero) (subst (Ev _) (cap-self (κ Fl) n _) u) zero

  P₁ : zero <ᴵ w n
  P₁ = ac₁ (e↓ e n (inj₁ refl) r)

  E₁ : Eh n m w (lo n (Z* χ₁) ∪ χ₁)
  E₁ = e⁺ n ok (e↓ e)

  h↓ : ∀ ξ ζ → Q n zero ξ ζ → Q m zero (ξ ⊔ Fl) (lo n ζ ∪ χ₁)
  h↓ ξ ζ z = qwk (λ u → u) (⇑ (c-∪ {lo n ζ} {κ Fl} n)) (ι↓ r (Hs n zero ξ ζ z))

  stepV : Q n zero Fl (Z* χ₁) → Q n zero Fl (Z* χ₁)
  stepV v = qwk (λ u → u , (u , u)) (⇑ (cv* n)) (Ψ r ok E₁ P₁ (h↓ Fl (Z* χ₁) v))

  chD↓ : ℕ → Q n zero Fl (Z* χ₁)
  chD↓ = chainᵠ (λ u → u) fc* (λ z → stepV (outV r (intoV r z)))

  chain-↓ : ∀ i → Rq n zero zero (chL n zero i) (chD↓ i)
  chain-↓ zero = rwk (RΩ̇ n z≅)
  chain-↓ (suc i) =
    subst (λ v → Rq n zero zero (chL n zero (suc i)) (stepV v)) (sym (out-intoV r (chD↓ i)))
      (rwk (rwk (rwkʳ (rwkʳ (D-ψΨ r zero ok _ P₁ z≅ (Dι r zero (chain-↓ i)))))))

  term↓ : ∀ {c c′} → Rq n zero zero c c′ → (E : Eh h₀ n w₀ (lo n Zκ ∪ κ Fl)) (E′ : Eh h₀ m w (lo n (Z* χ₁) ∪ χ₁)) →
          ψ̄ᵠ ok₀ E (Hs n zero Fl Zκ c) ≈ᴿ ψ̄ᵠ ok E′ (h↓ Fl (Z* χ₁) c′)
  term↓ {c} {c′} rc E E′ =
    wkR {R = ψ̄ᵠ ok₀ (λ i h r′ → subst (Ev _) (lo-lt Zκ r′) (proj₁ (E i h r′))) (ι zero c)}
        {R′ = ψ̄ᵠ ok (λ i h r′ → ⇑ (c-∪ {lo n (Z* χ₁)} {κ Fl} n) i r′ (E′ i h r′)) (ι↓ r (Hs n zero Fl (Z* χ₁) c′))}
        proj₁ (λ u → u)
        (D→≈ᵠ {δ = r} {x = ι zero c} {x′ = ι↓ r (Hs n zero Fl (Z* χ₁) c′)} (dwkʳ (dwkʳ (Dι r zero rc)))
              ok₀ (λ i h r′ → subst (Ev _) (lo-lt Zκ r′) (proj₁ (E i h r′)))
              ok (λ i h r′ → ⇑ (c-∪ {lo n (Z* χ₁)} {κ Fl} n) i r′ (E′ i h r′)))

  Br₁ : ψ̄ᵠ ok₀ e₀ (Ω̇ n (suc zero)) ≈ᴿ ψ̄ᵠ ok e (Ωd r (suc zero))
  Br₁ = limR {F = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok₀ (e⁺ n ok₀ e₀) (Hs n zero Fl Zκ (chL n zero i)))}
             {G = λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ n ok e) (h↓ Fl (Z* χ₁) (outV r (intoV r (chD↓ i)))))}
             (λ i → wkR (λ v → v , v) (λ v → v , v)
               (subst (λ v → ψ̄ᵠ ok₀ (e⁺ n ok₀ e₀) (Hs n zero Fl Zκ (chL n zero i)) ≈ᴿ ψ̄ᵠ ok (e⁺ n ok e) (h↓ Fl (Z* χ₁) v)) (sym (out-intoV r (chD↓ i)))
                  (term↓ (chain-↓ i) (e⁺ n ok₀ e₀) (e⁺ n ok e))))

-- 第 1 行的值
V₁-F : ∀ {n m} (r : n <ᴸ m) → IsF r (suc zero) (V n (suc zero))
V₁-F {n} r ok e G = ≅-trans (forceᴺ-≅ (≅ᶻ-sym′ (toZ-≅ (Br.Br₁ r ok e ev₀ zero ev₀ zero z≅))) G (GV n (suc zero))) (V-G n (suc zero) (GV n (suc zero)))
  where open import OCF.Free.Eq using () renaming (≅ᶻ-sym to ≅ᶻ-sym′)

V₁≺ : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → V n (suc zero) ≺ᵛ V m zero
V₁≺ r ev = clos-first≺ r ev (V₁-F r)
```
