# 树侧判据 (二): 闭包以下的折叠, 目标在闭包之下, 世界任意 (底座)

> 不含记号. 结论写在 [TreeJudge2](TreeJudge2.lagda.md). 这是 [GuardTightCert](GuardTightCert.lagda.md) 的 `R-ψ` 在 $\psi_0(\Omega_{\Omega+1})$ 这棵树 (`Fold (suc c₁)`, **任意读法** `tc`) 上的版本, 只对上下文为空的状态. 用途: 两个头在不同的世界, 不同的目标下算出来, 都 $\cong^{\mathsf z}$ 同一棵 `toZ` 的树 (`head-≅`), 所以头律可以在它们之间搬运.
>
> 与 `R-ψ` 的差别: (1) 层是 `suc c₁`; (2) `Full` 换成 `Emp π`; (3) `Tgt` 的 $t\approx\lceil i\rceil$ 排除了目标是 $\Omega$ 本身. 这些头的计算里上下文确实是空的, 因为闭包 `Ω̇ c₁` 由 `ψ o0` 带着空上下文长出来 (`owk (λ ())`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2Rel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.GuardTightCum hiding (ψ)
open import OCF.Free.Prefix using (Z; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; Ωˢ; toZ; _≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ)
open Ord₊ˢ
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo; bound; Bd; Fc; iF; FM)
import OCF.Free.Tree as FT
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightCertRel
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁; Fr; FrL→Fr; Fr-c₁; rep-rel; Rz)
```

## §1 这棵树

```agda
L₁ : LG
L₁ = Lv.suc c₁

tcI : Tc L₁
tcI = Tc-id c₁

sfL : L₁ ≈ L₁
sfL = Lv.s≈ sf₁

module RelT (tc : Tc L₁) where
  open Fold L₁ wf₁ sfL tc

  -- 空上下文上, 证据总是齐全的 (路径上的 `bra` 要一个帧)
  toTab-emp : ∀ {E ρ π} (st : St E ρ π) → Emp π → ∀ {a b} (r : a < b) (x : Adm (cov π) r) → Σ _ λ a′ → Vis.toTab st r x ≡ just a′
  toTab-emp st em′ Lv.zero x = tt , refl
  toTab-emp st em′ (Lv.suc r) x = toTab-emp st em′ r x
  toTab-emp st em′ (Lv.lim n r) x = toTab-emp st em′ r x
  toTab-emp st em′ (Lv.fst r) x = toTab-emp st em′ r x
  toTab-emp st em′ (Lv.bra η e r) ((c₂ , t₂ , g₂ , e₁ , m , k) , x) = ⊥-elim (em′ m)
```

## §2 比较不给 `cj`

与 [GuardTightCert](GuardTightCert.lagda.md) 的 `NJM` 同一个骨架. `bra` 对 `bra` 这一行由空上下文排除. 目标不是节点 $\Omega$ 本身, 所以 `suc` 层的 `zero` 行由 $t\approx\lceil i\rceil$ 排除 (`notΩ`).

```agda
  notΩ : ∀ {i} → c₁ ≈ ⌜ i ⌝ → ⊥
  notΩ {i = zero} ()
  notΩ {i = suc i} ()
  notΩ {i = lim f s} ()

  module NJE {E : Ents} {ρ π : Fl} (st : St E ρ π) (em′ : Emp π) where
    open Vis st

    toOut-free : ∀ {b} → FrL b → ∀ {a} (r : a < b) (x : Adm (cov π) r) → Σ _ λ a′ → toOut r x ≡ just a′
    toOut-free (fs′ h) Lv.zero x = tt , refl
    toOut-free (fs′ h) (Lv.suc r) x = toOut-free h r x
    toOut-free (fl h) (Lv.lim n r) x = toOut-free (h n) r x

    NJ : ∀ {k t} → CN k t → Set
    NJ (cb _ _ _) = ⊤
    NJ (cu _) = ⊤
    NJ cj = ⊥

    shlJ : ∀ {k k′ t} (e : k ≈ k′) (x : CN k′ t) → NJ x → NJ (shl e x)
    shlJ e (cb d s a) h = tt
    shlJ e (cu (inj₁ d)) h = tt
    shlJ e (cu (inj₂ (pre d s))) h with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ _ = tt

    shrJ : ∀ {k t t′} (e : t ≈ t′) (x : CN k t′) → NJ x → NJ (shr e x)
    shrJ e (cb d s a) h with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ u = tt
    shrJ e (cu (inj₁ d)) h = tt
    shrJ e (cu (inj₂ (pre d s))) h = tt

    cmpNJ : ∀ {c′} (w : WFˢ c′) (s : c′ ≈ c′) → Fr c′ → ∀ {k t} (r : k < c′) (q : t < c′) (cv : Adm (cov π) r) (aq : Adm (tab E) q) → NJ (cmpN w s r q cv aq)
    cmpNJ w (Lv.s≈ e) fr Lv.zero Lv.zero _ _ = tt
    cmpNJ w (Lv.s≈ e) fr Lv.zero (Lv.suc q) _ _ = tt
    cmpNJ w (Lv.s≈ e) fr (Lv.suc r) Lv.zero cv _ with toOut r cv | toOut-free fr r cv
    ... | just a | a , refl = tt
    cmpNJ w (Lv.s≈ e) fr (Lv.suc r) (Lv.suc q) cv aq = cmpNJ w e (FrL→Fr fr) r q cv aq
    cmpNJ (st′ , w) (Lv.l≈ e) fr (Lv.lim n r) (Lv.lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
    ...   | viaᴸ d r′ u = shlJ d _ (cmpNJ (w m) (e m) (fr m) r′ q (u (cov π) cv) aq)
    cmpNJ (st′ , w) (Lv.l≈ e) fr (Lv.lim n r) (Lv.lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = shrJ d _ (cmpNJ (w n) (e n) (fr n) r q′ cv (u (tab E) aq))
    cmpNJ (st′ , w) (Lv.l≈ e) fr (Lv.lim n r) (Lv.lim _ q) cv aq | injᶜ refl = cmpNJ (w n) (e n) (fr n) r q cv aq
    cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.fst r) (Lv.fst q) cv aq = cmpNJ wt se (proj₁ fr) r q cv aq
    cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.fst r) (Lv.bra y e q) cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shlJ d′ _ (cmpNJ (wg y e) (sh y e y e (≅ᴰ-refl y)) (proj₂ fr y e) r′ q (u (cov π) cv) aq)
    cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.bra x e₁ r) (Lv.fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shrJ d′ _ (cmpNJ (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) (proj₂ fr x e₁) r q′ cv (u (tab E) aq))
    cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.bra x e₁ r) (Lv.bra y e₂ q) ((c₃ , t₃ , g₃ , e₃ , m , k) , cv) aq = ⊥-elim (em′ m)
```

## §3 折叠

```agda
  data Tgt {E : Ents} : ∀ {t} → Tg E t → Ordᴵ → Set where
    tg0 : Tgt t0 zero
    tgp : ∀ {t i} {q : t < L₁} {aq : Adm (tab E) q} → t ≈ ⌜ i ⌝ → Tgt (tp q aq) i

  teq : ∀ {E t i} {T : Tg E t} → Tgt T i → t ≈ ⌜ i ⌝
  teq tg0 = Lv.z≈
  teq (tgp e) = e

  R-ψ₁ : ∀ {k₀ π ρ t i} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (em′ : Emp π) {x : O L₁ π} {ŷ : Ordˢ k₀} → Rs k₀ x ŷ →
         (φ : Flr) (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) (ℓ : Ordᴵ) (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) →
         Rs i (ψ E T st x) (FT.ψ̄ (FT.tl {c = zero} φ cv ŷ) ev₁ p)

  module RiseM {k₀ π ρ t i k j} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (em′ : Emp π)
               (r : k < L₁) (cv′ : Adm (cov π) r) (q : j <ᴵ k₀) {h : ∀ ξ → Us L₁ r ξ → O L₁ (ξ ∪ π)} {f : Uˢ j (<→◃ q) → Ordˢ k₀}
               (dk : k ≈ ⌜ j ⌝)
               (prem : ∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → LRs k₀ (<→◃ q) z ẑ → Rs k₀ (h ξ (intoU r z)) (f (intoˢ (<→◃ q) ẑ)))
               (φ : Flr) (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) (ℓ : Ordᴵ) (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) where
    h̃ : Ordˢ j → ∀ {i′ ℓ′} → Ev ℓ′ φ → i′ <ᴵ ℓ′ → Ordˢ i′
    h̃ x e₀ p₀ = FT.ψ̄ (FT.tl {c = zero} φ cv (f (intoˢ (<→◃ q) x))) e₀ p₀

    A′ : j <ᴵ ℓ
    A′ = cv ev₁ q

    rise-rel : Rs i (riseΩ E T st r cv′ h) (Ord₊ˢ.lim (λ m → h̃ (iter (λ x → h̃ x ev₁ A′) (Ωˢ j) m) ev₁ p))
    rise-rel with Vis.toTab st r cv′ | toTab-emp st em′ r cv′
    ... | just a | a , refl with nfT L₁ tc r | trim π st {r} a
    ...   | nft d r′ tb | mkTr ξ w bk = rl (λ n → R-ψ₁ E T tg (stBody ξ w st) body-em (prem ξ em₁ _ _ (intoR (<→◃ q) (ch n))) φ cv ℓ ev₁ p)
      where
      em₁ : Emp ξ
      em₁ m = em′ (w m)
      body-em : Emp (ξ ∪ π)
      body-em (ml m) = em′ (w m)
      body-em (mr m) = em′ m
      ch : ∀ n → Rs j (chainᵒ (Tc-at r tc) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n) (iter (λ x → h̃ x ev₁ A′) (Ωˢ j) n)
      ch zero = rwk (RΩ̇ j dk (Tc-at r tc))
      ch (suc n) = R-trL⁻ d (R-ψ₁ E (tp r′ (tb E a)) (tgp (lk≈ d dk)) (stChain ξ bk w st) body-em (prem ξ em₁ _ _ (intoR (<→◃ q) (ch n))) φ cv ℓ ev₁ A′)

  R-ψ₁ {t = t} {i = i} E T tg st em′ rz φ cv ℓ ev₁ p = rwk (RΩ̇ i (teq tg) (tcT T))
  R-ψ₁ E T tg st em′ (rs r) φ cv ℓ ev₁ p = rl (rep-rel (R-ψ₁ E T tg st em′ r φ cv ℓ ev₁ p))
  R-ψ₁ E T tg st em′ (rl h) φ cv ℓ ev₁ p = rl (λ n → R-ψ₁ E T tg st em′ (h n) φ cv ℓ ev₁ p)
  R-ψ₁ E T tg st em′ (rwk {w = w} r) φ cv ℓ ev₁ p = R-ψ₁ E T tg (λ m → st (w m)) (λ m → em′ (w m)) r φ cv ℓ ev₁ p
  R-ψ₁ E T tg st em′ (rcv {π = π′} {w = w} r) φ cv ℓ ev₁ p with lowerSt π′ w st
  ... | σ , st′ , c′ = rcv (R-ψ₁ E T tg st′ (λ m → em′ (proj₁ (proj₂ (w m)))) r φ cv ℓ ev₁ p)
  R-ψ₁ E T tg st em′ (rmk r l x) φ cv ℓ ev₁ p = R-ψ₁ E T tg st em′ x φ cv ℓ ev₁ p
  R-ψ₁ {k₀ = suc k′} E T tg st em′ (rup zero l) φ cv ℓ ev₁ p =
    R-ψ₁ E T tg st em′ l (flo k′) (cvFlo k′) ℓ (toFlo k′ (λ q → cv ev₁ (suc q))) p
  R-ψ₁ {k₀ = lim g s} E T tg st em′ (rup (self n) l) φ cv ℓ ev₁ p =
    R-ψ₁ E T tg st em′ l (flo (g n)) (cvFlo (g n)) ℓ (toFlo (g n) (λ q → cv ev₁ (lim n q))) p
  R-ψ₁ E t0 tg0 st em′ (rΩ r cv′ q {h = h₁} {f = f} dk prem) φ cv ℓ ev₁ p with <ᴵ-dec (cv ev₁ q) p
  ... | injᵃ (via e ())
  ... | injᵇ _ = RiseM.rise-rel E t0 tg0 st em′ r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
  ... | injᶜ _ = RiseM.rise-rel E t0 tg0 st em′ r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
  R-ψ₁ E (tp Lv.zero aq₁) (tgp et) st em′ (rΩ r cv′ q dk prem) φ cv ℓ ev₁ p = ⊥-elim (notΩ et)
  R-ψ₁ E (tp (Lv.suc q₁) aq₁) (tgp et) st em′ (rΩ Lv.zero cv′ q dk prem) φ cv ℓ ev₁ p = ⊥-elim (notΩ dk)
  R-ψ₁ {i = i} E (tp (Lv.suc q₁) aq₁) (tgp et) st em′ (rΩ {k = k} {j = j} (Lv.suc r₀) cv′ q {h = h₁} {f = f} dk prem) φ cv ℓ ev₁ p
    with Vis.cmpN st wf₁ sfL (Lv.suc r₀) (Lv.suc q₁) cv′ aq₁ | NJE.cmpNJ st em′ wf₁ sf₁ Fr-c₁ r₀ q₁ cv′ aq₁ | <ᴵ-dec (cv ev₁ q) p
  ... | Vis.cb d s a | _ | injᵃ (via e r₂) =
    rΩ s a r₂ (≈-trans (≈-sym d) (≈-trans dk (⌜≈⌝ e)))
       (λ ξ em₁ z ẑ l → subst₂ (λ u v → Rs i (ψ E (tp (Lv.suc q₁) aq₁) (stξ ξ st) (h₁ ξ (intoU (Lv.suc r₀) (tr⁻O d u)))) (FT.ψ̄ (FT.tl {c = zero} φ cv (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) ev₁ p))
                                (sym (out-intoU s z)) (sym (out-intoˢ (<→◃ r₂) ẑ))
                                (R-ψ₁ E (tp (Lv.suc q₁) aq₁) (tgp et) (stξ ξ st) (λ { (ml m) → em₁ m ; (mr m) → em′ m })
                                     (prem ξ em₁ _ _ (intoR (<→◃ q) (R-tr⁻ˢ e (R-tr⁻O d (outR (<→◃ r₂) l))))) φ cv ℓ ev₁ p))
  ... | Vis.cb d s a | _ | injᵇ w = ⊥-elim (clash (cb-sem et dk d s) (inj₁ w))
  ... | Vis.cb d s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem et dk d s) (inj₂ (≅ᴵ-sym c′)))
  ... | Vis.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem et dk x))
  ... | Vis.cu x | _ | injᵇ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq₁) (tgp et) st em′ (Lv.suc r₀) cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
  ... | Vis.cu x | _ | injᶜ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq₁) (tgp et) st em′ (Lv.suc r₀) cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
```

## §4 头都 $\cong^{\mathsf z}$ 同一棵树

`Ref`: $\psi_0(\Omega_1)$ 在 [OCF.Free.Tree](../Free/Tree.lagda.md) 那边的读法. `tc-rel`: $\Omega_\Omega$ 的第一支 (嵌到 $\Omega+1$ 的 `suc self`) 与 $\Omega_1$ 相关. `head-≅`: 在任何世界, 任何目标 (层 0), 空上下文的折叠, 读出来都是 `Ref`.

```agda
  ev₀ : Ev (suc zero) FT.Fl
  ev₀ = tt , (λ q → q)

  Ref : Z
  Ref = toZ (FT.ψ̄ (FT.tl {c = zero} (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) {zero} {suc zero} ev₀ zero)

  head-≅ : ∀ {π ρ} (E : Ents) (T : Tg E Lv.zero) (tg : Tgt T zero) (st : St E ρ π) (em′ : Emp π) {x : O L₁ π} → Rs (suc zero) x (Ωˢ (suc zero)) →
           rdZ (ψ E T st x) ≅ᶻ Ref
  head-≅ E T tg st em′ r = Rz (R-ψ₁ E T tg st em′ r (fz ⊔ fk zero) proj₂ (suc zero) ev₀ zero)

  -- 同一个关系, 过 `tr⁻O`
  head-≅⁻ : ∀ {π ρ} (E : Ents) (T : Tg E Lv.zero) (tg : Tgt T zero) (st : St E ρ π) (em′ : Emp π) {x : O L₁ π} (d : Lv.zero ≈ Lv.zero) → Rs (suc zero) x (Ωˢ (suc zero)) →
            rdZ (tr⁻O d (ψ E T st x)) ≅ᶻ Ref
  head-≅⁻ E T tg st em′ d r = Rz (R-tr⁻O d (R-ψ₁ E T tg st em′ r (fz ⊔ fk zero) proj₂ (suc zero) ev₀ zero))

  tI : Tc (Lv.suc Lv.zero)
  tI = proj₁ (proj₂ tc)

  -- 第一支: Ω₁ 嵌进 Ω_Ω 的 `fst`, 再嵌进 Ω+1 的 `suc self`. `w` 是定义里的那个扩展 λ, 作参数
  t-c : Wk (tz ∪ tz) tz → O c₁ tz
  t-c w = owk w (Emb.ι c₁ tc (Lv.suc Lv.zero) (Lv.fst Lv.self) (inj₂ refl) (Ω̇ (Lv.suc Lv.zero) tI))

  rel-t : (w : Wk (tz ∪ tz) tz) → Rs (suc zero) (Emb.ι L₁ tc c₁ (Lv.suc Lv.self) (inj₂ refl) (t-c w)) (Ωˢ (suc zero))
  rel-t w = EmbR.R-ι L₁ tc (Lv.suc Lv.self) (inj₂ refl)
              (rwk {w = w} (EmbR.R-ι c₁ tc (Lv.fst Lv.self) (inj₂ refl) (RΩ̇ (suc zero) (⌜≈⌝ (≅ᴵ-refl (suc zero))) tI)))

open RelT tcI public
```
