# 不带高度的树接上带高度的树 (六): 折叠的互模拟, 对一切 $\theta$

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 层 $c=c_1+\theta$. 没有写死 `Tgt`, `Sf`, `P = suc self`.
>
> - `R-ψᵒ`: 目标在高层 $t\approx c_1+j$. 节点高层: `<ᴵ-dec` 与 `cmpN` 对上 (`hi-sem`, `cu-hi`, `clash`); 节点低层: 必答 `cb`. 闭包: 必答 `ka` (保留). 地板: `FV`, `AbF` 是归纳不变量.
> - `R-ψ`: 目标是 0 或低层. 节点低层: 与 [GuardCertFold](GuardCertFold.lagda.md) 同一个论证, 规范形由 `nfP` 给. 节点高层: 必答 `cu`, 上链, 链的目标是高层 (`R-ψᵒ`), `ξ` 是全部的帧, 不再是空的. 闭包: 必答 `kb`, 界的比较不计算 (`ubd`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Free.Level
module OCF.Align.WeakBridgeFold (θ : Ordᴵ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Free.Prefix using (Ordˢ; Ord₊ˢ; Ωˢ; outˢ; intoˢ; out-intoˢ; tr⁻ˢ)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; bound; Bd; Fc; evF; iF; FM; Top; ubd)
import OCF.Free.Tree as FT
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using (O; Us; o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl; intoU; outU; trL⁻; tr⁻O; repᵒ; Ω̇; adm-wk)
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; FrL; FrG; Emp; ZZ; cb-sem; cu-sem; clash; out-intoU)
open import OCF.Align.GuardWeakTree
open import OCF.Align.GuardCertRel using (rz; rs; rl; rwk; rcv; rΩ; rŝ; rĉ; fr-of; RΩ̇; R-tr⁻O; R-trL⁻; R-tr⁻ˢ; lk≈′; outR; intoR)
open import OCF.Align.GuardTightCert using (c₁)
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeNf using (NT; NP; np→nt; ntF; ntB; nts; ntl; nt≈; one)
open import OCF.Align.WeakBridgeRel
open import OCF.Align.WeakBridgeC
open CR using (Rs; fr; gd)
open import OCF.Align.WeakBridgeOp
open import OCF.Align.WeakBridgeTr
open import OCF.Align.WeakBridgeEmb using (ΩH)
open import OCF.Align.WeakBridgeSel θ
open I using (q0; qs; ql; qi; qŝ; qĉ; qclo; qwk; qΩ)

open FoldW (c⁺ θ) (wf⁺ θ) (sf⁺ θ) (tc⁺ θ)
```

## §1 到高层的折叠

```agda
fv-r : ∀ {ρ π} (ξ : Fl) → FV ρ π → FV ρ (ξ ∪ π)
fv-r ξ a f′ m with a f′ m
... | f , m₁ , l = f , mr m₁ , l

ab-body : ∀ {E ρ π} (ξ : Fl) (w : Wk ξ π) (st : St E ρ π) → AbF st → AbF (stBody ξ w st)
ab-body ξ w st a (ml m) = a (w m)
ab-body ξ w st a (mr m) = a m

R-ψᵒ : ∀ {E ρ π φ χ t j B} (q : t < c) (aq : Adm (tab E) q) (s : j <ᴵ B) → t ≈ c⁺ j → (st : St E ρ π) → FV ρ π → AbF st →
       ∀ {x : O c π} {y : QQ B φ χ} → C θ x y → C j (ψ E (tp q aq) st x) (I.ψᵠ s y)

-- 高层节点的链: 链的目标是高层
module ChainM {E ρ π φ χ B k j′ j₂ rp ξ ξ̂ ζ} (st : St E ρ π) (r : k < c)
       (q′ : j′ <ᴵ B) (dk : k ≈ c⁺ j′) (e₂ : j′ ≅ᴵ j₂) (q₂ : j₂ <ᴵ θ)
       {h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)} {f : ∀ ξ ζ → I.Us 0 j′ (<→◃ q′) ξ ζ → QQ B (ξ ⊔ φ) (I.lo 0 ζ I.∪ χ)}
       (prem : ∀ ξ ξ̂ ζ → CvL ξ ξ̂ → (z : O k ξ) (ẑ : QQ j′ ξ̂ ζ) → LC θ (<→◃ q₂) z ẑ → C θ (h ξ (intoU r z)) (f ξ̂ ζ (I.intoU (<→◃ q′) ẑ)))
       (cvξ : CvL ξ ξ̂) (d : Lk k rp) (p : rp < c) (ap : Adm (tab E) p)
       (w : Wk ξ π) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) (bkJ : ∀ {f} (m : Mem π f) → IsJ (bk m))
       (fe : ∀ {ℓ} → Ev ℓ ξ̂ → Ev ℓ FT.Fl) (fc : I.Sub 0 ζ (I.κ FT.Fl))
       (le : ∀ {ℓ} → Ev ℓ ξ̂ → Ev ℓ (FT.Fl ⊔ (ξ̂ ⊔ φ))) (le′ : I.Sub 0 ζ (I.Z* (I.lo 0 ζ I.∪ χ))) where

  F̂ : QQ j′ ξ̂ ζ → QQ j′ ξ̂ ζ
  F̂ z = qwk le le′ (I.ψᵠ q′ (f ξ̂ ζ (I.intoU (<→◃ q′) z)))

  Fl′ : O k ξ → O k ξ
  Fl′ z = trL⁻ d (ψ E (tp p ap) (stChain ξ bk w st) (h ξ (intoU r z)))

  ch : ∀ n → C j₂ (chainᵒ (Tc-at r (tc⁺ θ)) Fl′ n) (I.chainᵠ fe fc F̂ n)
  ch zero = cwl (cwr (C-≅ e₂ (ΩH θ r dk)))
  ch (suc n) =
    Cf-trL⁻ d (cwr (C-≅ e₂ (R-ψᵒ p ap q′ (lk≈′ d dk) (stChain ξ bk w st) (fv-wk w) (ab-chain ξ bk w st bkJ)
      (prem ξ ξ̂ ζ cvξ _ _ (intoL (<→◃ q₂) (ch n))))))

rise-o : ∀ {E ρ π φ χ t j B k j′ j₂} (q : t < c) (aq : Adm (tab E) q) (s : j <ᴵ B) → t ≈ c⁺ j → (st : St E ρ π) → FV ρ π → AbF st →
         (r : k < c) {cv : Adm (cov π) r} (q′ : j′ <ᴵ B) {h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)} {f : ∀ ξ ζ → I.Us 0 j′ (<→◃ q′) ξ ζ → QQ B (ξ ⊔ φ) (I.lo 0 ζ I.∪ χ)} →
         (dk : k ≈ c⁺ j′) (e₂ : j′ ≅ᴵ j₂) (q₂ : j₂ <ᴵ θ) → CvL π φ →
         (∀ ξ ξ̂ ζ → CvL ξ ξ̂ → (z : O k ξ) (ẑ : QQ j′ ξ̂ ζ) → LC θ (<→◃ q₂) z ẑ → C θ (h ξ (intoU r z)) (f ξ̂ ζ (I.intoU (<→◃ q′) ẑ))) →
         C j (riseΩ E (tp q aq) st r cv h)
             (ql (λ n → qwk FT.dupr2 (I.⇑ (I.cv* 0)) (I.ψᵠ s (f (FT.Fl ⊔ φ) (I.Z* χ) (I.intoU (<→◃ q′) (I.chainᵠ proj₁ I.fc* (λ z → qwk FT.dupr2 (I.⇑ (I.cv* 0)) (I.ψᵠ q′ (f (FT.Fl ⊔ φ) (I.Z* χ) (I.intoU (<→◃ q′) z)))) n))))))

rise-o {E} {ρ} {π} {φ} {χ} q aq s dt st fv ab′ r {cv = cv} q′ {h = h} {f = f} dk e₂ q₂ c prem with nfR r
... | nr d Q rl₁ with Rd.toTabR st Q (rl₁ π cv) | toTabR-nb st (nb⁺ θ Q (NF-suc (NF-hi (lk≈′ d dk)))) (rl₁ π cv)
...   | just ap₀ | _ , refl with trim π st {fromCpS Q} (admFromS Q ap₀) | trim-bk π st (fromCpS Q) (admFromS Q ap₀) (lk≈′ d dk)
...     | mkTr ξ w bk | bkJ = cl (λ n → cwr (R-ψᵒ q aq s dt (stBody ξ w st) (fv-r ξ fv) (ab-body ξ w st ab′) (prem ξ (FT.Fl ⊔ φ) (I.Z* χ) cvξ _ _ (intoL (<→◃ q₂) (CH.ch n)))))
  where
  cvξ : CvL ξ (FT.Fl ⊔ φ)
  cvξ = cvL-wk w (λ f₀ m e → c f₀ m (proj₂ e))
  module CH = ChainM st r q′ dk e₂ q₂ {h = h} {f = f} prem cvξ d (fromCpS Q) (admFromS Q ap₀) w bk bkJ proj₁ I.fc* FT.dupr2 (I.⇑ (I.cv* 0))

R-ψᵒ q aq s dt st fv ab′ cz = cwl (cwr (ΩH θ q dt))
R-ψᵒ q aq s dt st fv ab′ (cs c r) = cl (rep-C (cv-fv fv c proj₂) (R-ψᵒ q aq s dt st fv ab′ r))
R-ψᵒ q aq s dt st fv ab′ (cl h) = cl (λ n → R-ψᵒ q aq s dt st fv ab′ (h n))
R-ψᵒ q aq s dt st fv ab′ (cwl {π = π′} {w = w} r) with lowerSt π′ (cov-exact w) st | lower-fv π′ (cov-exact w) st | lower-ab π′ (cov-exact w) st ab′
... | σ , st′ , cv₁ | fv′ | ab″ = cvl (R-ψᵒ q aq s dt st′ fv′ ab″ r)
R-ψᵒ q aq s dt st fv ab′ (cvl {π = π′} {w = w} r) with lowerSt π′ w st | lower-fv π′ w st | lower-ab π′ w st ab′
... | σ , st′ , cv₁ | fv′ | ab″ = cvl (R-ψᵒ q aq s dt st′ fv′ ab″ r)
R-ψᵒ q aq s dt st fv ab′ (cwr r) = cwr (R-ψᵒ q aq s dt st fv ab′ r)
R-ψᵒ q aq s dt st fv ab′ (cdr {y = y₀} r) = R-ψᵒ q aq s dt st fv ab′ {y = y₀} r
R-ψᵒ q aq s dt st fv ab′ (cm {x = x₀} r l dk lr E D) = R-ψᵒ q aq s dt st fv ab′ {x = x₀} D
R-ψᵒ q aq s dt st fv ab′ (cml {x = x₀} r cv l p E D) = R-ψᵒ q aq s dt st fv ab′ {x = x₀} D
R-ψᵒ {E} {ρ} {π} {t = t} {j = j} q aq s dt st fv ab′ (ci r {cv = cv} {h = h} {f = f} dk prem) with nfR r
... | nr d Q rl₁ with Cmp.cmpN st (covOf Q (rl₁ π cv)) (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-hiQ st (covOf Q (rl₁ π cv)) θ (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq dt
...   | Cmp.cu x | _ = ⊥-elim (cross-u dt (lk≈′ d dk) x)
...   | Cmp.cb d′ s₀ a | _ with Cmp.covOut st (covOf Q (rl₁ π cv)) s₀ a | NJM.cov-just st (covOf Q (rl₁ π cv)) ab′ s₀ a
...     | just cs₁ | tt =
  cvl (ci s₀ (≈-trans (≈-sym d′) (lk≈′ d dk))
          (λ ξ em z ẑ l → subst (λ u → C j (ψ E (tp q aq) (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU r (trL⁻ d (tr⁻O d′ u))))) (I.ψᵠ s (f ẑ)))
                                (sym (out-intoU s₀ z))
                                (R-ψᵒ q aq s dt (stξ ξ (λ m → mapFs ml (st m))) (fv-ξ ξ (fv-ml fv (NJM.fv-pl st (covOf Q (rl₁ π cv)) s₀ a))) (ab-ξ ξ (λ m → mapFs ml (st m)) (ab-ml ml st ab′))
                                      (prem ξ em (trL⁻ d (tr⁻O d′ z)) ẑ (R-trL⁻ d (R-tr⁻O d′ l))))))
R-ψᵒ {E} {ρ} {π} {φ} {χ} {t} {j} {B} q aq s dt st fv ab′ (cΩ {k = k} {j = j′} {j₂ = j₂} r {cv = cv} {fe = fe} q′ {h = h} {f = f} dk e₂ q₂ c prem) with nfR r
... | nr d Q rl₁ with Cmp.cmpN st (covOf Q (rl₁ π cv)) (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-hiQ st (covOf Q (rl₁ π cv)) θ (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq dt | <ᴵ-dec q′ s
...   | Cmp.cb d′ s₀ a | _ | injᵃ (via e r₂) with Cmp.covOut st (covOf Q (rl₁ π cv)) s₀ a | NJM.cov-just st (covOf Q (rl₁ π cv)) ab′ s₀ a
...     | just cs₁ | tt =
  cvl (cΩ s₀ r₂ (≈-trans (≈-sym d′) (≈-trans (lk≈′ d dk) (c⁺-≈ e))) (≅ᴵ-refl _) r₂ (cv-fv (fv-ml fv (NJM.fv-pl st (covOf Q (rl₁ π cv)) s₀ a)) c proj₂)
          (λ ξ ξ̂ ζ cv₁ z ẑ l → cwr (subst₂ (λ u v → C j (ψ E (tp q aq) (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU r (trL⁻ d (tr⁻O d′ u))))) (I.ψᵠ s (f ξ̂ ζ (I.intoU (<→◃ q′) (I.tr⁻Q e v)))))
                                (sym (out-intoU s₀ z)) (sym (outU-into (<→◃ r₂) ẑ))
                                (R-ψᵒ q aq s dt (stξ ξ (λ m → mapFs ml (st m))) (fv-ξ ξ (fv-ml fv (NJM.fv-pl st (covOf Q (rl₁ π cv)) s₀ a))) (ab-ξ ξ (λ m → mapFs ml (st m)) (ab-ml ml st ab′))
                                      (prem ξ ξ̂ ζ cv₁ (trL⁻ d (tr⁻O d′ z)) (I.tr⁻Q e ẑ)
                                            (intoL (<→◃ q₂) (C-≅ (≅ᴵ-trans (≅ᴵ-sym e) e₂) (Cf-trL⁻ d (Cf-tr⁻O d′ (R-tr⁻Q e (outL (<→◃ r₂) l))))))))))) 
R-ψᵒ {j = j} q aq s dt st fv ab′ (cΩ r {cv = cv} q′ dk e₂ q₂ c prem) | nr d Q rl₁ | Cmp.cb d′ s₀ a | _ | injᵇ w = ⊥-elim (clash (hi-sem dt (lk≈′ d dk) d′ s₀) (inj₁ w))
R-ψᵒ {j = j} q aq s dt st fv ab′ (cΩ r {cv = cv} q′ dk e₂ q₂ c prem) | nr d Q rl₁ | Cmp.cb d′ s₀ a | _ | injᶜ w = ⊥-elim (clash (hi-sem dt (lk≈′ d dk) d′ s₀) (inj₂ (≅ᴵ-sym w)))
R-ψᵒ {j = j} q aq s dt st fv ab′ (cΩ r {cv = cv} q′ dk e₂ q₂ c prem) | nr d Q rl₁ | Cmp.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-hi dt (lk≈′ d dk) x))
R-ψᵒ q aq s dt st fv ab′ (cΩ r q′ {f = f} dk e₂ q₂ c prem) | nr d Q rl₁ | Cmp.cu x | _ | injᵇ _ = rise-o q aq s dt st fv ab′ r q′ {f = f} dk e₂ q₂ c prem
R-ψᵒ q aq s dt st fv ab′ (cΩ r q′ {f = f} dk e₂ q₂ c prem) | nr d Q rl₁ | Cmp.cu x | _ | injᶜ _ = rise-o q aq s dt st fv ab′ r q′ {f = f} dk e₂ q₂ c prem
R-ψᵒ q aq s dt st fv ab′ (cŝ n ec rt rg) = cŝ (nz-≈ (≈-sym dt) (nz-c _)) ec (R-ψᵒ q aq s dt st fv ab′ rt) (λ η e e′ → R-ψᵒ q aq s dt st fv ab′ (rg η e e′))
R-ψᵒ q aq s dt st fv ab′ (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-ψᵒ q aq s dt st fv ab′ ro) (λ η e e′ → R-ψᵒ q aq s dt st fv ab′ (rg η e e′))
R-ψᵒ {E} {ρ} {π} q aq s dt st fv ab′ (ccl {c₁′ = c₁′} {t₁′ = t₁′} {g₁′ = g₁′} {P = P} {k = k} {ad = ad} c rt rg) with nfK P
... | nk d Q rl₁ with Cmp.cmpK st (covOf Q (rl₁ π ad)) (wf⁺ θ) (sf⁺ θ) Q q (admP Q) aq | NJM.ka-hi st (covOf Q (rl₁ π ad)) θ (wf⁺ θ) (sf⁺ θ) Q q (admP Q) aq dt
...   | Cmp.ka {c′} {t′} {g′} Q′ d₂ a | _ with Cmp.covOutC st (covOf Q (rl₁ π ad)) Q′ a | NJM.covC-just st (covOf Q (rl₁ π ad)) ab′ Q′ a
...     | just cs₁ | tt =
  cvl (cwr (ccl (cv-fv (fv-ml fv (NJM.fv-plC st (covOf Q (rl₁ π ad)) Q′ a)) c proj₂)
                (cwr (R-ψᵒ q aq s dt (λ m → mapFs ml (st m)) (fv-ml fv (NJM.fv-plC st (covOf Q (rl₁ π ad)) Q′ a)) (ab-ml ml st ab′) rt))
                (λ η e′ → cwr (R-ψᵒ q aq s dt _ (fv-br η e′ _) (λ { (ml m) → ab-map (λ u → ml (ml u)) (st m) (ab′ m) ; (mr hr) → tt }) (rg η _)))))
  where
  fv-br : ∀ η e′ e₁ → FV ((ρ ∪ pF Q′) ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁′ t₁′ g₁′ η e₁))
  fv-br η e′ e₁ f′ (ml m) with fv-ml fv (NJM.fv-plC st (covOf Q (rl₁ π ad)) Q′ a) f′ m
  ... | f₀ , m₁ , l = f₀ , ml m₁ , l
  fv-br η e′ e₁ f′ (mr hr) = frm c₁′ t₁′ g₁′ η e₁ , mr hr , ⊑ᴵ-refl
```

## §2 到低层的折叠

```agda
R-ψ : ∀ {ρ π t i B φ χ ℓ w} (ok : I.Ok w) (e₀ : I.Eh 0 0 w χ) (E : Ents) (T : Tg E t) → Tgt T i → (st : St E ρ π) → Full st → Emp ρ → {x : O c π} {y : QQ B φ χ} → C θ x y →
      (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) → Rs i fr (ψ E T st x) (I.ψ̄ᵠ ok e₀ y ev₁ p)

module RiseLo {ρ π t i k j B φ χ w} (ok : I.Ok w) (e₀ : I.Eh 0 0 w χ) (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) (eρ : Emp ρ)
             (r : k < c) (cv′ : Adm (cov π) r) {h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)} {f : Ordˢ j → QQ B φ χ}
             (dk : k ≈ ⌜ j ⌝)
             (prem : ∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → Rs j fr z ẑ → C θ (h ξ (intoU r z)) (f ẑ))
             (ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) {ℓ} (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) where

  body-rel : ∀ {rp} (d : Lk k rp) (r′ : rp < c) (aq : Adm (tab E) r′) → Tgt (tp r′ aq) j →
             ∀ ξ (w₁ : Wk ξ π) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) → Emp ξ →
             Rs i fr (ol (λ n → ψ E T (stBody ξ w₁ st) (h ξ (intoU r (chainᵒ (Tc-at r (tc⁺ θ)) (λ z → trL⁻ d (ψ E (tp r′ aq) (stChain ξ bk w₁ st) (h ξ (intoU r z)))) n)))))
                     (Ord₊ˢ.lim (λ m → I.ψ̄ᵠ ok e₀ (f (iter (λ x → I.ψ̄ᵠ ok e₀ (f x) ev₁ (ac ev₁)) (Ωˢ j) m)) ev₁ p))
  body-rel d r′ aq tq ξ w₁ bk em′ = rl (λ n → R-ψ ok e₀ E T tg (stBody ξ w₁ st) (full-body ξ w₁ st full) eρ (prem ξ em′ _ _ (ch n)) ev₁ p)
    where
    ch : ∀ n → Rs j fr (chainᵒ (Tc-at r (tc⁺ θ)) (λ z → trL⁻ d (ψ E (tp r′ aq) (stChain ξ bk w₁ st) (h ξ (intoU r z)))) n) (iter (λ x → I.ψ̄ᵠ ok e₀ (f x) ev₁ (ac ev₁)) (Ωˢ j) n)
    ch zero = rwk (fr-of (RΩ̇ j dk (Tc-at r (tc⁺ θ))))
    ch (suc n) = R-trL⁻ d (R-ψ ok e₀ E (tp r′ aq) tq (stChain ξ bk w₁ st) (full-chain ξ bk w₁ st full) em′ (prem ξ em′ _ _ (ch n)) ev₁ (ac ev₁))

  rise-lo : Rs i fr (riseΩ E T st r cv′ h) (Ord₊ˢ.lim (λ m → I.ψ̄ᵠ ok e₀ (f (iter (λ x → I.ψ̄ᵠ ok e₀ (f x) ev₁ (ac ev₁)) (Ωˢ j) m)) ev₁ p))
  rise-lo with nfR r | nr-lo r dk
  ... | nr d Q rl₁ | nrl n with Rd.toTabR st Q (rl₁ π cv′) | toTabR-np st full n (rl₁ π cv′)
  ...   | just ap₀ | _ , refl with trim π st {fromCpS Q} (admFromS Q ap₀) | trim-emp π st (fromCpS Q) (admFromS Q ap₀) (nt≈ (np→nt n)) full
  ...     | mkTr ξ w₁ bk | em′ = body-rel d (fromCpS Q) (admFromS Q ap₀) (tgL (np→nt n)) ξ w₁ bk em′

  cb-row : ∀ {rp rp′ j′} (d : Lk k rp) (d′ : rp ≈ rp′) (s : rp′ < t) → Emp (pFl s) → (e : j ≅ᴵ j′) (r₂ : j′ <ᴵ i) →
           ∀ {w₁ : Cov (ρ ∪ pFl s) ρ} →
           Rs i fr (ocv w₁ (oΩ s (adm-wk mr s (admPl s)) (λ ξ y → ψ E T (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU r (trL⁻ d (tr⁻O d′ (outU s y))))))))
                   (Ord₊ˢ.limᵢ r₂ (λ y → I.ψ̄ᵠ ok e₀ (f (tr⁻ˢ e (outˢ (<→◃ r₂) y))) ev₁ p))
  cb-row d d′ s es e r₂ =
    rcv (rΩ s _ r₂ (≈-trans (≈-sym d′) (≈-trans (lk≈′ d dk) (⌜≈⌝ e)))
           (λ ξ em′ z ẑ l → subst₂ (λ u v → Rs i fr (ψ E T (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU r (trL⁻ d (tr⁻O d′ u))))) (I.ψ̄ᵠ ok e₀ (f (tr⁻ˢ e v)) ev₁ p))
                                   (sym (out-intoU s z)) (sym (out-intoˢ (<→◃ r₂) ẑ))
                                   (R-ψ ok e₀ E T tg (stξ ξ (λ m → mapFs ml (st m))) (full-ξ ξ em′ (λ m → mapFs ml (st m)) (full-ml ml st full))
                                        (λ { (ml m) → em′ m ; (mr (ml m)) → eρ m ; (mr (mr m)) → es m })
                                        (prem ξ em′ _ _ (R-tr⁻ˢ e (R-trL⁻ d (R-tr⁻O d′ (outR (<→◃ r₂) l))))) ev₁ p)))

-- 高层节点, 低层目标: 上链
module RiseHi {ρ π t i k j′ j₂ B φ χ w} (ok : I.Ok w) (e₀ : I.Eh 0 0 w χ) (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) (eρ : Emp ρ)
             (r : k < c) (cv′ : Adm (cov π) r) {fe : ∀ {ℓ} → Ev ℓ φ → Ev ℓ FT.Fl} (q′ : j′ <ᴵ B) {h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)} {f : ∀ ξ ζ → I.Us 0 j′ (<→◃ q′) ξ ζ → QQ B (ξ ⊔ φ) (I.lo 0 ζ I.∪ χ)}
             (dk : k ≈ c⁺ j′) (e₂ : j′ ≅ᴵ j₂) (q₂ : j₂ <ᴵ θ) (c₀ : CvL π φ)
             (prem : ∀ ξ ξ̂ ζ → CvL ξ ξ̂ → (z : O k ξ) (ẑ : QQ j′ ξ̂ ζ) → LC θ (<→◃ q₂) z ẑ → C θ (h ξ (intoU r z)) (f ξ̂ ζ (I.intoU (<→◃ q′) ẑ)))
             {ℓ} (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) where

  rise-hi : Rs i fr (riseΩ E T st r cv′ h) (I.ψ̄ᵠ ok e₀ (qΩ fe q′ f) ev₁ p)
  rise-hi with nfR r
  ... | nr d Q rl₁ with Rd.toTabR st Q (rl₁ π cv′) | toTabR-nb st (nb⁺ θ Q (NF-suc (NF-hi (lk≈′ d dk)))) (rl₁ π cv′)
  ...   | just ap₀ | _ , refl with trim π st {fromCpS Q} (admFromS Q ap₀) | trim-bk π st (fromCpS Q) (admFromS Q ap₀) (lk≈′ d dk)
  ...     | mkTr ξ w₁ bk | bkJ = rl (λ n → R-ψ ok (I.e⁺ 0 ok e₀) E T tg (stBody ξ w₁ st) (full-body ξ w₁ st full) eρ (prem ξ φ (I.Z* χ) cvξ _ _ (intoL (<→◃ q₂) (CH.ch n))) (ev₁ , ev₁) p)
    where
    cvξ : CvL ξ φ
    cvξ = cvL-wk w₁ c₀
    module CH = ChainM st r q′ dk e₂ q₂ {h = h} {f = f} prem cvξ d (fromCpS Q) (admFromS Q ap₀) w₁ bk bkJ fe I.fc* (λ v → fe v , (v , v)) (I.⇑ (I.cv* 0))

-- 闭包
module CloM {ρ π t i} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) (eρ : Emp ρ)
            {c₁′ t₁′ g₁′} {B φ χ w} (ok : I.Ok w) (e₀ : I.Eh 0 0 w χ)
            (P : Cp c₁ c) (k : Lk c₁ (lc c₁′ t₁′ g₁′)) (ad : AdmC (cov π) P)
            {x : O c π} {g : ∀ η e → O c (π ∪ tk (frm c₁′ t₁′ g₁′ η e))} {t̂ : QQ B (φ ⊔ fk zero) χ} {ĝ : ∀ η → QQ B (φ ⊔ fk η) χ}
            (cv : CvL π φ) (rt : C θ x t̂) (rg : ∀ η e → C θ (g η e) (ĝ η)) {ℓ} (ev₁ : Ev ℓ (φ ⊔ fk zero)) (p : i <ᴵ ℓ) where

  module WithAp (ap : AdmC (tab E) P) where
    open SelM E P ap

    SS : M.S (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))
    SS = SSc E T st P ap

    BR : Top i ℓ (φ ⊔ fk zero)
    BR = bound (φ ⊔ fk zero) ev₁ p

    X : Ordᴵ
    X = Bd BR

    i≺X : i ≺ᴵ X
    i≺X = sim (FM BR) (iF BR)

    gd-SS : Good X SS
    gd-SS = good-⋈ (M.selSt π st) (M._⋈_ (tgSel P E ap T) (M.walk Lv.self tt P ap))
              (good-sel π st full (λ f m → ⊑ᴵ-trans (cv f m (proj₁ (evF BR))) (FM BR)))
              (good-⋈ (tgSel P E ap T) (M.walk Lv.self tt P ap) (good-tg tg i≺X) (good-walk Lv.self tt (nb⁺ θ P NF-lc) ap))

    e₁ : suc zero ⊑ᴵ X
    e₁ = ⊑ᴵ-trans (Sim→⊑ᴵ (proj₂ (evF BR))) (FM BR)

    go-rel : (w₁ : M.Sl (M.φ SS)) → OKS X w₁ →
             Rs i fr (goC E T st P k ap x g SS w₁) (I.ψ̄ᵠ ok e₀ (qclo t̂ ĝ) ev₁ p)
    go-rel (M.emp f) _ =
      rŝ (tzz tg) e₁ (R-ψ ok e₀ E T tg st full eρ rt ev₁ p)
         (λ η d d′ → R-ψ ok e₀ (M.E′ (suc η)) _ (tg-lft tg (suc η) (proj₁ (proj₂ (f (suc η))))) _
                         (λ { (ml m) → full-sel π st full (suc η) (proj₁ (f (suc η))) m ; (mr hr) → tt }) eρ (rg η _) _ _)
    go-rel (M.sel ℓ₁ K₀ a q y dm) k₁ =
      rŝ (tzz tg) (ubd (bound (M.φ SS) y q) k₁ (proj₁ gd-SS)) (R-ψ ok e₀ E T tg st full eρ rt ev₁ p)
         (λ η d d′ → R-ψ ok e₀ (M.E′ _) _ (tg-lft tg _ _) _
                         (λ { (ml m) → full-sel π st full _ _ m ; (mr hr) → tt }) eρ (rg η _) _ _)

    clo-rel : Rs i fr (goC E T st P k ap x g SS (M.wit SS)) (I.ψ̄ᵠ ok e₀ (qclo t̂ ĝ) ev₁ p)
    clo-rel = go-rel (M.wit SS) (proj₂ gd-SS)

  eval-rel : Rs i fr (evalC E T st P k ad x g) (I.ψ̄ᵠ ok e₀ (qclo t̂ ĝ) ev₁ p)
  eval-rel with nfK P | nk-id P
  ... | _ | nkv {rl = rl₁} with Rd.toTabR st P (rl₁ π ad) | toTabR-nb st (nb⁺ θ P NF-lc) (rl₁ π ad)
  ...   | just ap | _ , refl = WithAp.clo-rel ap

R-ψ ok e₀ E T tg st full eρ cz ev₁ p = rwk (fr-of (RΩ̇ _ (teq tg) (tcT T)))
R-ψ ok e₀ E T tg st full eρ (cs c r) ev₁ p = rl (rep-rel (tzz tg) eρ (R-ψ ok e₀ E T tg st full eρ r ev₁ p))
R-ψ ok e₀ E T tg st full eρ (cl h) ev₁ p = rl (λ n → R-ψ ok e₀ E T tg st full eρ (h n) ev₁ p)
R-ψ ok e₀ E T tg st full eρ (cwl {π = π′} {w = w} r) ev₁ p with lowerSt π′ (cov-exact w) st | lower-full π′ (cov-exact w) st full | lower-emp π′ (cov-exact w) st eρ
... | σ , st′ , cv₁ | full′ | eσ = rcv (R-ψ ok e₀ E T tg st′ full′ eσ r ev₁ p)
R-ψ ok e₀ E T tg st full eρ (cvl {π = π′} {w = w} r) ev₁ p with lowerSt π′ w st | lower-full π′ w st full | lower-emp π′ w st eρ
... | σ , st′ , cv₁ | full′ | eσ = rcv (R-ψ ok e₀ E T tg st′ full′ eσ r ev₁ p)
R-ψ ok e₀ E T tg st full eρ (cwr {le = le} {le′ = le′} r) ev₁ p = R-ψ ok (λ i h r′ → le′ i r′ (e₀ i h r′)) E T tg st full eρ r (le ev₁) p
R-ψ ok e₀ E T tg st full eρ (cdr {y = y₀} r) ev₁ p = R-ψ ok e₀ E T tg st full eρ {y = y₀} r ev₁ p
R-ψ ok e₀ E T tg st full eρ (cm {x = x₀} r l dk lr E₀ D) ev₁ p = R-ψ ok e₀ E T tg st full eρ {x = x₀} D ev₁ p
R-ψ ok e₀ E T tg st full eρ (cml {x = x₀} r cv l q E₀ D) ev₁ p = R-ψ ok e₀ E T tg st full eρ {x = x₀} D ev₁ p
R-ψ ok e₀ E t0 tg0 st full eρ (ci r {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p with <ᴵ-dec (ac ev₁) p
... | injᵃ (via e ())
... | injᵇ _ = RiseLo.rise-lo ok e₀ E t0 tg0 st full eρ r cv {h = h} {f = f} dk prem ac ev₁ p
... | injᶜ _ = RiseLo.rise-lo ok e₀ E t0 tg0 st full eρ r cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ {ρ} {π} {t} {i} ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p with nfR r | nr-lo r dk
... | nr d Q rl₁ | nrl n with Cmp.cmpN st (covOf Q (rl₁ π cv)) (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-NT st (covOf Q (rl₁ π cv)) full θ (sf⁺ θ) (fromCpS Q) q (np→nt n) (admFromS {E = cov (pF Q)} Q (admP Q)) aq | <ᴵ-dec (ac ev₁) p
...   | Cmp.cb d′ s a | _ | injᵃ (via e r₂) with Cmp.covOut st (covOf Q (rl₁ π cv)) s a | NJM.fr-just st (covOf Q (rl₁ π cv)) (tfr-nt nq) s a
...     | just cs₁ | tt = RiseLo.cb-row ok e₀ E (tp q aq) (tgL nq) st full eρ r cv {h = h} {f = f} dk prem ac ev₁ p d d′ s (fr-pl (tfr-nt nq) s) e r₂
R-ψ ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} dk prem) ev₁ p | nr d Q rl₁ | nrl n | Cmp.cb d′ s a | _ | injᵇ w = ⊥-elim (clash (cb-sem (nt≈ nq) (lk≈′ d dk) d′ s) (inj₁ w))
R-ψ ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} dk prem) ev₁ p | nr d Q rl₁ | nrl n | Cmp.cb d′ s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem (nt≈ nq) (lk≈′ d dk) d′ s) (inj₂ (≅ᴵ-sym c′)))
R-ψ ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} dk prem) ev₁ p | nr d Q rl₁ | nrl n | Cmp.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem (nt≈ nq) (lk≈′ d dk) x))
R-ψ ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nrl n | Cmp.cu x | _ | injᵇ _ = RiseLo.rise-lo ok e₀ E (tp q aq) (tgL nq) st full eρ r cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ ok e₀ E (tp q aq) (tgL nq) st full eρ (ci r {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nrl n | Cmp.cu x | _ | injᶜ _ = RiseLo.rise-lo ok e₀ E (tp q aq) (tgL nq) st full eρ r cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ ok e₀ E t0 tg0 st full eρ (cΩ r {cv = cv} q′ {h = h} {f = f} dk e₂ q₂ c prem) ev₁ p = RiseHi.rise-hi ok e₀ E t0 tg0 st full eρ r cv q′ {h = h} {f = f} dk e₂ q₂ c prem ev₁ p
R-ψ {ρ} {π} ok e₀ E (tp q aq) (tgL nq) st full eρ (cΩ r {cv = cv} q′ {h = h} {f = f} dk e₂ q₂ c prem) ev₁ p with nfR r
... | nr d Q rl₁ with Cmp.cmpN st (covOf Q (rl₁ π cv)) (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-hiR st (covOf Q (rl₁ π cv)) θ (wf⁺ θ) (sf⁺ θ) (fromCpS Q) q (admFromS {E = cov (pF Q)} Q (admP Q)) aq (lk≈′ d dk)
...   | Cmp.cb d′ s a | _ = ⊥-elim (cross-b (nt≈ nq) (lk≈′ d dk) d′ s)
...   | Cmp.cu x | _ = RiseHi.rise-hi ok e₀ E (tp q aq) (tgL nq) st full eρ r cv q′ {h = h} {f = f} dk e₂ q₂ c prem ev₁ p
R-ψ ok e₀ E T tg st full eρ (cŝ n ec rt rg) ev₁ p = rŝ (tzz tg) ec (R-ψ ok e₀ E T tg st full eρ rt ev₁ p) (λ η e e′ → R-ψ ok e₀ E T tg st full eρ (rg η e e′) ev₁ p)
R-ψ ok e₀ E T tg st full eρ (cĉ ec dz dg ro rg) ev₁ p = rĉ ec dz dg (R-ψ ok e₀ E T tg st full eρ ro ev₁ p) (λ η e e′ → R-ψ ok e₀ E T tg st full eρ (rg η e e′) ev₁ p)
R-ψ ok e₀ E t0 tg0 st full eρ (ccl {P = P} {k = k} {ad = ad} c rt rg) ev₁ p with key⁺ θ P
... | refl = CloM.eval-rel E t0 tg0 st full eρ ok e₀ P k ad c rt rg ev₁ p
R-ψ {ρ} {π} ok e₀ E (tp q aq) (tgL nq) st full eρ (ccl {P = P} {k = k} {ad = ad} c rt rg) ev₁ p with key⁺ θ P
... | refl with nfK P
...   | nk d Q rl₁ with Cmp.cmpK st (covOf Q (rl₁ π ad)) (wf⁺ θ) (sf⁺ θ) Q q (admP Q) aq | NJM.kb-lo st (covOf Q (rl₁ π ad)) θ (wf⁺ θ) (sf⁺ θ) Q q (admP Q) aq (nt≈ nq)
...     | Cmp.kb | _ = CloM.eval-rel E (tp q aq) (tgL nq) st full eρ ok e₀ P k ad c rt rg ev₁ p
```
