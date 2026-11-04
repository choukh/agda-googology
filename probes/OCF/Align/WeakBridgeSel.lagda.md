# 不带高度的树接上带高度的树 (五): 折叠的状态, 比较, 闭包的界

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). 模块参数 $\theta$ 是层号 `c⁺ θ`, 不是假设. 由 [GuardCertFold](GuardCertFold.lagda.md) 的 §1, §2, §4 推广, 不再写死 $c_1+1$:
>
> - `Full`: 帧都有证据. 不再要 `Pf = suc self`: 闭包在 `c⁺ θ` 里的位置都无分支 (`nb⁺`), 键都是 $c_1$ (`key⁺`).
> - `keepP-lo`, `keepP-hi`: **`keepP` 只看节点的类: 低层答 `false`, 高层答 `true`.** 这是 `keep-Ω+2` 的一般形式. 所以低层节点的链地板是空的 (`trim-emp`), 高层节点的链保留全部的帧 (`trim-bk`).
> - `nj-hiQ`, `nj-hiR`, `nj-NT`: 比较不答 `cj`. 只要目标或节点是高层, 或节点是规范路径 (`NT`).
> - `ka-hi`, `kb-lo`: 闭包对高层目标保留, 对低层目标计值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Free.Level
module OCF.Align.WeakBridgeSel (θ : Ordᴵ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Trich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Prefix using (Ordˢ; Ord₊ˢ; _+ˢ_; addˢ)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; toFlo; InF; ink; inb; inl; inr; Dem; DemB; isB)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTab Dom₀ using (kdec; _⊙_; adm⊙)
open import OCF.Align.GuardTightTree using (Us; Vs; O; repᵒ; adm-wk; oc≅)
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; pullG; FrL; fz; fs′; fl; FrG; Fr≈; Emp; ZZ; zz-≅)
open import OCF.Align.GuardWeakNorm using (prOf-suc)
open import OCF.Align.GuardWeakTree
open import OCF.Align.GuardCertRel using (Rs; fr; R-⊕; rz; rwk; le-emp; ⊲→⊑; fr-cp)
open import OCF.Align.GuardTightCert using (c₁)
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeNf using (NT; ntF; ntB; nts; ntl; nt≈; one; pnt-steps; NTV; ntv; lo-c; NP; npF; npB; nps; npl; NPV; npv; nfP)
open import OCF.Align.WeakBridgeRel using (CvL)

open FoldW (c⁺ θ) (wf⁺ θ) (sf⁺ θ) (tc⁺ θ)

c : LG
c = c⁺ θ
```

## §1 状态

```agda
IsJ : ∀ {A : Set} → Maybe A → Set
IsJ (just _) = ⊤
IsJ nothing = ⊥

Full : ∀ {E ρ π} → St E ρ π → Set
Full {π = π} st = ∀ {f} (m : Mem π f) → IsJ (ev (st m))

AbF : ∀ {E ρ π} → St E ρ π → Set
AbF {π = π} st = ∀ {f} (m : Mem π f) → IsJ (abm (st m))

mapF : ∀ {E ρ ρ′ f} (w₁ : Wk ρ ρ′) (s : Fs E ρ f) → IsJ (ev s) → IsJ (ev (mapFs w₁ s))
mapF w₁ (fs e nothing) h = h
mapF w₁ (fs e (just (ab m k))) h = h

fsLow-full : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → IsJ (ev s) → IsJ (ev (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
fsLow-full lk lt (fs (just (evd Pf adf lkf (ℓ , b , q))) nothing) _ = tt
fsLow-full lk lt (fs (just (evd Pf adf lkf (ℓ , b , q))) (just (ab m k))) _ = tt

lower-full : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → Full st → Full (proj₁ (proj₂ (lowerSt π′ w st)))
lower-full (tk f) w st full m with w hr
... | f′ , m₁ , lk , lt with fsLow {f = f} {f′ = f′} lk lt (st m₁) | fsLow-full {f = f} {f′ = f′} lk lt (st m₁) (full m₁)
... | σ , F , c′ | h with m
... | hr = h
lower-full (a ∪ b) w st full m with lowerSt a (λ m₁ → w (ml m₁)) st | lower-full a (λ m₁ → w (ml m₁)) st full | lowerSt b (λ m₁ → w (mr m₁)) st | lower-full b (λ m₁ → w (mr m₁)) st full
lower-full (a ∪ b) w st full (ml m) | σa , sa , ca | ha | σb , sb , cb | hb = mapF ml (sa m) (ha m)
lower-full (a ∪ b) w st full (mr m) | σa , sa , ca | ha | σb , sb , cb | hb = mapF mr (sb m) (hb m)

full-ξ : ∀ {E ρ π} (ξ : Fl) → Emp ξ → (st : St E ρ π) → Full st → Full (stξ ξ st)
full-ξ ξ em′ st full (ml m) = ⊥-elim (em′ m)
full-ξ ξ em′ st full (mr m) = mapF mr (st m) (full m)

full-ml : ∀ {E ρ ρ′ π} (w : Wk ρ ρ′) (st : St E ρ π) → Full st → Full (λ m → mapFs w (st m))
full-ml w st full m = mapF w (st m) (full m)

full-body : ∀ {E ρ π} (ξ : Fl) (w : Wk ξ π) (st : St E ρ π) → Full st → Full (stBody ξ w st)
full-body ξ w st full (ml m) = full (w m)
full-body ξ w st full (mr m) = full m

full-chain : ∀ {E ρ π} (ξ : Fl) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) (w : Wk ξ π) (st : St E ρ π) → Full st → Full (stChain ξ bk w st)
full-chain ξ bk w st full (ml m) = full (w m)
full-chain ξ bk w st full {f} (mr m) with bk m
... | just m′ = full m
... | nothing = full m

-- 输出的地板
fsLow-emp : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) → Emp ρ → (s : Fs E ρ f′) → Emp (proj₁ (fsLow {f = f} {f′ = f′} lk lt s))
fsLow-emp lk lt eρ (fs e nothing) ()
fsLow-emp lk lt eρ (fs e (just (ab mem k))) hr = eρ mem

lower-emp : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → Emp ρ → Emp (proj₁ (lowerSt π′ w st))
lower-emp tz w st eρ ()
lower-emp (tk f) w st eρ m with w hr
... | f′ , m₁ , lk , lt = fsLow-emp {f = f} {f′ = f′} lk lt eρ (st m₁) m
lower-emp (a ∪ b) w st eρ (ml m) = lower-emp a (λ m₁ → w (ml m₁)) st eρ m
lower-emp (a ∪ b) w st eρ (mr m) = lower-emp b (λ m₁ → w (mr m₁)) st eρ m

-- 输出的帧被输入的帧支配 (只看值)
FV : Fl → Fl → Set
FV ρ π = ∀ f′ → Mem ρ f′ → Σ Frm λ f → Mem π f × (fη f′ ⊑ᴵ fη f)

fsLow-fv : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → FV (proj₁ (fsLow {f = f} {f′ = f′} lk lt s)) (tk f)
fsLow-fv lk lt (fs e nothing) f″ ()
fsLow-fv {f = f} lk lt (fs e (just (ab mem k))) f″ hr = f , hr , ⊑ᴵ-refl

lower-fv : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → FV (proj₁ (lowerSt π′ w st)) π′
lower-fv tz w st f″ ()
lower-fv (tk f) w st f″ m with w hr
... | f′ , m₁ , lk , lt = fsLow-fv {f = f} {f′ = f′} lk lt (st m₁) f″ m
lower-fv (a ∪ b) w st f″ (ml m) with lower-fv a (λ m₁ → w (ml m₁)) st f″ m
... | f , m₁ , l = f , ml m₁ , l
lower-fv (a ∪ b) w st f″ (mr m) with lower-fv b (λ m₁ → w (mr m₁)) st f″ m
... | f , m₁ , l = f , mr m₁ , l

ab-map : ∀ {E ρ ρ′ f} (w : Wk ρ ρ′) (s : Fs E ρ f) → IsJ (abm s) → IsJ (abm (mapFs w s))
ab-map w (fs e (just _)) _ = tt

fsLow-ab : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → IsJ (abm s) → IsJ (abm (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
fsLow-ab lk lt (fs e (just (ab m k))) _ = tt

lower-ab : ∀ {E ρ π} (π′ : Fl) (w : Cov π′ π) (st : St E ρ π) → AbF st → AbF (proj₁ (proj₂ (lowerSt π′ w st)))
lower-ab (tk f) w st ab′ m with w hr
... | f′ , m₁ , lk , lt with fsLow {f = f} {f′ = f′} lk lt (st m₁) | fsLow-ab {f = f} {f′ = f′} lk lt (st m₁) (ab′ m₁)
... | σ , F , c′ | h with m
... | hr = h
lower-ab (a ∪ b) w st ab′ m with lowerSt a (λ m₁ → w (ml m₁)) st | lower-ab a (λ m₁ → w (ml m₁)) st ab′ | lowerSt b (λ m₁ → w (mr m₁)) st | lower-ab b (λ m₁ → w (mr m₁)) st ab′
lower-ab (a ∪ b) w st ab′ (ml m) | σa , sa , ca | ha | σb , sb , cb | hb = ab-map ml (sa m) (ha m)
lower-ab (a ∪ b) w st ab′ (mr m) | σa , sa , ca | ha | σb , sb , cb | hb = ab-map mr (sb m) (hb m)

ab-ξ : ∀ {E ρ π} (ξ : Fl) (st : St E ρ π) → AbF st → AbF (stξ ξ st)
ab-ξ ξ st ab′ (ml m) = tt
ab-ξ ξ st ab′ (mr m) = ab-map mr (st m) (ab′ m)

ab-ml : ∀ {E ρ ρ′ π} (w : Wk ρ ρ′) (st : St E ρ π) → AbF st → AbF (λ m → mapFs w (st m))
ab-ml w st ab′ m = ab-map w (st m) (ab′ m)

ab-chain : ∀ {E ρ π} (ξ : Fl) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) (w : Wk ξ π) (st : St E ρ π) → (∀ {f} (m : Mem π f) → IsJ (bk m)) → AbF (stChain ξ bk w st)
ab-chain ξ bk w st h (ml m) = tt
ab-chain ξ bk w st h {f} (mr m) with bk m | h m
... | just m′ | tt = tt

cv-fv : ∀ {ρ π φ₀ φ} → FV ρ π → CvL π φ → (∀ {ℓ} → Ev ℓ φ₀ → Ev ℓ φ) → CvL ρ φ₀
cv-fv fv c le f′ m e with fv f′ m
... | f , m₁ , l = ⊑ᴵ-trans l (c f m₁ (le e))

fv-ml : ∀ {ρ π σ} → FV ρ π → FV σ π → FV (ρ ∪ σ) π
fv-ml a b f′ (ml m) = a f′ m
fv-ml a b f′ (mr m) = b f′ m

fv-ξ : ∀ {ρ π} (ξ : Fl) → FV ρ π → FV (ξ ∪ ρ) (ξ ∪ π)
fv-ξ ξ a f′ (ml m) = f′ , ml m , ⊑ᴵ-refl
fv-ξ ξ a f′ (mr m) with a f′ m
... | f , m₁ , l = f , mr m₁ , l

fv-tz : ∀ {π} → FV tz π
fv-tz f′ ()

fv-wk : ∀ {ξ π} → Wk ξ π → FV ξ (ξ ∪ π)
fv-wk w f′ m = f′ , ml m , ⊑ᴵ-refl
```

## §2 `keepP` 只看节点的类

```agda
keepP-lo : ∀ θ′ {E} (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {c₂ t₂ g₂ t j} (P : Cp (lc c₂ t₂ g₂) (c⁺ θ′)) (q : t < c⁺ θ′) (cv : AdmC (tab E) P) (aq : Adm (tab E) q) → t ≈ ⌜ j ⌝ → keepP {E} w s P q cv aq ≡ false
keepP-lo zero w s Lv.self q cv aq d = refl
keepP-lo zero w s (Lv.fst P) q cv aq d = ⊥-elim (NF-lc (fr-cp (FrG one) P))
keepP-lo zero w s (Lv.bra η e P) q cv aq d = ⊥-elim (NF-lc (fr-cp (FrG η) P))
keepP-lo (suc a) w (Lv.s≈ e) (Lv.suc P) Lv.zero cv aq d = ⊥-elim (lo-c d)
keepP-lo (suc a) w (Lv.s≈ e) (Lv.suc P) (Lv.suc q) cv aq d = keepP-lo a w e P q cv aq d
keepP-lo (lim f s₀) {E} (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d with <ᴺ-dec n m
... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
...   | viaᴷ d′ P′ u = keepP-lo (f m) (w m) (e m) P′ q (u (tab E) cv) aq d
keepP-lo (lim f s₀) {E} (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
...   | viaᴸ d′ q′ u = keepP-lo (f n) (w n) (e n) P q′ cv (u (tab E) aq) (≈-trans (≈-sym d′) d)
keepP-lo (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim _ q) cv aq d | injᶜ refl = keepP-lo (f n) (w n) (e n) P q cv aq d

hi-in-c₁ : ∀ {t j} → t < c₁ → t ≈ c⁺ j → ⊥
hi-in-c₁ q d with pull⁺ zero q
... | hi e ()
... | lo refl = lo≠hi (⌜≈⌝ (≅ᴵ-refl _)) d

keepP-hi : ∀ θ′ {E} (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {c₂ t₂ g₂ t j} (P : Cp (lc c₂ t₂ g₂) (c⁺ θ′)) (q : t < c⁺ θ′) (cv : AdmC (tab E) P) (aq : Adm (tab E) q) → t ≈ c⁺ j → keepP {E} w s P q cv aq ≡ true
keepP-hi zero w s P q cv aq d = ⊥-elim (hi-in-c₁ q d)
keepP-hi (suc a) w (Lv.s≈ e) (Lv.suc P) Lv.zero cv aq d = refl
keepP-hi (suc a) w (Lv.s≈ e) (Lv.suc P) (Lv.suc q) cv aq d = keepP-hi a w e P q cv aq d
keepP-hi (lim f s₀) {E} (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d with <ᴺ-dec n m
... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
...   | viaᴷ d′ P′ u = keepP-hi (f m) (w m) (e m) P′ q (u (tab E) cv) aq d
keepP-hi (lim f s₀) {E} (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
...   | viaᴸ d′ q′ u = keepP-hi (f n) (w n) (e n) P q′ cv (u (tab E) aq) (≈-trans (≈-sym d′) d)
keepP-hi (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim _ q) cv aq d | injᶜ refl = keepP-hi (f n) (w n) (e n) P q cv aq d

keepF-lo : ∀ {E ρ f k j} (s : Fs E ρ f) (r : k < c) (a : Adm (tab E) r) → k ≈ ⌜ j ⌝ → IsJ (ev s) → keepF s {r} a ≡ false
keepF-lo (fs (just (evd Pf adf lkf blf)) a′) r a d _ = keepP-lo θ (wf⁺ θ) (sf⁺ θ) Pf r adf a d

keepF-hi : ∀ {E ρ f k j} (s : Fs E ρ f) (r : k < c) (a : Adm (tab E) r) → k ≈ c⁺ j → keepF s {r} a ≡ true
keepF-hi (fs nothing a′) r a d = refl
keepF-hi (fs (just (evd Pf adf lkf blf)) a′) r a d = keepP-hi θ (wf⁺ θ) (sf⁺ θ) Pf r adf a d

trim-emp : ∀ {E ρ k j} (π : Fl) (st : St E ρ π) (r : k < c) (ar : Adm (tab E) r) → k ≈ ⌜ j ⌝ → Full st → Emp (ξᵗ (trim π st {r} ar))
trim-emp tz st r ar d full ()
trim-emp (tk f) st r ar d full m with keepF (st hr) {r} ar | keepF-lo (st hr) r ar d (full hr)
trim-emp (tk f) st r ar d full () | false | refl
trim-emp (a ∪ b) st r ar d full m with trim a (λ m₁ → st (ml m₁)) {r} ar | trim-emp a (λ m₁ → st (ml m₁)) r ar d (λ m₁ → full (ml m₁)) | trim b (λ m₁ → st (mr m₁)) {r} ar | trim-emp b (λ m₁ → st (mr m₁)) r ar d (λ m₁ → full (mr m₁))
trim-emp (a ∪ b) st r ar d full (ml m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = ha m
trim-emp (a ∪ b) st r ar d full (mr m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = hb m

trim-bk : ∀ {E ρ k j} (π : Fl) (st : St E ρ π) (r : k < c) (ar : Adm (tab E) r) → k ≈ c⁺ j → ∀ {f} (m : Mem π f) → IsJ (bkᵗ (trim π st {r} ar) m)
trim-bk (tk f) st r ar d m with keepF (st hr) {r} ar | keepF-hi (st hr) r ar d
trim-bk (tk f) st r ar d hr | true | refl = tt
trim-bk (a ∪ b) st r ar d m with trim a (λ m₁ → st (ml m₁)) {r} ar | trim-bk a (λ m₁ → st (ml m₁)) r ar d | trim b (λ m₁ → st (mr m₁)) {r} ar | trim-bk b (λ m₁ → st (mr m₁)) r ar d
trim-bk (a ∪ b) st r ar d (ml m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb with ba m | ha m
... | just _ | tt = tt
trim-bk (a ∪ b) st r ar d (mr m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb with bb m | hb m
... | just _ | tt = tt
```

## §3 比较

```agda
fr-pl : ∀ {a b} → FrL b → (s : a < b) → Emp (pFl s)
fr-pl (fs′ h) Lv.zero ()
fr-pl (fs′ h) (Lv.suc s) m = fr-pl h s m
fr-pl (fl h) (Lv.lim n s) m = fr-pl (h n) s m

belR-suc : ∀ {E ρ π} (st : St E ρ π) → Full st → ∀ {y b} (d : Dm π y (suc b)) → Σ _ λ B → Rd.belR st d ≡ just B
belR-suc st full (f , m , lk , lt) with ev (st m) | full m
... | just (evd _ _ _ (ℓ , b , σ)) | tt with prOf lt σ | prOf-suc lt σ
...   | just q | _ , refl = _ , refl

module NJM {E : Ents} {ρ π : Fl} (st : St E ρ π) {φ̂ : Fl} (dm : Cov φ̂ π) where
  open Rd st
  open Cmp st dm

  dom-just : AbF st → ∀ {y a} (d : Dm π y a) → IsJ (domOut d)
  dom-just ab′ (f , m , lk , lt) with abm (st m) | ab′ m
  ... | just (ab mem lk₄) | tt = tt

  cov-just : AbF st → ∀ {a b} (s : a < b) (x : Adm (cov φ̂) s) → IsJ (covOut s x)
  cov-just ab′ Lv.zero _ = tt
  cov-just ab′ (Lv.suc s) x = cov-just ab′ s x
  cov-just ab′ (Lv.lim n s) x = cov-just ab′ s x
  cov-just ab′ (Lv.fst s) x = cov-just ab′ s x
  cov-just ab′ (Lv.bra η e s) (u , x) with domOut (dmC u) | dom-just ab′ (dmC u) | covOut s x | cov-just ab′ s x
  ... | just d | tt | just cs₁ | tt = tt

  covC-just : AbF st → ∀ {a b} (s : Cp a b) (x : AdmC (cov φ̂) s) → IsJ (covOutC s x)
  covC-just ab′ Lv.self _ = tt
  covC-just ab′ (Lv.suc s) x = covC-just ab′ s x
  covC-just ab′ (Lv.lim n s) x = covC-just ab′ s x
  covC-just ab′ (Lv.fst s) x = covC-just ab′ s x
  covC-just ab′ (Lv.bra η e s) (u , x) with domOut (dmC u) | dom-just ab′ (dmC u) | covOutC s x | covC-just ab′ s x
  ... | just d | tt | just cs₁ | tt = tt

  fr-just : ∀ {a b} → FrL b → (s : a < b) (x : Adm (cov φ̂) s) → IsJ (covOut s x)
  fr-just (fs′ h) Lv.zero x = tt
  fr-just (fs′ h) (Lv.suc s) x = fr-just h s x
  fr-just (fl h) (Lv.lim n s) x = fr-just (h n) s x

  fv-pl : ∀ {a b} (s : a < b) → Adm (cov φ̂) s → FV (pFl s) π
  fv-pl Lv.zero _ f′ ()
  fv-pl (Lv.suc s) x = fv-pl s x
  fv-pl (Lv.lim n s) x = fv-pl s x
  fv-pl (Lv.fst s) x = fv-pl s x
  fv-pl (Lv.bra η e s) (u , x) f′ (ml hr) with dmC u
  ... | f , m , lk , lt = f , m , ⊲→⊑ lt
  fv-pl (Lv.bra η e s) (u , x) f′ (mr m) = fv-pl s x f′ m

  fv-plC : ∀ {a b} (s : Cp a b) → AdmC (cov φ̂) s → FV (pF s) π
  fv-plC Lv.self _ f′ ()
  fv-plC (Lv.suc s) x = fv-plC s x
  fv-plC (Lv.lim n s) x = fv-plC s x
  fv-plC (Lv.fst s) x = fv-plC s x
  fv-plC (Lv.bra η e s) (u , x) f′ (ml hr) with dmC u
  ... | f , m , lk , lt = f , m , ⊲→⊑ lt
  fv-plC (Lv.bra η e s) (u , x) f′ (mr m) = fv-plC s x f′ m

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

  nj-F : ∀ {c′} (w : WFˢ c′) (s : c′ ≈ c′) → FrL c′ → ∀ {k t} (r : k < c′) (q : t < c′) (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → NJ (cmpN w s r q cv aq)
  nj-F w (Lv.s≈ e) f Lv.zero Lv.zero _ _ = tt
  nj-F w (Lv.s≈ e) f Lv.zero (Lv.suc q) _ _ = tt
  nj-F w (Lv.s≈ e) f (Lv.suc r) Lv.zero cv _ = tt
  nj-F w (Lv.s≈ e) (fs′ f) (Lv.suc r) (Lv.suc q) cv aq = nj-F w e f r q cv aq
  nj-F (st′ , w) (Lv.l≈ e) (fl f) (Lv.lim n r) (Lv.lim m q) cv aq with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
  ...   | viaᴸ d r′ u = shlJ d _ (nj-F (w m) (e m) (f m) r′ q (u (cov φ̂) cv) aq)
  nj-F (st′ , w) (Lv.l≈ e) (fl f) (Lv.lim n r) (Lv.lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d q′ u = shrJ d _ (nj-F (w n) (e n) (f n) r q′ cv (u (tab E) aq))
  nj-F (st′ , w) (Lv.l≈ e) (fl f) (Lv.lim n r) (Lv.lim _ q) cv aq | injᶜ refl = nj-F (w n) (e n) (f n) r q cv aq

  -- 目标是高层
  nj-hiQ : ∀ θ′ (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {k t j} (r : k < c⁺ θ′) (q : t < c⁺ θ′) (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → t ≈ c⁺ j → NJ (cmpN w s r q cv aq)
  nj-hiQ zero w s r q cv aq d = ⊥-elim (hi-in-c₁ q d)
  nj-hiQ (suc a) w (Lv.s≈ e) Lv.zero Lv.zero _ _ d = tt
  nj-hiQ (suc a) w (Lv.s≈ e) Lv.zero (Lv.suc q) _ _ d = tt
  nj-hiQ (suc a) w (Lv.s≈ e) (Lv.suc r) Lv.zero cv _ d = tt
  nj-hiQ (suc a) w (Lv.s≈ e) (Lv.suc r) (Lv.suc q) cv aq d = nj-hiQ a w e r q cv aq d
  nj-hiQ (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) cv aq d with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
  ...   | viaᴸ d′ r′ u = shlJ d′ _ (nj-hiQ (f m) (w m) (e m) r′ q (u (cov φ̂) cv) aq d)
  nj-hiQ (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d′ q′ u = shrJ d′ _ (nj-hiQ (f n) (w n) (e n) r q′ cv (u (tab E) aq) (≈-trans (≈-sym d′) d))
  nj-hiQ (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim _ q) cv aq d | injᶜ refl = nj-hiQ (f n) (w n) (e n) r q cv aq d

  -- 节点是高层
  nj-hiR : ∀ θ′ (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {k t j} (r : k < c⁺ θ′) (q : t < c⁺ θ′) (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → k ≈ c⁺ j → NJ (cmpN w s r q cv aq)
  nj-hiR zero w s r q cv aq d = ⊥-elim (hi-in-c₁ r d)
  nj-hiR (suc a) w (Lv.s≈ e) Lv.zero Lv.zero _ _ d = tt
  nj-hiR (suc a) w (Lv.s≈ e) Lv.zero (Lv.suc q) _ _ d = tt
  nj-hiR (suc a) w (Lv.s≈ e) (Lv.suc r) Lv.zero cv _ d = tt
  nj-hiR (suc a) w (Lv.s≈ e) (Lv.suc r) (Lv.suc q) cv aq d = nj-hiR a w e r q cv aq d
  nj-hiR (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) cv aq d with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
  ...   | viaᴸ d′ r′ u = shlJ d′ _ (nj-hiR (f m) (w m) (e m) r′ q (u (cov φ̂) cv) aq (≈-trans (≈-sym d′) d))
  nj-hiR (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d′ q′ u = shrJ d′ _ (nj-hiR (f n) (w n) (e n) r q′ cv (u (tab E) aq) d)
  nj-hiR (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n r) (Lv.lim _ q) cv aq d | injᶜ refl = nj-hiR (f n) (w n) (e n) r q cv aq d

  -- 节点是规范路径, 帧有证据
  module _ (full : Full st) where
    nj-₁ : (w : WFˢ c₁) (s : c₁ ≈ c₁) → ∀ {k t′ j} (r : k < c₁) (q : t′ < c₁) → NT zero r j → (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → NJ (cmpN w s r q cv aq)
    nj-₁ (tg , dir , wt , wg) (Lv.o≈ d se sh) (Lv.fst r) (Lv.fst q) _ cv aq = nj-F wt se (FrG one) r q cv aq
    nj-₁ (tg , dir , wt , wg) (Lv.o≈ d se sh) (Lv.fst r) (Lv.bra y e q) _ cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shlJ d′ _ (nj-F (wg y e) (sh y e y e (≅ᴰ-refl y)) (FrG y) r′ q (u (cov φ̂) cv) aq)
    nj-₁ (tg , dir , wt , wg) (Lv.o≈ d se sh) (Lv.bra x e₁ r) (Lv.fst q) _ (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shrJ d′ _ (nj-F (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) (FrG x) r q′ cv (u (tab E) aq))
    nj-₁ (tg , dir , wt , wg) (Lv.o≈ d se sh) (Lv.bra (suc b) e₁ r) (Lv.bra y e₂ q) (ntB _) (b₀ , cv) ((ℓ , b₁ , ly) , aq) with belR (dmC b₀) | belR-suc st full (dmC b₀)
    ... | just (ℓ′ , b₂ , lx) | _ , refl with at-uq {E} (Lv.o≈ d se sh) b₂ b₁
    ...   | refl with bd {a = suc b} {b = y} lx ly
    ...     | inj₁ s with ⊴p (dir (suc b) e₁ y e₂ s) r
    ...       | viaᴸ d′ r′ u = shlJ d′ _ (nj-F (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) (FrG y) r′ q (u (cov φ̂) cv) aq)
    nj-₁ (tg , dir , wt , wg) (Lv.o≈ d se sh) (Lv.bra (suc b) e₁ r) (Lv.bra y e₂ q) (ntB _) (b₀ , cv) ((ℓ , b₁ , ly) , aq) | just (ℓ , b₂ , lx) | _ , refl | refl | inj₂ s with ⊴p (dir y e₂ (suc b) e₁ s) q
    ...       | viaᴸ d′ q′ u = shrJ d′ _ (nj-F (wg (suc b) e₁) (sh (suc b) e₁ (suc b) e₁ (≅ᴰ-refl (suc b))) (FrG (suc b)) r q′ cv (u (tab E) aq))

    nj-NT : ∀ θ′ (s : c⁺ θ′ ≈ c⁺ θ′) {k t j} (r : k < c⁺ θ′) (q : t < c⁺ θ′) → NT θ′ r j → (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → NJ (cmpN (wf⁺ θ′) s r q cv aq)
    nj-NT zero s r q n cv aq = nj-₁ (wf⁺ zero) s r q n cv aq
    nj-NT (suc a) (Lv.s≈ e) (Lv.suc r) Lv.zero (nts n) cv aq = tt
    nj-NT (suc a) (Lv.s≈ e) (Lv.suc r) (Lv.suc q) (nts n) cv aq = nj-NT a e r q n cv aq
    nj-NT (lim f s₀) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) (ntl .n nn) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ (λ i → ⊴⁺ (s₀ i)) n<m) r | pnt-steps s₀ n<m r nn
    ...   | viaᴸ d′ r′ u | ntv nn′ = shlJ d′ _ (nj-NT (f m) (e m) r′ q nn′ (u (cov φ̂) cv) aq)
    nj-NT (lim f s₀) (Lv.l≈ e) (Lv.lim n r) (Lv.lim m q) (ntl .n nn) cv aq | injᵇ m<n with ⊴p (stepsˢ (λ i → ⊴⁺ (s₀ i)) m<n) q
    ...   | viaᴸ d′ q′ u = shrJ d′ _ (nj-NT (f n) (e n) r q′ nn cv (u (tab E) aq))
    nj-NT (lim f s₀) (Lv.l≈ e) (Lv.lim n r) (Lv.lim _ q) (ntl .n nn) cv aq | injᶜ refl = nj-NT (f n) (e n) r q nn cv aq

  -- 闭包对目标
  IsKb IsKa : ∀ {c₂ t₂ g₂ t} → CK c₂ t₂ g₂ t → Set
  IsKb kb = ⊤
  IsKb (ka Q d a) = ⊥
  IsKb kj = ⊥
  IsKa kb = ⊥
  IsKa (ka Q d a) = ⊤
  IsKa kj = ⊥

  sklB : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} (e : lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃) (x : CK c₃ t₃ g₃ t) → IsKb x → IsKb (skl e x)
  sklB e kb h = tt

  skrB : ∀ {c₂ t₂ g₂ t t′} (e : t ≈ t′) (x : CK c₂ t₂ g₂ t′) → IsKb x → IsKb (skr e x)
  skrB e kb h = tt

  sklA : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} (e : lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃) (x : CK c₃ t₃ g₃ t) → IsKa x → IsKa (skl e x)
  sklA e (ka Q d a) h = tt

  skrA : ∀ {c₂ t₂ g₂ t t′} (e : t ≈ t′) (x : CK c₂ t₂ g₂ t′) → IsKa x → IsKa (skr e x)
  skrA e (ka Q d a) h with ≈-moveᴷ (≈-sym e) Q
  ... | viaᴷ d′ Q′ u = tt

  kb-lo : ∀ θ′ (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {c₂ t₂ g₂ t j} (P : Cp (lc c₂ t₂ g₂) (c⁺ θ′)) (q : t < c⁺ θ′) (cv : AdmC (cov φ̂) P) (aq : Adm (tab E) q) → t ≈ ⌜ j ⌝ → IsKb (cmpK w s P q cv aq)
  kb-lo zero w s Lv.self q cv aq d = tt
  kb-lo zero w s (Lv.fst P) q cv aq d = ⊥-elim (NF-lc (fr-cp (FrG one) P))
  kb-lo zero w s (Lv.bra η e P) q cv aq d = ⊥-elim (NF-lc (fr-cp (FrG η) P))
  kb-lo (suc a) w (Lv.s≈ e) (Lv.suc P) Lv.zero cv aq d = ⊥-elim (lo-c d)
  kb-lo (suc a) w (Lv.s≈ e) (Lv.suc P) (Lv.suc q) cv aq d = kb-lo a w e P q cv aq d
  kb-lo (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
  ...   | viaᴷ d′ P′ u = sklB d′ _ (kb-lo (f m) (w m) (e m) P′ q (u (cov φ̂) cv) aq d)
  kb-lo (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d′ q′ u = skrB d′ _ (kb-lo (f n) (w n) (e n) P q′ cv (u (tab E) aq) (≈-trans (≈-sym d′) d))
  kb-lo (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim _ q) cv aq d | injᶜ refl = kb-lo (f n) (w n) (e n) P q cv aq d

  ka-hi : ∀ θ′ (w : WFˢ (c⁺ θ′)) (s : c⁺ θ′ ≈ c⁺ θ′) {c₂ t₂ g₂ t j} (P : Cp (lc c₂ t₂ g₂) (c⁺ θ′)) (q : t < c⁺ θ′) (cv : AdmC (cov φ̂) P) (aq : Adm (tab E) q) → t ≈ c⁺ j → IsKa (cmpK w s P q cv aq)
  ka-hi zero w s P q cv aq d = ⊥-elim (hi-in-c₁ q d)
  ka-hi (suc a) w (Lv.s≈ e) (Lv.suc P) Lv.zero cv aq d = tt
  ka-hi (suc a) w (Lv.s≈ e) (Lv.suc P) (Lv.suc q) cv aq d = ka-hi a w e P q cv aq d
  ka-hi (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
  ...   | viaᴷ d′ P′ u = sklA d′ _ (ka-hi (f m) (w m) (e m) P′ q (u (cov φ̂) cv) aq d)
  ka-hi (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim m q) cv aq d | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d′ q′ u = skrA d′ _ (ka-hi (f n) (w n) (e n) P q′ cv (u (tab E) aq) (≈-trans (≈-sym d′) d))
  ka-hi (lim f s₀) (st′ , w) (Lv.l≈ e) (Lv.lim n P) (Lv.lim _ q) cv aq d | injᶜ refl = ka-hi (f n) (w n) (e n) P q cv aq d
```

## §4 目标

```agda
data Tgt {E : Ents} : ∀ {t} → Tg E t → Ordᴵ → Set where
  tg0 : Tgt t0 zero
  tgL : ∀ {t i} {q : t < c} {aq : Adm (tab E) q} → NT θ q i → Tgt (tp q aq) i

teq : ∀ {E t i} {T : Tg E t} → Tgt T i → t ≈ ⌜ i ⌝
teq tg0 = Lv.z≈
teq (tgL n) = nt≈ n

zz-self : ∀ b → ZZ ⌜ b ⌝ b
zz-self zero = tt
zz-self (suc b) = tt
zz-self (lim f s) = tt

tzz-nt : ∀ {θ′ t i} {q : t < c⁺ θ′} → NT θ′ q i → ZZ t i
tzz-nt (ntF e) = zz-≅ (≅ᴵ-sym e) tt
tzz-nt (ntB {b = b} e) = zz-≅ e (zz-self b)
tzz-nt (nts n) = tzz-nt n
tzz-nt (ntl m n) = tzz-nt n

tzz : ∀ {E t i} {T : Tg E t} → Tgt T i → ZZ t i
tzz tg0 = tt
tzz (tgL n) = tzz-nt n

tfr-nt : ∀ {θ′ t i} {q : t < c⁺ θ′} → NT θ′ q i → FrL t
tfr-nt n = Fr≈ (FrG _) (≈-sym (nt≈ n))

tfr : ∀ {E t i} {T : Tg E t} → Tgt T i → FrL t
tfr tg0 = fz
tfr (tgL n) = tfr-nt n
```

## §5 闭包的界

`Sel` 的位置 `P : Cp c₁ c`: 字面的键.

```agda
lc-one : ∀ {c₀ t g} → Lv.lc c₀ t g ≡ c₁ → c₀ ≡ suc zero
lc-one refl = refl

module SelM (E : Ents) (P : Cp c₁ c) (ap : AdmC (tab E) P) where
  module M = Sel P E ap

  DemF : Ordᴵ → Flr → Set
  DemF X φ = ∀ {K} (k : InF K φ) → Dem X k

  OKS : ∀ {φ} → Ordᴵ → M.Sl φ → Set
  OKS X (M.emp _) = ⊤
  OKS X (M.sel ℓ K₀ a q y d) = K₀ ≺ᴵ X

  Good : ∀ {G : Ents → Set} → Ordᴵ → M.S G → Set
  Good X s = DemF X (M.φ s) × OKS X (M.wit s)

  ok-mg : ∀ {X a b} (w : M.Sl a) (w′ : M.Sl b) → OKS X w → OKS X w′ → OKS X (M.mg w w′)
  ok-mg (M.emp f) (M.emp h) x y = tt
  ok-mg (M.emp f) (M.sel ℓ K a q y′ d) x y = y
  ok-mg (M.sel ℓ K a q x′ d) (M.emp h) x y = x
  ok-mg (M.sel ℓ K a q x′ d) (M.sel ℓ′ K′ a′ q′ y′ d′) x y with at-uq {E} M.kself a a′
  ... | refl = x

  good-⋈ : ∀ {X} {A B : Ents → Set} (s : M.S A) (s′ : M.S B) → Good X s → Good X s′ → Good X (s M.⋈ s′)
  good-⋈ s s′ (d , x) (d′ , y) = (λ { (inl k) → d k ; (inr k) → d′ k }) , ok-mg (M.wit s) (M.wit s′) x y

  zlt-one : ∀ {K} (e : suc zero ⊑ᴵ K) → IsJ (zlt e)
  zlt-one (s⊑ z≅ q) = tt

  -- 帧的 pickW
  pw-good : ∀ {X c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) (aq : AdmC (tab E) Q) K (e : c₅ ⊑ᴵ K) ℓ a (σ : Simᴵ K ℓ) → K ⊑ᴵ X → Good X (M.pickW Q aq K e (ℓ , a , σ))
  pw-good Q aq zero e ℓ a σ h with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = (λ ()) , tt
  ... | inj₁ d = (λ ()) , tt
  pw-good Q aq (suc b) e ℓ a σ h with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = (λ ()) , tt
  ... | inj₁ d = (λ { ink → inj₁ (sim h zero) }) , sim h zero
  pw-good Q aq (lim f s) e ℓ a σ h with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = (λ ()) , tt
  ... | inj₁ d with zlt e
  ...   | nothing = (λ ()) , tt
  ...   | just z = (λ { inb → h }) , sim h z

  pw-just : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) (aq : AdmC (tab E) Q) K (e : c₅ ⊑ᴵ K) ℓ a (σ : Simᴵ K ℓ) → c₅ ≡ suc zero → ∀ X x → IsJ (M.lft (M.pickW Q aq K e (ℓ , a , σ)) X x)
  pw-just Q aq zero (s⊑ _ ()) ℓ a σ refl X x
  pw-just Q aq (suc b) e ℓ a σ eq X x with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = tt
  ... | inj₁ d = tt
  pw-just Q aq (lim f s) e ℓ a σ refl X x with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = tt
  ... | inj₁ d with zlt e | zlt-one e
  ...   | just z | tt = tt

  good-walk : ∀ {a x X} (Q : Cp a c) (aq : AdmC (tab E) Q) {r : Cp x a} → Nb r → (ad : AdmC (tab E) r) → Good X (M.walk Q aq r ad)
  good-walk Q aq nself ad = (λ ()) , tt
  good-walk Q aq (nsuc h) ad = good-walk (Q ⊙ Lv.suc Lv.self) (adm⊙ {tab E} Q aq tt) h ad
  good-walk Q aq (nlim {n = n} h) ad = good-walk (Q ⊙ Lv.lim n Lv.self) (adm⊙ {tab E} Q aq tt) h ad
  good-walk Q aq (nfst h) ad = good-walk (Q ⊙ Lv.fst Lv.self) (adm⊙ {tab E} Q aq tt) h ad

  good-sel : ∀ {X ρ} π (st : St E ρ π) → Full st → (∀ f → Mem π f → fη f ⊑ᴵ X) → Good X (M.selSt π st)
  good-sel tz st full h = (λ ()) , tt
  good-sel {X} (tk f) st full h with st hr | full hr
  ... | fs (just (evd Pf adf lkf (ℓ , b , σ))) a | tt =
    good-⋈ (M.walk Lv.self tt Pf adf) (M.pickW Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , σ))
           (good-walk Lv.self tt (nb⁺ θ Pf NF-lc) adf) (pw-good Pf adf (fη f) _ ℓ _ σ (h f hr))
  good-sel (a ∪ b) st full h =
    good-⋈ (M.selSt a (λ m → st (ml m))) (M.selSt b (λ m → st (mr m))) (good-sel a (λ m → st (ml m)) (λ m → full (ml m)) (λ f m → h f (ml m))) (good-sel b (λ m → st (mr m)) (λ m → full (mr m)) (λ f m → h f (mr m)))

  full-sel : ∀ {ρ} π (st : St E ρ π) → Full st → ∀ X x → Full (M.lft (M.selSt π st) X x)
  full-sel tz st full X x ()
  full-sel (tk f) st full X x m with st hr | full hr
  full-sel (tk f) st full X x hr | fs (just (evd Pf adf lkf (ℓ , b , σ))) a | tt
    with M.lft (M.pickW Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , σ)) X (proj₂ x)
       | pw-just Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) ℓ (at-resp {E} (≈-sym lkf) b) σ (lc-one (key⁺ θ Pf)) X (proj₂ x)
  ... | just _ | tt = tt
  full-sel (a ∪ b) st full X x (ml m) = full-sel a (λ m₁ → st (ml m₁)) (λ m₁ → full (ml m₁)) X (proj₁ x) m
  full-sel (a ∪ b) st full X x (mr m) = full-sel b (λ m₁ → st (mr m₁)) (λ m₁ → full (mr m₁)) X (proj₂ x) m

  -- 目标
  good-walkA : ∀ θ′ {t X i} (Q : Cp (c⁺ θ′) c) (aq : AdmC (tab E) Q) (q : t < c⁺ θ′) (ad : Adm (tab E) q) → NT θ′ q i → i ≺ᴵ X → Good X (M.walkA Q aq q ad)
  good-walkA zero Q aq (Lv.fst Lv.zero) ad (ntF e) h = (λ ()) , tt
  good-walkA zero Q aq (Lv.bra (suc b) e₁ Lv.zero) ((ℓ , a , q) , ad) (ntB x) h with kdec (wf⁺ θ) (sf⁺ θ) Q P E aq ap
  ... | inj₂ n = (λ { (inl ()) ; (inr ()) }) , tt
  ... | inj₁ d = (λ { (inl ink) → inj₁ (≺ᴵ-respˡ x h) ; (inr ()) }) , ≺ᴵ-respˡ x h
  good-walkA (suc a) Q aq (Lv.suc q) ad (nts n) h = good-walkA a (Q ⊙ Lv.suc Lv.self) (adm⊙ {tab E} Q aq tt) q ad n h
  good-walkA (lim f s) Q aq (Lv.lim m q) ad (ntl .m n) h = good-walkA (f m) (Q ⊙ Lv.lim m Lv.self) (adm⊙ {tab E} Q aq tt) q ad n h

  good-tg : ∀ {X t i} {T : Tg E t} → Tgt T i → i ≺ᴵ X → Good X (tgSel P E ap T)
  good-tg tg0 h = (λ ()) , tt
  good-tg (tgL {q = q} {aq = aq} n) h = good-walkA θ Lv.self tt q aq n h

  tg-lft : ∀ {t i} {T : Tg E t} → Tgt T i → ∀ X x → Tgt {E = M.E′ X} (M.lft (tgSel P E ap T) X x) i
  tg-lft tg0 X x = tg0
  tg-lft (tgL n) X x = tgL n

rep-rel : ∀ {i A π m} {y : O A π} {Y : Ordˢ i} → ZZ A i → Emp π → Rs i m y Y → ∀ n → Rs i fr (repᵒ y n) (iter (Y +ˢ_) Ord₊ˢ.zero n)
rep-rel zz e r zero = rz
rep-rel zz e r (suc m) = rwk (R-⊕ zz (le-emp e) r (rep-rel zz e r m))
```

## §6 语义, `toTabR`, 规范化的视图

```agda
cross-u : ∀ {t k i j} → t ≈ c⁺ i → k ≈ ⌜ j ⌝ → (t ≈ k ⊎ Below t k) → ⊥
cross-u et ek (inj₁ d) = lo≠hi (≈-trans d ek) et
cross-u {j = j} et ek (inj₂ (pre d s)) with ≈-move ek s
... | viaᴸ d′ s′ _ with pullG j s′
... | a′ , refl , q = lo≠hi (≈-trans d d′) et

cross-b : ∀ {t k rp i j} → t ≈ ⌜ i ⌝ → k ≈ c⁺ j → k ≈ rp → rp < t → ⊥
cross-b {i = i} et ek d s with ≈-move et s
... | viaᴸ d′ s′ _ with pullG i s′
... | a′ , refl , q = lo≠hi (≈-trans d d′) ek

cu-hi : ∀ {t k i j} → t ≈ c⁺ i → k ≈ c⁺ j → (t ≈ k ⊎ Below t k) → (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
cu-hi et ek (inj₁ d) = inj₂ (c⁺-≈⁻ (≈-trans (≈-sym et) (≈-trans d ek)))
cu-hi {j = j} et ek (inj₂ (pre d s)) with ≈-move ek s
... | viaᴸ d′ s′ _ with pull⁺ j s′
...   | hi refl q = inj₁ (via (c⁺-≈⁻ (≈-trans (≈-sym et) (≈-trans d d′))) q)
...   | lo refl = ⊥-elim (lo≠hi (≈-trans d d′) et)

toTabR-nb : ∀ {E ρ π} (st : St E ρ π) {a b} {Q : Cp a b} → Nb Q → (x : AdmR π Q) → Σ _ λ y → Rd.toTabR st Q x ≡ just y
toTabR-nb st nself x = tt , refl
toTabR-nb st (nsuc h) x = toTabR-nb st h x
toTabR-nb st (nlim h) x = toTabR-nb st h x
toTabR-nb st (nfst h) x = toTabR-nb st h x

toTabR-np : ∀ {E ρ π} (st : St E ρ π) → Full st → ∀ {θ′ rp j} {Q : Cp (Lv.suc rp) (c⁺ θ′)} → NP θ′ Q j → (x : AdmR π Q) → Σ _ λ y → Rd.toTabR st Q x ≡ just y
toTabR-np st full (npF e) x = tt , refl
toTabR-np st full (npB e) (d , x) with Rd.belR st d | belR-suc st full d
... | just u | _ , refl = (u , tt) , refl
toTabR-np st full (nps n) x = toTabR-np st full n x
toTabR-np st full (npl m n) x = toTabR-np st full n x

-- nfK 在闭包的位置上是恒等
data NKV {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) : NK P → Set where
  nkv : ∀ {rl} → NKV P (nk (inj₂ refl) P rl)

nk-id : ∀ {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) → NKV P (nfK P)
nk-id P with nfC c (tc⁺ θ) P | nf-nb c (tc⁺ θ) (nb⁺ θ P NF-lc)
... | nfc (inj₂ refl) .P t r | ni = nkv

-- nfR 的视图: 低层
data NRL (j : Ordᴵ) {k} (r : k < c) : NR r → Set where
  nrl : ∀ {rp d} {Q : Cp (Lv.suc rp) c} {rl} → NP θ Q j → NRL j r (nr {rpR = rp} d Q rl)

nr-lo : ∀ {k j} (r : k < c) → k ≈ ⌜ j ⌝ → NRL j r (nfR r)
nr-lo r dk with nfC c (tc⁺ θ) (toCpS r) | nfP θ (toCpS r) dk
... | nfc (inj₁ (Lv.s≈ d)) Q t rl | npv n = nrl n
... | nfc (inj₂ refl) Q t rl | npv n = nrl n
```
