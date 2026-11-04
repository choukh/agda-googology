# 证书 (四): 折叠的互模拟

> 不含记号. 结论写在 [GuardCert](GuardCert.lagda.md). 层 $c=c_1+1$. `R-ψ`: `Rc post x y` 推出 `ψ` 到层 $\lceil i\rceil$ 的结果与 `ψ̄ y` 有 `Rs`. `R-ψᵒ`: `Rc post x y` 推出 `ψ` 到层 $c_1$ 的结果与 `ψᵒ y` 有 `Rc pre`. 两者都是对 `Rc` 结构的归纳.
>
> - 状态 `Full`: 每个帧都有证据, `Pf` 是 `suc self` (这一层只有一个闭包位置).
> - 目标 `Tgt`: `t0`, 或规范形 `suc (fst zero)`, `suc (bra (b+1) e zero)` ($b\cong i$). 规范形由 `nv` ([GuardWeakNorm](GuardWeakNorm.lagda.md)) 给.
> - **闭包的界 (`bd-le`):** `CvL π φ` 说左边地板的帧 $\sqsubseteq$ 右边地板的每个世界, 取世界 `Fc` 就是 $\sqsubseteq$ `Bd`. 所以左边的界 $\sqsubseteq$ 右边的界, 比较不计算.
> - 目标在 $\lceil i\rceil$ 的折叠, 输出地板是空的 (`eρ`): `rep-rel` 要的 `FlrLe` 由此给.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; module Trich; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.GuardTightCum hiding (ψ; _+_)
open import OCF.Free.Prefix using (Z; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; Ωˢ; toZ)
open Ord₊ˢ
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo; bound; Bd; Fc; evF; iF; FB; liftEv; Top; FM; ubd; InF; ink; inb; inl; inr; Dem; DemB; isB)
open import OCF.Free.Aux using (Mlev; ≅ᴵ→⊑ᴵ)
import OCF.Free.Tree as FT
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTab Dom₀ using (kdec; _⊙_; adm⊙; Strict; stCp)
open import OCF.Align.GuardTightTree using (O; Us; Vs; o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl; outU; intoU; trL⁻; trO; tr⁻O; repᵒ; Ω̇; _⊕_; rdZ; adm-wk; oc≅; module Emb)
open import OCF.Align.GuardWeakTree
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; FrL; fz; fs′; fl; FrG; Emp; ZZ; zz-≅; cb-sem; cu-sem; clash; out-intoU)
open import OCF.Align.GuardWeakNorm using (NV; nvF; nvB; nv; belR-suc)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardCertRel
open import OCF.Align.GuardCertHi
open import OCF.Align.GuardCertNf using (lc-absurd)

open FoldW cT wf₁ (Lv.s≈ sf₁) tcʷ
```

## §1 状态: 证据齐全, 映射齐全

```agda
data Sf {E : Ents} {f : Frm} : Maybe (Evd E f) → Set where
  sf : ∀ {adf lkf blf} → Sf (just (evd (Lv.suc Lv.self) adf lkf blf))

Full : ∀ {E ρ π} → St E ρ π → Set
Full {π = π} st = ∀ {f} (m : Mem π f) → Sf (ev (st m))

mapF : ∀ {E ρ ρ′ f} (w₁ : Wk ρ ρ′) (s : Fs E ρ f) → Sf (ev s) → Sf (ev (mapFs w₁ s))
mapF w₁ (fs e nothing) h = h
mapF w₁ (fs e (just (ab m k))) h = h

fsLow-full : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → Sf (ev s) → Sf (ev (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
fsLow-full lk lt (fs (just (evd (Lv.suc Lv.self) adf lkf (ℓ , b , q))) nothing) sf = sf
fsLow-full lk lt (fs (just (evd (Lv.suc Lv.self) adf lkf (ℓ , b , q))) (just (ab m k))) sf = sf

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

keepF-false : ∀ {E ρ f k} (s : Fs E ρ f) (r₁ : k < c₁) {a : Adm (tab E) r₁} → Sf (ev s) → keepF s {Lv.suc r₁} a ≡ false
keepF-false (fs (just (evd (Lv.suc Lv.self) adf lkf blf)) a) r₁ sf = refl

trim-emp : ∀ {E ρ k} (π : Fl) (st : St E ρ π) (r₁ : k < c₁) (ar : Adm (tab E) r₁) → Full st → Emp (ξᵗ (trim π st {Lv.suc r₁} ar))
trim-emp tz st r₁ ar full ()
trim-emp (tk f) st r₁ ar full m with keepF (st hr) {Lv.suc r₁} ar | keepF-false (st hr) r₁ {ar} (full hr)
trim-emp (tk f) st r₁ ar full () | false | refl
trim-emp (a ∪ b) st r₁ ar full m with trim a (λ m₁ → st (ml m₁)) {Lv.suc r₁} ar | trim-emp a (λ m₁ → st (ml m₁)) r₁ ar (λ m₁ → full (ml m₁)) | trim b (λ m₁ → st (mr m₁)) {Lv.suc r₁} ar | trim-emp b (λ m₁ → st (mr m₁)) r₁ ar (λ m₁ → full (mr m₁))
trim-emp (a ∪ b) st r₁ ar full (ml m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = ha m
trim-emp (a ∪ b) st r₁ ar full (mr m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = hb m

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

IsJ : ∀ {A : Set} → Maybe A → Set
IsJ (just _) = ⊤
IsJ nothing = ⊥

AbF : ∀ {E ρ π} → St E ρ π → Set
AbF {π = π} st = ∀ {f} (m : Mem π f) → IsJ (abm (st m))

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
```

## §2 比较: 输出, 不答 `cj`

```agda
fr-pl : ∀ {a b} → FrL b → (s : a < b) → Emp (pFl s)
fr-pl (fs′ h) Lv.zero ()
fr-pl (fs′ h) (Lv.suc s) m = fr-pl h s m
fr-pl (fl h) (Lv.lim n s) m = fr-pl (h n) s m

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

  fr-just : ∀ {a b} → FrL b → (s : a < b) (x : Adm (cov φ̂) s) → IsJ (covOut s x)
  fr-just (fs′ h) Lv.zero x = tt
  fr-just (fs′ h) (Lv.suc s) x = fr-just h s x
  fr-just (fl h) (Lv.lim n s) x = fr-just (h n) s x

  -- 路径上的帧被 π 支配
  fv-pl : ∀ {a b} (s : a < b) → Adm (cov φ̂) s → FV (pFl s) π
  fv-pl Lv.zero _ f′ ()
  fv-pl (Lv.suc s) x = fv-pl s x
  fv-pl (Lv.lim n s) x = fv-pl s x
  fv-pl (Lv.fst s) x = fv-pl s x
  fv-pl (Lv.bra η e s) (u , x) f′ (ml hr) with dmC u
  ... | f , m , lk , lt = f , m , ⊲→⊑ lt
  fv-pl (Lv.bra η e s) (u , x) f′ (mr m) = fv-pl s x f′ m

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

  IsS : Ordᴵ → Set
  IsS zero = ⊥
  IsS (suc _) = ⊤
  IsS (lim _ _) = ⊥

  BS : ∀ {k c t g} → k < Lv.lc c t g → Set
  BS (Lv.fst _) = ⊤
  BS (Lv.bra η e _) = IsS η

  module _ (full : ∀ {f} (m : Mem π f) → Σ _ λ d → ev (st m) ≡ just d) where
    nj-c : ∀ {c t g} (w : WFˢ (Lv.lc c t g)) (s : Lv.lc c t g ≈ Lv.lc c t g) → FrL t → (∀ y e → FrL (g y e)) → ∀ {k t′} (r : k < Lv.lc c t g) (q : t′ < Lv.lc c t g) → BS r → (cv : Adm (cov φ̂) r) (aq : Adm (tab E) q) → NJ (cmpN w s r q cv aq)
    nj-c (tg , dir , wt , wg) (Lv.o≈ d se sh) Ft Fg (Lv.fst r) (Lv.fst q) _ cv aq = nj-F wt se Ft r q cv aq
    nj-c (tg , dir , wt , wg) (Lv.o≈ d se sh) Ft Fg (Lv.fst r) (Lv.bra y e q) _ cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shlJ d′ _ (nj-F (wg y e) (sh y e y e (≅ᴰ-refl y)) (Fg y e) r′ q (u (cov φ̂) cv) aq)
    nj-c (tg , dir , wt , wg) (Lv.o≈ d se sh) Ft Fg (Lv.bra x e₁ r) (Lv.fst q) _ (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shrJ d′ _ (nj-F (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) (Fg x e₁) r q′ cv (u (tab E) aq))
    nj-c (tg , dir , wt , wg) (Lv.o≈ d se sh) Ft Fg (Lv.bra (suc b) e₁ r) (Lv.bra y e₂ q) tt (b₀ , cv) ((ℓ , b₁ , ly) , aq) with belR (dmC b₀) | belR-suc st full (dmC b₀)
    ... | just (ℓ′ , b₂ , lx) | _ , refl with at-uq {E} (Lv.o≈ d se sh) b₂ b₁
    ...   | refl with bd {a = suc b} {b = y} lx ly
    ...     | inj₁ s with ⊴p (dir (suc b) e₁ y e₂ s) r
    ...       | viaᴸ d′ r′ u = shlJ d′ _ (nj-F (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) (Fg y e₂) r′ q (u (cov φ̂) cv) aq)
    nj-c (tg , dir , wt , wg) (Lv.o≈ d se sh) Ft Fg (Lv.bra (suc b) e₁ r) (Lv.bra y e₂ q) tt (b₀ , cv) ((ℓ , b₁ , ly) , aq) | just (ℓ , b₂ , lx) | _ , refl | refl | inj₂ s with ⊴p (dir y e₂ (suc b) e₁ s) q
    ...       | viaᴸ d′ q′ u = shrJ d′ _ (nj-F (wg (suc b) e₁) (sh (suc b) e₁ (suc b) e₁ (≅ᴰ-refl (suc b))) (Fg (suc b) e₁) r q′ cv (u (tab E) aq))
```

## §3 到 $c_1$ 的折叠

```agda
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

no-zero : ∀ {j} → (c₁ ≈ ⌜ j ⌝) → ⊥
no-zero = lc-absurd

s₀ : Lv.zero < c₁
s₀ = Lv.fst Lv.zero

s₁ : ∀ b (e : one ⊑ᴵ suc b) → ⌜ b ⌝ < c₁
s₁ b e = Lv.bra (suc b) e Lv.zero

Tz : ∀ {E} → Tg E c₁
Tz = tp Lv.zero tt

R-ψᵒ : ∀ {E ρ π φ} (st : St E ρ π) → FV ρ π → AbF st → ∀ {x : O cT π} {y : FT.O (suc zero) φ} → Rc post x y →
       Rc pre (ψ E Tz st x) (FT.ψᵒ {α = suc zero} {t = zero} zero y)
R-ψᵒ st fv ab′ cz = cwl (cwr RΩ̇₀)
R-ψᵒ {φ = φ} st fv ab′ (cs {x = x} c r) = cl (rep-Rc (cv-fv fv c proj₂) (R-ψᵒ st fv ab′ r))
R-ψᵒ st fv ab′ (cl h) = cl (λ n → R-ψᵒ st fv ab′ (h n))
R-ψᵒ st fv ab′ (cwl {π = π′} {w = w} r) with lowerSt π′ (cov-exact w) st | lower-fv π′ (cov-exact w) st | lower-ab π′ (cov-exact w) st ab′
... | σ , st′ , cv₁ | fv′ | ab″ = cvl (R-ψᵒ st′ fv′ ab″ r)
R-ψᵒ st fv ab′ (cvl {π = π′} {w = w} r) with lowerSt π′ w st | lower-fv π′ w st | lower-ab π′ w st ab′
... | σ , st′ , cv₁ | fv′ | ab″ = cvl (R-ψᵒ st′ fv′ ab″ r)
R-ψᵒ st fv ab′ (cwr r) = cwr (R-ψᵒ st fv ab′ r)
R-ψᵒ st fv ab′ (cmp {x = x} r) = R-ψᵒ st fv ab′ {x = x} r
R-ψᵒ st fv ab′ (ci Lv.zero dk prem) = ⊥-elim (no-zero dk)
R-ψᵒ {E} {ρ} {π} st fv ab′ (ci {j = j} (Lv.suc r₁) {cv = cv} {h = h} {f = f} dk prem) with nfR (Lv.suc r₁) | nv r₁ dk
... | nr d Q rl₁ | nvF _ =
  cvl (ci s₀ (≈-trans (≈-sym e₀) (lk≈′ d dk))
          (λ ξ em z ẑ l → subst (λ u → Rc pre (ψ E Tz (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU (Lv.suc r₁) (trL⁻ d (tr⁻O e₀ u))))) (FT.ψᵒ {α = suc zero} {t = zero} zero (f ẑ)))
                                (sym (out-intoU s₀ z))
                                (R-ψᵒ (stξ ξ (λ m → mapFs ml (st m))) (fv-ξ ξ (fv-ml fv (NJM.fv-pl st (covOf Q (rl₁ π cv)) s₀ tt))) (ab-ξ ξ (λ m → mapFs ml (st m)) (ab-ml ml st ab′))
                                      (prem ξ em (trL⁻ d (tr⁻O e₀ z)) ẑ (R-trL⁻ d (R-tr⁻O e₀ l))))))
  where
  e₀ : _ ≈ _
  e₀ = selfAt (Lv.s≈ sf₁) (Lv.suc (Lv.fst {g = _} Lv.zero))
R-ψᵒ {E} {ρ} {π} st fv ab′ (ci {j = j} (Lv.suc r₁) {cv = cv} {h = h} {f = f} dk prem) | nr d Q rl₁ | nvB {b = b} {e = e₁} _ with Cmp.covOut st (covOf Q (rl₁ π cv)) (s₁ b e₁) (admFromS (toCpS (s₁ b e₁)) (admP (toCpS (s₁ b e₁)))) | NJM.cov-just st (covOf Q (rl₁ π cv)) ab′ (s₁ b e₁) (admFromS (toCpS (s₁ b e₁)) (admP (toCpS (s₁ b e₁))))
...   | nothing | ()
...   | just cs₁ | tt =
  cvl (ci (s₁ b e₁) (≈-trans (≈-sym e₀) (lk≈′ d dk))
          (λ ξ em z ẑ l → subst (λ u → Rc pre (ψ E Tz (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU (Lv.suc r₁) (trL⁻ d (tr⁻O e₀ u))))) (FT.ψᵒ {α = suc zero} {t = zero} zero (f ẑ)))
                                (sym (out-intoU (s₁ b e₁) z))
                                (R-ψᵒ (stξ ξ (λ m → mapFs ml (st m))) (fv-ξ ξ (fv-ml fv (NJM.fv-pl st (covOf Q (rl₁ π cv)) (s₁ b e₁) (admFromS (toCpS (s₁ b e₁)) (admP (toCpS (s₁ b e₁))))))) (ab-ξ ξ (λ m → mapFs ml (st m)) (ab-ml ml st ab′))
                                      (prem ξ em (trL⁻ d (tr⁻O e₀ z)) ẑ (R-trL⁻ d (R-tr⁻O e₀ l))))))
  where
  e₀ : _ ≈ _
  e₀ = selfAt (Lv.s≈ sf₁) (Lv.suc (s₁ b e₁))
R-ψᵒ st fv ab′ (cŝ ec rt rg) = cŝ ec (R-ψᵒ st fv ab′ rt) (λ η e e′ → R-ψᵒ st fv ab′ (rg η e e′))
R-ψᵒ st fv ab′ (cĉ ec dz dg ro rg) = cĉ ec dz dg (R-ψᵒ st fv ab′ ro) (λ η e e′ → R-ψᵒ st fv ab′ (rg η e e′))
R-ψᵒ {E} {ρ} {π} st fv ab′ (ccl cv rt rg) =
  cvl (cwr (ccl (cv-fv (fv-ml fv fv-tz) cv proj₂)
                (cwr (R-ψᵒ (λ m → mapFs ml (st m)) (fv-ml fv fv-tz) (ab-ml ml st ab′) rt))
                (λ η e′ → cwr (R-ψᵒ _ (fv-br η e′ _) (λ { (ml m) → ab-map (λ u → ml (ml u)) (st m) (ab′ m) ; (mr hr) → tt }) (rg η _)))))
  where
  fv-br : ∀ η e′ e₁ → FV ((ρ ∪ tz) ∪ tk (frm one ⌜ one ⌝ G₁ η e′)) (π ∪ tk (frm one ⌜ one ⌝ G₁ η e₁))
  fv-br η e′ e₁ f′ (ml (ml m)) with fv f′ m
  ... | f₀ , m₁ , l = f₀ , ml m₁ , l
  fv-br η e′ e₁ f′ (ml (mr ()))
  fv-br η e′ e₁ f′ (mr hr) = frm one ⌜ one ⌝ G₁ η e₁ , mr hr , ⊑ᴵ-refl
```

## §4 目标

```agda
Lk₁ : Cp c₁ cT
Lk₁ = Lv.suc Lv.self

data Tgt {E : Ents} : ∀ {t} → Tg E t → Ordᴵ → Set where
  tg0 : Tgt t0 zero
  tgF : ∀ {i aq} → i ≅ᴵ zero → Tgt (tp (Lv.suc s₀) aq) i
  tgB : ∀ {b e i aq} → b ≅ᴵ i → Tgt (tp (Lv.suc (s₁ b e)) aq) i

teq : ∀ {E t i} {T : Tg E t} → Tgt T i → t ≈ ⌜ i ⌝
teq tg0 = Lv.z≈
teq (tgF e) = ⌜≈⌝ (≅ᴵ-sym e)
teq (tgB e) = ⌜≈⌝ e

zz-self : ∀ b → ZZ ⌜ b ⌝ b
zz-self zero = tt
zz-self (suc b) = tt
zz-self (lim f s) = tt

tzz : ∀ {E t i} {T : Tg E t} → Tgt T i → ZZ t i
tzz tg0 = tt
tzz (tgF e) = zz-≅ (≅ᴵ-sym e) tt
tzz (tgB {b = b} e) = zz-≅ e (zz-self b)

tfr : ∀ {E t i} {T : Tg E t} → Tgt T i → FrL t
tfr tg0 = fz
tfr (tgF e) = fz
tfr (tgB {b = b} e) = FrG b

-- 选择的好性质
module SelM (E : Ents) where
  module M = Sel Lk₁ E tt

  DemF : Ordᴵ → Flr → Set
  DemF X φ = ∀ {K} (k : InF K φ) → Dem X k

  OKS : ∀ {φ} → Ordᴵ → M.Sl φ → Set
  OKS X (M.emp _) = ⊤
  OKS X (M.sel ℓ K₀ a q y d) = K₀ ≺ᴵ X

  EmpOK : ∀ {φ} → Ordᴵ → M.Sl φ → Set
  EmpOK X (M.emp _) = suc zero ⊑ᴵ X
  EmpOK X (M.sel _ _ _ _ _ _) = ⊤

  Good : ∀ {G : Ents → Set} → Ordᴵ → M.S G → Set
  Good X s = DemF X (M.φ s) × OKS X (M.wit s)

  ok-mg : ∀ {X a b} (w : M.Sl a) (w′ : M.Sl b) → OKS X w → OKS X w′ → OKS X (M.mg w w′)
  ok-mg (M.emp f) (M.emp h) x y = tt
  ok-mg (M.emp f) (M.sel ℓ K a q y′ d) x y = y
  ok-mg (M.sel ℓ K a q x′ d) (M.emp h) x y = x
  ok-mg (M.sel ℓ K a q x′ d) (M.sel ℓ′ K′ a′ q′ y′ d′) x y with at-uq {E} M.kself a a′
  ... | refl = x

  eo-l : ∀ {X a b} (w : M.Sl a) (w′ : M.Sl b) → EmpOK X w → EmpOK X (M.mg w w′)
  eo-l (M.emp f) (M.emp h) x = x
  eo-l (M.emp f) (M.sel ℓ K a q y′ d) x = tt
  eo-l (M.sel ℓ K a q x′ d) (M.emp h) x = tt
  eo-l (M.sel ℓ K a q x′ d) (M.sel ℓ′ K′ a′ q′ y′ d′) x with at-uq {E} M.kself a a′
  ... | refl = tt

  eo-r : ∀ {X a b} (w : M.Sl a) (w′ : M.Sl b) → EmpOK X w′ → EmpOK X (M.mg w w′)
  eo-r (M.emp f) (M.emp h) x = x
  eo-r (M.emp f) (M.sel ℓ K a q y′ d) x = tt
  eo-r (M.sel ℓ K a q x′ d) (M.emp h) x = tt
  eo-r (M.sel ℓ K a q x′ d) (M.sel ℓ′ K′ a′ q′ y′ d′) x with at-uq {E} M.kself a a′
  ... | refl = tt

  good-⋈ : ∀ {X} {A B : Ents → Set} (s : M.S A) (s′ : M.S B) → Good X s → Good X s′ → Good X (s M.⋈ s′)
  good-⋈ s s′ (d , x) (d′ , y) = (λ { (inl k) → d k ; (inr k) → d′ k }) , ok-mg (M.wit s) (M.wit s′) x y

  zlt-one : ∀ {K} (e : suc zero ⊑ᴵ K) → IsJ (zlt e)
  zlt-one (s⊑ z≅ q) = tt

  -- 帧的 pickW
  pw-good : ∀ {X} K (e : suc zero ⊑ᴵ K) ℓ a (σ : Simᴵ K ℓ) → K ⊑ᴵ X → Good X (M.pickW Lk₁ tt K e (ℓ , a , σ))
  pw-good zero e ℓ a σ h = (λ ()) , tt
  pw-good (suc b) e ℓ a σ h = (λ { ink → inj₁ (sim h zero) }) , sim h zero
  pw-good (lim f s) e ℓ a σ h with zlt e | zlt-one e
  ... | just z | tt = (λ { inb → h }) , sim h z

  pw-just : ∀ K (e : suc zero ⊑ᴵ K) ℓ a (σ : Simᴵ K ℓ) X x → IsJ (M.lft (M.pickW Lk₁ tt K e (ℓ , a , σ)) X x)
  pw-just zero (s⊑ _ ()) ℓ a σ X x
  pw-just (suc b) e ℓ a σ X x = tt
  pw-just (lim f s) e ℓ a σ X x with zlt e | zlt-one e
  ... | just z | tt = tt

  good-sel : ∀ {X ρ} π (st : St E ρ π) → Full st → (∀ f → Mem π f → fη f ⊑ᴵ X) → Good X (M.selSt π st)
  good-sel tz st full h = (λ ()) , tt
  good-sel {X} (tk f) st full h with st hr | full hr
  ... | fs (just (evd (Lv.suc Lv.self) adf lkf (ℓ , b , σ))) a | sf =
    good-⋈ (M.walk Lv.self tt Lk₁ adf) (M.pickW Lk₁ adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , σ)) ((λ ()) , tt) (pw-good (fη f) _ ℓ _ σ (h f hr))
  good-sel (a ∪ b) st full h =
    good-⋈ (M.selSt a (λ m → st (ml m))) (M.selSt b (λ m → st (mr m))) (good-sel a (λ m → st (ml m)) (λ m → full (ml m)) (λ f m → h f (ml m))) (good-sel b (λ m → st (mr m)) (λ m → full (mr m)) (λ f m → h f (mr m)))

  full-sel : ∀ {ρ} π (st : St E ρ π) → Full st → ∀ X x → Full (M.lft (M.selSt π st) X x)
  full-sel tz st full X x ()
  full-sel (tk f) st full X x m with st hr | full hr
  full-sel (tk f) st full X x hr | fs (just (evd (Lv.suc Lv.self) adf lkf (ℓ , b , σ))) a | sf
    with M.lft (M.pickW Lk₁ tt (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , σ)) (X) (proj₂ x)
       | pw-just (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) ℓ (at-resp {E} (≈-sym lkf) b) σ X (proj₂ x)
  ... | just _ | tt = sf
  full-sel (a ∪ b) st full X x (ml m) = full-sel a (λ m₁ → st (ml m₁)) (λ m₁ → full (ml m₁)) X (proj₁ x) m
  full-sel (a ∪ b) st full X x (mr m) = full-sel b (λ m₁ → st (mr m₁)) (λ m₁ → full (mr m₁)) X (proj₂ x) m

  -- 目标
  good-tg : ∀ {X t i} {T : Tg E t} → Tgt T i → i ≺ᴵ X → Good X (tgSel Lk₁ E tt T)
  good-tg tg0 h = (λ ()) , tt
  good-tg (tgF e) h = (λ ()) , tt
  good-tg (tgB e) h = (λ { (inl ink) → inj₁ (≺ᴵ-respˡ e h) }) , ≺ᴵ-respˡ e h

  eo-tg : ∀ {X t i} {T : Tg E t} → Tgt T i → i ≺ᴵ X → EmpOK X (M.wit (tgSel Lk₁ E tt T))
  eo-tg tg0 (via d r) = s⊑ d r
  eo-tg (tgF e) (via d r) = s⊑ (≅ᴵ-trans (≅ᴵ-sym e) d) r
  eo-tg (tgB e) h = tt

  tg-lft : ∀ {t i} {T : Tg E t} → Tgt T i → ∀ X x → Tgt {E = M.E′ X} (M.lft (tgSel Lk₁ E tt T) X x) i
  tg-lft tg0 X x = tg0
  tg-lft (tgF e) X x = tgF e
  tg-lft (tgB e) X x = tgB e
```

## §5 到 $\lceil i\rceil$ 的折叠

```agda
rep-rel : ∀ {i A π m} {y : O A π} {Y : Ordˢ i} → ZZ A i → Emp π → Rs i m y Y → ∀ n → Rs i fr (repᵒ y n) (iter (Y +ˢ_) Ord₊ˢ.zero n)
rep-rel zz e r zero = rz
rep-rel zz e r (suc m) = rwk (R-⊕ zz (le-emp e) r (rep-rel zz e r m))

fullJ : ∀ {E ρ π} {st : St E ρ π} → Full st → ∀ {f} (m : Mem π f) → Σ _ λ d → ev (st m) ≡ just d
fullJ {st = st} full m with ev (st m) | full m
... | just _ | sf = _ , refl

R-ψ : ∀ {ρ π t i B φ ℓ} (E : Ents) (T : Tg E t) → Tgt T i → (st : St E ρ π) → Full st → Emp ρ → {x : O cT π} {y : FT.O B φ} → Rc post x y →
      (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) → Rs i fr (ψ E T st x) (FT.ψ̄ y ev₁ p)

module RiseM {ρ π t i k j} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) (eρ : Emp ρ)
             (r₁ : k < c₁) (cv′ : Adm (cov π) (Lv.suc r₁)) {h : ∀ ξ → Us cT (Lv.suc r₁) ξ → O cT (ξ ∪ π)} {B φ} {f : Ordˢ j → FT.O B φ}
             (dk : k ≈ ⌜ j ⌝)
             (prem : ∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → Rs j fr z ẑ → Rc post (h ξ (intoU (Lv.suc r₁) z)) (f ẑ))
             (ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) {ℓ} (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) where

  body-rel : ∀ {rp} (d : Lk k rp) (r′ : rp < c₁) (aq : Adm (tab E) (Lv.suc r′)) → Tgt (tp (Lv.suc r′) aq) j →
             ∀ ξ (w : Wk ξ π) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) → Emp ξ →
             Rs i fr (ol (λ n → ψ E T (stBody ξ w st) (h ξ (intoU (Lv.suc r₁) (chainᵒ (Tc-at (Lv.suc r₁) tcʷ) (λ z → trL⁻ d (ψ E (tp (Lv.suc r′) aq) (stChain ξ bk w st) (h ξ (intoU (Lv.suc r₁) z)))) n)))))
                     (Ord₊ˢ.lim (λ m → FT.ψ̄ (f (iter (λ x → FT.ψ̄ (f x) ev₁ (ac ev₁)) (Ωˢ j) m)) ev₁ p))
  body-rel d r′ aq tq ξ w bk em′ = rl (λ n → R-ψ E T tg (stBody ξ w st) (full-body ξ w st full) eρ (prem ξ em′ _ _ (ch n)) ev₁ p)
    where
    ch : ∀ n → Rs j fr (chainᵒ (Tc-at (Lv.suc r₁) tcʷ) (λ z → trL⁻ d (ψ E (tp (Lv.suc r′) aq) (stChain ξ bk w st) (h ξ (intoU (Lv.suc r₁) z)))) n) (iter (λ x → FT.ψ̄ (f x) ev₁ (ac ev₁)) (Ωˢ j) n)
    ch zero = rwk (fr-of (RΩ̇ j dk (Tc-at (Lv.suc r₁) tcʷ)))
    ch (suc n) = R-trL⁻ d (R-ψ E (tp (Lv.suc r′) aq) tq (stChain ξ bk w st) (full-chain ξ bk w st full) em′ (prem ξ em′ _ _ (ch n)) ev₁ (ac ev₁))

  rise-rel : Rs i fr (riseΩ E T st (Lv.suc r₁) cv′ h) (Ord₊ˢ.lim (λ m → FT.ψ̄ (f (iter (λ x → FT.ψ̄ (f x) ev₁ (ac ev₁)) (Ωˢ j) m)) ev₁ p))
  rise-rel with nfR (Lv.suc r₁) | nv r₁ dk
  ... | nr d Q rl₁ | nvF e with trim π st {Lv.suc s₀} tt | trim-emp π st s₀ tt full
  ...   | mkTr ξ w bk | em′ = body-rel d s₀ tt (tgF e) ξ w bk em′
  rise-rel | nr d Q rl₁ | nvB {b = b} {e = e₁} e with Rd.belR st (proj₁ (rl₁ π cv′)) | belR-suc st (fullJ {st = st} full) (proj₁ (rl₁ π cv′))
  ... | just u | _ , refl with trim π st {Lv.suc (s₁ b e₁)} (u , tt) | trim-emp π st (s₁ b e₁) (u , tt) full
  ...   | mkTr ξ w bk | em′ = body-rel d (s₁ b e₁) (u , tt) (tgB e) ξ w bk em′

  -- 目标在节点之上: 比较的结果 cb
  cb-row : ∀ {rp rp′ j′} (d : Lk k rp) (d′ : rp ≈ rp′) (s : rp′ < t) → Emp (pFl s) → (e : j ≅ᴵ j′) (r₂ : j′ <ᴵ i) →
           ∀ {w : Cov (ρ ∪ pFl s) ρ} →
           Rs i fr (ocv w (oΩ s (adm-wk mr s (admPl s)) (λ ξ y → ψ E T (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU (Lv.suc r₁) (trL⁻ d (tr⁻O d′ (outU s y))))))))
                   (Ord₊ˢ.limᵢ r₂ (λ y → FT.ψ̄ (f (tr⁻ˢ e (outˢ (<→◃ r₂) y))) ev₁ p))
  cb-row d d′ s es e r₂ =
    rcv (rΩ s _ r₂ (≈-trans (≈-sym d′) (≈-trans (lk≈′ d dk) (⌜≈⌝ e)))
           (λ ξ em′ z ẑ l → subst₂ (λ u v → Rs i fr (ψ E T (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU (Lv.suc r₁) (trL⁻ d (tr⁻O d′ u))))) (FT.ψ̄ (f (tr⁻ˢ e v)) ev₁ p))
                                   (sym (out-intoU s z)) (sym (out-intoˢ (<→◃ r₂) ẑ))
                                   (R-ψ E T tg (stξ ξ (λ m → mapFs ml (st m))) (full-ξ ξ em′ (λ m → mapFs ml (st m)) (full-ml ml st full))
                                        (λ { (ml m) → em′ m ; (mr (ml m)) → eρ m ; (mr (mr m)) → es m })
                                        (prem ξ em′ _ _ (R-tr⁻ˢ e (R-trL⁻ d (R-tr⁻O d′ (outR (<→◃ r₂) l))))) ev₁ p)))

-- 闭包
module CloM {ρ π t i} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) (eρ : Emp ρ)
            {x : O cT π} {g : ∀ η e → O cT (π ∪ tk (Fr₁ η e))} {B φ} {t̂ : FT.O B (φ ⊔ fk zero)} {ĝ : ∀ η → FT.O B (φ ⊔ fk η)}
            (cv : CvL π φ) (rt : Rc post x t̂) (rg : ∀ η e → Rc post (g η e) (ĝ η)) {ℓ} (ev₁ : Ev ℓ (φ ⊔ fk zero)) (p : i <ᴵ ℓ) where
  open SelM E

  SS : M.S (λ F → St F ρ π × (Tg F t × AdmC (tab F) Lk₁))
  SS = SSc E T st Lk₁ tt

  BR : Top i ℓ (φ ⊔ fk zero)
  BR = bound (φ ⊔ fk zero) ev₁ p

  X : Ordᴵ
  X = Bd BR

  i≺X : i ≺ᴵ X
  i≺X = sim (FM BR) (iF BR)

  gd-SS : Good X SS
  gd-SS = good-⋈ (M.selSt π st) (M._⋈_ (tgSel Lk₁ E tt T) (M.walk Lv.self tt Lk₁ tt))
            (good-sel π st full (λ f m → ⊑ᴵ-trans (cv f m (proj₁ (evF BR))) (FM BR)))
            (good-⋈ (tgSel Lk₁ E tt T) (M.walk Lv.self tt Lk₁ tt) (good-tg tg i≺X) ((λ ()) , tt))

  eo-SS : EmpOK X (M.wit SS)
  eo-SS = eo-r (M.wit (M.selSt π st)) (M.wit (M._⋈_ (tgSel Lk₁ E tt T) (M.walk Lv.self tt Lk₁ tt)))
            (eo-l (M.wit (tgSel Lk₁ E tt T)) (M.wit (M.walk Lv.self tt Lk₁ tt)) (eo-tg tg i≺X))

  go-rel : (w : M.Sl (M.φ SS)) → OKS X w → EmpOK X w →
           Rs i fr (goC E T st Lk₁ (inj₂ refl) tt x g SS w) (FT.ψ̄ (FT.oclo t̂ ĝ) ev₁ p)
  go-rel (M.emp f) _ e₁ =
    rŝ (tzz tg) e₁ (R-ψ E T tg st full eρ rt ev₁ p)
       (λ η d d′ → R-ψ (M.E′ (suc η)) _ (tg-lft tg (suc η) (proj₁ (proj₂ (f (suc η))))) _
                       (λ { (ml m) → full-sel π st full (suc η) (proj₁ (f (suc η))) m ; (mr hr) → sf }) eρ (rg η _) _ _)
  go-rel (M.sel ℓ₁ K₀ a q y dm) k₁ _ =
    rŝ (tzz tg) (ubd (bound (M.φ SS) y q) k₁ (proj₁ gd-SS)) (R-ψ E T tg st full eρ rt ev₁ p)
       (λ η d d′ → R-ψ (M.E′ _) _ (tg-lft tg _ _) _
                       (λ { (ml m) → full-sel π st full _ _ m ; (mr hr) → sf }) eρ (rg η _) _ _)

  clo-rel : Rs i fr (goC E T st Lk₁ (inj₂ refl) tt x g SS (M.wit SS)) (FT.ψ̄ (FT.oclo t̂ ĝ) ev₁ p)
  clo-rel = go-rel (M.wit SS) (proj₂ gd-SS) eo-SS

R-ψ E T tg st full eρ cz ev₁ p = rwk (fr-of (RΩ̇ _ (teq tg) (tcT T)))
R-ψ E T tg st full eρ (cs c r) ev₁ p = rl (rep-rel (tzz tg) eρ (R-ψ E T tg st full eρ r ev₁ p))
R-ψ E T tg st full eρ (cl h) ev₁ p = rl (λ n → R-ψ E T tg st full eρ (h n) ev₁ p)
R-ψ E T tg st full eρ (cwl {π = π′} {w = w} r) ev₁ p with lowerSt π′ (cov-exact w) st | lower-full π′ (cov-exact w) st full | lower-emp π′ (cov-exact w) st eρ
... | σ , st′ , cv₁ | full′ | eσ = rcv (R-ψ E T tg st′ full′ eσ r ev₁ p)
R-ψ E T tg st full eρ (cvl {π = π′} {w = w} r) ev₁ p with lowerSt π′ w st | lower-full π′ w st full | lower-emp π′ w st eρ
... | σ , st′ , cv₁ | full′ | eσ = rcv (R-ψ E T tg st′ full′ eσ r ev₁ p)
R-ψ E T tg st full eρ (cwr {le = le} r) ev₁ p = R-ψ E T tg st full eρ r (le ev₁) p
R-ψ E T tg st full eρ (cmp {x = x} r) ev₁ p = R-ψ E T tg st full eρ {x = x} r ev₁ p
R-ψ E T tg st full eρ (ci Lv.zero dk prem) ev₁ p = ⊥-elim (lc-absurd dk)
R-ψ E t0 tg0 st full eρ (ci (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p with <ᴵ-dec (ac ev₁) p
... | injᵃ (via e ())
... | injᵇ _ = RiseM.rise-rel E t0 tg0 st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
... | injᶜ _ = RiseM.rise-rel E t0 tg0 st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ E (tp Lv.zero aq) () st full eρ (ci (Lv.suc r₁) dk prem) ev₁ p
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p with nfR (Lv.suc r₁) | nv r₁ dk
... | nr d Q rl₁ | nvF e₀ with Cmp.cmpN st (covOf Q (rl₁ π cv)) wf₁ (Lv.s≈ sf₁) (fromCpS Q) (Lv.suc q₁) (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-c st (covOf Q (rl₁ π cv)) (fullJ {st = st} full) wf₁ sf₁ (FrG one) (λ y e → FrG y) s₀ q₁ tt (admFromS {E = cov (pF Q)} Q (admP Q)) aq | <ᴵ-dec (ac ev₁) p
...   | Cmp.cb d′ s a | _ | injᵃ (via e r₂) with Cmp.covOut st (covOf Q (rl₁ π cv)) s a | NJM.fr-just st (covOf Q (rl₁ π cv)) (tfr tg) s a
...     | just cs₁ | tt = RiseM.cb-row E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p d d′ s (fr-pl (tfr tg) s) e r₂
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvF e₀ | Cmp.cb d′ s a | _ | injᵇ w = ⊥-elim (clash (cb-sem (teq tg) (lk≈′ d dk) d′ s) (inj₁ w))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvF e₀ | Cmp.cb d′ s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem (teq tg) (lk≈′ d dk) d′ s) (inj₂ (≅ᴵ-sym c′)))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvF e₀ | Cmp.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem (teq tg) (lk≈′ d dk) x))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvF e₀ | Cmp.cu x | _ | injᵇ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvF e₀ | Cmp.cu x | _ | injᶜ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ with Cmp.cmpN st (covOf Q (rl₁ π cv)) wf₁ (Lv.s≈ sf₁) (fromCpS Q) (Lv.suc q₁) (admFromS {E = cov (pF Q)} Q (admP Q)) aq | NJM.nj-c st (covOf Q (rl₁ π cv)) (fullJ {st = st} full) wf₁ sf₁ (FrG one) (λ y e → FrG y) (s₁ b e₁) q₁ tt (admFromS {E = cov (pF Q)} Q (admP Q)) aq | <ᴵ-dec (ac ev₁) p
...   | Cmp.cb d′ s a | _ | injᵃ (via e r₂) with Cmp.covOut st (covOf Q (rl₁ π cv)) s a | NJM.fr-just st (covOf Q (rl₁ π cv)) (tfr tg) s a
...     | just cs₁ | tt = RiseM.cb-row E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p d d′ s (fr-pl (tfr tg) s) e r₂
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ | Cmp.cb d′ s a | _ | injᵇ w = ⊥-elim (clash (cb-sem (teq tg) (lk≈′ d dk) d′ s) (inj₁ w))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ | Cmp.cb d′ s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem (teq tg) (lk≈′ d dk) d′ s) (inj₂ (≅ᴵ-sym c′)))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ | Cmp.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem (teq tg) (lk≈′ d dk) x))
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ | Cmp.cu x | _ | injᵇ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ {ρ} {π} {t} {i} E (tp (Lv.suc q₁) aq) tg st full eρ (ci {j = j} (Lv.suc r₁) {cv = cv} {ac = ac} {h = h} {f = f} dk prem) ev₁ p | nr d Q rl₁ | nvB {b = b} {e = e₁} e₀ | Cmp.cu x | _ | injᶜ _ = RiseM.rise-rel E (tp (Lv.suc q₁) aq) tg st full eρ r₁ cv {h = h} {f = f} dk prem ac ev₁ p
R-ψ E T tg st full eρ (cŝ ec rt rg) ev₁ p = rŝ (tzz tg) ec (R-ψ E T tg st full eρ rt ev₁ p) (λ η e e′ → R-ψ E T tg st full eρ (rg η e e′) ev₁ p)
R-ψ E T tg st full eρ (cĉ ec dz dg ro rg) ev₁ p = rĉ ec dz dg (R-ψ E T tg st full eρ ro ev₁ p) (λ η e e′ → R-ψ E T tg st full eρ (rg η e e′) ev₁ p)
R-ψ E t0 tg0 st full eρ (ccl cv rt rg) ev₁ p = CloM.clo-rel E t0 tg0 st full eρ cv rt rg ev₁ p
R-ψ E (tp Lv.zero aq) () st full eρ (ccl cv rt rg) ev₁ p
R-ψ E (tp (Lv.suc q₁) aq) tg st full eρ (ccl cv rt rg) ev₁ p = CloM.clo-rel E (tp (Lv.suc q₁) aq) tg st full eρ cv rt rg ev₁ p
```
