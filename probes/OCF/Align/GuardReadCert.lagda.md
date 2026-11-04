# 第一条证书在统一读法上 (由 [GuardTightCert](GuardTightCert.lagda.md) 用脚本生成)

> 不含记号. 结论写在 [GuardRead](GuardRead.lagda.md). 只差一行: `tc₁` 是 [GuardReadRd](GuardReadRd.lagda.md) 的 `Tc-Ω₁`, 不是 `RdIter.Tc-c`. 证明没有读读法的内容: `nfT c₁ tc₁ r` 是抽象的. 所以 `Good-Ω₁` 换读法不用重证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadCert where

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
open import OCF.Align.GuardTightCum hiding (ψ)
open import OCF.Free.Prefix using (Z; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; Ωˢ; toZ; _≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; ≅ᶻ-sym)
open Ord₊ˢ
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo; bound; Bd; Fc; iF; FM)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Aux using (⊑ᴵ-≅ˡ)
import OCF.Free.Tree as FT
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightCertRel
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; rb-≈₁₁; Good-Ω; Good→WF₁)
open import OCF.Align.GuardReadRd using (Tc-Ω₁)
```

## §1 层号与状态

```agda
c₁ : LG
c₁ = rb₁ (Ω (suc zero))

wf₁ : WFˢ c₁
wf₁ = Good→WF₁ (Good-Ω (suc zero))

sf₁ : c₁ ≈ c₁
sf₁ = rb-≈₁₁ (Ω-refl (suc zero))

tc₁ : Tc c₁
tc₁ = Tc-Ω₁

open Fold c₁ wf₁ sf₁ tc₁

data Sf {E : Ents} {f : Frm} : Maybe (Evd E f) → Set where
  sf : ∀ {adf lkf blf} → Sf (just (evd self adf lkf blf))

Full : ∀ {E ρ π} → St E ρ π → Set
Full {π = π} st = ∀ {f} (m : Mem π f) → Sf (ev (st m))

-- 地板下降, 分支, 链都保持
fsLow-full : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) (lt : fη f ⊲ fη f′) (s : Fs E ρ f′) → Sf (ev s) → Sf (ev (proj₁ (proj₂ (fsLow {f = f} {f′ = f′} lk lt s))))
fsLow-full lk lt (fs (just (evd self adf lkf (ℓ , b , q))) nothing) sf = sf
fsLow-full lk lt (fs (just (evd self adf lkf (ℓ , b , q))) (just (ab m k))) sf = sf

mapF : ∀ {E ρ ρ′ f} (w₁ : Wk ρ ρ′) (s : Fs E ρ f) → Sf (ev s) → Sf (ev (mapFs w₁ s))
mapF w₁ (fs e nothing) h = h
mapF w₁ (fs e (just (ab m k))) h = h

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

full-body : ∀ {E ρ π} (ξ : Fl) (w : Wk ξ π) (st : St E ρ π) → Full st → Full (stBody ξ w st)
full-body ξ w st full (ml m) = full (w m)
full-body ξ w st full (mr m) = full m

full-chain : ∀ {E ρ π} (ξ : Fl) (bk : ∀ {f} → Mem π f → Maybe (Mem ξ f)) (w : Wk ξ π) (st : St E ρ π) → Full st → Full (stChain ξ bk w st)
full-chain ξ bk w st full (ml m) = full (w m)
full-chain ξ bk w st full {f} (mr m) with bk m
... | just m′ = full m
... | nothing = full m

-- 链的地板是空的
keepF-false : ∀ {E ρ f k} (s : Fs E ρ f) {r : k < c₁} (ar : Adm (tab E) r) → Sf (ev s) → keepF s {r} ar ≡ false
keepF-false (fs (just (evd self adf lkf blf)) a) ar sf = refl

trim-emp : ∀ {E ρ k} (π : Fl) (st : St E ρ π) {r : k < c₁} (ar : Adm (tab E) r) → Full st → Emp (ξᵗ (trim π st {r} ar))
trim-emp tz st ar full ()
trim-emp (tk f) st {r} ar full m with keepF (st hr) {r} ar | keepF-false (st hr) {r} ar (full hr)
trim-emp (tk f) st {r} ar full () | false | refl
trim-emp (a ∪ b) st {r} ar full m with trim a (λ m₁ → st (ml m₁)) {r} ar | trim-emp a (λ m₁ → st (ml m₁)) {r} ar (λ m₁ → full (ml m₁)) | trim b (λ m₁ → st (mr m₁)) {r} ar | trim-emp b (λ m₁ → st (mr m₁)) {r} ar (λ m₁ → full (mr m₁))
trim-emp (a ∪ b) st {r} ar full (ml m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = ha m
trim-emp (a ∪ b) st {r} ar full (mr m) | mkTr ξa wa ba | ha | mkTr ξb wb bb | hb = hb m

-- 证据齐全
toTab-just : ∀ {E ρ π} (st : St E ρ π) → Full st → ∀ {a b} (r : a < b) (x : Adm (cov π) r) → Σ _ λ a′ → Vis.toTab st r x ≡ just a′
toTab-just st full Lv.zero x = tt , refl
toTab-just st full (Lv.suc r) x = toTab-just st full r x
toTab-just st full (Lv.lim n r) x = toTab-just st full r x
toTab-just st full (Lv.fst r) x = toTab-just st full r x
toTab-just st full (Lv.bra η e r) ((c₂ , t₂ , g₂ , e₁ , m , k) , x) with ev (st m) | full m | Vis.toTab st r x | toTab-just st full r x
... | just _ | sf | just a′ | a′ , refl = _ , refl
```

## §2 比较不给 `cj`

`Fr c′`: `suc b` 的位置上 $b$ 没有闭包. 证据齐全时 `cmpN` 不答 `cj`. 与 `cmpN` 同一个骨架.

```agda
Fr : LG → Set
Fr Lv.zero = ⊤
Fr (Lv.suc b) = FrL b
Fr (Lv.lim f) = ∀ n → Fr (f n)
Fr (Lv.lc c t g) = Fr t × (∀ η e → Fr (g η e))

FrL→Fr : ∀ {b} → FrL b → Fr b
FrL→Fr fz = tt
FrL→Fr (fs′ h) = h
FrL→Fr (fl h) = λ n → FrL→Fr (h n)

module NJM {E : Ents} {ρ π : Fl} (st : St E ρ π) (full : Full st) where
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
  cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.bra x e₁ r) (Lv.bra y e₂ q) ((c₃ , t₃ , g₃ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) with ev (st m) | full m
  ... | just (evd self adf lkf blf) | sf with belOf {f = frm c₃ t₃ g₃ x e₃} k refl (evd self adf lkf blf)
  ...   | ℓ′ , b₂ , lx with at-uq {E} (Lv.o≈ d se sh) b₂ b₁
  ...     | refl with bd lx ly
  ...       | inj₁ s with ⊴p (dir x e₁ y e₂ s) r
  ...         | viaᴸ d′ r′ u = shlJ d′ _ (cmpNJ (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) (proj₂ fr y e₂) r′ q (u (cov π) cv) aq)
  cmpNJ (tg , dir , wt , wg) (Lv.o≈ d se sh) fr (Lv.bra x e₁ r) (Lv.bra y e₂ q) ((c₃ , t₃ , g₃ , e₃ , m , k) , cv) ((ℓ , b₁ , ly) , aq) | just (evd self adf lkf blf) | sf | ℓ , b₂ , lx | refl | inj₂ s with ⊴p (dir y e₂ x e₁ s) q
  ...         | viaᴸ d′ q′ u = shrJ d′ _ (cmpNJ (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) (proj₂ fr x e₁) r q′ cv (u (tab E) aq))

Fr-c₁ : Fr c₁
Fr-c₁ = fs′′ , (λ η e → FrL→Fr (FrG η))
  where
  fs′′ : FrL Lv.zero
  fs′′ = fz
```

## §3 折叠

`Tgt T i`: 目标的层模 `≈` 是 $\lceil i\rceil$. `R-ψ`: 折叠与 `ψ̄ ∘ tl` 同形.

```agda
data Tgt {E : Ents} : ∀ {t} → Tg E t → Ordᴵ → Set where
  tg0 : Tgt t0 zero
  tgp : ∀ {t i} {q : t < c₁} {aq : Adm (tab E) q} → t ≈ ⌜ i ⌝ → Tgt (tp q aq) i

teq : ∀ {E t i} {T : Tg E t} → Tgt T i → t ≈ ⌜ i ⌝
teq tg0 = Lv.z≈
teq (tgp e) = e

rep-rel : ∀ {i A π} {y : O A π} {Y : Ordˢ i} → Rs i y Y → ∀ n → Rs i (repᵒ y n) (iter (Y +ˢ_) Ord₊ˢ.zero n)
rep-rel r zero = rz
rep-rel r (suc m) = rwk (R-⊕ r (rep-rel r m))

R-ψ : ∀ {k₀ π ρ t i} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st) {x : O c₁ π} {ŷ : Ordˢ k₀} → Rs k₀ x ŷ →
      (φ : Flr) (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) (ℓ : Ordᴵ) (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) →
      Rs i (ψ E T st x) (FT.ψ̄ (FT.tl {c = zero} φ cv ŷ) ev₁ p)

module RiseM {k₀ π ρ t i k j} (E : Ents) (T : Tg E t) (tg : Tgt T i) (st : St E ρ π) (full : Full st)
             (r : k < c₁) (cv′ : Adm (cov π) r) (q : j <ᴵ k₀) {h : ∀ ξ → Us c₁ r ξ → O c₁ (ξ ∪ π)} {f : Uˢ j (<→◃ q) → Ordˢ k₀}
             (dk : k ≈ ⌜ j ⌝)
             (prem : ∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → LRs k₀ (<→◃ q) z ẑ → Rs k₀ (h ξ (intoU r z)) (f (intoˢ (<→◃ q) ẑ)))
             (φ : Flr) (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) (ℓ : Ordᴵ) (ev₁ : Ev ℓ φ) (p : i <ᴵ ℓ) where
  h̃ : Ordˢ j → ∀ {i′ ℓ′} → Ev ℓ′ φ → i′ <ᴵ ℓ′ → Ordˢ i′
  h̃ x e₀ p₀ = FT.ψ̄ (FT.tl {c = zero} φ cv (f (intoˢ (<→◃ q) x))) e₀ p₀

  A′ : j <ᴵ ℓ
  A′ = cv ev₁ q

  rise-rel : Rs i (riseΩ E T st r cv′ h) (Ord₊ˢ.lim (λ m → h̃ (iter (λ x → h̃ x ev₁ A′) (Ωˢ j) m) ev₁ p))
  rise-rel with Vis.toTab st r cv′ | toTab-just st full r cv′
  ... | just a | a , refl with nfT c₁ tc₁ r | trim π st {r} a | trim-emp π st {r} a full
  ...   | nft d r′ tb | mkTr ξ w bk | em′ = rl (λ n → R-ψ E T tg (stBody ξ w st) (full-body ξ w st full) (prem ξ em′ _ _ (intoR (<→◃ q) (ch n))) φ cv ℓ ev₁ p)
    where
    ch : ∀ n → Rs j (chainᵒ (Tc-at r tc₁) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n) (iter (λ x → h̃ x ev₁ A′) (Ωˢ j) n)
    ch zero = rwk (RΩ̇ j dk (Tc-at r tc₁))
    ch (suc n) = R-trL⁻ d (R-ψ E (tp r′ (tb E a)) (tgp (lk≈ d dk)) (stChain ξ bk w st) (full-chain ξ bk w st full) (prem ξ em′ _ _ (intoR (<→◃ q) (ch n))) φ cv ℓ ev₁ A′)

R-ψ {t = t} {i = i} E T tg st full rz φ cv ℓ ev₁ p = rwk (RΩ̇ i (teq tg) (tcT T))
R-ψ E T tg st full (rs r) φ cv ℓ ev₁ p = rl (rep-rel (R-ψ E T tg st full r φ cv ℓ ev₁ p))
R-ψ E T tg st full (rl h) φ cv ℓ ev₁ p = rl (λ n → R-ψ E T tg st full (h n) φ cv ℓ ev₁ p)
R-ψ E T tg st full (rwk {w = w} r) φ cv ℓ ev₁ p = R-ψ E T tg (λ m → st (w m)) (λ m → full (w m)) r φ cv ℓ ev₁ p
R-ψ E T tg st full (rcv {π = π′} {w = w} r) φ cv ℓ ev₁ p with lowerSt π′ w st | lower-full π′ w st full
... | σ , st′ , c′ | h = rcv (R-ψ E T tg st′ h r φ cv ℓ ev₁ p)
R-ψ E T tg st full (rmk r l x) φ cv ℓ ev₁ p = R-ψ E T tg st full x φ cv ℓ ev₁ p
R-ψ {k₀ = suc k′} E T tg st full (rup zero l) φ cv ℓ ev₁ p =
  R-ψ E T tg st full l (flo k′) (cvFlo k′) ℓ (toFlo k′ (λ q → cv ev₁ (suc q))) p
R-ψ {k₀ = lim g s} E T tg st full (rup (self n) l) φ cv ℓ ev₁ p =
  R-ψ E T tg st full l (flo (g n)) (cvFlo (g n)) ℓ (toFlo (g n) (λ q → cv ev₁ (lim n q))) p
R-ψ E t0 tg0 st full (rΩ r cv′ q {h = h₁} {f = f} dk prem) φ cv ℓ ev₁ p with <ᴵ-dec (cv ev₁ q) p
... | injᵃ (via e ())
... | injᵇ _ = RiseM.rise-rel E t0 tg0 st full r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
... | injᶜ _ = RiseM.rise-rel E t0 tg0 st full r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
R-ψ {i = i} E (tp q₁ aq₁) (tgp et) st full (rΩ {k = k} {j = j} r cv′ q {h = h₁} {f = f} dk prem) φ cv ℓ ev₁ p
  with Vis.cmpN st wf₁ sf₁ r q₁ cv′ aq₁ | NJM.cmpNJ st full wf₁ sf₁ Fr-c₁ r q₁ cv′ aq₁ | <ᴵ-dec (cv ev₁ q) p
... | Vis.cb d s a | _ | injᵃ (via e r₂) =
  rΩ s a r₂ (≈-trans (≈-sym d) (≈-trans dk (⌜≈⌝ e)))
     (λ ξ em′ z ẑ l → subst₂ (λ u v → Rs i (ψ E (tp q₁ aq₁) (stξ ξ st) (h₁ ξ (intoU r (tr⁻O d u)))) (FT.ψ̄ (FT.tl {c = zero} φ cv (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) ev₁ p))
                              (sym (out-intoU s z)) (sym (out-intoˢ (<→◃ r₂) ẑ))
                              (R-ψ E (tp q₁ aq₁) (tgp et) (stξ ξ st) (full-ξ ξ em′ st full)
                                   (prem ξ em′ _ _ (intoR (<→◃ q) (R-tr⁻ˢ e (R-tr⁻O d (outR (<→◃ r₂) l))))) φ cv ℓ ev₁ p))
... | Vis.cb d s a | _ | injᵇ w = ⊥-elim (clash (cb-sem et dk d s) (inj₁ w))
... | Vis.cb d s a | _ | injᶜ c′ = ⊥-elim (clash (cb-sem et dk d s) (inj₂ (≅ᴵ-sym c′)))
... | Vis.cu x | _ | injᵃ w = ⊥-elim (clash w (cu-sem et dk x))
... | Vis.cu x | _ | injᵇ _ = RiseM.rise-rel E (tp q₁ aq₁) (tgp et) st full r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
... | Vis.cu x | _ | injᶜ _ = RiseM.rise-rel E (tp q₁ aq₁) (tgp et) st full r cv′ q {h = h₁} {f = f} dk prem φ cv ℓ ev₁ p
```

## §4 第 0 层, 下界不 $\cong$ 的搬运

```agda
Rz : ∀ {π} {y : O Lv.zero π} {ŷ : Ordˢ zero} → Rs zero y ŷ → rdZ y ≅ᶻ toZ ŷ
Rz rz = zᶻ
Rz (rs r) = sᶻ (Rz r)
Rz (rl h) = lᶻ (λ n → Rz (h n))
Rz (rwk {π = π′} {x = x} r) = Rz {π′} {x} r
Rz (rcv {π = π′} {x = x} r) = Rz {π′} {x} r
Rz (rmk () l r)
Rz (rup () l)
Rz (rΩ () cv q d h)

-- 下界只要一个方向: 我的下界 ⊑ 对面的下界. 分支只在同一个 η 上比较.
Goodᴺ-c : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} → c ⊑ᴵ c′ →
          t₀ ≅ᶻ t₀′ → (∀ η e e′ → g η e ≅ᶻ g′ η e′) → o₀ ≅ᶻ o₀′ → (∀ η e e′ → o η e ≅ᶻ o′ η e′) →
          Goodᴺ (Z.ĉᴸ c′ t₀′ g′ o₀′ o′) → Goodᴺ (Z.ĉᴸ c t₀ g o₀ o)
Goodᴺ-c {c} {c′} {t₀} {t₀′} {o₀} {o₀′} {g} {o} {g′} {o′} ec dt dg dp dO (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy′ G₀′ l₀′ Gg′ lE′ Go₀′ Go′ mo₀′ mo′
  where
  dy′ : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m)
  dy′ m = ⊑ᴵ-trans ec (dy m)
  G₀′ : Goodᴺ t₀
  G₀′ = Goodᴺ-tr (≅ᶻ-sym dt) G₀
  l₀′ : forceᴺ t₀ G₀′ ≅ ys 0
  l₀′ = ≅-trans (≅-sym (forceᴺ-≅ (≅ᶻ-sym dt) G₀ G₀′)) l₀
  dgm : ∀ m → g′ (toLevel (ys m) (hy m)) (dy m) ≅ᶻ g (toLevel (ys m) (hy m)) (dy′ m)
  dgm m = ≅ᶻ-sym (dg _ (dy′ m) (dy m))
  Gg′ : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy′ m))
  Gg′ m = Goodᴺ-tr (dgm m) (Gg m)
  lE′ : ∀ m → forceᴺ _ (Gg′ m) ≅ ys (suc m)
  lE′ m = ≅-trans (≅-sym (forceᴺ-≅ (dgm m) (Gg m) (Gg′ m))) (lE m)
  Go₀′ : Goodᴺ o₀
  Go₀′ = Goodᴺ-tr (≅ᶻ-sym dp) Go₀
  dOk : ∀ k → o′ (toLevel (ys k) (hy k)) (dy k) ≅ᶻ o (toLevel (ys k) (hy k)) (dy′ k)
  dOk k = ≅ᶻ-sym (dO _ (dy′ k) (dy k))
  Go′ : ∀ k → Goodᴺ (o (toLevel (ys k) (hy k)) (dy′ k))
  Go′ k = Goodᴺ-tr (dOk k) (Go k)
  mo₀′ : forceᴺ o₀ Go₀′ ⊑⁰ forceᴺ _ (Go′ 0)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (≅ᶻ-sym dp) Go₀ Go₀′))) (⊑-trans mo₀ (≅→⊑ (forceᴺ-≅ (dOk 0) (Go 0) (Go′ 0))))
  mo′ : ∀ k → forceᴺ _ (Go′ k) ⊑⁰ forceᴺ _ (Go′ (suc k))
  mo′ k = ⊑-trans (≅→⊑ (≅-sym (forceᴺ-≅ (dOk k) (Go k) (Go′ k)))) (⊑-trans (mo k) (≅→⊑ (forceᴺ-≅ (dOk (suc k)) (Go (suc k)) (Go′ (suc k)))))
```

## §5 $\psi_0(\Omega_\Omega)$

```agda
ev₀ : Ev (suc zero) FT.Fl
ev₀ = tt , (λ q → q)

B₀ = bound (fz ⊔ fk zero) ev₀ zero

one⊑Bd : suc zero ⊑ᴵ Bd B₀
one⊑Bd with sim (FM B₀) (iF B₀)
... | via d r = s⊑ d r

self≈ : ∀ a → ⌜ a ⌝ ≈ ⌜ a ⌝
self≈ a = ⌜≈⌝ (≅ᴵ-refl a)

Good-Ω₁ : Goodᴺ (T₀ c₁ (wf₁ , sf₁) tc₁)
Good-Ω₁ = Goodᴺ-c one⊑Bd
  (Rz (R-ψ _ t0 tg0 _ (λ { (ml ()) ; (mr ()) }) rel₁ (fz ⊔ fk zero) proj₂ _ _ _))
  (λ η e e′ → Rz (R-ψ _ t0 tg0 _ (λ { (ml ()) ; (mr (ml hr)) → sf ; (mr (mr ())) }) (relη η) (fz ⊔ fk η) (λ e₁ q → proj₂ e₁ (suc q)) _ _ _))
  (Rz (R-ψ _ t0 tg0 _ (λ { (ml ()) ; (mr ()) }) rel₁ (fz ⊔ fk zero) proj₂ _ _ _))
  (λ η e e′ → Rz (R-ψ _ t0 tg0 _ (λ { (ml ()) ; (mr (ml hr)) → sf ; (mr (mr ())) }) (relη η) (fz ⊔ fk η) (λ e₁ q → proj₂ e₁ (suc q)) _ _ _))
  (GᴺΩ̇ zero ev₀ zero)
  where
  rel₁ : Rs (suc zero) (Emb.ι c₁ tc₁ ⌜ suc zero ⌝ (Lv.fst Lv.self) (inj₂ refl) (Ω̇ ⌜ suc zero ⌝ (proj₁ (proj₂ tc₁)))) (Ωˢ (suc zero))
  rel₁ = EmbR.R-ι c₁ tc₁ (Lv.fst Lv.self) (inj₂ refl) (RΩ̇ (suc zero) (self≈ (suc zero)) (proj₁ (proj₂ tc₁)))
  relη : ∀ η {e : suc zero ⊑ᴵ η} →
         Rs η (Emb.ι c₁ tc₁ ⌜ η ⌝ (Lv.bra η e Lv.self) (inj₂ refl) (Ω̇ ⌜ η ⌝ (proj₂ (proj₂ tc₁) η e))) (Ωˢ η)
  relη η {e} = EmbR.R-ι c₁ tc₁ (Lv.bra η e Lv.self) (inj₂ refl) (RΩ̇ η (self≈ η) (proj₂ (proj₂ tc₁) η e))
```
