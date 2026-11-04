# 弱证据的树: 帧只留 `Simᴵ`, 比较前规范化

> 不含记号. 结论写在 [GuardWeak](GuardWeak.lagda.md). 数据树 `O`, `ι`, `Ω̇` 全部取自 [GuardTightTree](GuardTightTree.lagda.md), 只重写折叠 (`§5` 到 `§9`). 与 [GuardBridgeTree](GuardBridgeTree.lagda.md) 的 `Fold′` 的差别:
>
> 1. **`Evd` 只留 `Belʷ`: 帧的分支值 $a$ 有 $\mathrm{Sim}(a,\ell)$, 不要字面的 `pr a <ᴵ ℓ`.** 地板用 `flo a`: 分支 $b+1$ 是 `fk b`, 极限 $L$ 是 `fb L`. 于是极限帧的界是 $L$, 不是 $L+1$.
> 2. **比较前规范化** (`nfR`, `nfK`, 就是 `nfC`). 规范位置的每个分支 $a$ 被帧支配 (`Dm`, $a\lhd\eta$). `prOf`: $a\lhd\eta$ 且 $\mathrm{Sim}(\eta,\ell)$ 给字面的 `pr a <ᴵ ℓ`, 只要 $a$ 是后继或 $a$ 严格下降. 紧的读法下后继节点与闭包节点的规范位置只有后继分支 (`rec-exact`, `mark-exact` 的形状). 比较 `bd` 读的就是这个字面证据, **不读 $L$.**
> 3. **`cmpN`, `cmpK` 比较规范路径, 地板是规范路径自己的帧 $\hat\varphi$** (`pF`), 由 `Cov` 支配. 答案在输出里要的是 $\hat\varphi$ 的帧被输出的帧支配 (`covOut`); 输出用 `ocv` 盖住, 与 `ι` 的 `omk` 行同形.
> 4. `pick` 的两半分开: 路径上的值 (规范, 字面, `fk (pr K)`), 帧自己的值 (`pickW`, `flo K`).
> 5. `Sl.sel` 的种子 $K_0$: 后继取前驱. 极限取 0, 由闭包的下界 $1\sqsubseteq K$ 给 $0<\ell$ (`seed`). 下界不是字面 1 的退化闭包没有证据, 走 `o0`.
> 6. `owk` 也收窄输出 (同 `Fold′`).
>
> 证据缺失的分支给 `o0`, 走不走得到是证书的事. 这是定义, 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using
  (Ordᴵ; suc; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; Simᴵ; ⊑ᴵ-trans; ≅ᴵ-refl; ≅ᴵ-sym; Sim→⊑ᴵ; <ᴵ-trans; z⊑; s⊑; l⊑; z≅)
import OCF.Free.Level as Lvl
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo; bound; Bd; Fc; evF; iF; FB; liftEv; Top; FM)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightTab Dom₀ using (kdec; Dec′; _⊙_; adm⊙; toCp; admTo; Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using
  (O; O₊; Us; Vs; Vc; outU; intoU; outC; intoC; outV; intoV; rdZ; adm-wk; asl; asr; swp; sw₃; _⊕_; trO; tr⁻O; trL; trL⁻; module Emb; Ω̇; repᵒ; oc≅; selfC;
   o0; os; ol; oŝ; oĉ; owk; ocv; omk; oΩ; ocl)
```

## §0 字面证据从弱证据

`prOf`: 规范位置的分支 $a$ 被帧的值 $\eta$ 支配. 严格下降 (`⊲ˢ`) 时, 只要 $\mathrm{Sim}(\eta,\ell)$ 就有 `pr a <ᴵ ℓ`; 相等时 $a$ 是后继才有. **极限的 $a$ 不答: 这里不比较极限.**

`seed`: 帧的值 $K$ 进界时要一个字面的 $K_0<\ell$. 后继取前驱. 其余看闭包的下界: $1\sqsubseteq K$ 且 $\mathrm{Sim}(K,\ell)$ 给 $0<\ell$.

```agda
prOf : ∀ {a η ℓ} → a ⊲ η → Simᴵ η ℓ → Maybe (pr a <ᴵ ℓ)
prOf {a = suc b} ⊲= σ = just (σ Lvl.zero)
prOf {a = Lvl.zero} ⊲= σ = nothing
prOf {a = Lvl.lim f s} ⊲= σ = nothing
prOf (⊲ˢ h) σ = just (h σ)

simDown : ∀ {a η ℓ} → a ⊲ η → Simᴵ η ℓ → Simᴵ a ℓ
simDown ⊲= σ = σ
simDown (⊲ˢ h) σ = pr→Sim (h σ)

zlt : ∀ {c K} → c ⊑ᴵ K → Maybe (Lvl.zero <ᴵ K)
zlt z⊑ = nothing
zlt (s⊑ z≅ q) = just q
zlt (s⊑ (Lvl.s≅ _) q) = nothing
zlt (s⊑ (Lvl.l≅ _) q) = nothing
zlt (l⊑ h) = zlt (h 0)

Seed : Ordᴵ → Set
Seed ℓ = Σ Ordᴵ λ K₀ → K₀ <ᴵ ℓ

seed : ∀ {c ℓ} K → c ⊑ᴵ K → Simᴵ K ℓ → Maybe (Seed ℓ)
seed (suc b) e σ = just (b , σ Lvl.zero)
seed Lvl.zero e σ = nothing
seed (Lvl.lim f s) e σ with zlt e
... | nothing = nothing
... | just z = just (Lvl.zero , σ z)

-- 路径自己的帧
pFl : ∀ {a b} → a < b → Fl
pFl zero = tz
pFl (suc r) = pFl r
pFl (lim n r) = pFl r
pFl (fst r) = pFl r
pFl (bra {c = c} {t = t} {g = g} η e r) = tk (frm c t g η e) ∪ pFl r

admPl : ∀ {a b} (r : a < b) → Adm (cov (pFl r)) r
admPl zero = tt
admPl (suc r) = admPl r
admPl (lim n r) = admPl r
admPl (fst r) = admPl r
admPl (bra {c = c} {t = t} {g = g} η e r) = (c , t , g , e , ml hr , inj₂ refl) , adm-wk mr r (admPl r)
```

## §5 折叠的状态

```agda
module FoldW (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  Belʷ : Ents → LG → Ordᴵ → Set
  Belʷ E y η = Σ Ordᴵ λ ℓ → at E y ℓ × Simᴵ η ℓ

  record Evd (E : Ents) (f : Frm) : Set where
    constructor evd
    field
      {c₃} : Ordᴵ
      {t₃} : LG
      {g₃} : (η : Ordᴵ) → c₃ ⊑ᴵ η → LG
      Pf   : Cp (lc c₃ t₃ g₃) c
      adf  : AdmC (tab E) Pf
      lkf  : lc c₃ t₃ g₃ ≈ κ f
      blf  : Belʷ E (κ f) (fη f)

  record Ab (ρ : Fl) (f : Frm) : Set where
    constructor ab
    field
      {c₄} : Ordᴵ
      {t₄} : LG
      {g₄} : (η : Ordᴵ) → c₄ ⊑ᴵ η → LG
      {e₄} : c₄ ⊑ᴵ fη f
      mem₄ : Mem ρ (frm c₄ t₄ g₄ (fη f) e₄)
      lk₄  : κ f ≈ lc c₄ t₄ g₄ ⊎ κ f ≡ lc c₄ t₄ g₄

  record Fs (E : Ents) (ρ : Fl) (f : Frm) : Set where
    constructor fs
    field
      ev  : Maybe (Evd E f)
      abm : Maybe (Ab ρ f)
  open Fs public

  St : Ents → Fl → Fl → Set
  St E ρ π = ∀ {f} → Mem π f → Fs E ρ f

  mapFs : ∀ {E ρ ρ′ f} → Wk ρ ρ′ → Fs E ρ f → Fs E ρ′ f
  mapFs w (fs e nothing) = fs e nothing
  mapFs w (fs e (just (ab m k))) = fs e (just (ab (w m) k))

  stξ : ∀ {E ρ π} ξ → St E ρ π → St E (ξ ∪ ρ) (ξ ∪ π)
  stξ ξ st (ml m) = fs nothing (just (ab (ml m) (inj₂ refl)))
  stξ ξ st (mr m) = mapFs mr (st m)
```

## §6 规范化, 从帧到表, 从帧到输出

```agda
  record NR {k : LG} (r : k < c) : Set where
    constructor nr
    field
      {rpR} : LG
      eqR   : Lk k rpR
      cpR   : Cp (suc rpR) c
      relR  : ∀ ρ → Adm (cov ρ) r → AdmR ρ cpR
  open NR public

  nfR : ∀ {k} (r : k < c) → NR r
  nfR r with nfC c tc (toCpS r)
  ... | nfc (inj₁ (s≈ d)) Q _ rl = nr (inj₁ d) Q (λ ρ a → rl ρ (admToS r a))
  ... | nfc (inj₂ refl) Q _ rl = nr (inj₂ refl) Q (λ ρ a → rl ρ (admToS r a))

  record NK {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) : Set where
    constructor nk
    field
      {cK} : Ordᴵ
      {tK} : LG
      {gK} : (η : Ordᴵ) → cK ⊑ᴵ η → LG
      eqK  : Lk (lc c₂ t₂ g₂) (lc cK tK gK)
      cpK  : Cp (lc cK tK gK) c
      relK : ∀ ρ → AdmC (cov ρ) P → AdmR ρ cpK
  open NK public

  nfK : ∀ {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) → NK P
  nfK P with nfC c tc P
  ... | nfc (inj₁ (o≈ a b h)) Q _ rl = nk (inj₁ (o≈ a b h)) Q rl
  ... | nfc (inj₂ refl) Q _ rl = nk (inj₂ refl) Q rl

  module Rd {E : Ents} {ρ π : Fl} (st : St E ρ π) where
    atL : ∀ {u v ℓ} → Lk u v → at E v ℓ → at E u ℓ
    atL (inj₁ d′) b = at-resp {E} (≈-sym d′) b
    atL (inj₂ refl) b = b

    -- 规范位置的分支: 由支配它的帧的弱证据给字面证据
    belR : ∀ {y a} → Dm π y a → Maybe (Bel′ E y a)
    belR (f , m , lk , lt) with ev (st m)
    ... | nothing = nothing
    ... | just (evd _ _ _ (ℓ , b , σ)) with prOf lt σ
    ...   | nothing = nothing
    ...   | just q = just (ℓ , atL lk b , q)

    toTabR : ∀ {a b} (Q : Cp a b) → AdmR π Q → Maybe (AdmC (tab E) Q)
    toTabR self _ = just tt
    toTabR (suc Q) a = toTabR Q a
    toTabR (lim n Q) a = toTabR Q a
    toTabR (fst Q) a = toTabR Q a
    toTabR (bra η e Q) (d , a) with belR d | toTabR Q a
    ... | just u | just a′ = just (u , a′)
    ... | _ | _ = nothing

    domOut : ∀ {y a} → Dm π y a → Maybe (Dm ρ y a)
    domOut (f , m , lk , lt) with abm (st m)
    ... | nothing = nothing
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk₄) = just (frm c₄ t₄ g₄ (fη f) e₄ , mem , lkC lk lk₄ , lt)
```

## §7 节点对目标

`cmpN`: 比较规范路径 ($\hat\varphi$ 上的帧) 与目标. 骨架与 [GuardTightTree](GuardTightTree.lagda.md) 相同. `bra` 对 `bra`: 证据由支配的帧来 (`belR`), 没有就 `cj`. `cb` 的路径是 $\hat\varphi$ 上的, 输出时才问它的帧在不在输出里 (`covOut`).

```agda
  module Cmp {E : Ents} {ρ π : Fl} (st : St E ρ π) {φ̂ : Fl} (dm : Cov φ̂ π) where
    open Rd st

    dmC : ∀ {y a} → Bel (cov φ̂) y a → Dm π y a
    dmC (c₁ , t₁ , g₁ , e₁ , m , k) with dm m
    ... | f , m′ , lk , lt = f , m′ , lkC k lk , lt

    covOut : ∀ {a b} (s : a < b) → Adm (cov φ̂) s → Maybe (Cov (pFl s) ρ)
    covOut zero _ = just (λ ())
    covOut (suc s) a = covOut s a
    covOut (lim n s) a = covOut s a
    covOut (fst s) a = covOut s a
    covOut (bra η e s) (u , a) with domOut (dmC u) | covOut s a
    ... | just d | just cs = just (λ { (ml hr) → d ; (mr m) → cs m })
    ... | _ | _ = nothing

    covOutC : ∀ {a b} (s : Cp a b) → AdmC (cov φ̂) s → Maybe (Cov (pF s) ρ)
    covOutC self _ = just (λ ())
    covOutC (suc s) a = covOutC s a
    covOutC (lim n s) a = covOutC s a
    covOutC (fst s) a = covOutC s a
    covOutC (bra η e s) (u , a) with domOut (dmC u) | covOutC s a
    ... | just d | just cs = just (λ { (ml hr) → d ; (mr m) → cs m })
    ... | _ | _ = nothing

    data CN (k t : LG) : Set where
      cb : ∀ {rp} → k ≈ rp → (s : rp < t) → Adm (cov φ̂) s → CN k t
      cu : (t ≈ k ⊎ Below t k) → CN k t
      cj : CN k t

    shl : ∀ {k k′ t} → k ≈ k′ → CN k′ t → CN k t
    shl e (cb d s a) = cb (≈-trans e d) s a
    shl e (cu (inj₁ d)) = cu (inj₁ (≈-trans d (≈-sym e)))
    shl e (cu (inj₂ (pre d s))) with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ _ = cu (inj₂ (pre (≈-trans d d′) s′))
    shl e cj = cj

    shr : ∀ {k t t′} → t ≈ t′ → CN k t′ → CN k t
    shr e (cb d s a) with ≈-move (≈-sym e) s
    ... | viaᴸ d′ s′ u = cb (≈-trans d d′) s′ (u (cov φ̂) a)
    shr e (cu (inj₁ d)) = cu (inj₁ (≈-trans e d))
    shr e (cu (inj₂ (pre d s))) = cu (inj₂ (pre (≈-trans e d) s))
    shr e cj = cj

    cmpN : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {k t} (r : k < c′) (q : t < c′) → Adm (cov φ̂) r → Adm (tab E) q → CN k t
    cmpN w (s≈ e) zero zero _ _ = cu (inj₁ e)
    cmpN w (s≈ e) zero (suc q) _ _ = cu (inj₂ (pre (selfAt e q) q))
    cmpN w (s≈ e) (suc r) zero cv _ = cb (selfAt e r) r cv
    cmpN w (s≈ e) (suc r) (suc q) cv aq = cmpN w e r q cv aq
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
    ...   | viaᴸ d r′ u = shl d (cmpN (w m) (e m) r′ q (u (cov φ̂) cv) aq)
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = shr d (cmpN (w n) (e n) r q′ cv (u (tab E) aq))
    cmpN (st′ , w) (l≈ e) (lim n r) (lim _ q) cv aq | injᶜ refl = cmpN (w n) (e n) r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (fst r) (fst q) cv aq = cmpN wt se r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (fst r) (bra y e q) cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e) (sh y e y e (≅ᴰ-refl y)) r′ q (u (cov φ̂) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) r q′ cv (u (tab E) aq))
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (bra y e₂ q) (b₀ , cv) ((ℓ , b₁ , ly) , aq) with belR (dmC b₀)
    ... | nothing = cj
    ... | just (ℓ′ , b₂ , lx) with at-uq {E} (o≈ d se sh) b₂ b₁
    ...   | refl with bd lx ly
    ...     | inj₁ s with ⊴p (dir x e₁ y e₂ s) r
    ...       | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) r′ q (u (cov φ̂) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ r) (bra y e₂ q) (b₀ , cv) ((ℓ , b₁ , ly) , aq) | just (ℓ , b₂ , lx) | refl | inj₂ s with ⊴p (dir y e₂ x e₁ s) q
    ...       | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) r q′ cv (u (tab E) aq))

    data CK (c₂ : Ordᴵ) (t₂ : LG) (g₂ : (η : Ordᴵ) → c₂ ⊑ᴵ η → LG) (t : LG) : Set where
      kb : CK c₂ t₂ g₂ t
      ka : ∀ {c′ t′ g′} (Q : Cp (lc c′ t′ g′) t) → lc c₂ t₂ g₂ ≈ lc c′ t′ g′ → AdmC (cov φ̂) Q → CK c₂ t₂ g₂ t
      kj : CK c₂ t₂ g₂ t

    skl : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} → lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃ → CK c₃ t₃ g₃ t → CK c₂ t₂ g₂ t
    skl e kb = kb
    skl e (ka Q d a) = ka Q (≈-trans e d) a
    skl e kj = kj

    skr : ∀ {c₂ t₂ g₂ t t′} → t ≈ t′ → CK c₂ t₂ g₂ t′ → CK c₂ t₂ g₂ t
    skr e kb = kb
    skr e (ka Q d a) with ≈-moveᴷ (≈-sym e) Q
    ... | viaᴷ d′ Q′ u = ka Q′ (≈-trans d d′) (u (cov φ̂) a)
    skr e kj = kj

    cmpK : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (cov φ̂) P → Adm (tab E) q → CK c₂ t₂ g₂ t
    cmpK w sf′ self q cv aq = kb
    cmpK w (s≈ e) (suc P) zero cv _ = ka P (selfC e P) cv
    cmpK w (s≈ e) (suc P) (suc q) cv aq = cmpK w e P q cv aq
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
    ...   | viaᴷ d P′ u = skl d (cmpK (w m) (e m) P′ q (u (cov φ̂) cv) aq)
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = skr d (cmpK (w n) (e n) P q′ cv (u (tab E) aq))
    cmpK (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = cmpK (w n) (e n) P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (fst P) (fst q) cv aq = cmpK wt se P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
    ... | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e) (sh y e y e (≅ᴰ-refl y)) P′ q (u (cov φ̂) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq))
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) (b₀ , cv) ((ℓ , b₁ , ly) , aq) with belR (dmC b₀)
    ... | nothing = kj
    ... | just (ℓ′ , b₂ , lx) with at-uq {E} (o≈ d se sh) b₂ b₁
    ...   | refl with bd lx ly
    ...     | inj₁ s with ⊴K (dir x e₁ y e₂ s) P
    ...       | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) P′ q (u (cov φ̂) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) (b₀ , cv) ((ℓ , b₁ , ly) , aq) | just (ℓ , b₂ , lx) | refl | inj₂ s with ⊴p (dir y e₂ x e₁ s) q
    ...       | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq))
```

## §8 闭包的界

`pick`: 路径上的值 (规范位置的分支, 字面). `pickW`: 帧自己的值, 弱证据, 地板 `flo K`. 种子由 `seed` 给.

```agda
  module Sel {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) where
    kself : lc c₂ t₂ g₂ ≈ lc c₂ t₂ g₂
    kself = selfC sf P

    E′ : Ordᴵ → Ents
    E′ X = E ▸ lc c₂ t₂ g₂ , X

    data Sl (φ : Flr) : Set where
      emp : (∀ ℓ → Ev ℓ φ) → Sl φ
      sel : ∀ ℓ K₀ → at E (lc c₂ t₂ g₂) ℓ → K₀ <ᴵ ℓ → Ev ℓ φ → (∀ ℓ′ → Ev ℓ′ φ → c₂ ⊑ᴵ ℓ′) → Sl φ

    record S (G : Ents → Set) : Set where
      constructor mkS
      field
        φ   : Flr
        wit : Sl φ
        lft : ∀ X → Ev X φ → G (E′ X)
    open S public

    triv : ∀ {G} → (∀ X → G (E′ X)) → S G
    triv f = mkS fz (emp (λ _ → tt)) (λ X _ → f X)

    mapS : ∀ {A B : Ents → Set} → (∀ F → A F → B F) → S A → S B
    mapS f s = mkS (φ s) (wit s) (λ X x → f _ (lft s X x))

    mg : ∀ {a b} → Sl a → Sl b → Sl (a ⊔ b)
    mg (emp f) (emp h) = emp (λ ℓ → f ℓ , h ℓ)
    mg (emp f) (sel ℓ K a q y d) = sel ℓ K a q (f ℓ , y) (λ ℓ′ x → d ℓ′ (proj₂ x))
    mg (sel ℓ K a q x d) (emp h) = sel ℓ K a q (x , h ℓ) (λ ℓ′ u → d ℓ′ (proj₁ u))
    mg (sel ℓ K a q x d) (sel ℓ′ K′ a′ q′ y d′) with at-uq {E} kself a a′
    ... | refl = sel ℓ K a q (x , y) (λ ℓ″ u → d ℓ″ (proj₁ u))

    _⋈_ : ∀ {A B : Ents → Set} → S A → S B → S (λ F → A F × B F)
    s ⋈ s′ = mkS (φ s ⊔ φ s′) (mg (wit s) (wit s′)) (λ X x → lft s X (proj₁ x) , lft s′ X (proj₂ x))

    lit : ∀ {K ℓ} → K <ᴵ ℓ → Simᴵ (suc K) ℓ
    lit q Lvl.zero = q
    lit q (Lvl.suc r) = <ᴵ-trans r q

    pick : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) → AdmC (tab E) Q → ∀ K → c₅ ⊑ᴵ K → Bel′ E (lc c₅ t₅ g₅) K → S (λ F → Bel′ F (lc c₅ t₅ g₅) K)
    pick Q aq K eK (ℓ , a , q) with kdec wf sf Q P E aq ap
    ... | inj₁ e = mkS (fk (pr K))
                       (sel ℓ (pr K) (at-resp {E} e a) q (lit q)
                            (λ ℓ′ x → ⊑ᴵ-trans (conv (oc≅ e) eK) (pr⊑ K (x Lvl.zero))))
                       (λ X x → X , inj₁ (e , refl) , x Lvl.zero)
    ... | inj₂ n = mkS fz (emp (λ _ → tt)) (λ X _ → ℓ , inj₂ (n , a) , q)

    pickW : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) → AdmC (tab E) Q → ∀ K → c₅ ⊑ᴵ K → Belʷ E (lc c₅ t₅ g₅) K → S (λ F → Maybe (Belʷ F (lc c₅ t₅ g₅) K))
    pickW Q aq K eK (ℓ , a , σ) with kdec wf sf Q P E aq ap
    ... | inj₂ n = mkS fz (emp (λ _ → tt)) (λ X _ → just (ℓ , inj₂ (n , a) , σ))
    ... | inj₁ e with seed K eK σ
    ...   | nothing = mkS fz (emp (λ _ → tt)) (λ X _ → nothing)
    ...   | just (K₀ , q) = mkS (flo K)
                                (sel ℓ K₀ (at-resp {E} e a) q (toFlo K σ)
                                     (λ ℓ′ x → ⊑ᴵ-trans (conv (oc≅ e) eK) (Sim→⊑ᴵ (cvFlo K x))))
                                (λ X x → just (X , inj₁ (e , refl) , cvFlo K x))

    walk : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : Cp x a) → AdmC (tab E) r → S (λ F → AdmC (tab F) r)
    walk Q aq self _ = triv (λ _ → tt)
    walk Q aq (suc r) ad = walk (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (lim n r) ad = walk (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (fst r) ad = walk (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walk (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    walkA : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : x < a) → Adm (tab E) r → S (λ F → Adm (tab F) r)
    walkA Q aq zero _ = triv (λ _ → tt)
    walkA Q aq (suc r) ad = walkA (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (lim n r) ad = walkA (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (fst r) ad = walkA (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walkA (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    selSt : ∀ {ρ} π → St E ρ π → S (λ F → St F ρ π)
    selSt tz st = triv (λ X → λ ())
    selSt (tk f) st with st hr
    ... | fs nothing a = triv (λ X → λ { hr → fs nothing a })
    ... | fs (just (evd Pf adf lkf (ℓ , b , σ))) a =
      mapS (λ F x → λ { hr → fs (mk F x) a })
           (walk self tt Pf adf ⋈ pickW Pf adf (fη f) (conv (≅ᴰ-sym (oc≅ lkf)) (fe f)) (ℓ , at-resp {E} (≈-sym lkf) b , σ))
      where
      mk : ∀ F → AdmC (tab F) Pf × Maybe (Belʷ F (lc _ _ _) (fη f)) → Maybe (Evd F f)
      mk F (ad , nothing) = nothing
      mk F (ad , just (ℓ′ , b′ , σ′)) = just (evd Pf ad lkf (ℓ′ , at-resp {F} lkf b′ , σ′))
    selSt (a ∪ b) st =
      mapS (λ F x → λ { (ml m) → proj₁ x m ; (mr m) → proj₂ x m })
           (selSt a (λ m → st (ml m)) ⋈ selSt b (λ m → st (mr m)))
```

## §5′ 地板下降时的状态

```agda
  sbL : ∀ {x u v} → Lk u v → x ≈ v → x ≈ u
  sbL (inj₁ d′) d = ≈-trans d (≈-sym d′)
  sbL (inj₂ refl) d = d

  atL : ∀ {E u v ℓ} → Lk u v → at E v ℓ → at E u ℓ
  atL {E} (inj₁ d′) b = at-resp {E} (≈-sym d′) b
  atL (inj₂ refl) b = b

  fsLow : ∀ {E ρ f f′} → Lk (κ f) (κ f′) → fη f ⊲ fη f′ → Fs E ρ f′ → Σ Fl λ σ → Fs E σ f × Cov σ ρ
  fsLow {E} {ρ} {f} {f′} lk lt (fs e a) = go₂ a
    where
    me : Maybe (Evd E f′) → Maybe (Evd E f)
    me nothing = nothing
    me (just (evd Pf adf lkf (ℓ , b , σ))) =
      just (evd Pf adf (sbL lk lkf) (ℓ , atL {E} lk b , simDown lt σ))
    go₂ : Maybe (Ab ρ f′) → Σ Fl λ σ → Fs E σ f × Cov σ ρ
    go₂ nothing = tz , fs (me e) nothing , (λ ())
    go₂ (just (ab {c₄} {t₄} {g₄} {e₄} mem lk₄)) =
      tk (frm c₄ t₄ g₄ (fη f) (lkG (lkC lk lk₄) (fe f))) ,
      fs (me e) (just (ab {c₄ = c₄} {t₄ = t₄} {g₄ = g₄} {e₄ = lkG (lkC lk lk₄) (fe f)} hr (lkC lk lk₄))) ,
      (λ { hr → frm c₄ t₄ g₄ (fη f′) e₄ , mem , inj₂ refl , lt })

  lowerSt : ∀ {E ρ π} (π′ : Fl) → Cov π′ π → St E ρ π → Σ Fl λ σ → St E σ π′ × Cov σ ρ
  lowerSt tz w st = tz , (λ ()) , (λ ())
  lowerSt (tk f) w st with w hr
  ... | f′ , m , lk , lt with fsLow lk lt (st m)
  ...   | σ , F , c = σ , (λ { hr → F }) , c
  lowerSt (a ∪ b) w st with lowerSt a (λ m → w (ml m)) st | lowerSt b (λ m → w (mr m)) st
  ... | σa , sa , ca | σb , sb , cb =
    σa ∪ σb , (λ { (ml m) → mapFs ml (sa m) ; (mr m) → mapFs mr (sb m) }) , (λ { (ml m) → ca m ; (mr m) → cb m })
```

## §5″ 链的地板

`keepP`: 同 [GuardTightTree](GuardTightTree.lagda.md), 表里的证据都在规范位置上, 字面.

```agda
  keepP : ∀ {E c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (tab E) P → Adm (tab E) q → Bool
  keepP w sf′ self q cv aq = false
  keepP w (s≈ e) (suc P) zero cv _ = true
  keepP w (s≈ e) (suc P) (suc q) cv aq = keepP w e P q cv aq
  keepP {E = E} (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
  ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
  ...   | viaᴷ d P′ u = keepP (w m) (e m) P′ q (u (tab E) cv) aq
  keepP {E = E} (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
  ...   | viaᴸ d q′ u = keepP (w n) (e n) P q′ cv (u (tab E) aq)
  keepP (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = keepP (w n) (e n) P q cv aq
  keepP (tg , dir , wt , wg) (o≈ d se sh) (fst P) (fst q) cv aq = keepP wt se P q cv aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
  ... | viaᴷ d′ P′ u = keepP (wg y e) (sh y e y e (≅ᴰ-refl y)) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
  ... | viaᴸ d′ q′ u = keepP (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq)
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , lx) , cv) ((ℓ , b₁ , ly) , aq) with at-uq {E} (o≈ d se sh) b₂ b₁
  ... | refl with bd lx ly
  ...   | inj₁ s with ⊴K (dir x e₁ y e₂ s) P
  ...     | viaᴷ d′ P′ u = keepP (wg y e₂) (sh y e₂ y e₂ (≅ᴰ-refl y)) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , lx) , cv) ((ℓ , b₁ , ly) , aq) | refl | inj₂ s with ⊴p (dir y e₂ x e₁ s) q
  ...     | viaᴸ d′ q′ u = keepP (wg x e₁) (sh x e₁ x e₁ (≅ᴰ-refl x)) P q′ cv (u (tab E) aq)

  record Tr {E : Ents} {ρ : Fl} (π : Fl) (st : St E ρ π) : Set where
    constructor mkTr
    field
      ξᵗ   : Fl
      wkᵗ  : Wk ξᵗ π
      bkᵗ  : ∀ {f} → Mem π f → Maybe (Mem ξᵗ f)
  open Tr public

  keepF : ∀ {E ρ f k} (s : Fs E ρ f) {r : k < c} → Adm (tab E) r → Bool
  keepF (fs nothing a) ar = true
  keepF (fs (just (evd Pf adf _ _)) a) {r} ar = keepP wf sf Pf r adf ar

  trim : ∀ {E ρ k} (π : Fl) (st : St E ρ π) {r : k < c} → Adm (tab E) r → Tr π st
  trim tz st ar = mkTr tz (λ ()) (λ ())
  trim (tk f) st {r} ar with keepF (st hr) {r} ar
  ... | true = mkTr (tk f) (λ m → m) just
  ... | false = mkTr tz (λ ()) (λ _ → nothing)
  trim (a ∪ b) st {r} ar with trim a (λ m → st (ml m)) {r} ar | trim b (λ m → st (mr m)) {r} ar
  ... | mkTr ξa wa ba | mkTr ξb wb bb =
    mkTr (ξa ∪ ξb) (λ { (ml m) → ml (wa m) ; (mr m) → mr (wb m) })
         (λ { (ml m) → mapM ml (ba m) ; (mr m) → mapM mr (bb m) })
    where
    mapM : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
    mapM g nothing = nothing
    mapM g (just x) = just (g x)

  stBody : ∀ {E ρ π} (ξ : Fl) → Wk ξ π → St E ρ π → St E ρ (ξ ∪ π)
  stBody ξ w st (ml m) = st (w m)
  stBody ξ w st (mr m) = st m

  stChain : ∀ {E ρ π} (ξ : Fl) → (∀ {f} → Mem π f → Maybe (Mem ξ f)) → Wk ξ π → St E ρ π → St E ξ (ξ ∪ π)
  stChain ξ bk w st (ml m) = fs (ev (st (w m))) (just (ab m (inj₂ refl)))
  stChain ξ bk w st {f} (mr m) with bk m
  ... | just m′ = fs (ev (st m)) (just (ab m′ (inj₂ refl)))
  ... | nothing = fs (ev (st m)) nothing
```

## §9 折叠

```agda
  data Tg (E : Ents) : LG → Set where
    t0 : Tg E zero
    tp : ∀ {t} (q : t < c) → Adm (tab E) q → Tg E t

  tcT : ∀ {E t} → Tg E t → Tc t
  tcT t0 = tt
  tcT (tp q _) = Tc-at q tc

  tgSel : ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) → Tg E t → Sel.S P E ap (λ F → Tg F t)
  tgSel P E ap t0 = Sel.triv P E ap (λ _ → t0)
  tgSel P E ap (tp q aq) = Sel.mapS P E ap (λ F a → tp q a) (Sel.walkA P E ap self tt q aq)

  chainᵒ : ∀ {k π} → Tc k → (O k π → O k π) → ℕ → O k π
  chainᵒ {k} tk′ f zero    = owk (λ ()) (Ω̇ k tk′)
  chainᵒ tk′ f (suc n) = f (chainᵒ tk′ f n)

  SSc : ∀ {t π ρ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) (ap : AdmC (tab E) P) →
        Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))
  SSc {π = π} E T st P ap = Sel._⋈_ P E ap (Sel.selSt P E ap π st) (Sel._⋈_ P E ap (tgSel P E ap T) (Sel.walk P E ap self tt P ap))

  -- 输出的地板: ρ 加上路径自己的帧, 由 ocv 盖回 ρ
  covJ : ∀ {ρ σ} → Cov σ ρ → Cov (ρ ∪ σ) ρ
  covJ cs (ml m) = cov-exact (λ x → x) m
  covJ cs (mr m) = cs m

  ψ : ∀ {t π ρ} (E : Ents) → Tg E t → St E ρ π → O c π → O t ρ
  evalC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → AdmC (cov π) P →
          O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → O t ρ
  goC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → (ap : AdmC (tab E) P) →
        O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → (SS : Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))) → Sel.Sl P E ap (Sel.φ SS) → O t ρ
  riseΩ : ∀ {t π ρ k} (E : Ents) → Tg E t → St E ρ π → (r : k < c) → Adm (cov π) r → (∀ ξ → Us c r ξ → O c (ξ ∪ π)) → O t ρ

  ψ {t} E T st o0 = owk (λ ()) (Ω̇ t (tcT T))
  ψ E T st (os a) = ol (repᵒ (ψ E T st a))
  ψ E T st (ol F) = ol (λ n → ψ E T st (F n))
  ψ E T st (oŝ c₀ x g) = oŝ c₀ (ψ E T st x) (λ η e → ψ E T st (g η e))
  ψ E T st (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψ E T st o₀) (λ η e → ψ E T st (o η e))
  ψ E T st (owk {π = π′} w x) with lowerSt π′ (cov-exact w) st
  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)
  ψ E T st (ocv {π = π′} w x) with lowerSt π′ w st
  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)
  ψ E T st (omk R lk ad z x) = ψ E T st x
  ψ E t0 st (oΩ r cv h) = riseΩ E t0 st r cv h
  ψ {π = π} {ρ = ρ} E (tp q aq) st (oΩ r cv h) with nfR r
  ... | nr d Q rl with Cmp.cmpN st (covOf Q (rl π cv)) wf sf (fromCpS Q) q (admFromS Q (admP Q)) aq
  ...   | Cmp.cu _ = riseΩ E (tp q aq) st r cv h
  ...   | Cmp.cj = o0
  ...   | Cmp.cb d′ s a with Cmp.covOut st (covOf Q (rl π cv)) s a
  ...     | nothing = o0
  ...     | just cs = ocv (covJ cs)
              (oΩ s (adm-wk mr s (admPl s))
                  (λ ξ y → ψ E (tp q aq) (stξ ξ (λ m → mapFs ml (st m))) (h ξ (intoU r (trL⁻ d (tr⁻O d′ (outU s y)))))))
  ψ E t0 st (ocl P k cv x g) = evalC E t0 st P k cv x g
  ψ {π = π} {ρ = ρ} E (tp q aq) st (ocl {c₁ = c₁} {t₁} {g₁} P k cv x g) with nfK P
  ... | nk d Q rl with Cmp.cmpK st (covOf Q (rl π cv)) wf sf Q q (admP Q) aq
  ...   | Cmp.kb = evalC E (tp q aq) st P k cv x g
  ...   | Cmp.kj = o0
  ...   | Cmp.ka {c′} {t′} {g′} Q′ d₂ a with Cmp.covOutC st (covOf Q (rl π cv)) Q′ a
  ...     | nothing = o0
  ...     | just cs =
    ocv (covJ cs)
      (ocl Q′ (inj₂ refl) (admC-wk mr Q′ (admP Q′)) (ψ E (tp q aq) (λ m → mapFs ml (st m)) x)
        (λ η e′ → ψ E (tp q aq) (st″ η e′) (g η (eg e′))))
    where
    lks₁ : lc c₁ t₁ g₁ ≈ lc c′ t′ g′
    lks₁ = ≈-trans (≈-sym (lk→≈ (selfC sf P) k)) (≈-trans (lk→≈ (selfC sf P) d) d₂)
    eg : ∀ {η} → c′ ⊑ᴵ η → c₁ ⊑ᴵ η
    eg e′ = conv (oc≅ (≈-sym lks₁)) e′
    st″ : ∀ η e′ → St E ((ρ ∪ pF Q′) ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁ t₁ g₁ η (eg e′)))
    st″ η e′ (ml m) = mapFs (λ u → ml (ml u)) (st m)
    st″ η e′ (mr hr) = fs nothing (just (ab {c₄ = c′} {t₄ = t′} {g₄ = g′} {e₄ = e′} (mr hr) (inj₁ lks₁)))

  riseΩ {π = π} E T st r cv h with nfR r
  ... | nr d Q rl with Rd.toTabR st Q (rl π cv)
  ...   | nothing = o0
  ...   | just aq with admFromS Q aq | trim π st {fromCpS Q} (admFromS Q aq)
  ...     | a | mkTr ξ w bk = ol (λ n → ψ E T (stBody ξ w st) (h ξ (intoU r (chainᵒ (Tc-at r tc) (λ z → trL⁻ d (ψ E (tp (fromCpS Q) a) (stChain ξ bk w st) (h ξ (intoU r z)))) n))))

  evalC {π = π} E T st P k cv x g with nfK P
  ... | nk d Q rl with Rd.toTabR st Q (rl π cv)
  ...   | nothing = o0
  ...   | just ap = goC E T st Q (lkC (lkS d) k) ap x g (SSc E T st Q ap) (Sel.wit (SSc E T st Q ap))

  goC {t} {π} {ρ} {c₁} {t₁} {g₁} {c₂} {t₂} {g₂} E T st P k ap x g SS w = go w
    where
    module M = Sel P E ap
    lk₂ : lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁
    lk₂ = lk→≈ M.kself k
    guardC : ∀ {η} → c₂ ⊑ᴵ η → c₁ ⊑ᴵ η
    guardC d = conv (oc≅ lk₂) d
    body : ∀ η (e : c₁ ⊑ᴵ η) X → Ev X (M.φ SS) → η <ᴵ X → O t ρ
    body η e X ex q = ψ (M.E′ X) (proj₁ (proj₂ L)) stn (g η e)
      where
      L = M.lft SS X ex
      stn : St (M.E′ X) ρ (π ∪ tk (frm c₁ t₁ g₁ η e))
      stn (ml m) = proj₁ L m
      stn (mr hr) = fs (just (evd P (proj₂ (proj₂ L)) lk₂ (X , inj₁ (≈-sym lk₂ , refl) , (λ r → <ᴵ-trans r q)))) nothing
    go : M.Sl (M.φ SS) → O t ρ
    go (M.emp f) = oŝ c₂ (ψ E T st x) (λ η d → body η (guardC d) (suc η) (f (suc η)) Lvl.zero)
    go (M.sel ℓ K₀ a q y dm) = oŝ (Bd B) (ψ E T st x)
         (λ η d → body η (guardC (⊑ᴵ-trans (dm (Fc B) (evF B)) (⊑ᴵ-trans (FM B) d)))
                       (Mlev (Fc B) (suc η) (FB B d))
                       (liftEv (M.φ SS) (λ r → Lvl.lim 0 r) (evF B))
                       (Lvl.lim 1 Lvl.zero))
      where
      B : Top K₀ ℓ (M.φ SS)
      B = bound (M.φ SS) y q

Tʷ : (L : LG) → Cfˢ L → Tc L → O zero tz
Tʷ L (w , s) tc = FoldW.ψ L w s tc (∅ Lvl.zero) FoldW.t0 (λ ()) (Ω̇ L tc)

T₀ʷ : (L : LG) → Cfˢ L → Tc L → Z
T₀ʷ L cf tc = rdZ (Tʷ L cf tc)
```
