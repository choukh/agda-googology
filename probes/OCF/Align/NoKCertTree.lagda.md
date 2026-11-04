# 折叠: `owk` 也收窄输出

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). 由 [LevelNoKTree](LevelNoKTree.lagda.md) 的折叠用脚本取来 (`module Fold` 到文件末), **只差一行**: `owk` 收窄输入的同时也收窄输出的地板, 与 `ocv` 同一行. 这是 [GuardBridgeTree](GuardBridgeTree.lagda.md) 的 `T₀′` 的同一处改法, 那里由测试逼出: 否则过两遍折叠后保留的闭包读到不依赖的外层帧. 数据树 `O`, `ι`, `Ω̇`, `Sel` 之前的都不动, 类型也不动.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LevelNoKX using (XU)

module OCF.Align.NoKCertTree (X : XU) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.LevelNoKLv
open XU X
open Lv 𝔻
open import OCF.Align.LevelNoKTab 𝔻 using (kdec; Dec′; _⊙_; adm⊙; toCp; admTo; Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙)
open import OCF.Align.LevelNoKBase X
open import OCF.Align.LevelNoKTree X hiding (module Fold; Tn)

module FoldO (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  record Evd (E : Ents) (f : Frm) : Set where
    constructor evd
    field
      {c₃} : D
      {t₃} : LG
      {g₃} : (η : D) → c₃ ⊑ᴰ η → LG
      Pf   : Cp (lc c₃ t₃ g₃) c
      adf  : AdmC (tab E) Pf
      lkf  : lc c₃ t₃ g₃ ≈ κ f
      blf  : Bel′ E (fc f) (ft f) (fg f) (fe f)

  record Ab (ρ : Fl) (f : Frm) : Set where
    constructor ab
    field
      {c₄} : D
      {t₄} : LG
      {g₄} : (η : D) → c₄ ⊑ᴰ η → LG
      {e₄} : c₄ ⊑ᴰ fη f
      mem₄ : Mem ρ (frm c₄ t₄ g₄ (fη f) e₄)
      lk₄  : Lk (κ f) (lc c₄ t₄ g₄)
      eq₄  : e₄ ≡ lkG lk₄ (fe f)

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
  mapFs w (fs e (just (ab m k q))) = fs e (just (ab (w m) k q))

  stξ : ∀ {E ρ π} ξ → St E ρ π → St E (ξ ∪ ρ) (ξ ∪ π)
  stξ ξ st (ml m) = fs nothing (just (ab (ml m) (inj₂ refl) refl))
  stξ ξ st (mr m) = mapFs mr (st m)

  stDup : ∀ {E ρ π} → St E ρ π → St E ρ (π ∪ π)
  stDup st (ml m) = st m
  stDup st (mr m) = st m

  stSelf : ∀ {E ρ π} → St E ρ π → St E π (π ∪ π)
  stSelf st (ml m) = fs (ev (st m)) (just (ab m (inj₂ refl) refl))
  stSelf st (mr m) = fs (ev (st m)) (just (ab m (inj₂ refl) refl))
```

## §6 从帧到输出, 从帧到表

```agda
  module Vis {E : Ents} {ρ π : Fl} (st : St E ρ π) where
    toOut : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (cov ρ) r)
    toOut zero _ = just tt
    toOut (suc r) a = toOut r a
    toOut (lim n r) a = toOut r a
    toOut (fst r) a = toOut r a
    toOut (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with abm (st m) | toOut r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk q) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk , trans q (trans (cong (lkG lk) eq) (lkG-∘ k lk e))) , a′)
    ... | _ | _ = nothing

    toOutC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (cov ρ) r)
    toOutC self _ = just tt
    toOutC (suc r) a = toOutC r a
    toOutC (lim n r) a = toOutC r a
    toOutC (fst r) a = toOutC r a
    toOutC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with abm (st m) | toOutC r a
    ... | just (ab {c₄} {t₄} {g₄} {e₄} mem lk q) | just a′ = just ((c₄ , t₄ , g₄ , e₄ , mem , lkC k lk , trans q (trans (cong (lkG lk) eq) (lkG-∘ k lk e))) , a′)
    ... | _ | _ = nothing

    belOf : ∀ {c t g c₁ t₁ g₁ η} {e : c ⊑ᴰ η} {e₁ : c₁ ⊑ᴰ η} (k : Lk (lc c t g) (lc c₁ t₁ g₁)) → e₁ ≡ lkG k e → Evd E (frm c₁ t₁ g₁ η e₁) → Bel (tab E) c t g e
    belOf {e = e} (inj₁ d) refl (evd _ _ _ (u , a , o , q)) =
      u , at-resp {E} (≈-sym d) a , ≈-trans d o , subst (λ z → z <ᵉ uF u) (sym (oc-tr d o e)) q
    belOf (inj₂ refl) refl (evd _ _ _ b) = b

    toTab : ∀ {a b} (r : a < b) → Adm (cov π) r → Maybe (Adm (tab E) r)
    toTab zero _ = just tt
    toTab (suc r) a = toTab r a
    toTab (lim n r) a = toTab r a
    toTab (fst r) a = toTab r a
    toTab (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with ev (st m) | toTab r a
    ... | just d | just a′ = just (belOf k eq d , a′)
    ... | _ | _ = nothing

    toTabC : ∀ {a b} (r : Cp a b) → AdmC (cov π) r → Maybe (AdmC (tab E) r)
    toTabC self _ = just tt
    toTabC (suc r) a = toTabC r a
    toTabC (lim n r) a = toTabC r a
    toTabC (fst r) a = toTabC r a
    toTabC (bra η e r) ((c₁ , t₁ , g₁ , e₁ , m , k , eq) , a) with ev (st m) | toTabC r a
    ... | just d | just a′ = just (belOf k eq d , a′)
    ... | _ | _ = nothing
```

## §7 节点对目标

`cmpN`: 与 `kdec` 同一个骨架. 同一个节点上的两个分支才读表 (`bd`). 输出 `cb`: 节点在目标之下, 路径搬到目标里, 帧搬到输出. `cu`: 目标不在节点之上, 要上升. `cj`: 证据缺失. **`bra` 对 `bra` 且帧没有证据时给 `cj`: 这不是判定, 没有比较任何东西.**

```agda
    data CN (k t : LG) : Set where
      cb : ∀ {rp} → k ≈ rp → (s : rp < t) → Adm (cov ρ) s → CN k t
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
    ... | viaᴸ d′ s′ u = cb (≈-trans d d′) s′ (u (cov ρ) a)
    shr e (cu (inj₁ d)) = cu (inj₁ (≈-trans e d))
    shr e (cu (inj₂ (pre d s))) = cu (inj₂ (pre (≈-trans e d) s))
    shr e cj = cj

    cmpN : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {k t} (r : k < c′) (q : t < c′) → Adm (cov π) r → Adm (tab E) q → CN k t
    cmpN w (s≈ e) zero zero _ _ = cu (inj₁ e)
    cmpN w (s≈ e) zero (suc q) _ _ = cu (inj₂ (pre (selfAt e q) q))
    cmpN w (s≈ e) (suc r) zero cv _ with toOut r cv
    ... | just a = cb (selfAt e r) r a
    ... | nothing = cj
    cmpN w (s≈ e) (suc r) (suc q) cv aq = cmpN w e r q cv aq
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴p (stepsˢ st′ n<m) r
    ...   | viaᴸ d r′ u = shl d (cmpN (w m) (e m) r′ q (u (cov π) cv) aq)
    cmpN (st′ , w) (l≈ e) (lim n r) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = shr d (cmpN (w n) (e n) r q′ cv (u (tab E) aq))
    cmpN (st′ , w) (l≈ e) (lim n r) (lim _ q) cv aq | injᶜ refl = cmpN (w n) (e n) r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst r) (fst q) cv aq = cmpN wt se r q cv aq
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst r) (bra y e q) cv (_ , aq) with ⊴p (tg y e) r
    ... | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e) (shˡ y e) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (shˡ x e₁) r q′ cv (u (tab E) aq))
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with ev (st m)
    ... | nothing = cj
    ... | just evi with belOf k eq evi
    ...   | ℓ′ , b₂ , o₁ , lx with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
    ...     | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
    ...       | inj₁ s with ⊴p s r
    ...         | viaᴸ d′ r′ u = shl d′ (cmpN (wg y e₂) (shˡ y e₂) r′ q (u (cov π) cv) aq)
    cmpN (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ r) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | just evi | ℓ , b₂ , o₁ , lx | refl | inj₂ s with ⊴p s q
    ...         | viaᴸ d′ q′ u = shr d′ (cmpN (wg x e₁) (shˡ x e₁) r q′ cv (u (tab E) aq))
```

**闭包对目标.** `kb`: 目标在闭包之下, 所以闭包要立刻计值. `ka`: 闭包 (模 $\approx$) 在目标里, 所以保留.

```agda
    data CK (c₂ : D) (t₂ : LG) (g₂ : (η : D) → c₂ ⊑ᴰ η → LG) (t : LG) : Set where
      kb : CK c₂ t₂ g₂ t
      ka : ∀ {c′ t′ g′} (Q : Cp (lc c′ t′ g′) t) → lc c₂ t₂ g₂ ≈ lc c′ t′ g′ → AdmC (cov ρ) Q → CK c₂ t₂ g₂ t
      kj : CK c₂ t₂ g₂ t

    skl : ∀ {c₂ t₂ g₂ c₃ t₃ g₃ t} → lc c₂ t₂ g₂ ≈ lc c₃ t₃ g₃ → CK c₃ t₃ g₃ t → CK c₂ t₂ g₂ t
    skl e kb = kb
    skl e (ka Q d a) = ka Q (≈-trans e d) a
    skl e kj = kj

    skr : ∀ {c₂ t₂ g₂ t t′} → t ≈ t′ → CK c₂ t₂ g₂ t′ → CK c₂ t₂ g₂ t
    skr e kb = kb
    skr e (ka Q d a) with ≈-moveᴷ (≈-sym e) Q
    ... | viaᴷ d′ Q′ u = ka Q′ (≈-trans d d′) (u (cov ρ) a)
    skr e kj = kj

    cmpK : ∀ {c′} → WFˢ c′ → c′ ≈ c′ → ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c′) (q : t < c′) → AdmC (cov π) P → Adm (tab E) q → CK c₂ t₂ g₂ t
    cmpK w sf′ self q cv aq = kb
    cmpK w (s≈ e) (suc P) zero cv _ with toOutC P cv
    ... | just a = ka P (selfC e P) a
    ... | nothing = kj
    cmpK w (s≈ e) (suc P) (suc q) cv aq = cmpK w e P q cv aq
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq with <ᴺ-dec n m
    ... | injᵃ n<m with ⊴K (stepsˢ st′ n<m) P
    ...   | viaᴷ d P′ u = skl d (cmpK (w m) (e m) P′ q (u (cov π) cv) aq)
    cmpK (st′ , w) (l≈ e) (lim n P) (lim m q) cv aq | injᵇ m<n with ⊴p (stepsˢ st′ m<n) q
    ...   | viaᴸ d q′ u = skr d (cmpK (w n) (e n) P q′ cv (u (tab E) aq))
    cmpK (st′ , w) (l≈ e) (lim n P) (lim _ q) cv aq | injᶜ refl = cmpK (w n) (e n) P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (fst q) cv aq = cmpK wt se P q cv aq
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
    ... | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e) (shˡ y e) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
    ... | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq))
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with ev (st m)
    ... | nothing = kj
    ... | just evi with belOf k eq evi
    ...   | ℓ′ , b₂ , o₁ , lx with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
    ...     | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
    ...       | inj₁ s with ⊴K s P
    ...         | viaᴷ d′ P′ u = skl d′ (cmpK (wg y e₂) (shˡ y e₂) P′ q (u (cov π) cv) aq)
    cmpK (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((c₁ , t₁ , g₁ , e₃ , m , k , eq) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | just evi | ℓ , b₂ , o₁ , lx | refl | inj₂ s with ⊴p s q
    ...         | viaᴸ d′ q′ u = skr d′ (cmpK (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq))
```

## §8 闭包的界: 只看同键的帧与目标的分支

`Sel`: 与 [LvKeyTree](LvKeyTree.lagda.md) 的 `Sel` 同形. `Sl`: 什么也没有挑出 (`emp`), 或者挑出了 (`sel`): 表项 $u$, 节点到 $u$ 的 `≈`, 表项纤维里的一个证据. 地板 `φ` 的项是帧, 所以 `lft` 由 `Ev` 直接读出 `Bel′` 要的东西, 不要比较两个证据.

```agda
  module Sel {c₂ t₂ g₂} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) where
    kself : lc c₂ t₂ g₂ ≈ lc c₂ t₂ g₂
    kself = selfC sf P

    w₂ : (X : D) → c₂ ⊑ᴰ X → Up
    w₂ X F = mkU c₂ t₂ g₂ X F

    E′ : (X : D) → c₂ ⊑ᴰ X → Ents
    E′ X F = E ▸ w₂ X F

    data Sl (φ : Flr) : Set where
      emp : (∀ w → Ev w φ) → Sl φ
      sel : ∀ u → at E (lc c₂ t₂ g₂) u → lc c₂ t₂ g₂ ≈ key u → ∀ {K₀} (e₀ : uc u ⊑ᴰ K₀) → e₀ <ᵉ uF u → Ev u φ → Sl φ

    record S (G : Ents → Set) : Set where
      constructor mkS
      field
        φ   : Flr
        wit : Sl φ
        lft : ∀ X F → Ev (w₂ X F) φ → G (E′ X F)
    open S public

    triv : ∀ {G} → (∀ X F → G (E′ X F)) → S G
    triv f = mkS fz (emp (λ _ → tt)) (λ X F _ → f X F)

    mapS : ∀ {A B : Ents → Set} → (∀ F → A F → B F) → S A → S B
    mapS f s = mkS (φ s) (wit s) (λ X F x → f _ (lft s X F x))

    mg : ∀ {a b} → Sl a → Sl b → Sl (a ⊔ b)
    mg (emp f) (emp h) = emp (λ w → f w , h w)
    mg (emp f) (sel u a o e q y) = sel u a o e q (f u , y)
    mg (sel u a o e q x) (emp h) = sel u a o e q (x , h u)
    mg (sel u a o e q x) (sel u′ a′ o′ e′ q′ y) with at-uq {E} kself a a′
    ... | refl = sel u a o e q (x , y)

    _⋈_ : ∀ {A B : Ents → Set} → S A → S B → S (λ F → A F × B F)
    s ⋈ s′ = mkS (φ s ⊔ φ s′) (mg (wit s) (wit s′)) (λ X F x → lft s X F (proj₁ x) , lft s′ X F (proj₂ x))

    -- 节点 ν 与 K: 是同一个键就进界. 地板的项是帧本身.
    pick : ∀ {c₅ t₅ g₅} (Q : Cp (lc c₅ t₅ g₅) c) → AdmC (tab E) Q → ∀ K (eK : c₅ ⊑ᴰ K) → Bel′ E c₅ t₅ g₅ eK → S (λ F → Bel′ F c₅ t₅ g₅ eK)
    pick {c₅} {t₅} {g₅} Q aq K eK (u , a , o , q) with kdec wf sf Q P E aq ap
    ... | inj₁ e = mkS (fk (frm c₅ t₅ g₅ K eK))
                       (sel u (at-resp {E} e a) (≈-trans (≈-sym e) o) (conv (oc≅ o) eK) q (o , q))
                       (λ Y F x → w₂ Y F , inj₁ (e , refl) , proj₁ x , proj₂ x)
    ... | inj₂ n = mkS fz (emp (λ _ → tt)) (λ Y F _ → u , inj₂ (n , a) , o , q)

    walk : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : Cp x a) → AdmC (tab E) r → S (λ F → AdmC (tab F) r)
    walk Q aq self _ = triv (λ _ _ → tt)
    walk Q aq (suc r) ad = walk (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (lim n r) ad = walk (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (fst r) ad = walk (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walk Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walk (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    walkA : ∀ {a x} (Q : Cp a c) → AdmC (tab E) Q → (r : x < a) → Adm (tab E) r → S (λ F → Adm (tab F) r)
    walkA Q aq zero _ = triv (λ _ _ → tt)
    walkA Q aq (suc r) ad = walkA (Q ⊙ suc self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (lim n r) ad = walkA (Q ⊙ lim n self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (fst r) ad = walkA (Q ⊙ fst self) (adm⊙ {tab E} Q aq tt) r ad
    walkA Q aq (bra η e r) (u , ad) =
      pick Q aq η e u ⋈ walkA (Q ⊙ bra η e self) (adm⊙ {tab E} Q aq (u , tt)) r ad

    selSt : ∀ {ρ} π → St E ρ π → S (λ F → St F ρ π)
    selSt tz st = triv (λ X F → λ ())
    selSt (tk f) st with st hr
    ... | fs nothing a = triv (λ X F → λ { hr → fs nothing a })
    ... | fs (just (evd Pf adf lkf (u , b , o , q))) a =
      mapS (λ F x → λ { hr → fs (just (evd Pf (proj₁ x) lkf (bel-to F (proj₂ x)))) a })
           (walk self tt Pf adf ⋈ pick Pf adf (fη f) eK (u , at-resp {E} (≈-sym lkf) b , ≈-trans lkf o , q′))
      where
      eK = conv⁻ (oc≅ lkf) (fe f)
      q′ : conv (oc≅ (≈-trans lkf o)) eK <ᵉ uF u
      q′ = subst (λ z → z <ᵉ uF u) (sym (trans (oc-tr lkf o eK) (cong (conv (oc≅ o)) (sec (oc≅ lkf) (fe f))))) q
      bel-to : ∀ F → Bel′ F _ _ _ eK → Bel′ F (fc f) (ft f) (fg f) (fe f)
      bel-to F x = subst (λ z → Bel′ F (fc f) (ft f) (fg f) z) (sec (oc≅ lkf) (fe f)) (Bel-resp {tab F} lkf x)
    selSt (a ∪ b) st =
      mapS (λ F x → λ { (ml m) → proj₁ x m ; (mr m) → proj₂ x m })
           (selSt a (λ m → st (ml m)) ⋈ selSt b (λ m → st (mr m)))
```

## §5′ 地板下降时的状态

`lowerSt`: 外层状态在 $\pi$ 上, `Cov π′ π` 说 $\pi'$ 的帧被 $\pi$ 支配. 表里的证据随分支值下降 (字面子项, 所以 $a<\ell$ 还是字面的). 输出里的帧也下降: 输出的地板是算出来的 ($\sigma$), 不是 $\rho$ 本身, 所以闭包只看到紧的帧.

```agda
  sbL : ∀ {x u v} → Lk u v → x ≈ v → x ≈ u
  sbL (inj₁ d′) d = ≈-trans d (≈-sym d′)
  sbL (inj₂ refl) d = d

  atL : ∀ {E u v ℓ} → Lk u v → at E v ℓ → at E u ℓ
  atL {E} (inj₁ d′) b = at-resp {E} (≈-sym d′) b
  atL (inj₂ refl) b = b

  fsLow : ∀ {E ρ f f′} (lk : Lk (κ f) (κ f′)) → lkG lk (fe f) ⊲ fe f′ → Fs E ρ f′ → Σ Fl λ σ → Fs E σ f × Cov σ ρ
  fsLow {E} {ρ} {f} {f′} lk lt (fs e a) = go₂ a
    where
    me : Maybe (Evd E f′) → Maybe (Evd E f)
    me nothing = nothing
    me (just (evd Pf adf lkf (u , b , o , q))) =
      just (evd Pf adf (sbL lk lkf)
        (u , atL {E} lk b , lkO lk o ,
         subst (λ z → z <ᵉ uF u) (sym (lkO-conv lk o (fe f)))
           (⊲-conv (oc≅ o) (lkG lk (fe f)) (fe f′) lt (uF u) q)))
    go₂ : Maybe (Ab ρ f′) → Σ Fl λ σ → Fs E σ f × Cov σ ρ
    go₂ nothing = tz , fs (me e) nothing , (λ ())
    go₂ (just (ab {c₄} {t₄} {g₄} {e₄} mem lk₄ eq₄)) =
      tk (frm c₄ t₄ g₄ (fη f) (lkG (lkC lk lk₄) (fe f))) ,
      fs (me e) (just (ab {c₄ = c₄} {t₄ = t₄} {g₄ = g₄} {e₄ = lkG (lkC lk lk₄) (fe f)} hr (lkC lk lk₄) refl)) ,
      (λ { hr → frm c₄ t₄ g₄ (fη f′) e₄ , mem , inj₂ refl ,
          subst (λ z → lkG (lkC lk lk₄) (fe f) ⊲ z) (sym eq₄)
            (subst (λ z → z ⊲ lkG lk₄ (fe f′)) (lkG-∘ lk lk₄ (fe f))
              (⊲-lk lk₄ (lkG lk (fe f)) (fe f′) lt)) })

  lowerSt : ∀ {E ρ π} (π′ : Fl) → Cov π′ π → St E ρ π → Σ Fl λ σ → St E σ π′ × Cov σ ρ
  lowerSt tz w st = tz , (λ ()) , (λ ())
  lowerSt (tk f) w st with w hr
  ... | f′ , m , lk , lt with fsLow lk lt (st m)
  ...   | σ , F , c = σ , (λ { hr → F }) , c
  lowerSt (a ∪ b) w st with lowerSt a (λ m → w (ml m)) st | lowerSt b (λ m → w (mr m)) st
  ... | σa , sa , ca | σb , sb , cb =
    σa ∪ σb , (λ { (ml m) → mapFs ml (sa m) ; (mr m) → mapFs mr (sb m) }) , (λ { (ml m) → ca m ; (mr m) → cb m })
```

## §5″ 链的地板: 只留层里有位置的帧

节点 $k$ 的链在 `O k` 里. 外层的帧 $f$ 进链, 只在 $f$ 的闭包在 $k$ 里有位置时才有意义: 否则 $k$ 里的节点与闭包都用不到它, 但它会经 `⊕` 的左边读进右边闭包的界. [ScafLadderQ](ScafLadderQ.lagda.md) 由类型做这件事: 高度 $n$ 的节点的输入只带 $<n$ 的高度 (`lo n ζ`). **这里没有高度: `keepP` 用表里的证据比较闭包的位置与节点的路径**, 与 `cmpK` 同一个骨架. 这是 "位置作键" 取代高度的地方. 没有证据的帧 (活的分支变量, 闭包保留在输出里) 总留下: 它的闭包在目标里, 目标不高于节点.

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
  keepP (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (fst q) cv aq = keepP wt se P q cv aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst P) (bra y e q) cv (_ , aq) with ⊴K (tg y e) P
  ... | viaᴷ d′ P′ u = keepP (wg y e) (shˡ y e) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (fst q) (_ , cv) aq with ⊴p (tg x e₁) q
  ... | viaᴸ d′ q′ u = keepP (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq)
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , o₁ , lx) , cv) ((ℓ , b₁ , o₂ , ly) , aq) with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) b₂ b₁
  ... | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
  ...   | inj₁ s with ⊴K s P
  ...     | viaᴷ d′ P′ u = keepP (wg y e₂) (shˡ y e₂) P′ q (u (tab E) cv) aq
  keepP {E = E} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ P) (bra y e₂ q) ((ℓ′ , b₂ , o₁ , lx) , cv) ((ℓ , b₁ , o₂ , ly) , aq) | refl | inj₂ s with ⊴p s q
  ...     | viaᴸ d′ q′ u = keepP (wg x e₁) (shˡ x e₁) P q′ cv (u (tab E) aq)

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
  stChain ξ bk w st (ml m) = fs (ev (st (w m))) (just (ab m (inj₂ refl) refl))
  stChain ξ bk w st {f} (mr m) with bk m
  ... | just m′ = fs (ev (st m)) (just (ab m′ (inj₂ refl) refl))
  ... | nothing = fs (ev (st m)) nothing
```

## §9 折叠

`ψ`: 对树结构递归. 与 [LvGuardTree](LvGuardTree.lagda.md) 的差别: `ocv` 一行 (状态下降, 输出的地板下降), `omk` 一行 (读 $x$, 不读 $z$, 与 `ψᵠ` 同), `riseΩ` 的目标规范化 (`nfT`). `Ω̇` 带 `Tc`. 目标 0 (`t0`) 没有路径.

```agda
  data Tg (E : Ents) : LG → Set where
    tn : ∀ n → Tg E (natL n)
    tp : ∀ {t} (q : t < c) → Adm (tab E) q → Tg E t

  tcT : ∀ {E t} → Tg E t → Tc t
  tcT (tn n) = Tc-id (natL n)
  tcT (tp q _) = Tc-at q tc

  gapT : ∀ {E t} → Tg E t → D → Maybe ℕ
  gapT (tn n) c′ with leq (suc n) (ix c′)
  ... | true = just (ix c′)
  ... | false = nothing
  gapT (tp q a) c′ = nothing

  tgSel : ∀ {c₂ t₂ g₂ t} (P : Cp (lc c₂ t₂ g₂) c) (E : Ents) (ap : AdmC (tab E) P) → Tg E t → Sel.S P E ap (λ F → Tg F t)
  tgSel P E ap (tn n) = Sel.triv P E ap (λ _ _ → tn n)
  tgSel P E ap (tp q aq) = Sel.mapS P E ap (λ F a → tp q a) (Sel.walkA P E ap self tt q aq)

  chainᵒ : ∀ {k π} → Tc k → (O k π → O k π) → ℕ → O k π
  chainᵒ {k} tk′ f zero    = owk (λ ()) (Ω̇ k tk′)
  chainᵒ tk′ f (suc n) = f (chainᵒ tk′ f n)

  dd : ∀ {π} → Wk (π ∪ π) π
  dd (ml m) = m
  dd (mr m) = m

  SSc : ∀ {t π ρ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) (ap : AdmC (tab E) P) →
        Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))
  SSc {π = π} E T st P ap = Sel._⋈_ P E ap (Sel.selSt P E ap π st) (Sel._⋈_ P E ap (tgSel P E ap T) (Sel.walk P E ap self tt P ap))

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
  ψ E (tn n) st (oΩ {k = k} r cv h) with natCmp k n
  ... | nb d s = oΩ s (admN s) (λ ξ y → ψ E (tn n) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | na = riseΩ E (tn n) st r cv h
  ψ E (tp q aq) st (oΩ r cv h) with Vis.cmpN st wf sf r q cv aq
  ... | Vis.cb d s a = oΩ s a (λ ξ y → ψ E (tp q aq) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | Vis.cu _ = riseΩ E (tp q aq) st r cv h
  ... | Vis.cj = o0
  ψ E (tn n) st (ocl P k cv x g) = evalC E (tn n) st P k cv x g
  ψ {π = π} {ρ = ρ} E (tp q aq) st (ocl {c₁ = c₁} {t₁} {g₁} P k cv x g) with Vis.cmpK st wf sf P q cv aq
  ... | Vis.kb = evalC E (tp q aq) st P k cv x g
  ... | Vis.kj = o0
  ... | Vis.ka {c′} {t′} {g′} Q d a =
    ocl Q (inj₂ refl) a (ψ E (tp q aq) st x)
      (λ η e′ → ψ E (tp q aq) (st″ η e′) (g η (eg e′)))
    where
    lks₁ : lc c₁ t₁ g₁ ≈ lc c′ t′ g′
    lks₁ = ≈-trans (≈-sym (lk→≈ (selfC sf P) k)) d
    eg : ∀ {η} → c′ ⊑ᴰ η → c₁ ⊑ᴰ η
    eg e′ = conv (oc≅ (≈-sym lks₁)) e′
    st″ : ∀ η e′ → St E (ρ ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁ t₁ g₁ η (eg e′)))
    st″ η e′ (ml m) = mapFs ml (st m)
    st″ η e′ (mr hr) = fs nothing (just (ab {c₄ = c′} {t₄ = t′} {g₄ = g′} {e₄ = e′} (mr hr) (inj₁ lks₁) (sym (oc-sym-sec lks₁ e′))))

  riseΩ {π = π} E T st r cv h with Vis.toTab st r cv
  ... | nothing = o0
  ... | just a with nfT c tc r | trim π st {r} a
  ...   | nft d r′ tb | mkTr ξ w bk = ol (λ n → ψ E T (stBody ξ w st) (h ξ (intoU r (chainᵒ (Tc-at r tc) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n))))

  evalC E T st P k cv x g with Vis.toTabC st P cv
  ... | nothing = o0
  ... | just ap = goC E T st P k ap x g (SSc E T st P ap) (Sel.wit (SSc E T st P ap))

  goC {t} {π} {ρ} {c₁} {t₁} {g₁} {c₂} {t₂} {g₂} E T st P k ap x g SS w = go w
    where
    module M = Sel P E ap
    lk₂ : lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁
    lk₂ = lk→≈ M.kself k
    guardC : ∀ {η} → c₂ ⊑ᴰ η → c₁ ⊑ᴰ η
    guardC d = conv (oc≅ lk₂) d
    bodyG : ∀ {t′} η (d : c₂ ⊑ᴰ η) Y (F : c₂ ⊑ᴰ Y) → Ev (M.w₂ Y F) (M.φ SS) → d <ᵉ F → Tg (M.E′ Y F) t′ → O t′ ρ
    bodyG η d Y F ex q T′ = ψ (M.E′ Y F) T′ stn (g η (guardC d))
      where
      L = M.lft SS Y F ex
      stn : St (M.E′ Y F) ρ (π ∪ tk (frm c₁ t₁ g₁ η (guardC d)))
      stn (ml m) = proj₁ L m
      stn (mr hr) = fs (just (evd P (proj₂ (proj₂ L)) lk₂ (M.w₂ Y F , inj₁ (≈-sym lk₂ , refl) , ≈-sym lk₂ , subst (λ z → z <ᵉ F) (sym (oc-sym-ret lk₂ d)) q))) nothing
    body : ∀ η (d : c₂ ⊑ᴰ η) Y (F : c₂ ⊑ᴰ Y) → Ev (M.w₂ Y F) (M.φ SS) → d <ᵉ F → O t ρ
    body η d Y F ex q = bodyG η d Y F ex q (proj₁ (proj₂ (M.lft SS Y F ex)))
    go : M.Sl (M.φ SS) → O t ρ
    go (M.emp f) = mkOut (gapT T c₂) c₂
         (λ m → rb (ψ E (tn m) st x))
         (λ m η d → rb (bodyG η d (sD η) (sF d) (f _) (self<ᵉ d) (tn m)))
         (ψ E T st x)
         (λ η d → body η d (sD η) (sF d) (f _) (self<ᵉ d))
    go (M.sel u a o₃ e₀ q₀ y) = mkOut (gapT T (Bd B)) (Bd B)
         (λ m → rb (ψ E (tn m) st x))
         (λ m η d → rb (bodyG η (dG d) (upX B d) (FG d) (exG d) (qG d) (tn m)))
         (ψ E T st x)
         (λ η d → body η (dG d) (upX B d) (FG d) (exG d) (qG d))
      where
      B : Tp (uF u) (toFᵉ (M.φ SS) y)
      B = bound (uF u) (toFᵉ (M.φ SS) y) {e₀ = e₀} q₀
      dG : ∀ {η} → Bd B ⊑ᴰ η → c₂ ⊑ᴰ η
      dG d = conv⁻ (oc≅ o₃) (gr B d)
      FG : ∀ {η} (d : Bd B ⊑ᴰ η) → c₂ ⊑ᴰ upX B d
      FG d = conv⁻ (oc≅ o₃) (upF B d)
      exG : ∀ {η} (d : Bd B ⊑ᴰ η) → Ev (M.w₂ (upX B d) (FG d)) (M.φ SS)
      exG d = evBack o₃ (upF B d) (M.φ SS) y (upEv B d)
      qG : ∀ {η} (d : Bd B ⊑ᴰ η) → dG d <ᵉ FG d
      qG d = <-conv⁻ (oc≅ o₃) _ _ (up< B d)


-- ψ_n(Ω_L)
Tn : (L : LG) → Cfˢ L → Tc L → (n : ℕ) → O (natL n) tz
Tn L (w , s) tc n = FoldO.ψ L w s tc ∅ (FoldO.tn n) (λ ()) (Ω̇ L tc)
```
