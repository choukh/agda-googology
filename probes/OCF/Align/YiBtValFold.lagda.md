# YiBtVal 主引理：新折叠在一切输入层与目标层上保持关系

**验收文件，档位：编译定理 (模块参数 `AdmI` 是层号类的接口，实例在 [YiBtValAdm](YiBtValAdm.lagda.md))。** `FOLD`：`RelF K y η` 且外部派发完全，
推出 `RelF m (ψ p σ y) (Ψ m K … x η)`，目标的参照层号 `i` 只要求 `Corr i m`。结点处参照一侧按 `<ᴵ-dec` 分情况：保留时由 `adm-sep` 与派发完全性得到树一侧的保留，
其余两种由 `POS` 排除树一侧的保留；折叠时两条链同步 (`Chainᴿ`)。极限层号上 `top` 的 `mix` 行经部分和 (`PSUM`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL; Gd; Lgl; Nested)
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawFoldBase using (Ext; low; mix; wayOf; inS; inL; Nd; nd; NdR; NdL; Ψn; ΨN)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvAllRel using (R0; r0; TRC)
open import OCF.Align.YiBtValRel
open import OCF.Align.YiBtValAdd
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open L using (_≅ᴵ_; _<ᴵ_)
open V using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 层号类的接口

`adm-sep`：参照一侧在目标之下的层号是目标里某个位置的字面层号 (结构对应推出字面相等，一般要函数外延，所以作为层号类的条款)。

```agda
record AdmI : Set₁ where
  field
    Adm : LF → Set
    adm-S : ∀ {k} → Adm (B.suc k) → Adm k
    adm-L : ∀ {f} → Adm (B.lim f) → ∀ n → Adm (f n)
    adm-lev : ∀ {K} → Adm K → ∀ r → Adm (lev K r)
    adm-plain : ∀ {K} → Adm K → Plain K
    adm-sep : ∀ {k m j a i} → Adm k → Adm m → Corr j k → j ≅ᴵ a → a <ᴵ i → Corr i m → At m k

module FoldA (I : AdmI) where
  open AdmI I
```

## 2 只看第一支

```agda
  FIRSTn : ∀ m → Plain m → ∀ k .(pk : Plain k) (y : Way m k) (Nd₀ : NdR m k) {j} {z : L.Ordᶜ j} →
    (∀ .(e : Gd k (Nd.c Nd₀) (Nd.c Nd₀)) → RelF m z (Nd.gm Nd₀ (Nd.c Nd₀) e)) →
    RelF m z (Ψn m k pk y Nd₀)
  FIRSTn m pm .(lev m s) pk (keep s refl) Nd₀ h =
    bRaw m pm s (Nd.c Nd₀) (Nd.t Nd₀) (Nd.gm Nd₀) h
  FIRSTn m pm k pk fold (nd c lw nw t gm gk lk nk ps) h = out-l m 0 (h (inj₁ refl , lw , nw))

  FIRSTN : ∀ m → Plain m → ∀ k (pk : Plain k) r (y : Way m (lev k r)) (Nd₀ : NdL m k r)
    {j} {z : L.Ordᶜ j} →
    (∀ .(e : GdL k r (Nd.c Nd₀) (Nd.c Nd₀)) → RelF m z (Nd.gm Nd₀ (Nd.c Nd₀) e)) →
    RelF m z (ΨN m k pk r y Nd₀)
  FIRSTN m pm B.zero pk () y Nd₀ h
  FIRSTN m pm (B.suc k) pk (inj₁ _) y Nd₀ h = FIRSTn m pm k pk y Nd₀ h
  FIRSTN m pm (B.suc k) pk (inj₂ r) y Nd₀ h = FIRSTN m pm k pk r y Nd₀ h
  FIRSTN m pm (B.lim f) pk (n , r) y Nd₀ h = FIRSTN m pm (f n) (pk n) r y Nd₀ h
  FIRSTN m pm (B.lc k c w b t g) () r y Nd₀ h
```

## 3 结点：保留、链、两侧派发的一致

```agda
  module Target (m : LF) (am : Adm m) {i ℓ : L.Ordᴵ} (ei : Corr i m) (p : i <ᴵ ℓ) where

    pm : Plain m
    pm = adm-plain am

    keep-below : ∀ {j} k → Corr j k → ∀ (y : Way m k) → IsKeep y → j L.≺ᴵ i
    keep-below .(lev m s) lv (keep s refl) h = POS m s lv ei

    sep-at : ∀ k → Adm k → ∀ {j a′} → Corr j k → j ≅ᴵ a′ → a′ <ᴵ i → At m k
    sep-at k ak lv e r = adm-sep ak am lv e r ei

    KEEPc : ∀ k .(pk : Plain k) (y : Way m k) (Nd₀ : NdR m k) → IsKeep y →
      ∀ {j K} (q : j <ᴵ K) (F : L.U j (L.<→◃ q) → L.Ordᶜ K) (σ : L.Simᴵ K ℓ)
      {a′} (e : j ≅ᴵ a′) (r : a′ <ᴵ i) → Corr j k →
      (∀ {j′} → Corr j′ k → RelF k (L.Ω j′) (Nd.c Nd₀)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) y′))) (Nd.gm Nd₀ a e)) →
      RelF m (L.limᵢ r (λ y′ → L.ψ p σ (F (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) y′))))))
        (Ψn m k pk y Nd₀)
    KEEPc .(lev m s) pk (keep s refl) Nd₀ kp q F σ e r lv base hm =
      ndRaw m pm s (Nd.c Nd₀) (Nd.t Nd₀) (Nd.gm Nd₀) (Corr-≅ (L.≅ᴵ-sym e) lv) base
        (λ y′ a e′ rl →
          subst (λ w → RelF m (L.ψ p σ (F (L.into (L.<→◃ q) (L.tr⁻ e w)))) (Nd.gm Nd₀ a e′))
            (sym (L.out-into (L.<→◃ r) y′))
            (hm (L.tr⁻ e y′) a e′ (TRC.tr⁻ᴿ (TRC-all (lev m s)) e rl)))
    KEEPc k pk fold Nd₀ () q F σ e r lv base hm

    module Chainᴿ {j K} (q : j <ᴵ K) (F : L.U j (L.<→◃ q) → L.Ordᶜ K) (σ : L.Simᴵ K ℓ)
      (k : LF) .(pk : Plain k) (Nd₀ : NdR m k)
      (base : RelF k (L.Ω j) (Nd.c Nd₀))
      (hm : ∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) y′))) (Nd.gm Nd₀ a e))
      (hk : ∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF k (L.ψ q (λ r → r) (F (L.into (L.<→◃ q) y′))) (Nd.gk Nd₀ a e)) where

      pts : ℕ → Pt k (Nd.c Nd₀)
      pts = iterate (N.nextᴿ pk Nd₀) (N.startᴿ Nd₀)

      δ : ℕ → L.Ordᶜ j
      δ = iter (λ x → L.ψ q (λ r → r) (F (L.into (L.<→◃ q) x))) (L.Ω j)

      stepAt : ∀ (P : Pt k (Nd.c Nd₀)) {x} → RelF k x (atᵖ P) →
        RelF k (L.ψ q (λ r → r) (F (L.into (L.<→◃ q) x))) (atᵖ (N.nextᴿ pk Nd₀ P))
      stepAt (pt a e) r = ABSORB k a (hk _ a e r)

      chain : ∀ n → RelF k (δ n) (atᵖ (pts n))
      chain zero = base
      chain (suc n) = stepAt (pts n) (chain n)

      obsAt : ∀ (P : Pt k (Nd.c Nd₀)) {x} → RelF k x (atᵖ P) →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) x))) (N.obsᴿ Nd₀ P)
      obsAt (pt a e) r = hm _ a e r

      result : RelF m (L.lim (λ n → L.ψ p σ (F (L.into (L.<→◃ q) (δ n))))) (Ψn m k pk fold Nd₀)
      result = out-ll m (λ n → out-l m n (obsAt (pts n) (chain n)))

    FOLDc : ∀ k .(pk : Plain k) (y : Way m k) (Nd₀ : NdR m k) → (IsKeep y → ⊥) →
      ∀ {j K} (q : j <ᴵ K) (F : L.U j (L.<→◃ q) → L.Ordᶜ K) (σ : L.Simᴵ K ℓ) →
      RelF k (L.Ω j) (Nd.c Nd₀) →
      (∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) y′))) (Nd.gm Nd₀ a e)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF k (L.ψ q (λ r → r) (F (L.into (L.<→◃ q) y′))) (Nd.gk Nd₀ a e)) →
      RelF m (L.lim (λ n → L.ψ p σ (F (L.into (L.<→◃ q)
          (iter (λ x → L.ψ q (λ r → r) (F (L.into (L.<→◃ q) x))) (L.Ω j) n)))))
        (Ψn m k pk y Nd₀)
    FOLDc k pk fold Nd₀ nk q F σ base hm hk = Chainᴿ.result q F σ k pk Nd₀ base hm hk
    FOLDc .(lev m s) pk (keep s refl) Nd₀ nk q F σ base hm hk = ⊥-elim (nk tt)

    NODEn : ∀ k → Adm k → .(pk : Plain k) (y : Way m k) (Nd₀ : NdR m k) → (At m k → IsKeep y) →
      ∀ {j K} (q : j <ᴵ K) (F : L.U j (L.<→◃ q) → L.Ordᶜ K) (σ : L.Simᴵ K ℓ) → Corr j k →
      (∀ {j′} → Corr j′ k → RelF k (L.Ω j′) (Nd.c Nd₀)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) y′))) (Nd.gm Nd₀ a e)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : Gd k (Nd.c Nd₀) a) → RelF k y′ a →
        RelF k (L.ψ q (λ r → r) (F (L.into (L.<→◃ q) y′))) (Nd.gk Nd₀ a e)) →
      RelF m (L.ψ p σ (L.limᵢ q F)) (Ψn m k pk y Nd₀)
    NODEn k ak pk y Nd₀ cy q F σ lv base hm hk with L.<ᴵ-dec (σ q) p
    ... | injᵃ (L.via e r) = KEEPc k pk y Nd₀ (cy (sep-at k ak lv e r)) q F σ e r lv base hm
    ... | injᵇ (L.via e r) =
      FOLDc k pk y Nd₀
        (λ kp → L.clash₁ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (keep-below k lv y kp) (L.via e r))
        q F σ (base lv) hm hk
    ... | injᶜ e =
      FOLDc k pk y Nd₀
        (λ kp → L.clash₂ (L.≅ᴵ-refl _) (L.≅ᴵ-refl _) (keep-below k lv y kp) e)
        q F σ (base lv) hm hk

    NODEW : ∀ k (pk : Plain k) r (y : Way m (lev k r)) (Nd₀ : NdL m k r) →
      (At m (lev k r) → IsKeep y) → Adm (lev k r) →
      ∀ {j K} (q : j <ᴵ K) (F : L.U j (L.<→◃ q) → L.Ordᶜ K) (σ : L.Simᴵ K ℓ) →
      Corr j (lev k r) →
      (∀ {j′} → Corr j′ (lev k r) → RelL k r (L.Ω j′) (Nd.c Nd₀)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : GdL k r (Nd.c Nd₀) a) → RelL k r y′ a →
        RelF m (L.ψ p σ (F (L.into (L.<→◃ q) y′))) (Nd.gm Nd₀ a e)) →
      (∀ (y′ : L.Ordᶜ j) a .(e : GdL k r (Nd.c Nd₀) a) → RelL k r y′ a →
        RelF (lev k r) (L.ψ q (λ r → r) (F (L.into (L.<→◃ q) y′))) (Nd.gk Nd₀ a e)) →
      RelF m (L.ψ p σ (L.limᵢ q F)) (ΨN m k pk r y Nd₀)
    NODEW B.zero pk () y Nd₀ cy al q F σ lv base hm hk
    NODEW (B.suc k) pk (inj₁ _) y Nd₀ cy al q F σ lv base hm hk =
      NODEn k al pk y Nd₀ cy q F σ lv base hm hk
    NODEW (B.suc k) pk (inj₂ r) y Nd₀ cy al q F σ lv base hm hk =
      NODEW k pk r y Nd₀ cy al q F σ lv base hm hk
    NODEW (B.lim f) pk (n , r) y Nd₀ cy al q F σ lv base hm hk =
      NODEW (f n) (pk n) r y Nd₀ cy al q F σ lv base hm hk
    NODEW (B.lc k c w b t g) () r y Nd₀ cy al q F σ lv base hm hk
```

## 4 起点 (参照的零) 与主引理

```agda
  OMEGA : ∀ K → Adm K → (pl : Plain K) (Lg : Legal K) → ∀ m → Adm m → (x : Ext m K) →
    ∀ {i} → Corr i m → ∀ η .(l : Lgl K η) .(nb : Nested K η) →
    RelF m (L.Ω i) (N.Ψ m K pl Lg x η l nb)
  OMEGA K aK pl Lg m am x ei G.zero l nb = START m ei
  OMEGA K aK pl Lg m am x ei (G.suc a) l nb = out-l m 0 (OMEGA K aK pl Lg m am x ei a l nb)
  OMEGA K aK pl Lg m am x ei (G.lim F) l nb =
    out-l m 0 (OMEGA K aK pl Lg m am x ei (F 0) (proj₂ l 0) (nb 0))
  OMEGA K aK pl Lg m am x ei (G.lc r c t g) l nb =
    FIRSTN m (adm-plain am) K pl r (wayOf x r) (N.ndL m K pl Lg x r c t g l nb)
      (λ e → OMEGA K aK pl Lg m am x ei (g c e)
        (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
  OMEGA B.zero aK pl Lg m am x ei (G.em () T) l nb
  OMEGA (B.suc k) aK pl Lg m am x ei (G.em _ T) l nb =
    OMEGA k (adm-S aK) pl Lg m am (inS x) ei T l nb
  OMEGA (B.lim f) aK pl Lg m am x ei (G.em n T) l nb =
    OMEGA (f n) (adm-L aK n) (pl n) (proj₂ Lg n) m am (inL x n) ei T l nb
  OMEGA (B.lc k c w b t g) aK () Lg m am x ei (G.em i′ T) l nb
  OMEGA B.zero aK pl Lg m am x ei G.top l nb = out-l m 0 (START m ei)
  OMEGA (B.suc k) aK pl Lg m am x ei G.top l nb =
    FIRSTn m (adm-plain am) k pl (wayOf x (inj₁ tt)) (N.ndT m k pl Lg (inS x))
      (λ e → OMEGA k (adm-S aK) pl Lg m am (inS x) ei (cO k) (cO-Lgl k) (cO-Nested k))
  OMEGA (B.lim f) aK pl Lg m am low ei G.top l nb =
    out-l m 0 (OMEGA (f 0) (adm-L aK 0) (pl 0) (proj₂ Lg 0) m am low ei G.top tt tt)
  OMEGA (B.lim f) aK pl Lg m am (mix w) ei G.top l nb =
    out-l m 0 (OMEGA (f 0) (adm-L aK 0) (pl 0) (proj₂ Lg 0) m am (mix (λ r → w (0 , r))) ei G.top tt tt)
  OMEGA (B.lc k c w b t g) aK () Lg m am x ei G.top l nb

  FOLD0 : Adm B.zero → (pl : Plain B.zero) (Lg : Legal B.zero) → ∀ m → Adm m → (x : Ext m B.zero) →
    ∀ {i ℓ} → Corr i m → (p : i <ᴵ ℓ) →
    ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a → (σ : L.Simᴵ L.zero ℓ) →
    .(l : Lgl B.zero a) .(nb : Nested B.zero a) →
    RelF m (L.ψ p σ y) (N.Ψ m B.zero pl Lg x a l nb)
  FOLD0 aK pl Lg m am x ei p z≼ a q σ l nb = OMEGA B.zero aK pl Lg m am x ei a l nb
  FOLD0 aK pl Lg m am x ei p (s≼s r) (G.suc a) refl σ l nb =
    SUCC m (FOLD0 aK pl Lg m am x ei p r a refl σ l nb)
  FOLD0 aK pl Lg m am x ei p (s≼s r) G.top refl σ l nb =
    SUCC m (FOLD0 aK pl Lg m am x ei p r G.zero refl σ tt tt)
  FOLD0 aK pl Lg m am x ei p (≼l n r) (G.lim F) refl σ l nb =
    out-l m n (FOLD0 aK pl Lg m am x ei p r (F n) refl σ (proj₂ l n) (nb n))
  FOLD0 aK pl Lg m am x ei p (l≼ h) a q σ l nb =
    out-ll m (λ n → FOLD0 aK pl Lg m am x ei p (h n) a q σ l nb)
  FOLD0 aK pl Lg m am x ei p (≼i {p = ()} x′ ex r) a q σ l nb
  FOLD0 aK pl Lg m am x ei p (i≼ {p = ()} h) a q σ l nb
  FOLD0 aK pl Lg m am x ei p (≼u {r = ()} r) a q σ l nb
  FOLD0 aK pl Lg m am x ei p (u≼ {r = ()} r) a q σ l nb

  FOLD : ∀ K → Adm K → (pl : Plain K) (Lg : Legal K) → ∀ m → Adm m → (x : Ext m K) → N.Complete x →
    ∀ {j} {y : L.Ordᶜ j} {η} → RelF K y η →
    ∀ {i ℓ} → Corr i m → (p : i <ᴵ ℓ) (σ : L.Simᴵ j ℓ) →
    .(l : Lgl K η) .(nb : Nested K η) → RelF m (L.ψ p σ y) (N.Ψ m K pl Lg x η l nb)
  FOLD B.zero aK pl Lg m am x cx {η = a} (r0 q) ei p σ l nb =
    FOLD0 aK pl Lg m am x ei p q a refl σ l nb
  FOLD (B.suc k) aK pl Lg m am x cx {η = η} zr ei p σ l nb =
    OMEGA (B.suc k) aK pl Lg m am x ei η l nb
  FOLD (B.suc k) aK pl Lg m am x cx (ssr r) ei p σ l nb =
    SUCC m (FOLD (B.suc k) aK pl Lg m am x cx r ei p σ l nb)
  FOLD (B.suc k) aK pl Lg m am x cx (sr r) ei p σ l nb =
    out-l m 0 (FOLD (B.suc k) aK pl Lg m am x cx r ei p σ l nb)
  FOLD (B.suc k) aK pl Lg m am x cx (lr n r) ei p σ l nb =
    out-l m n (FOLD (B.suc k) aK pl Lg m am x cx r ei p σ (proj₂ l n) (nb n))
  FOLD (B.suc k) aK pl Lg m am x cx (llr h) ei p σ l nb =
    out-ll m (λ n → FOLD (B.suc k) aK pl Lg m am x cx (h n) ei p σ l nb)
  FOLD (B.suc k) aK pl Lg m am x cx (br {s = s} {c = c} {t = t} {g = g} h) ei p σ l nb =
    FIRSTN m (adm-plain am) (B.suc k) pl s (wayOf x s) (N.ndL m (B.suc k) pl Lg x s c t g l nb)
      (λ e → FOLD (B.suc k) aK pl Lg m am x cx (h e) ei p σ
        (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
  FOLD (B.suc k) aK pl Lg m am x cx
    (ndr {s = s} {c = c} {t = t} {g = g} {q = q} {f = F} lv base h) ei p σ l nb =
    Target.NODEW m am ei p (B.suc k) pl s (wayOf x s) (N.ndL m (B.suc k) pl Lg x s c t g l nb)
      (cx s) (adm-lev aK s) q F σ lv base
      (λ y′ a e r′ → FOLD (B.suc k) aK pl Lg m am x cx (h y′ a e r′) ei p σ
        (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
      (λ y′ a e r′ → FOLD (B.suc k) aK pl Lg (lev (B.suc k) s) (adm-lev aK s)
        (N.own (B.suc k) pl Lg s) (N.complete-own (B.suc k) pl Lg s) (h y′ a e r′) lv q (λ r → r)
        (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
  FOLD (B.suc k) aK pl Lg m am x cx (ntr {q = q} {f = F} lv base h) ei p σ l nb =
    Target.NODEn m am ei p k (adm-S aK) pl (wayOf x (inj₁ tt)) (N.ndT m k pl Lg (inS x))
      (cx (inj₁ tt)) q F σ lv base
      (λ y′ a e r′ → FOLD (B.suc k) aK pl Lg m am x cx (h y′ a r′) ei p σ
        (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
      (λ y′ a e r′ → FOLD (B.suc k) aK pl Lg k (adm-S aK)
        (N.own (B.suc k) pl Lg (inj₁ tt)) (N.complete-own (B.suc k) pl Lg (inj₁ tt)) (h y′ a r′)
        lv q (λ r → r) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  FOLD (B.suc k) aK pl Lg m am x cx (emr r) ei p σ l nb =
    FOLD k (adm-S aK) pl Lg m am (inS x) (N.complete-S x cx) r ei p σ l nb
  FOLD (B.suc k) aK pl Lg m am x cx (ur r) ei p σ l nb =
    FOLD (B.suc k) aK pl Lg m am x cx r ei p (λ q → σ (L.suc q)) l nb
  FOLD (B.suc k) aK pl Lg m am x cx (us {n = n} r) ei p σ l nb =
    FOLD (B.suc k) aK pl Lg m am x cx r ei p (λ q → σ (L.lim n q)) l nb
  FOLD (B.lim f) aK pl Lg m am x cx {η = η} zrˡ ei p σ l nb =
    OMEGA (B.lim f) aK pl Lg m am x ei η l nb
  FOLD (B.lim f) aK pl Lg m am x cx (ssrˡ r) ei p σ l nb =
    SUCC m (FOLD (B.lim f) aK pl Lg m am x cx r ei p σ l nb)
  FOLD (B.lim f) aK pl Lg m am x cx (srˡ r) ei p σ l nb =
    out-l m 0 (FOLD (B.lim f) aK pl Lg m am x cx r ei p σ l nb)
  FOLD (B.lim f) aK pl Lg m am x cx (lrˡ n r) ei p σ l nb =
    out-l m n (FOLD (B.lim f) aK pl Lg m am x cx r ei p σ (proj₂ l n) (nb n))
  FOLD (B.lim f) aK pl Lg m am x cx (llrˡ h) ei p σ l nb =
    out-ll m (λ n → FOLD (B.lim f) aK pl Lg m am x cx (h n) ei p σ l nb)
  FOLD (B.lim f) aK pl Lg m am x cx (brˡ {s = s} {c = c} {t = t} {g = g} h) ei p σ l nb =
    FIRSTN m (adm-plain am) (B.lim f) pl s (wayOf x s) (N.ndL m (B.lim f) pl Lg x s c t g l nb)
      (λ e → FOLD (B.lim f) aK pl Lg m am x cx (h e) ei p σ
        (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
  FOLD (B.lim f) aK pl Lg m am x cx
    (ndrˡ {s = s} {c = c} {t = t} {g = g} {q = q} {h = F} lv base h) ei p σ l nb =
    Target.NODEW m am ei p (B.lim f) pl s (wayOf x s) (N.ndL m (B.lim f) pl Lg x s c t g l nb)
      (cx s) (adm-lev aK s) q F σ lv base
      (λ y′ a e r′ → FOLD (B.lim f) aK pl Lg m am x cx (h y′ a e r′) ei p σ
        (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
      (λ y′ a e r′ → FOLD (B.lim f) aK pl Lg (lev (B.lim f) s) (adm-lev aK s)
        (N.own (B.lim f) pl Lg s) (N.complete-own (B.lim f) pl Lg s) (h y′ a e r′) lv q (λ r → r)
        (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
  FOLD (B.lim f) aK pl Lg m am x cx (emrˡ {n = n} r) ei p σ l nb =
    FOLD (f n) (adm-L aK n) (pl n) (proj₂ Lg n) m am (inL x n) (N.complete-L x cx n) r ei p σ l nb
  FOLD (B.lim f) aK pl Lg m am low cx (tlrˡ n r) ei p σ l nb =
    out-l m n (FOLD (f n) (adm-L aK n) (pl n) (proj₂ Lg n) m am low (N.complete-L low cx n)
      r ei p σ tt tt)
  FOLD (B.lim f) aK pl Lg m am (mix w) cx (tlrˡ n r) ei p σ l nb =
    out-l m n (PSUM m (λ n → N.Ψ m (f n) (pl n) (proj₂ Lg n) (mix (λ r → w (n , r))) G.top tt tt) n
      (FOLD (f n) (adm-L aK n) (pl n) (proj₂ Lg n) m am (mix (λ r → w (n , r)))
        (N.complete-L (mix w) cx n) r ei p σ tt tt))
  FOLD (B.lim f) aK pl Lg m am x cx (urˡ r) ei p σ l nb =
    FOLD (B.lim f) aK pl Lg m am x cx r ei p (λ q → σ (L.suc q)) l nb
  FOLD (B.lim f) aK pl Lg m am x cx (usˡ {n = n} r) ei p σ l nb =
    FOLD (B.lim f) aK pl Lg m am x cx r ei p (λ q → σ (L.lim n q)) l nb
  FOLD (B.lc k c w b t g) aK pl Lg m am x cx () ei p σ l nb
```
