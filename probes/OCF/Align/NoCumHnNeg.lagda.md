# `Hn` 对字面任意的层是假的

> 不含记号. **定理 `no-Hn-b`:** 取 $w=\lim_n 2n$ (字面合法, `g-w`). `t₂ = ψ 0 0 (ψ 1 w (Ω̇ 1 0))`, 即 $\psi_0(\psi_{\Omega+w}(\Omega_\Omega))$ 这棵数据树, `Hn t₂` 推出 $\bot$. **这否定的只是:** 当前的 `mx` (把目标 $t$ 放进世界) 与字面第一位置的守卫, 对这个 $w$ 的 `Hn`. **不否定** 目标是输出的读出时的 `Hn`, 不否定 Ω+1, 不否定 "不累加".
>
> 判断, 未编译: `t₂` 的形状是 `Tᴰ 1 (w+1) …` 的链上第 1 个点在第 0 项处的闭包 (世界的证据不同). 直接对 `Tᴰ` 走这条路径, 类型检查堆耗尽 (退出码 251), 所以定理写在 `t₂` 上.
>
> 原因: 闭包的世界是 $w$, 而第一支的计值里找不到 $w$: `Pψ` 说折叠到第 0 层的项里, 每个极限要么第 0 项非零, 要么第 1 项不是 $2$. $w$ 的第 0 项是 $0$, 第 1 项是 $2$.
>
> 这说明守卫**不是**只看 $(p,a)$ 形状就成立的东西: 它依赖下标从哪里来. 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumHnNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪S; ≪∘; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumMain using (WF; ψW; ΩW)
open import OCF.Align.NoCumForce
```

## §1 形状

```agda
Nz Ns N2 P : ∀ {u} → 𝓡 u → Set
Nz o0 = ⊥
Nz (os _) = ⊤
Nz (ol _) = ⊤
Nz (oi () _)
Nz (od () _ _ _)
Nz (oc _ _) = ⊤
Nz (oe () _)
Nz (oL () _ _ _)
Nz (ow _ _ x) = Nz x

Ns o0 = ⊤
Ns (os _) = ⊥
Ns (ol _) = ⊤
Ns (oi () _)
Ns (od () _ _ _)
Ns (oc _ _) = ⊤
Ns (oe () _)
Ns (oL () _ _ _)
Ns (ow _ _ x) = Ns x

N2 o0 = ⊤
N2 (os x) = Ns x
N2 (ol _) = ⊤
N2 (oi () _)
N2 (od () _ _ _)
N2 (oc _ _) = ⊤
N2 (oe () _)
N2 (oL () _ _ _)
N2 (ow _ _ x) = N2 x

P o0 = ⊤
P (os x) = P x
P (ol F) = (Nz (F 0) ⊎ N2 (F 1)) × (∀ n → P (F n))
P (oi () _)
P (od () _ _ _)
P {u} (oc x h) = Nz x × P x × (∀ {v} (q : u ⊲ v) (g : Gw v) → P (h q g))
P (oe () _)
P (oL () _ _ _)
P (ow _ _ x) = P x

Sh : ∀ {u} → 𝓡 u → Set
Sh t = Nz t × N2 t × P t
```

## §2 加法, 折叠保形状

```agda
P-add  : ∀ {u₀ u′} (W : 𝓡 u₀) (gu : Gw u₀) (Q : azero ⊲ azero) (x : 𝓡 u′) (gx : Gw u′) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : u′ ⊲ v) (bv : azero ⊲ v) → Nz W → P W → P x → Nz (add W gu (sa Q) x gx v gv uv xv bv) × P (add W gu (sa Q) x gx v gv uv xv bv)
P-add⁰ : ∀ {u₀ u′} (W : 𝓡 u₀) (gu : Gw u₀) (Q : azero ⊲ azero) (x : 𝓡 u′) (gx : Gw u′) m (gm : Gw m) (um : u₀ ⊲ m) (tm : u′ ⊲ m) (am : azero ⊲ m) → Nz W → P W → P x → Nz (add⁰ W gu (sa Q) x gx m gm um tm am) × P (add⁰ W gu (sa Q) x gx m gm um tm am)

P-add W gu Q x gx v gv uv xv bv nw pw px with mx gu gv uv xv bv
... | mx′ m gm um tm am mv = P-add⁰ W gu Q x gx m gm um tm am nw pw px

P-add⁰ W gu Q o0 gx m gm um tm am nw pw px = nw , pw
P-add⁰ W gu Q (os x) gx m gm um tm am nw pw px = tt , proj₂ (P-add W gu Q x gx m gm um tm am nw pw px)
P-add⁰ W gu Q (ol F) gx m gm um tm am nw pw (_ , px) =
  tt , inj₁ (proj₁ (P-add W gu Q (F 0) gx m gm um tm am nw pw (px 0))) , (λ n → proj₂ (P-add W gu Q (F n) gx m gm um tm am nw pw (px n)))
P-add⁰ W gu Q (oi () _) gx m gm um tm am nw pw px
P-add⁰ W gu Q (od () _ _ _) gx m gm um tm am nw pw px
P-add⁰ W gu Q (oc x h) gx m gm um tm am nw pw (_ , px , ph) =
  tt , proj₁ (P-add W gu Q x gx m gm um tm am nw pw px) , proj₂ (P-add W gu Q x gx m gm um tm am nw pw px) ,
  (λ {v} q g → proj₂ (P-add W gu Q (h (⊲-tr tm q) g) g v g (⊲-tr um q) C.self (⊲-tr am q) nw pw (ph (⊲-tr tm q) g)))
P-add⁰ W gu Q (oe () _) gx m gm um tm am nw pw px
P-add⁰ W gu Q (oL () _ _ _) gx m gm um tm am nw pw px
P-add⁰ W gu Q (ow p g′ x) gx m gm um tm am nw pw px = P-add W gu Q x g′ m gm um (⊲-tr p tm) am nw pw px

P-rep : ∀ {u} (y : 𝓡 u) (g : Gw u) → Nz y → P y → ∀ n → P (rep y g n)
Nz-rep : ∀ {u} (y : 𝓡 u) (g : Gw u) → Nz y → P y → ∀ n → Nz (rep y g (suc n))
P-rep y g ny py zero = tt
P-rep y g ny py (suc zero) = py
P-rep {u} y g ny py (suc (suc m)) = proj₂ (P-add (rep y g (suc m)) g C.self y g u g C.self C.self (z⊲ u) (Nz-rep y g ny py m) (P-rep y g ny py (suc m)) py)
Nz-rep y g ny py zero = ny
Nz-rep {u} y g ny py (suc m) = proj₁ (P-add (rep y g (suc m)) g C.self y g u g C.self C.self (z⊲ u) (Nz-rep y g ny py m) (P-rep y g ny py (suc m)) py)

NN : ∀ {u} → 𝓡 u → Set
NN t = Nz t × N2 t

NNψ  : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : azero ⊲ v) (av : a ⊲ v) → NN (ψ zero azero x gu v gv uv tv av)
NNψ⁰ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) → NN (ψ⁰ zero azero x gu m gm um tm am)
NNL  : ∀ {p h k u} (j : h <ᴺ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (km : k ⊲ m) → NN (ψL zero azero j x gu m gm um tm km)

NNψ x gu v gv uv tv av with mx gu gv uv tv av
... | mx′ m gm um tm am mv = NNψ⁰ x gu m gm um tm am

NNψ⁰ o0 gu m gm um tm am = tt , tt
NNψ⁰ (os x) gu m gm um tm am = tt , tt
NNψ⁰ (ol F) gu m gm um tm am = tt , tt
NNψ⁰ {p = suc p} (oi r h) gu m gm um tm am = tt , tt
NNψ⁰ {p = zero} (oi r h) gu m gm um tm am with cmpN (≪∘ r am) tm (lgw gm)
... | keep ()
... | rise _ = tt , tt
NNψ⁰ (od {h = suc h₀} j k r h) gu m gm um tm am = tt , tt
NNψ⁰ (od {h = zero} j k r h) gu m gm um tm am with cmpN (≪∘ r um) tm (lgw gm)
... | keep ()
... | rise _ = tt , tt
NNψ⁰ (oc x h) gu m gm um tm am = tt , tt
NNψ⁰ (oe es x) gu m gm um tm am = NNψ x gu m gm um tm (⊲-tr (C.suc C.self) am)
NNψ⁰ (oe (el n) x) gu m gm um tm am = NNψ x gu m gm um tm (⊲-tr (C.lim n C.self) am)
NNψ⁰ (oL j k e x) gu m gm um tm am = NNL j x gu m gm um tm (⊲-tr e um)
NNψ⁰ (ow p g′ x) gu m gm um tm am = NNψ x g′ m gm (⊲-tr p um) tm am

NNL zero x gu m gm um tm km = NNψ x gu m gm um tm km
NNL (suc j) x gu m gm um tm km = NNL j x gu m gm um tm km

oiP : ∀ {p a u k} (r : k ≪ a) (h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) →
      (∀ z → P (ψ zero azero (h um gm (inS (≪S r) z)) gm m gm C.self tm am)) → (∀ z → Nz (ψ zero azero (h um gm (inS (≪S r) z)) gm m gm C.self tm am)) →
      P (ψ⁰ zero azero (oi r h) gu m gm um tm am)
oiP {p = suc p} r h gu m gm um tm am Pz Nz₁ = inj₁ (Nz₁ _) , (λ n → Pz _)
oiP {p = zero} r h gu m gm um tm am Pz Nz₁ with cmpN (≪∘ r am) tm (lgw gm)
... | keep ()
... | rise _ = inj₁ (Nz₁ _) , (λ n → Pz _)

odP : ∀ {p a u h₀ k} (j : h₀ <ᴺ p) (r : k ≪ u) (h : ∀ {v} → u ⊲ v → Gw v → Low p j k v → 𝓞 p a v) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) →
      (∀ z → P (ψ zero azero (h um gm (inL j z)) gm m gm C.self tm am)) → (∀ z → Nz (ψ zero azero (h um gm (inL j z)) gm m gm C.self tm am)) →
      P (ψ⁰ zero azero (od j k r h) gu m gm um tm am)
odP {h₀ = suc h₀} j r h gu m gm um tm am Pz Nz₁ = inj₁ (Nz₁ _) , (λ n → Pz _)
odP {h₀ = zero} j r h gu m gm um tm am Pz Nz₁ with cmpN (≪∘ r um) tm (lgw gm)
... | keep ()
... | rise _ = inj₁ (Nz₁ _) , (λ n → Pz _)

Pψ  : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : azero ⊲ v) (av : a ⊲ v) → P (ψ zero azero x gu v gv uv tv av)
Pψ⁰ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) → P (ψ⁰ zero azero x gu m gm um tm am)
PL  : ∀ {p h k u} (j : h <ᴺ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (km : k ⊲ m) → P (ψL zero azero j x gu m gm um tm km)

Pψ x gu v gv uv tv av with mx gu gv uv tv av
... | mx′ m gm um tm am mv = Pψ⁰ x gu m gm um tm am

Pψ⁰ o0 gu m gm um tm am = tt
Pψ⁰ (os x) gu m gm um tm am =
  inj₂ (proj₂ (NNψ x gu m gm um tm am)) , P-rep _ gm (proj₁ (NNψ x gu m gm um tm am)) (Pψ x gu m gm um tm am)
Pψ⁰ (ol F) gu m gm um tm am =
  inj₁ (proj₁ (NNψ (F 0) gu m gm um tm am)) , (λ n → Pψ (F n) gu m gm um tm am)
Pψ⁰ (oi r h) gu m gm um tm am =
  oiP r h gu m gm um tm am (λ z → Pψ (h um gm (inS (≪S r) z)) gm m gm C.self tm am) (λ z → proj₁ (NNψ (h um gm (inS (≪S r) z)) gm m gm C.self tm am))
Pψ⁰ (od j k r h) gu m gm um tm am =
  odP j r h gu m gm um tm am (λ z → Pψ (h um gm (inL j z)) gm m gm C.self tm am) (λ z → proj₁ (NNψ (h um gm (inL j z)) gm m gm C.self tm am))
Pψ⁰ (oc x h) gu m gm um tm am =
  proj₁ (NNψ x gu m gm um tm am) , Pψ x gu m gm um tm am ,
  (λ {v} w g → Pψ (h (⊲-tr um w) g) g v g C.self (⊲-tr tm w) (⊲-tr am w))
Pψ⁰ (oe es x) gu m gm um tm am = Pψ x gu m gm um tm (⊲-tr (C.suc C.self) am)
Pψ⁰ (oe (el n) x) gu m gm um tm am = Pψ x gu m gm um tm (⊲-tr (C.lim n C.self) am)
Pψ⁰ (oL j k e x) gu m gm um tm am = PL j x gu m gm um tm (⊲-tr e um)
Pψ⁰ (ow p g′ x) gu m gm um tm am = Pψ x g′ m gm (⊲-tr p um) tm am

PL zero x gu m gm um tm km = Pψ x gu m gm um tm km
PL (suc j) x gu m gm um tm km = PL j x gu m gm um tm km
```

## §3 $w$ 不在里面

```agda
nA : ℕ → A
nA zero = azero
nA (suc n) = asuc (nA n)

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

W₂ : ℕ → A
W₂ n = nA (dbl n)

w₂ : A
w₂ = alim W₂

nz-z : ∀ {u} {t : 𝓡 u} → Nz t → (d : G t) → azero ≈ᴬ rd (force d) → ⊥
nz-z n (gs d) ()
nz-z n (gl _ _) ()
nz-z n (gw d) e = nz-z n d e
nz-z n (gc _ _ _ _ _ _ _ _ _) ()

ns-s : ∀ {u} {t : 𝓡 u} → Ns t → (d : G t) → asuc azero ≈ᴬ rd (force d) → ⊥
ns-s n g0 ()
ns-s n (gl _ _) ()
ns-s n (gw d) e = ns-s n d e
ns-s n (gc _ _ _ _ _ _ _ _ _) ()

n2-2 : ∀ {u} {t : 𝓡 u} → N2 t → (d : G t) → nA 2 ≈ᴬ rd (force d) → ⊥
n2-2 n g0 ()
n2-2 n (gs d) (s≈ e) = ns-s n d e
n2-2 n (gl _ _) ()
n2-2 n (gw d) e = n2-2 n d e
n2-2 n (gc _ _ _ _ _ _ _ _ _) ()

J : ∀ {u} {t : 𝓡 u} → P t → (d : G t) → Fp w₂ (force d) → ⊥
J p (gw d) f = J p d f
J p g0 (fq ())
J p (gs d) (fq ())
J p (gs d) (fs f) = J p d f
J (a , _) (gl Gs _) (fq (l≈ h)) with a
... | inj₁ nz = nz-z nz (Gs 0) (h 0)
... | inj₂ n2 = n2-2 n2 (Gs 1) (h 1)
J (_ , u) (gl Gs _) (fl n f) = J (u n) (Gs n) f
J (nz , _) (gc G₀ _ _ _ _ _ _ _ _) (fq (l≈ h)) = nz-z nz G₀ (h 0)
J (_ , px , _) (gc G₀ _ _ _ _ _ _ _ _) (fl zero f) = J px G₀ f
J (_ , _ , ph) (gc _ _ gv up Gh _ _ _ _) (fl (suc n) f) = J (ph (up n) (gv n)) (Gh n) f
```

## §4 否定

```agda
lg-nA : ∀ n → C.Lg (nA n)
lg-nA zero = tt
lg-nA (suc n) = lg-nA n

w-steps : ∀ n → W₂ n ⊲ W₂ (suc n)
w-steps n = C.suc (C.suc C.self)

g-a : Gw (asuc w₂)
g-a = gw (w-steps , (λ n → lg-nA (dbl n))) (C.suc (C.lim 1 (C.suc C.self)))

g-w : Gw w₂
g-w = gw (w-steps , (λ n → lg-nA (dbl n))) (C.lim 1 (C.suc C.self))

no-oc : (x : 𝓡 w₂) (h : ∀ {v} → w₂ ⊲ v → Gw v → 𝓡 v) → P (oc x h) → WF (oc x h) → oc x h ≈ oc x h → Hn (oc x h) → ⊥
no-oc x h (_ , px , _) (_ , _ , wx , _) (_ , _ , _ , ex , _) (hx , _ , gd) = J px d (gd d)
  where
  d = C′ x g-w ex wx hx

t₁ : 𝓞 1 w₂ w₂
t₁ = ψ 1 w₂ (Ω̇ 1 azero) g₀ w₂ g-w (pos g-w) C.self (z⊲ w₂)

t₂ : 𝓡 w₂
t₂ = ψ zero azero t₁ g-w w₂ g-w C.self (z⊲ w₂) C.self

P-t₂ : P t₂
P-t₂ = Pψ t₁ g-w w₂ g-w C.self (z⊲ w₂) C.self

E₁ : t₁ ≈ t₁
E₁ = ψQ (Ω̇ 1 azero) (Ω̇ 1 azero) g₀ g₀ w₂ g-w (pos g-w) C.self (z⊲ w₂) w₂ g-w (pos g-w) C.self (z⊲ w₂) (≈ᴬ-refl w₂) (Ω≈ 1 z≈)

W₁ : WF t₁
W₁ = ψW 1 w₂ (Ω̇ 1 azero) g₀ w₂ g-w (pos g-w) C.self (z⊲ w₂) (Ω≈ 1 z≈) (ΩW 1 azero tt)

E₂ : t₂ ≈ t₂
E₂ = ψQ t₁ t₁ g-w g-w w₂ g-w C.self (z⊲ w₂) C.self w₂ g-w C.self (z⊲ w₂) C.self z≈ E₁

W₃ : WF t₂
W₃ = ψW zero azero t₁ g-w w₂ g-w C.self (z⊲ w₂) C.self E₁ W₁

no-Hn-b : Hn t₂ → ⊥
no-Hn-b hn = no-oc _ _ P-t₂ W₃ E₂ hn
```

