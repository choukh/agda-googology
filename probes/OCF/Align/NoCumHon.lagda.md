# 不累加的世界: $\psi_0(\Omega_\Omega)$ 的守卫

> 不含记号. `Hn-Ω`: $\psi_0(\Omega_\Omega)$ 这棵数据树的 `Hn` 成立, 无条件. 所以 `TΩᴺ` 是闭项, 不累加, 无前缀, 过 (p, a) 世界.
>
> `Fr`: 高度 0 的项里没有闭包. 目标是高度 0 时折叠保 `Fr` (`Fr-ψ`). 唯一的闭包是最外层那个, 世界是 $1$, 第一支的值至少是 $1$ (`Ωfst`). 这里守卫是平凡的, **这一站不足以说明更高的站.**
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumHon where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
import OCF.Free.Level as FL
open FL using (HS)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; ⊲-tr; z⊲; ≪S; ≪∘; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain
open import OCF.Align.NoCumForce
```

## §1 没有闭包

```agda
Fr  : ∀ {a u} → 𝓞 zero a u → Set
FrS : ∀ {a b} (R : Strict b a) {u} → Vs zero a R u → Set
FrC : ∀ {a b} (P : b ⊲ a) {u} → Vc zero a P u → Set

Fr o0 = ⊤
Fr (os x) = Fr x
Fr (ol F) = ∀ n → Fr (F n)
Fr {a} {u} (oi r h) = ∀ {v} (q : u ⊲ v) (g : Gw v) y → FrS (≪S r) y → Fr (h q g y)
Fr (od () _ _ _)
Fr (oc _ _) = ⊥
Fr (oe es x) = Fr x
Fr (oe (el n) x) = Fr x
Fr (oL () _ _ _)
Fr (ow _ _ x) = Fr x
FrS (ss P) x = FrC P x
FrS (sl n P) x = FrC P x
FrC C.self x = Fr x
FrC (C.suc P) x = FrC P x
FrC (C.lim n P) x = FrC P x

C→F : ∀ {a b u} (P : b ⊲ a) (x : Vc zero a P u) → FrC P x → Fr (outC P x)
C→F C.self x f = f
C→F (C.suc P) x f = C→F P x f
C→F (C.lim n P) x f = C→F P x f

S→F : ∀ {a b u} (R : Strict b a) (x : Vs zero a R u) → FrS R x → Fr (outS R x)
S→F (ss P) x f = C→F P x f
S→F (sl n P) x f = C→F P x f

F→C : ∀ {a b u} (P : b ⊲ a) (x : 𝓞 zero b u) → Fr x → FrC P (inC P x)
F→C C.self x f = f
F→C (C.suc P) x f = F→C P x f
F→C (C.lim n P) x f = F→C P x f

F→S : ∀ {a b u} (R : Strict b a) (x : 𝓞 zero b u) → Fr x → FrS R (inS R x)
F→S (ss P) x f = F→C P x f
F→S (sl n P) x f = F→C P x f
```

```agda
FrI : ∀ {a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs zero a (≪S r) v → 𝓞 zero a v} → Fr (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 zero k v) → Fr z → Fr (h q g (inS (≪S r) z))
FrI {r = r} w q g z fz = w q g _ (F→S (≪S r) z fz)

Fr-Ω : ∀ a → Fr (Ω̇ zero a)
Fr-Ω azero = tt
Fr-Ω (asuc c) = λ q g y fy → fy
Fr-Ω (alim f) = λ n → Fr-Ω (f n)

Fr-add  : ∀ {a b u₀ u′} (W : 𝓞 zero a u₀) (gu : Gw u₀) (R : Rel zero b zero a) (x : 𝓞 zero b u′) (gx : Gw u′) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : u′ ⊲ v) (bv : bw R ⊲ v) → Fr W → Fr x → Fr (add W gu R x gx v gv uv xv bv)
Fr-add⁰ : ∀ {a b u₀ u′} (W : 𝓞 zero a u₀) (gu : Gw u₀) (R : Rel zero b zero a) (x : 𝓞 zero b u′) (gx : Gw u′) m (gm : Gw m) (um : u₀ ⊲ m) (tm : u′ ⊲ m) (am : bw R ⊲ m) → Fr W → Fr x → Fr (add⁰ W gu R x gx m gm um tm am)

Fr-add W gu R x gx v gv uv xv bv fw fx with mx gu gv uv xv bv
... | mx′ m gm um tm am mv = Fr-add⁰ W gu R x gx m gm um tm am fw fx

Fr-add⁰ W gu R o0 gx m gm um tm am fw fx = fw
Fr-add⁰ W gu R (os x) gx m gm um tm am fw fx = Fr-add W gu R x gx m gm um tm am fw fx
Fr-add⁰ W gu R (ol F) gx m gm um tm am fw fx = λ n → Fr-add W gu R (F n) gx m gm um tm am fw (fx n)
Fr-add⁰ W gu (sa P) (oi r h) gx m gm um tm am fw fx =
  λ q g y fy → Fr-add W gu (sa P) (h (⊲-tr tm q) g _) g _ g (⊲-tr um q) C.self (z⊲ _) fw (FrI {r = r} fx (⊲-tr tm q) g _ (S→F (≪S (≪∘ r P)) y fy))
Fr-add⁰ W gu (lw ()) (oi r h) gx m gm um tm am fw fx
Fr-add⁰ W gu R (od () _ _ _) gx m gm um tm am fw fx
Fr-add⁰ W gu R (oc x h) gx m gm um tm am fw ()
Fr-add⁰ W gu (sa P) (oe es x) gx m gm um tm am fw fx = Fr-add W gu (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am fw fx
Fr-add⁰ W gu (lw ()) (oe es x) gx m gm um tm am fw fx
Fr-add⁰ W gu (sa P) (oe (el n) x) gx m gm um tm am fw fx = Fr-add W gu (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am fw fx
Fr-add⁰ W gu (lw ()) (oe (el n) x) gx m gm um tm am fw fx
Fr-add⁰ W gu R (oL () _ _ _) gx m gm um tm am fw fx
Fr-add⁰ W gu R (ow p g′ x) gx m gm um tm am fw fx = Fr-add W gu R x g′ m gm um (⊲-tr p tm) am fw fx

Fr-rep : ∀ {t u} (y : 𝓞 zero t u) (g : Gw u) → Fr y → ∀ n → Fr (rep y g n)
Fr-rep y g fy zero = tt
Fr-rep y g fy (suc zero) = fy
Fr-rep {u = u} y g fy (suc (suc m)) = Fr-add (rep y g (suc m)) g (sa C.self) y g u g C.self C.self (z⊲ u) (Fr-rep y g fy (suc m)) fy

Fr-ψ  : ∀ {a u} t (x : 𝓞 zero a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → Fr x → Fr (ψ zero t x gu v gv uv tv av)
Fr-ψ⁰ : ∀ {a u} t (x : 𝓞 zero a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Fr x → Fr (ψ⁰ zero t x gu m gm um tm am)

Fr-ψ t x gu v gv uv tv av fx with mx gu gv uv tv av
... | mx′ m gm um tm am mv = Fr-ψ⁰ t x gu m gm um tm am fx

Fr-ψ⁰ t o0 gu m gm um tm am fx = Fr-Ω t
Fr-ψ⁰ t (os x) gu m gm um tm am fx = Fr-rep _ gm (Fr-ψ t x gu m gm um tm am fx)
Fr-ψ⁰ t (ol F) gu m gm um tm am fx = λ n → Fr-ψ t (F n) gu m gm um tm am (fx n)
Fr-ψ⁰ t (oi {k = k} r h) gu m gm um tm am fx with cmpN (≪∘ r am) tm (lgw gm)
... | keep s₁ = λ w g y fy → Fr-ψ t (h (⊲-tr um w) g _) g _ g C.self (⊲-tr tm w) (⊲-tr am w) (FrI {r = r} fx (⊲-tr um w) g _ (S→F (≪S s₁) y fy))
... | rise _ = λ n → Fr-ψ t (h um gm _) gm m gm C.self tm am (FrI {r = r} fx um gm _ (chain n))
  where
  chain : ∀ n → Fr (chainᵒ gm (λ z₁ → ψ zero k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n)
  chain zero = Fr-Ω k
  chain (suc n) = Fr-ψ k (h um gm _) gm m gm C.self (⊲-tr (≪⊲ r) am) am (FrI {r = r} fx um gm _ (chain n))
Fr-ψ⁰ t (od () _ _ _) gu m gm um tm am fx
Fr-ψ⁰ t (oc x h) gu m gm um tm am ()
Fr-ψ⁰ t (oe es x) gu m gm um tm am fx = Fr-ψ t x gu m gm um tm (⊲-tr (C.suc C.self) am) fx
Fr-ψ⁰ t (oe (el n) x) gu m gm um tm am fx = Fr-ψ t x gu m gm um tm (⊲-tr (C.lim n C.self) am) fx
Fr-ψ⁰ t (oL () _ _ _) gu m gm um tm am fx
Fr-ψ⁰ t (ow p g′ x) gu m gm um tm am fx = Fr-ψ t x g′ m gm (⊲-tr p um) tm am fx

Fr→Hn : ∀ {u} (x : 𝓡 u) → Fr x → Hn x
Fr→Hn o0 f = tt
Fr→Hn (os x) f = Fr→Hn x f
Fr→Hn (ol F) f = λ n → Fr→Hn (F n) (f n)
Fr→Hn (oi () _) f
Fr→Hn (od () _ _ _) f
Fr→Hn (oc x h) ()
Fr→Hn (oe () _) f
Fr→Hn (oL () _ _ _) f
Fr→Hn (ow p g x) f = Fr→Hn x f
```

## §2 $\psi_0(\Omega_\Omega)$

```agda
fp₁ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : a ⊲ m) (d : G (ψ zero azero x gu m gm um tm am)) → Fp one (force d)
fp₁ x gu m gm um tm am d = ⊴→Fp (fo⊴ (Ωfst zero azero x gu m gm um tm am) (gw (gs g0)) d)

FrL : ∀ {k u} (e : k ⊲ u) (y : 𝓞 zero k u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : azero ⊲ v) (av : azero ⊲ v) → Fr y → Fr (ψ zero azero (oL {p = suc zero} {a = azero} zero k e y) gu v gv uv tv av)
FrL e y gu v gv uv tv av fy with mx gu gv uv tv av
... | mx′ m gm um tm am mv = Fr-ψ azero y gu m gm um tm (⊲-tr e um) fy

Hn-Ω : Hn (Tᴰ 1 azero one g₀ (z⊲ one))
Hn-Ω =
  Fr→Hn _ (FrL C.self (Ω̇ zero one) g₀ one g₀ C.self (z⊲ one) (z⊲ one) (Fr-Ω one)) ,
  (λ {v} q g _ → Fr→Hn _ (FrL C.self (ow (pos g) g₀ (Ω̇ zero v)) g v g C.self (⊲-tr (z⊲ one) q) (⊲-tr (z⊲ one) q) (Fr-Ω v))) ,
  (λ d → fp₁ (oL {p = suc zero} {a = azero} zero one C.self (Ω̇ zero one)) g₀ one g₀ C.self (z⊲ one) (z⊲ one) d)

TΩᴺ : Ord₀
TΩᴺ = Tᴺ 1 azero one g₀ (z⊲ one) Hn-Ω

HS-TΩᴺ : HS TΩᴺ
HS-TΩᴺ = HS-Tᴺ 1 azero one g₀ (z⊲ one) Hn-Ω
```
