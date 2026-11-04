# 序数高度的世界: 折叠

> 不含记号, 不含累加. 结论写在 [CumHt](CumHt.lagda.md). 与 [CumUpW](CumUpW.lagda.md) 同形, 差别:
>
> - **目标 $(q,t)$ 与项的层 $(p,a)$ 的四位都进 `mx`**: 输出的世界是 $\max(u,q_p,t,p_p,a)$, 只看项与目标.
> - **高度的比较 `cmpH` 在这个世界之下.** 被比较的两个高度的 $p$ 位都是世界的第一位置, 字面公共上界就是世界. 没有全局三歧 (`no-tri-code` 否定的那个), 也用不着.
> - 模块参数 `𝓝 : Nx` 只用在第 0 层闭包 (`ψ₀⁰` 的 `oc` 行). 没有别处读它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumHtBase using (Nx)
module OCF.Align.CumHtW (𝓝 : Nx) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
open Nx 𝓝
```

## §1 第 0 层闭包的链

```agda
gnext : ∀ {u} (y : Ord₀) → Gw u → Gw (nxt u y)
gnext {u} y g = gw (nxt-L u y (lgw g)) (⊲-tr (pos g) (nxt-⊲ u y))

record Ix (b : A) : Set where
  constructor ix
  field
    η  : A
    gη : Gw η
    up : b ⊲ η

step : ∀ {b} → Ix b → Ord₀ → Ix b
step (ix η g u) y = ix (nxt η y) (gnext y g) (⊲-tr u (nxt-⊲ η y))

ixs : ∀ {m} → Gw m → Ord₀ → (Ix m → Ord₀) → ℕ → Ix m
ixs {m} gm y₀ val zero = step (ix m gm C.self) y₀
ixs gm y₀ val (suc n) = step (ixs gm y₀ val n) (val (ixs gm y₀ val n))

yss : ∀ {m} → Gw m → Ord₀ → (Ix m → Ord₀) → ℕ → Ord₀
yss gm y₀ val zero = y₀
yss gm y₀ val (suc n) = val (ixs gm y₀ val n)

-- 第 0 层: 直接算到序数
infixl 6 _+₀_
_+₀_ : Ord₀ → Ord₀ → Ord₀
a +₀ FL.zero = a
a +₀ FL.suc b = FL.suc (a +₀ b)
a +₀ FL.lim f = FL.lim (λ n → a +₀ f n)
a +₀ FL.limᵢ () f
a +₀ FL.up () x

rep₀ : Ord₀ → ℕ → Ord₀
rep₀ y zero = FL.zero
rep₀ y (suc zero) = y
rep₀ y (suc (suc m)) = rep₀ y (suc m) +₀ y
```

## §2 折叠

`dR`, `dE`: 低高度节点, 嵌入的两位在世界之下. 自由的一位来自节点的证据, 其余来自项的 $p$ 位.

```agda
dR : ∀ {p h k u m} (j : h <ᴴ p) → Rd (fd j) k u → u ⊲ m → pp p ⊲ m → D⊲ (pp h) k m
dR j r um pm = pp⊲ j pm (⊲-tr (r₁ r) um) ,ᵈ ⊲-tr (≪⊲ (r₂ r)) um

dE : ∀ {p h k u m} (j : h <ᴴ p) → D⊲ (fd j) k u → u ⊲ m → pp p ⊲ m → D⊲ (pp h) k m
dE j e um pm = pp⊲ j pm (⊲-tr (d₁ e) um) ,ᵈ ⊲-tr (d₂ e) um

ψ  : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → D⊲ (pp q) t v → D⊲ (pp p) a v → 𝓞 q t v
ψᵐ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → D⊲ (pp q) t v → D⊲ (pp p) a v → 𝓞 q t v
ψ⁰ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → D⊲ (pp q) t m → D⊲ (pp p) a m → 𝓞 q t m
ψL : ∀ {p h k u} q t (j : h <ᴴ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → D⊲ (pp q) t m → D⊲ (pp h) k m → 𝓞 q t m
ψ₀  : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → D⊲ (pp p) a v → Ord₀
ψ₀⁰ : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → D⊲ (pp p) a m → Ord₀
ψ₀L : ∀ {p h k u} (j : h <ᴴ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → D⊲ (pp h) k m → Ord₀

ψ ⟨ suc s , y ⟩ t x gu v gv uv tv av = ψᵐ ⟨ suc s , y ⟩ t x gu v gv uv tv av
ψ ⟨ zero , asuc b ⟩ t x gu v gv uv tv av = ψᵐ ⟨ zero , asuc b ⟩ t x gu v gv uv tv av
ψ ⟨ zero , alim f ⟩ t x gu v gv uv tv av = ψᵐ ⟨ zero , alim f ⟩ t x gu v gv uv tv av
ψ ⟨ zero , azero ⟩ azero x gu v gv uv tv av = ow (pos gv) g₀ (em (ψ₀ x gu v gv uv av))
ψ ⟨ zero , azero ⟩ (asuc t) x gu v gv uv tv av = ψᵐ H₀ (asuc t) x gu v gv uv tv av
ψ ⟨ zero , azero ⟩ (alim f) x gu v gv uv tv av = ψᵐ H₀ (alim f) x gu v gv uv tv av

ψᵐ q t x gu v gv uv tv av with mx gu gv uv tv av
... | mx′ m gm um tm am mv _ = ow mv gm (ψ⁰ q t x gu m gm um tm am)

ψ⁰ q t o0 gu m gm um tm am = Ω̇at q t gm
ψ⁰ q t (os x) gu m gm um tm am = ol (rep (ψ q t x gu m gm um tm am) gm)
ψ⁰ q t (ol F) gu m gm um tm am = ol (λ n → ψ q t (F n) gu m gm um tm am)
ψ⁰ {p} {a} q t (oi {k = k} r h) gu m gm um tm am with cmpH p q (d₁ am) (d₁ tm) (lgw gm)
... | injᵃ i = od i k (rd (fd⊲ i (d₁ am)) (≪∘ r (d₂ am))) (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outL i y))) g _ g C.self (D-tr tm w) (D-tr am w))
... | injᵇ _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n))) gm m gm C.self tm am)
... | injᶜ refl with cmpN (≪∘ r (d₂ am)) (d₂ tm) (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outS (≪S s) y))) g _ g C.self (D-tr tm w) (D-tr am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n))) gm m gm C.self tm am)
ψ⁰ {p} {a} q t (od {h = h₀} j k r h) gu m gm um tm am with cmpH h₀ q (d₁ (dR j r um (d₁ am))) (d₁ tm) (lgw gm)
... | injᵃ i = od i k (rd (fd⊲ i (d₁ (dR j r um (d₁ am)))) (≪∘ (r₂ r) um)) (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outL i y))) g _ g C.self (D-tr tm w) (D-tr am w))
... | injᵇ _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n))) gm m gm C.self tm am)
... | injᶜ refl with cmpN (≪∘ (r₂ r) um) (d₂ tm) (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outS (≪S s) y))) g _ g C.self (D-tr tm w) (D-tr am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n))) gm m gm C.self tm am)
ψ⁰ q t (oc x h) gu m gm um tm am =
  oc (ψ q t x gu m gm um tm am) (λ {v} w g → ψ q t (h (⊲-tr um w) g) g v g C.self (D-tr tm w) (D-tr am w))
ψ⁰ q t (oe es x) gu m gm um tm am = ψ q t x gu m gm um tm (Dr (C.suc C.self) am)
ψ⁰ q t (oe (el n) x) gu m gm um tm am = ψ q t x gu m gm um tm (Dr (C.lim n C.self) am)
ψ⁰ q t (oL j k e x) gu m gm um tm am = ψL q t j x gu m gm um tm (dE j e um (d₁ am))
ψ⁰ q t (ow p g′ x) gu m gm um tm am = ψ q t x g′ m gm (⊲-tr p um) tm am

ψL q t hs0 (bx x) gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (hl0 n) (bx x) gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t hr0 (bx x) gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (hsS j) x gu m gm um tm km = ψL q t j x gu m gm um tm km
ψL q t (hlS n j) x gu m gm um tm km = ψL q t j x gu m gm um tm km
ψL q t (hrS j) x gu m gm um tm km = ψL q t j x gu m gm um tm km

ψ₀ x gu v gv uv av with mx gu gv uv (Dz v) av
... | mx′ m gm um tm am mv _ = ψ₀⁰ x gu m gm um am

ψ₀⁰ o0 gu m gm um am = FL.suc FL.zero
ψ₀⁰ (os x) gu m gm um am = FL.lim (rep₀ (ψ₀ x gu m gm um am))
ψ₀⁰ (ol F) gu m gm um am = FL.lim (λ n → ψ₀ (F n) gu m gm um am)
ψ₀⁰ {p} {a} (oi {k = k} r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am) n))) gm m gm C.self am)
ψ₀⁰ {a = a} (od {h = h₀} j k r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am) n))) gm m gm C.self am)
ψ₀⁰ (oc x h) gu m gm um am =
  FL.lim (yss gm (ψ₀ x gu m gm um am) (λ i → ψ₀ (h (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (D-tr am (Ix.up i))))
ψ₀⁰ (oe es x) gu m gm um am = ψ₀ x gu m gm um (Dr (C.suc C.self) am)
ψ₀⁰ (oe (el n) x) gu m gm um am = ψ₀ x gu m gm um (Dr (C.lim n C.self) am)
ψ₀⁰ (oL j k e x) gu m gm um am = ψ₀L j x gu m gm um (dE j e um (d₁ am))
ψ₀⁰ (ow p g′ x) gu m gm um am = ψ₀ x g′ m gm (⊲-tr p um) am

ψ₀L hs0 (bx x) gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (hl0 n) (bx x) gu m gm um km = ψ₀ x gu m gm um km
ψ₀L hr0 (bx x) gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (hsS j) x gu m gm um km = ψ₀L j x gu m gm um km
ψ₀L (hlS n j) x gu m gm um km = ψ₀L j x gu m gm um km
ψ₀L (hrS j) x gu m gm um km = ψ₀L j x gu m gm um km
```

## §3 闭项

读法 (判断) $\psi_0(\Omega_{\Omega^2\cdot r+\Omega\cdot p+a})$. 世界 $u_0$ 要在 $p$, $a$ 之上.

```agda
Tψ : ∀ H a u₀ → Gw u₀ → D⊲ (pp H) a u₀ → Ord₀
Tψ H a u₀ g e = ψ₀ (Ω̇ H a) g₀ u₀ g (pos g) e
```
