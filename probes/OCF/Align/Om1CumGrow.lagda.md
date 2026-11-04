# 累加树在 $\psi_0(\Omega_{\Omega+1})$: 严格增长

> **验收文件 (只读 `OCF.Align.Level`, `NoCumsum`).** 入口 [Om1Cum](Om1Cum.lagda.md). 方法搬自 [WorldTHGrow](WorldTHGrow.lagda.md) 的 `T-strict`. **定理 `T-strict`: 对一切不在 $(0,0)$ 的 $(p,a)$, $\psi_0(\Omega_{\Omega\cdot p+a})\prec\psi_0(\Omega_{\Omega\cdot p+a+1})$.** `TΩ≺TΩ+1`, `step-Ω+1`: `TΩ+1` 严格高于 $\psi_0(\Omega_\Omega)$.
>
> 第 1 项 $\psi_0(\psi_{(p,a)}(\Omega_{(p,a)}))$ 里, $\psi_{(p,a)}(\Omega_{(p,a)})$ 的第一位置是 $\psi_{(p,a)}(1)$, 它是 $\omega$ 个 $\Omega_{(p,a)}$ 的和. 第 2 项 $W+W$ 高于 $W+1$, 而 $\psi_0(W+1)\succ\psi_0(W)$. 这只用 `⊴` (`M₀`, `tR`), 不展开 `mx` 的嵌套, 也不读记号. 证明与高度无关.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1CumGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich using (zero; suc) renaming (_<_ to _<ᴺ_)
open import OCF.Free.Level using (_≺_; ≺z; ≺s; ≺l; ≺i; ≺u; _⊑⁰_; _≅_; ≅-refl⁰; ≅-trans; ≅-sym)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadW using (one; Gw; pos; g₀)
open import OCF.Align.CumUpW
open import OCF.Align.CumUpEq
open import OCF.Align.CumUpPsi
open import OCF.Align.CumUpLe
open import OCF.Align.CumUpMain
```

## §1 第 0 层: 后继把值抬高

```agda
≺L : ∀ {ℓ₀ ℓ₁ ℓ₂} {c′ : FL.Ordᶜ ℓ₀} {c : FL.Ordᶜ ℓ₁} {a : FL.Ordᶜ ℓ₂} → c′ ≅ c → c ≺ a → c′ ≺ a
≺L d (≺z e) = ≺z (≅-trans d e)
≺L d (≺s h) = ≺s (≺L d h)
≺L d (≺l n h) = ≺l n (≺L d h)
≺L d (≺i x ex h) = ≺i x ex (≺L d h)
≺L d (≺u h) = ≺u (≺L d h)

≺+ : ∀ y z → FL.suc FL.zero ⊴₀ z → y ≺ y +₀ z
≺+ y z d = ⊴₀→⊑⁰ (+⊴ y d) (≺z (≅-refl⁰ y))

O₀ : 𝓞 zero azero one
O₀ = o0

one⊴ψ₀ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → FL.suc FL.zero ⊴₀ ψ₀ x gu v gv uv av
one⊴ψ₀ x gu v gv uv av = M₀.mR (z⊴ {p₀ = zero} {a₀ = azero} {u₀ = v} x) gv gu v gv C.self (z⊲ v) (iu refl) v gv uv av

ψ₀-os : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → ψ₀ x gu m gm um am ≺ ψ₀⁰ (os x) gu m gm um am
ψ₀-os x gu m gm um am = ≺l 2 (≺+ (ψ₀ x gu m gm um am) (ψ₀ x gu m gm um am) (one⊴ψ₀ x gu m gm um am))
```

## §2 $1$ 是一切 $\Omega$ 的第一位置

```agda
X₁ : 𝓞 zero azero one
X₁ = Ω̇ zero azero

one⊴Ω : ∀ p a → X₁ ⊴ Ω̇ p a
one⊴Ω p (asuc c) = ni (λ q g → eR {stp = es} (rw (one⊴Ω p c)))
one⊴Ω p (alim f) = l 0 (eR {stp = el 0} (one⊴Ω p (f 0)))
one⊴Ω zero azero = rf (Ω≈ zero z≈)
one⊴Ω (suc p) azero = fc (rL (one⊴Ω p one))
```

## §3 $W+1\trianglelefteq W+W$

```agda
z<s : ∀ q → zero <ᴺ suc q
z<s zero = Trich.zero
z<s (suc q) = Trich.suc (z<s q)

rel : ∀ {p a} → NL p a → Rel zero azero p a
rel (ns {q}) = lw (z<s q)
rel zs = sa (z⊲ _)
rel zl = sa (z⊲ _)

relB : ∀ {p a} (nl : NL p a) v → bw (rel nl) ⊲ v
relB ns v = z⊲ v
relB zs v = z⊲ v
relB zl v = z⊲ v

module Rep {p a m₁} (nl : NL p a) (g₁ : Gw m₁) (Y : 𝓞 p a m₁) (E : Y ≈ Y) (d : X₁ ⊴ Y) where
  x″ : 𝓞 p a m₁
  x″ = add Y g₁ (rel nl) O₀ g₀ m₁ g₁ C.self (pos g₁) (relB nl m₁)

  E″ : Y ≈ x″
  E″ = ≈ow Y _ _ _ (≈ow Y _ _ _ E)

  D⁰ : os x″ ⊴ rep Y g₁ 2
  D⁰ = AddM.mR Y g₁ E d (rel nl) (sa C.self) g₀ g₁ m₁ g₁ C.self (pos g₁) (relB nl m₁) (iu refl) m₁ g₁ C.self C.self (z⊲ m₁)

  stepR : ∀ v (gv : Gw v) (uv : m₁ ⊲ v) (av : a ⊲ v) → Mis v m₁ azero a →
          ψ₀ Y g₁ v gv uv av ≺ ψ₀⁰ (ol (rep Y g₁)) g₁ v gv uv av
  stepR v gv uv av is = ≺l 2 (⊴₀→⊑⁰ (M₀.mR D⁰ g₁ g₁ v gv uv av is v gv uv av)
      (≺L (ψ₀Q Y x″ g₁ g₁ v gv uv av v gv uv av E″) (ψ₀-os x″ g₁ v gv uv av)))
```

## §4 目标进 `ψᵐ`

```agda
unψ : ∀ {p a p₀ a₀ u v} (nl : NL p a) (P : 𝓞 p a v → Set) (x : 𝓞 p₀ a₀ u) (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : a ⊲ v) (av : a₀ ⊲ v) →
      P (ψᵐ p a x gu v gv uv tv av) → P (ψ p a x gu v gv uv tv av)
unψ ns P x gu gv uv tv av r = r
unψ zs P x gu gv uv tv av r = r
unψ zl P x gu gv uv tv av r = r

Y₁ : ∀ {p a} m (gm : Gw m) (um : one ⊲ m) (tm : a ⊲ m) (am : azero ⊲ m) → 𝓞 p a m
Y₁ {p} {a} m gm um tm am = ψ p a O₀ g₀ m gm um tm am

X⊴Y : ∀ {p a m} (nl : NL p a) (gm : Gw m) (um : one ⊲ m) (tm : a ⊲ m) (am : azero ⊲ m) → X₁ ⊴ Y₁ {p} {a} m gm um tm am
X⊴Y {p} {a} nl gm um tm am = unψ nl (X₁ ⊴_) O₀ g₀ gm um tm am (rw (rw (one⊴Ω p a)))

Ω≈Y : ∀ {p a m} (nl : NL p a) (gm : Gw m) (um : one ⊲ m) (tm : a ⊲ m) (am : azero ⊲ m) → Ω̇ p a ≈ Y₁ {p} {a} m gm um tm am
Ω≈Y {p} {a} nl gm um tm am = unψ nl (Ω̇ p a ≈_) O₀ g₀ gm um tm am (≈ow (Ω̇ p a) _ _ _ (≈ow (Ω̇ p a) _ _ _ (Ω≈ p (≈ᴬ-refl a))))
```

## §5 第 1 项

世界全部抽象, 只在最后代入 `mx`.

```agda
T-gen₂ : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : a ⊲ u₀) m (gm : Gw m) (um : one ⊲ m) (am : asuc a ⊲ m) →
         ∀ m₃ (g₃ : Gw m₃) (u₃ : one ⊲ m₃) (t₃ : a ⊲ m₃) (a₃ : azero ⊲ m₃) → Mis m₃ one a azero →
         Tψ p a u₀ g e ≺ ψ₀⁰ (Ω̇ p (asuc a)) g₀ m gm um am
T-gen₂ {p} {a} nl u₀ g e m gm um am m₃ g₃ u₃ t₃ a₃ is₃ =
  ≺l 1 (⊴₀→⊑⁰ (M₀.mR d₂ g₃ gm m₃ g₃ C.self t₃ (iu refl) m gm C.self am)
    (≺L (ψ₀Q (Ω̇ p a) Y g₀ g₃ u₀ g (pos g) e m₃ g₃ C.self t₃ (Ω≈Y nl g₃ u₃ t₃ a₃))
      (Rep.stepR nl g₃ Y (ψQ O₀ O₀ g₀ g₀ m₃ g₃ u₃ t₃ a₃ m₃ g₃ u₃ t₃ a₃ (≈ᴬ-refl a) tt)
        (X⊴Y nl g₃ u₃ t₃ a₃) m₃ g₃ C.self t₃ (iu refl))))
  where
  t : a ⊲ m
  t = ⊲-tr (C.suc C.self) am
  Y = Y₁ {p} {a} m₃ g₃ u₃ t₃ a₃
  Z₀ : 𝓞 p a m
  Z₀ = Ω̇at p a gm
  d₀ : X₁ ⊴ oe {R = C.ss C.self} es Z₀
  d₀ = eR {stp = es} (rw (one⊴Ω p a))
  d₁ : ψ⁰ p a X₁ g₀ m₃ g₃ u₃ t₃ a₃ ⊴ ψ p a (oe {R = C.ss C.self} es Z₀) gm m gm C.self t am
  d₁ = tR nl d₀ g₀ gm m₃ g₃ u₃ t₃ a₃ is₃ m gm C.self t am
  d₂ : ψ⁰ p a X₁ g₀ m₃ g₃ u₃ t₃ a₃ ⊴ oe {R = C.ss C.self} es (ψ p a (oe {R = C.ss C.self} es Z₀) gm m gm C.self t am)
  d₂ = eR {stp = es} d₁

T-gen : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : a ⊲ u₀) m (gm : Gw m) (um : one ⊲ m) (am : asuc a ⊲ m) →
        Tψ p a u₀ g e ≺ ψ₀⁰ (Ω̇ p (asuc a)) g₀ m gm um am
T-gen {p} {a} nl u₀ g e m gm um am =
  T-gen₂ nl u₀ g e m gm um am (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is g₀ gm (pos gm) t (z⊲ m))
  where
  t : a ⊲ m
  t = ⊲-tr (C.suc C.self) am
  M = mx g₀ gm (pos gm) t (z⊲ m)
```

**定理.** 不按阶段定制.

```agda
T-strict : ∀ {p a} (nl : NL p a) u₀ (g : Gw u₀) (e : a ⊲ u₀) u₁ (g′ : Gw u₁) (e′ : asuc a ⊲ u₁) →
           Tψ p a u₀ g e ≺ Tψ p (asuc a) u₁ g′ e′
T-strict nl u₀ g e u₁ g′ e′ = T-gen nl u₀ g e (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M)
  where
  M = mx g₀ g′ (pos g′) (z⊲ u₁) e′
```

## §6 $\psi_0(\Omega_{\Omega+1})$

```agda
open import OCF.Align.Value using (_≼_; s≼s; ≼-trans)
open import OCF.Align.CumVal using (TΩ; TΩ+1; TΩ≈; ≺→s≼ₑ)
open import OCF.Align.CumUpAcceptSim using (fr)
import OCF.Align.NoCumsum as N
import OCF.Align.Level as L

TΩ≺TΩ+1 : TΩ ≺ TΩ+1
TΩ≺TΩ+1 = T-strict ns one g₀ (z⊲ one) one g₀ C.self

step-Ω+1 : L.suc N.BTBOᴵ ≼ fr TΩ+1
step-Ω+1 = ≼-trans (s≼s (proj₂ TΩ≈)) (≺→s≼ₑ TΩ≺TΩ+1)

-- 一切 Ω+a 上的阶梯: Ω+a 与 Ω+a+1 之间严格
ladder : ∀ a u₀ (g : Gw u₀) (e : a ⊲ u₀) u₁ (g′ : Gw u₁) (e′ : asuc a ⊲ u₁) → fr (FL.suc (Tψ 1 a u₀ g e)) ≼ fr (Tψ 1 (asuc a) u₁ g′ e′)
ladder a u₀ g e u₁ g′ e′ = ≺→s≼ₑ (T-strict ns u₀ g e u₁ g′ e′)
```
