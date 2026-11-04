# 第 0 层是值: 闭项

> 不含记号. 结论写在 [NoCumNode](NoCumNode.lagda.md). `G-N`: 对一切 $p,a$, 只要 `Root p a`, $\psi_0(\Omega_{\Omega\cdot p+a})$ 有证书. `G₁`, `T₁`: $\psi_0(\Omega_{\Omega+1})$, 无条件, 闭项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Free.Level using (HS)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (Ord₀; ≈ᴬ-refl)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumMain using (ΩW)
open import OCF.Align.NoCumForce using (Fp)
open import OCF.Align.NoCumNodeE
open import OCF.Align.Om1HnCx using (Fp-z)
open import OCF.Align.NoCumNodeCx
open import OCF.Align.NoCumNodeGd
open import OCF.Align.NoCumNodeOmega using (ΩG)
open import OCF.Align.NoCumNodeX using (X)

seen₀ : Seen idC one
seen₀ z (idr g v gv uv av) d = one-val z d

Root : ℕ → A → Set
Root p a = ∀ {c} → c ≪ a → Sees idC p c

root₀ : ∀ {p} → Root p azero
root₀ ()

root₁ : ∀ {p} → Root p one
root₁ C.zero z gz cu ω r d = Fp-z _ , seen₀ z r d
root₁ (C.suc ())

root₂ : ∀ {p} → Root p (asuc one)
root₂ C.zero z gz cu ω r d = seen₀ z r d , seen₀ z r d
root₂ (C.suc r′) = root₁ r′

G-N : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Root p a → Ev (Ω̇ p a) g₀ u₀ g (pos g) e
G-N p a u₀ g e root =
  X (Ω̇ p a) g₀ u₀ g (pos g) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a (lg⊲ e (lgw g))) (𝓥 p a) (vv (λ {p′} i → seen₀ , tt) root) (ΩG p a)

G₁ : Ev (Ω̇ 1 one) g₀ one g₀ C.self C.self
G₁ = G-N 1 one one g₀ C.self root₁

vᴱ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → Ev x gu v gv uv av → Ord₀
vᴱ x gu v gv uv av d = val x {gu} {Mx.m (Mz gu gv uv av)} {Mx.gm (Mz gu gv uv av)} {Mx.um (Mz gu gv uv av)} {Mx.am (Mz gu gv uv av)} d

HSᴱ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) (d : Ev x gu v gv uv av) → HS (vᴱ x gu v gv uv av d)
HSᴱ x gu v gv uv av d = HS-val x {gu} {Mx.m (Mz gu gv uv av)} {Mx.gm (Mz gu gv uv av)} {Mx.um (Mz gu gv uv av)} {Mx.am (Mz gu gv uv av)} d

T₁ : Ord₀
T₁ = vᴱ (Ω̇ 1 one) g₀ one g₀ C.self C.self G₁

HS-T₁ : HS T₁
HS-T₁ = HSᴱ (Ω̇ 1 one) g₀ one g₀ C.self C.self G₁

Gᵖ₁ : ∀ p → Ev (Ω̇ p one) g₀ one g₀ C.self C.self
Gᵖ₁ p = G-N p one one g₀ C.self root₁

GΩ : Ev (Ω̇ 1 azero) g₀ one g₀ C.self (z⊲ one)
GΩ = G-N 1 azero one g₀ (z⊲ one) root₀
```
