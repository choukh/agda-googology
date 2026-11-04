# 高度进世界: 实例与第 1 项的形状

> 不含记号. 入口 [WorldTH](WorldTH.lagda.md). 同一条定理 `HS-T`, `T-strict`, 下面只是代入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (HS; _≺_; _⊑⁰_; _≅_; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀; next)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪S)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; g₀; pos)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHPsi using (NL; nt; ns)
open import OCF.Align.WorldTHMain using (HS-T; T-mono)
open import OCF.Align.WorldTHGrow using (T-strict)
```

## §1 $\psi_0(\Omega_{\Omega^2+a})$

读法是判断. 顶行 `Ω̇ top azero` 的第 $v$ 支是 `Ω̇ (ht v) azero`.

```agda
-- ψ₀(Ω_{Ω²})
T₀ : Ord₀
T₀ = Tψ top azero one g₀ (z⊲ one , refl)

HS-T₀ : HS T₀
HS-T₀ = HS-T top azero one g₀ (z⊲ one , refl)

-- ψ₀(Ω_{Ω²+1}): 第一站
T₁ : Ord₀
T₁ = Tψ top one one g₀ (C.self , refl)

HS-T₁ : HS T₁
HS-T₁ = HS-T top one one g₀ (C.self , refl)

T₀≺T₁ : T₀ ≺ T₁
T₀≺T₁ = T-strict nt one g₀ (z⊲ one , refl) one g₀ (C.self , refl)

-- ψ₀(Ω_{Ω²+a}): 对一切合法且不低于 1 的 a
fgh₁ : ℕ → ℕ
fgh₁ = FGH T₁

T+ : (a : A) → Gw a → Ord₀
T+ a g = Tψ top a a g (C.self , refl)

HS-T+ : ∀ a (g : Gw a) → HS (T+ a g)
HS-T+ a g = HS-T top a a g (C.self , refl)

T+≺ : ∀ a (g : Gw a) (g′ : Gw (asuc a)) → T+ a g ≺ T+ (asuc a) g′
T+≺ a g g′ = T-strict nt a g (C.self , refl) (asuc a) g′ (C.self , refl)

T+⊑ : ∀ {a b} (g : Gw a) (g′ : Gw b) → a ⊲ b → T+ a g ⊑⁰ T+ b g′
T+⊑ g g′ d = T-mono top g g′ (C.self , refl) (C.self , refl) d
```

## §2 第 1 项折叠 $\Omega_{\Omega^2}$ 本身

下面对抽象的世界写, `refl`: 只展开定义. 这是定理 (对一切 $p,a,m$), 说的是基本列的形状, 不是强度. 强度的证据是 `T-strict`. 第 0 项是 $\psi_0(\Omega_{p,a})$, 第 1 项是 $\psi_0(\psi_{p,a}(\Omega_{p,a}))$, 第 2 项再套一层. `oe es` 只是包装.

```agda
at : Ord₀ → ℕ → Ord₀
at (FL.lim f) n = f n
at x n = x

-- 节点的基本列, 对任意分支 h. 把 h 代成 Ω 的 oe es 就是下面的 Ψ
fsI : ∀ {p a u k} (r : k ≪ a) (h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) n →
      at (ψ₀⁰ (oi r h) gu m gm um am) n ≡
      ψ₀ (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n))) gm m gm C.self am
fsI r h gu m gm um am n = refl

-- 闭包的基本列, 对任意第一支 x, 任意分支 h
fsC : ∀ {p a u} (x : 𝓞 p a u) (h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) →
      ψ₀⁰ (oc x h) gu m gm um am ≡ FL.lim (yss gm (ψ₀ x gu m gm um am) (λ i → ψ₀ (h (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (lb↑ am (Ix.up i))))
fsC x h gu m gm um am = refl

module Shape {p a} m (gm : Gw m) (um : one ⊲ m) (am : LB p (asuc a) m) where
  Ψ : 𝓞 p a m → 𝓞 p a m
  Ψ z = ψ p a (oe {R = C.ss C.self} es (inS (≪S C.zero) z)) gm m gm C.self (lb≪ C.zero am) am

  ch : ℕ → 𝓞 p a m
  ch = chainᵒ gm Ψ

  ch₀ : ch 0 ≡ Ω̇at p a gm
  ch₀ = refl

  ch₁ : ch 1 ≡ Ψ (Ω̇at p a gm)
  ch₁ = refl

  ch₂ : ch 2 ≡ Ψ (Ψ (Ω̇at p a gm))
  ch₂ = refl
```

顶行: `fsC` 代入 `Ω̇ top azero`, 第 $n+1$ 项是 `val (ixs … n)`, 由 `top-val` (定理, `WorldTHGrow`) $\cong$ 回灌下标 $v_n$ 上的 $\psi_0(\Omega_{\Omega\cdot v_n})$. **下标是累加的**, 下面两行是定义:

```agda
v₀ : ∀ {m} (gm : Gw m) (y₀ : Ord₀) (val : Ix m → Ord₀) → Ix.η (ixs gm y₀ val 0) ≡ next m y₀
v₀ gm y₀ val = refl

vₛ : ∀ {m} (gm : Gw m) (y₀ : Ord₀) (val : Ix m → Ord₀) n → Ix.η (ixs gm y₀ val (suc n)) ≡ next (Ix.η (ixs gm y₀ val n)) (val (ixs gm y₀ val n))
vₛ gm y₀ val n = refl
```
