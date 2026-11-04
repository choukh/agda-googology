# 序数高度的世界: $\Omega^2$, $\Omega^2+1$ 的展开

> 不含记号, 不含累加 (`Nx` 是模块参数). 结论写在 [CumHt](CumHt.lagda.md). 这一篇是定理, 不是读法: 只说树长什么样.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumHtBase using (Nx)
module OCF.Align.CumHtShape (𝓝 : Nx) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (_≅_)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
open import OCF.Align.CumHtEq
open import OCF.Align.CumHtW 𝓝
open import OCF.Align.CumHtPsi 𝓝 using (ψ₀Q; ψ₀l)
open Nx 𝓝

H² : ℕ → Ht
H² r = ⟨ suc r , azero ⟩

T² : ℕ → Ord₀
T² r = Tψ (H² r) azero one g₀ (Dz one)

T²⁺¹ : Ord₀
T²⁺¹ = Tψ (H² 0) one one g₀ (z⊲ one ,ᵈ C.self)
```

## §1 $\Omega^2$

`T² r` 模 $\cong$ 是 `yss` 这个极限 (`T²-≅`). 它的第 $n+1$ 项, 模 $\cong$, 就是高度 $\eta_n$ 的第 $r$ 行第 0 位 (`T²-term`), $\eta_n$ 是 `Nx` 走出来的字面递增链 (`η²-step`). 这是 [CrossM](CrossM.lagda.md) `T⊤` 的形状, 这里由闭包节点 `oc` 走出来, 没有另写节点.

这里写 `≅` 不写 `≡`, 对 $r$ 和世界抽象: 闭的 `refl` 让转换检查展开整棵树, 5 分钟没有结果 (计时观察, 不是否定).

```agda
-- 链本身, 对输出抽象
module Chain {m} (gm : Gw m) (y₀ : Ord₀) (val : Ix m → Ord₀) where
  ηc : ℕ → A
  ηc n = Ix.η (ixs gm y₀ val n)

  ηc-eq : ∀ n → ηc (suc n) ≡ nxt (ηc n) (yss gm y₀ val (suc n))
  ηc-eq n = refl

  ηc-step : ∀ n → ηc n ⊲ ηc (suc n)
  ηc-step n = nxt-⊲ (ηc n) (yss gm y₀ val (suc n))

  yss-term : (F : Ix m → Ord₀) → (∀ i → val i ≅ F i) → ∀ n → yss gm y₀ val (suc n) ≅ F (ixs gm y₀ val n)
  yss-term F h n = h (ixs gm y₀ val n)

module Ω² (r : ℕ) {m} (gm : Gw m) (am : D⊲ azero azero m) where
  y₀² : Ord₀
  y₀² = ψ₀ {p = H² r} {a = azero} (oL hr0 azero (C.self ,ᵈ z⊲ one) (bx (Ω̇′ r one azero))) g₀ m gm (pos gm) am

  val² : Ix m → Ord₀
  val² i = ψ₀ {p = H² r} {a = azero} (oL (hr0 {p′ = Ix.η i}) azero (C.self ,ᵈ z⊲ (Ix.η i)) (bx (ow (pos (Ix.gη i)) g₀ (Ω̇′ r (Ix.η i) azero)))) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (D-tr am (Ix.up i))

  T²⁰ : ψ₀⁰ (Ω̇ (H² r) azero) g₀ m gm (pos gm) am ≡ FL.lim (yss gm y₀² val²)
  T²⁰ = refl

  η² : ℕ → A
  η² n = Ix.η (ixs gm y₀² val² n)

  gη² : ∀ n → Gw (η² n)
  gη² n = Ix.gη (ixs gm y₀² val² n)

  eη² : ∀ n → D⊲ (η² n) azero (η² n)
  eη² n = C.self ,ᵈ z⊲ (η² n)

  -- 每一支就是 ⟨ r , η ⟩ 的第 0 位
  row² : Ix m → Ord₀
  row² i = Tψ ⟨ r , Ix.η i ⟩ azero (Ix.η i) (Ix.gη i) (C.self ,ᵈ z⊲ (Ix.η i))

  val²-≅ : ∀ i → val² i ≅ row² i
  val²-≅ i = ψ₀Q {p = H² r} {a = azero} (oL (hr0 {p′ = Ix.η i}) azero (C.self ,ᵈ z⊲ (Ix.η i)) (bx (ow (pos (Ix.gη i)) g₀ (Ω̇′ r (Ix.η i) azero)))) (Ω̇ ⟨ r , Ix.η i ⟩ azero) (Ix.gη i) g₀ (Ix.η i) (Ix.gη i) C.self (D-tr am (Ix.up i)) (Ix.η i) (Ix.gη i) (pos (Ix.gη i)) (C.self ,ᵈ z⊲ (Ix.η i)) (Ω≈′ r (≈ᴬ-refl (Ix.η i)) z≈)

  -- 第 n+1 项就是 ⟨ r , η_n ⟩ 的第 0 位
  T²-term : ∀ n → yss gm y₀² val² (suc n) ≅ row² (ixs gm y₀² val² n)
  T²-term = Chain.yss-term gm y₀² val² row² val²-≅

  -- 高度的链字面递增, 下一个是 nxt
  η²-step : ∀ n → η² n ⊲ η² (suc n)
  η²-step = Chain.ηc-step gm y₀² val²

  η²-eq : ∀ n → η² (suc n) ≡ nxt (η² n) (yss gm y₀² val² (suc n))
  η²-eq = Chain.ηc-eq gm y₀² val²

-- 回到闭项: 世界 1
T²-≅ : ∀ r → T² r ≅ ψ₀⁰ (Ω̇ (H² r) azero) g₀ one g₀ (pos g₀) (Dz one)
T²-≅ r = ψ₀l (Ω̇ (H² r) azero) (Ω̇ (H² r) azero) g₀ g₀ one g₀ (pos g₀) (Dz one) one g₀ (pos g₀) (Dz one) (iu refl) (Ω≈ (≈ᴴ-refl (H² r)) z≈)
```

## §2 $\Omega^2+1$

第 $n$ 项的被折叠者是 $z_n$, $z_0=\Omega_{\Omega^2}$, $z_{n+1}=\psi_{\Omega^2}(z_n)$, 目标是 $(1,0,0)$ 这一层: 被折叠的是 $\Omega^2$ 这一层的整个元素, 里面的闭包节点 `oc` 被 `ψ` 字面保留 (`CumHtW.ψ⁰` 的 `oc` 行).

```agda
module Ω²⁺¹ (r : ℕ) {m} (gm : Gw m) (am : D⊲ azero one m) where
  f²⁺¹ : 𝓞 (H² r) azero m → 𝓞 (H² r) azero m
  f²⁺¹ z = ψ (H² r) azero (oe es z) gm m gm C.self (Dr (C.suc C.self) am) am

  z²⁺¹ : ℕ → 𝓞 (H² r) azero m
  z²⁺¹ = chainᵒ gm f²⁺¹

  T²⁺¹⁰ : ψ₀⁰ (Ω̇ (H² r) one) g₀ m gm (pos gm) am ≡ FL.lim (λ n → ψ₀ {p = H² r} {a = one} (oe es (z²⁺¹ n)) gm m gm C.self am)
  T²⁺¹⁰ = refl

T²⁺¹-≅ : T²⁺¹ ≅ ψ₀⁰ (Ω̇ (H² 0) one) g₀ one g₀ (pos g₀) (z⊲ one ,ᵈ C.self)
T²⁺¹-≅ = ψ₀l (Ω̇ (H² 0) one) (Ω̇ (H² 0) one) g₀ g₀ one g₀ (pos g₀) (z⊲ one ,ᵈ C.self) one g₀ (pos g₀) (z⊲ one ,ᵈ C.self) (iu refl) (Ω≈ (≈ᴴ-refl (H² 0)) (≈ᴬ-refl one))
```
