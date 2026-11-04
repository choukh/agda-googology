# $\psi_0(\Omega_\Omega)$: 无证书前提的计值, 无条件的序数

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). `clo`: 第 0 层的闭包直接计值成 $\omega$-极限, 链点由累加读回给出, **没有 `Good` 这一步: 定义是全函数.** `HS-clo`: 只要分支对字面第一位置单调, 输出就是 `HS`. 与 [NoKCertEval](NoKCertEval.lagda.md) 的 `gŝ` 相比, `dy`, `hy`, `lE` 都消失了: 下标的字面证据由构造给出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (HS; hz; hs; hl; _⊑⁰_; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲; Lg-next; cumA; _⊞_)
open import OCF.Align.CumReadCFThm using (Y; HS-Y; Y-mono)
```

## §1 闭包的计值

```agda
module Clo (c : A) (wc : Lg c) (t₀ : Ord₀) (g : (η : A) → Lg η → c ⊲ η → Ord₀) where
  record Ix : Set where
    constructor ix
    field
      η  : A
      lg : Lg η
      up : c ⊲ η
  open Ix public

  step : Ix → Ord₀ → Ix
  step (ix η w u) y = ix (next η y) (Lg-next η y w) (⊲-tr u (next-⊲ η y))

  val : Ix → Ord₀
  val (ix η w u) = g η w u

  chain : ℕ → Ix
  chain zero = step (ix c wc self) t₀
  chain (suc n) = step (chain n) (val (chain n))

  ys : ℕ → Ord₀
  ys zero = t₀
  ys (suc n) = val (chain n)

  out : Ord₀
  out = FL.lim ys

  chain-⊲ : ∀ n → η (chain n) ⊲ η (chain (suc n))
  chain-⊲ n = next-⊲ (η (chain n)) (val (chain n))

  HS-clo : HS t₀ → (∀ i → HS (val i)) → (∀ i → t₀ ⊑⁰ val i) →
           (∀ i j → η i ⊲ η j → val i ⊑⁰ val j) → HS out
  HS-clo h₀ h m₀ m = hl hy st
    where
    hy : ∀ n → HS (ys n)
    hy zero = h₀
    hy (suc n) = h (chain n)
    st : ∀ n → ys n ⊑⁰ ys (suc n)
    st zero = m₀ (chain 0)
    st (suc n) = m (chain n) (chain (suc n)) (chain-⊲ n)
```

## §2 $\psi_0(\Omega_\Omega)$

下界 $c=1$, 第一支 $\psi_0(\Omega_1)$, 分支 $\psi_0(\Omega_\eta)$.

```agda
one : A
one = asuc azero

open Clo one tt (Y one tt) (λ η w _ → Y η w) renaming (out to Tᶜ; HS-clo to HS-Tᶜ′; ys to ysᶜ; chain to chainᶜ) public

HS-Tᶜ : HS Tᶜ
HS-Tᶜ = HS-Tᶜ′ (HS-Y one tt) (λ i → HS-Y (η i) (lg i)) (λ i → Y-mono tt (lg i) (up i)) (λ i j p → Y-mono (lg i) (lg j) p)

fghᶜ : ℕ → ℕ
fghᶜ = FGH Tᶜ
```

**$\psi_0$ 的小值.** `Y azero` 是 $\omega$, `Y one` 是 $\varepsilon_0$ (判断, 没有比较器). 第 $n$ 项的 `FGH` 是有限测试. 下面全部 `refl`.

```agda
_ : FGH (Y azero tt) 0 ≡ 1
_ = refl

_ : FGH (Y azero tt) 2 ≡ 8
_ = refl

_ : fghᶜ 0 ≡ 1
_ = refl
```
