# 键即节点: `noW` 走到的闭包 (有限测试)

> 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 跑得慢, 所以单独成文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyReach where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; natᴵ; zero; suc; lim)
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ)
open import OCF.Align.LvKeyBase
open import OCF.Align.LvKeyTree renaming (T to Tv)
```

## 有限测试: [LvCert](LvCert.lagda.md) 走到的那个闭包, 在这棵树上

$\Omega_{\Omega\cdot2}+\Omega_{\Omega+\tau}$ 在顶层 $\Omega\cdot2+1$ 里, $\tau$ 是字面的分支. 沿路径 `0, 1, 0, 0, 2`: 走到节点 $\Omega_{\Omega+1}$, 取第 1 个链点, 经第一支与 `limᵢ` 到 `rep` 的第 2 份, 那是 $W$ 的闭包. 这里只测**路径走得到那个闭包** (`c-W₂`). 它的键就是外层的键, 由 [LvKeyClo](LvKeyClo.lagda.md) 的 `noSameᵏ` 知界 $\ge\tau+1$. 把界的数值算出来 (`toN` 强制 `Bd`) 跑了 10 分钟没有结束, 所以没有留这个测试. $\tau$ 是字面值, 不是真实的链点, 这是有限测试, 不是否定.

```agda
module Reach (n : ℕ) where
  D : LI
  D = Ω· 2

  c₀ : LI
  c₀ = suc D

  cf : Cf c₀
  cf = WFΩ 2 , s≈ (selfΩ 2)

  open Over c₀
  open Fold cf

  P₂ : Cp D c₀
  P₂ = suc Cp.self

  τ : Ordᴵ
  τ = natᴵ (suc (suc n))

  W : O D Fl₀
  W = Ω̇ᵖ D P₂ idF (λ _ → tt)

  bd : Ordᴵ
  bd = suc τ

  kτ : Evt (wd (natᴵ 1) (∅ (suc bd))) (tk P₂ τ)
  kτ = tt , suc bd , refl , (λ q → suc q)

  Φ : Fᵗ
  Φ = (Fl₀ ∪ ((Fl₀ ∪ tk P₂ τ) ∪ tk P₂ τ)) ∪ tz

  Tr : O c₀ Φ
  Tr = ι ds (W ⊕ ι (db τ P₂) (Ω̇ᵖ (base ⊞ τ) {Fl₀ ∪ tk P₂ τ} (suc (bra τ Cp.self)) proj₁ (λ {w} e → S→B {Ε w} (proj₂ (proj₂ e)) , tt)))

  zb : ∀ m → zero <ᴵ natᴵ (suc m)
  zb zero    = zero
  zb (suc m) = suc (zb m)

  X : Ordˢ zero
  X = ψ̄ Tr {w = wd (natᴵ 1) (∅ (suc bd))} (zero , zb (suc (suc (suc n)))) (((tt , (λ q → q)) , (((tt , (λ q → q)) , kτ) , kτ)) , tt) zero

go : List ℕ → Ordˢ zero → Ordˢ zero
go [] x = x
go (n ∷ r) (Ord₊ˢ.lim f) = go r (f n)
go (n ∷ r) (Ord₊ˢ.ŝ c t g) = go r t
go (n ∷ r) x = x

kd : Ordˢ zero → ℕ
kd Ord₊ˢ.zero = 0
kd (Ord₊ˢ.suc _) = 1
kd (Ord₊ˢ.lim _) = 2
kd (Ord₊ˢ.ŝ _ _ _) = 3
kd _ = 4

-- 沿路径: 节点 (lim), 可数层闭包 (ŝ), `oi` 的折叠 (lim), rep (lim), W 的闭包 (ŝ)
c-W₂ : kd (go (0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) (Reach.X 0)) ≡ 3
c-W₂ = refl
```
