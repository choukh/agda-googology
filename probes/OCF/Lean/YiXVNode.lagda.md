# YiXV：结点回灌的部分和上界
> 验收文件。编译定理：带一格余量的分支上界，给出从零回灌的结点折叠上界；不提供全塔的分支上界。
> 参照增长估计复用 `YiOverMain.Node`，源部分和用 `YiCeilRead.plus≼`；`Sample` 实填接口前提。
> 源域与归纳证明在 `YiXVSim`，实际前缀底的实例在 `YiXVLocal`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVNode where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiCeilRead using (plus≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; 1≼ψ⁰; s≼s) renaming (+-mono to +ᵛ)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiOverMain as M
import OCF.Lean.YiLeanCore as Old

module Node (f : R.T₀ → R.T₁) (sc : O.SC f) (gm gk : Tr zero → Tr zero)
  (Hm : (a : Tr zero) (y : T₀) → R.𝟙 ≼ y → L.suc (read a) ≼ y → read (gm a) ≼ L.ψ⁰ (f y))
  (Hk : (a : Tr zero) (y : T₀) → R.𝟙 ≼ y → L.suc (read a) ≼ y → read (gk a) ≼ L.ψ⁰ (f y)) where

  module Ref = M.Node f sc (λ _ → Old.G.top) (λ _ → Old.G.top)
    (λ a y o q → 1≼ψ⁰ (f y)) (λ a y o q → 1≼ψ⁰ (f y))
  open Ref using (d; idx; le; incr; dbl)

  c : ℕ → Tr zero
  c = iter gk zero

  F : ℕ → Tr zero
  F n = gm (c n)

  bounds : (n : ℕ) → L.suc (read (c n)) ≼ d (idx n)
  bounds zero = R.one f 1
  bounds (suc n) = ≼-trans
    (s≼s (≼-trans (Hk (c n) (d (idx n)) (R.one f (idx n)) (bounds n)) (R.≼ψ₀ (f (d (idx n))))))
    (incr (suc (idx n)))

  rows : (n : ℕ) → read (F n) ≼ d (suc (idx n))
  rows n = ≼-trans (Hm (c n) (d (idx n)) (R.one f (idx n)) (bounds n)) (R.≼ψ₀ (f (d (idx n))))

  sums : (n : ℕ) → read (cum F n) ≼ d (suc (suc (idx n)))
  sums zero = ≼-trans (rows zero) (le 2)
  sums (suc n) = ≼-trans
    (plus≼ (cum F n) (F (suc n)) (≼-trans (sums n) (le (suc (suc (idx n))))) (rows (suc n)))
    (dbl (suc (suc (idx n))) (incr (suc (suc (idx n)))))

  result : (nz : (n : ℕ) → zero ⊢ zero ◃ F n) → read (limc F nz) ≼ L.ψ⁰ (L.limᵢ L.zero f)
  result nz = l≼ (λ n → ≼l (suc (idx n))
    (≼-trans (sums n) (R.ψ₀≼ (f (d (suc (idx n)))))))

module Sample = Node (L.up L.zero) O.SC-up (λ _ → suc zero) (λ _ → suc zero)
  (λ a y o q → 1≼ψ⁰ (L.up L.zero y)) (λ a y o q → 1≼ψ⁰ (L.up L.zero y))

sample : read (limc Sample.F (λ _ → ◃s)) ≼ L.ψ⁰ (L.Ω (L.suc L.zero))
sample = Sample.result (λ _ → ◃s)
```
