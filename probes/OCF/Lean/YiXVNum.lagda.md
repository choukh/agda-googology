# YiXV：节点上界的数值接口
> 验收文件。条件定理：Norm 的五个全量化字段给出从零回灌的节点部分和上界。
> Ref 的增长估计改写自 YiOverMain.Node，源回灌与部分和改写自 YiXVNode；P 与 ν 的关系显式携带。
> 整条 Norm 的闭实例及全称供给在 YiXVAffRef，源侧的实际调用在 YiXVAffine。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVNum where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiCeilRead using (ωx; plus≼)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
import OCF.Lean.YiOverRef as R
open import OCF.Align.Value using (_≼_; s≼s; z≼; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼) renaming (+-mono to +ᵛ)

record Norm (P ν : T₀ → T₀) : Set where
  field
    same : ∀ x → (P x ≼ ν x) × (ν x ≼ P x)
    pos : ∀ x → R.𝟙 ≼ P x
    mo : ∀ x y → R.𝟙 ≼ x → x ≼ y → ν x ≼ ν y
    db : ∀ x → R.𝟙 ≼ x → ωx (ν x) ≼ ν (L.suc x)
    two : L.suc R.𝟙 ≼ P (R.𝟙)

module Ref (P ν : T₀ → T₀) (s : Norm P ν) where
  open Norm s
  d : ℕ → T₀
  d = iterᴸ P (R.𝟙)
  one : ∀ n → R.𝟙 ≼ d n
  one zero = ≼-refl _
  one (suc n) = pos (d n)
  dbl : ∀ n → L.suc (d n) ≼ d (suc n) → (d (suc n) L.+ d (suc n)) ≼ d (suc (suc n))
  dbl n q = ≼-trans (+ᵛ (proj₁ (same (d n))) (proj₁ (same (d n))))
    (≼-trans (≼l 2 (≼-refl _)) (≼-trans (db (d n) (one n))
      (≼-trans (mo (L.suc (d n)) (d (suc n)) (s≼s z≼) q) (proj₂ (same (d (suc n)))))))
  incr : ∀ n → L.suc (d n) ≼ d (suc n)
  incr zero = two
  incr (suc n) = ≼-trans (+ᵛ (≼-refl (d (suc n))) (one (suc n))) (dbl n (incr n))
  le : ∀ n → d n ≼ d (suc n)
  le n = ≼-trans (≼-suc (≼-refl (d n))) (incr n)
  idx : ℕ → ℕ
  idx zero = 1
  idx (suc n) = suc (suc (idx n))

module Node (P ν : T₀ → T₀) (s : Norm P ν) (gm gk : Tr zero → Tr zero)
  (Hm : ∀ a y → R.𝟙 ≼ y → L.suc (read a) ≼ y → read (gm a) ≼ ν y)
  (Hk : ∀ a y → R.𝟙 ≼ y → L.suc (read a) ≼ y → read (gk a) ≼ ν y) where
  open Norm s
  open Ref P ν s
  c : ℕ → Tr zero
  c = iter gk zero
  F : ℕ → Tr zero
  F n = gm (c n)
  bounds : ∀ n → L.suc (read (c n)) ≼ d (idx n)
  bounds zero = one 1
  bounds (suc n) = ≼-trans (s≼s (≼-trans (Hk (c n) (d (idx n)) (one (idx n)) (bounds n))
    (proj₂ (same (d (idx n)))))) (incr (suc (idx n)))
  rows : ∀ n → read (F n) ≼ d (suc (idx n))
  rows n = ≼-trans (Hm (c n) (d (idx n)) (one (idx n)) (bounds n)) (proj₂ (same (d (idx n))))
  sums : ∀ n → read (cum F n) ≼ d (suc (suc (idx n)))
  sums zero = ≼-trans (rows zero) (le 2)
  sums (suc n) = ≼-trans
    (plus≼ (cum F n) (F (suc n)) (≼-trans (sums n) (le (suc (suc (idx n))))) (rows (suc n)))
    (dbl (suc (suc (idx n))) (incr (suc (suc (idx n)))))
  result : ∀ nz → read (limc F nz) ≼ L.lim (λ n → ν (d n))
  result nz = l≼ (λ n → ≼l (suc (idx n)) (≼-trans (sums n) (proj₁ (same (d (suc (idx n)))))))
```
