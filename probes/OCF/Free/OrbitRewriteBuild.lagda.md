# 沿原实际轨道运输程序与合法证书

闭包节点始终使用原 ys/hy/dy；分支只在同一层号及同一界证据处改写。
结论返回特定的新证书，不要求程序在异层号上的函数相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.OrbitRewriteBuild where

open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force
open import OCF.Free.OrbitRewriteIf

move : ∀ {x y} → Pointwise x y → (G : Goodᴺ x) →
  Σ (Goodᴺ y) (λ H → forceᴺ x G ≅ forceᴺ y H)
move pz gz = gz , z≅
move (ps p) (gs G) with move p G
... | H , e = gs H , s≅ e
move (pl p) (gl G st) = gl H st′ , l≅ e
  where
  H = λ n → proj₁ (move (p n) (G n))
  e = λ n → proj₂ (move (p n) (G n))
  st′ : ∀ n → forceᴺ _ (H n) ⊑⁰ forceᴺ _ (H (suc n))
  st′ = λ n → ⊑-trans (≅→⊑ (≅-sym (e n)))
    (⊑-trans (st n) (≅→⊑ (e (suc n))))
move (pc pt pg po pO) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  gc ys hy dy H₀ l₀′ Hg lE′ Ho₀ Ho mo₀′ mo′ , l≅ output-shape
  where
  H₀ = proj₁ (move pt G₀)
  e₀ = proj₂ (move pt G₀)
  l₀′ = ≅-trans (≅-sym e₀) l₀
  Hg = λ k → proj₁ (move (pg (toLevel (ys k) (hy k)) (dy k)) (Gg k))
  eg = λ k → proj₂ (move (pg (toLevel (ys k) (hy k)) (dy k)) (Gg k))
  lE′ = λ k → ≅-trans (≅-sym (eg k)) (lE k)
  Ho₀ = proj₁ (move po Go₀)
  eo₀ = proj₂ (move po Go₀)
  Ho = λ k → proj₁ (move (pO (toLevel (ys k) (hy k)) (dy k)) (Go k))
  eo = λ k → proj₂ (move (pO (toLevel (ys k) (hy k)) (dy k)) (Go k))
  mo₀′ : forceᴺ _ Ho₀ ⊑⁰ forceᴺ _ (Ho zero)
  mo₀′ = ⊑-trans (≅→⊑ (≅-sym eo₀)) (⊑-trans mo₀ (≅→⊑ (eo zero)))
  mo′ : ∀ k → forceᴺ _ (Ho k) ⊑⁰ forceᴺ _ (Ho (suc k))
  mo′ = λ k → ⊑-trans (≅→⊑ (≅-sym (eo k)))
    (⊑-trans (mo k) (≅→⊑ (eo (suc k))))
  output-shape : ∀ n → outsᴺ (forceᴺ _ Go₀) (λ k → forceᴺ _ (Go k)) n ≅
    outsᴺ (forceᴺ _ Ho₀) (λ k → forceᴺ _ (Ho k)) n
  output-shape zero = eo₀
  output-shape (suc k) = eo k

instance-transport : OrbitTransport
instance-transport = record { move = move }
```

gl 的相邻步进及 gc 的输出步进都经同形关系双向运输，未删去这些条件。
此模块仅实现共享改写合同；实际融合解释器须另提供 Pointwise 证明，
本定理本身不构造新的高值闭项，也不使用已经求出的 V 充当输出。
