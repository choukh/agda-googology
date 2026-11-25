# 由完整 Ω₂ 查询检验目标与任意有限理论标尺

第四层。对每枝乘 ω 仍严格低于端点的共尾列，指定正槽能达到端点，当且仅当每枝都被一次真实 Ω₂ 查询严格超过。充分方向无条件，抽取见证使用排中律。适用于 ψ₀ψ₃(Ω₂) 和所有有限行 ψ₀(Ωⱼ₊₁)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
open import WVOne using (T₀)
open import OCF.Lean.YiRVLevel using (LEM)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import OCF.Align.EboLeanDef using (hd<; ar<)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; s≼s; l≼; ≼l; +-mono)
import B17ValueDich as Order
import B18Product as M
import B26PSuffix as V
import Survey.EboPTOFinite as B
import Survey.W4FirstBranchRoom as T

record Scale (a : T₀) : Set where
  field
    piece : ℕ → T₀
    cover : a ≼ L.lim piece
    room : ∀ k → L.suc (piece k M.· L.ωᶜ) ≼ a

branch-scale : Scale T.target
branch-scale = record { piece = T.child ; cover = proj₁ (V.limit T.h refl T.child (λ k → V.same refl (T.branch k) (T.branch k))) ; room = T.room }

row-scale : ∀ j → Scale (Rt (B.row-h j))
row-scale j = record { piece = seq ; cover = proj₁ (B.row-sup j) ; room = room }
  where
  seq = λ k → Rt (B.tower-h j k)
  room : ∀ k → L.suc (seq k M.· L.ωᶜ) ≼ Rt (B.row-h j)
  room k = ≼-trans {b = L.suc (seq (suc k))}
    (s≼s (T.copies-bound (B.nf-collapsed j k) (B.nf-collapsed j (suc k)) (B.tower-h j k) (B.tower-h j (suc k)) (B.rise j k)))
    (mono<ⁿ (B.nf-collapsed j (suc k)) (B.nf-row j) (c∷ c[]) (B.tower-h j (suc k)) (B.row-h j)
      (hd< (ar< (B.small (B.tower-indices j (suc k))))))

module Sums (q : ℕ → ℕ → T₀) (first full : T₀) (start : first ≼ q 0 0) where
  total : ℕ → T₀
  total zero = first
  total (suc m) = total m L.+ L.lim (q m)

  module Test (exact : L.lim total ≈ᵛ full)
    (paid : ∀ m n → q m n ≼ full) {a : T₀} (s : Scale a) where
    open Scale s
    hit = λ k → Σ ℕ (λ m → Σ ℕ (λ n → L.suc (piece k) ≼ q m n))
    sufficient : (∀ k → hit k) → a ≼ full
    sufficient f = ≼-trans {b = L.lim piece} cover (l≼ each)
      where
      each : ∀ k → piece k ≼ full
      each k with f k
      ... | m , n , p = ≼-trans (≼-suc (≼-refl _)) (≼-trans p (paid m n))

    -- 一个统一的逐次查询界 x，给整个正槽以 x·ω 为界。
    bounded : (x : T₀) → (∀ m n → q m n ≼ x) → full ≼ x M.· L.ωᶜ
    bounded x cap = ≼-trans {b = L.lim total} (proj₂ exact) (l≼ λ m → ≼l (suc m) (finite m))
      where
      finite : ∀ m → total m ≼ x M.· L.natᶜ (suc m)
      finite zero = ≼-trans {b = x} (≼-trans start (cap 0 0)) (M.one-right x)
      finite (suc m) = +-mono (finite m) (l≼ (cap m))

    necessary : LEM → a ≼ full → ∀ k → hit k
    necessary lem le k with lem (hit k)
    ... | inj₁ yes = yes
    ... | inj₂ no = ⊥-elim (s≼-irrefl a (≼-trans {b = L.suc (piece k M.· L.ωᶜ)}
      (s≼s (≼-trans le (bounded (piece k) cap))) (room k)))
      where
      cap : ∀ m n → q m n ≼ piece k
      cap m n with Order.Classical.compare lem (q m n) (piece k)
      ... | inj₁ p = p
      ... | inj₂ p = ⊥-elim (no (m , n , p))
```
