# 值判据 (十): 规格接到树

> **判决: PARTIAL (条件定理).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). `emb` 把第 0 层的树搬到 `Ordᴸ`. **`spec-clos`, `spec-base`**: 给定 `IsPsiᴸ` 在链点上成立, 上升, 切口, 证书的计值就满足 $\psi_0(A)$ 的规格, 这里 $A$ 是字面的 (比如 $\Omega_\Omega$, $\Omega_{\Omega\cdot2}$). 前提都是条件, 经典地成立 (判断). 所以 `rejected-if-gap` 在这里不出现: 输入不是替身. 对 $\Omega_\Omega$, 切口由 `cut-ΩΩ` 的三条层号性质给 (`CutΩΩ`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.ValueJudgeSpecTree (𝕊 : HtS) where

open HtS 𝕊
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Free.Level
open import OCF.Align.InaccTreeBase using (Lv; Ordᴸ; Tree; limᵢ)
import OCF.Align.InaccTreeBase as L
open import OCF.Align.OCFSpecLv using (_≼ᴸ_; _≺ᴸ_; z≼; s≼s; ≼l; l≼; IsPsiᴸ)
open import OCF.Align.ValueJudgeSpec
open import OCF.Align.ValueJudgeLadder 𝕊 using (V; ClosRow; ys; hy; value; clos-row)
open import OCF.Align.ValueJudgeRowV 𝕊 using (BaseRow; ysᵇ; valueᵇ; base-row)

emb : Ordᶜ zero → Ordᴸ L.zero
emb zero    = Tree.zero
emb (suc x) = Tree.suc (emb x)
emb (lim f) = Tree.lim (λ n → emb (f n))
emb (limᵢ () f)
emb (up () x)

emb-≼ : ∀ {a b : Ordᶜ zero} → a ≅ b → emb a ≼ᴸ emb b
emb-≼ z≅     = z≼
emb-≼ (s≅ e) = s≼s (emb-≼ e)
emb-≼ (l≅ h) = l≼ (λ n → ≼l n (emb-≼ (h n)))

module _ {lvs : ℕ → Lv} (a : (i : ℕ) → Ordᴸ (lvs i)) {K} (A : Ordᴸ K) where
  spec-of : ∀ {Y : ℕ → Ordᶜ zero} {T : Ordᶜ zero} → T ≅ lim Y →
            (∀ n → IsPsiᴸ L.zero (a n) (emb (Y n))) →
            (∀ n → a n ≼ᴸ a (suc n)) → (∀ n → a n ≼ᴸ A) →
            (∀ n {m} {y : Ordᴸ m} → Cᴸ L.zero (a n) y → y ≺ᴸ A → y ≺ᴸ a (suc n)) →
            IsPsiᴸ L.zero A (emb T)
  spec-of {Y} eT H stp a≼A Cut = Sup-t (emb-≼ (≅-sym eT)) (emb-≼ eT) (FixRow.fix a A (λ n → emb (Y n)) H stp a≼A Cut)

  spec-clos : ∀ {n m} (r : n <ᴸ m) (ev : view m ≡ clos r) →
              (∀ k → IsPsiᴸ L.zero (a k) (emb (ys (clos-row r ev) k))) →
              (∀ k → a k ≼ᴸ a (suc k)) → (∀ k → a k ≼ᴸ A) →
              (∀ k {m′} {y : Ordᴸ m′} → Cᴸ L.zero (a k) y → y ≺ᴸ A → y ≺ᴸ a (suc k)) →
              IsPsiᴸ L.zero A (emb (V m zero))
  spec-clos r ev = spec-of (value (clos-row r ev))

  spec-base : (ev : view h₀ ≡ base) →
              (∀ k → IsPsiᴸ L.zero (a k) (emb (ysᵇ (base-row ev) k))) →
              (∀ k → a k ≼ᴸ a (suc k)) → (∀ k → a k ≼ᴸ A) →
              (∀ k {m′} {y : Ordᴸ m′} → Cᴸ L.zero (a k) y → y ≺ᴸ A → y ≺ᴸ a (suc k)) →
              IsPsiᴸ L.zero A (emb (V h₀ zero))
  spec-base ev = spec-of (valueᵇ (base-row ev))
```
