# 对象在折叠下怎么行动 (三): 只看值分不开

> 入口 [TLBehave](TLBehave.lagda.md). **判决: HOLDS (编译过, 无条件).** 不读记号. 这些定理否定的是 **对值单调的判据**: 下闭的或者上闭的值谓词.
>
> | 定理 | 陈述 | 前提可满足吗 |
> | --- | --- | --- |
> | `dom-ht` | `WorldTH` 里下标的秩不超过第 0 行的值 | 无假设 |
> | `row-above` | 一切第 0 层的树 $y$, 包括 `T₁`: 严格低于某个高度行的值 | 无假设 |
> | `cap-trivial` | 下闭的值谓词, 对一切高度行成立, 就对一切第 0 层的树成立 | $P=\top$ 满足; 结论说这样的 $P$ 只有平凡的 |
> | `floor-trivial` | 上闭的值谓词, 对 `T₁` 成立, 就对某个高度行成立 | $P=\top$ 满足 |
> | `blind` | 有一棵 `Ad` 的树 (`T₁`), 值严格低于一个不 `Ad` 的高度行 | 无假设 |
>
> `CrossM` 一族的对应事实已有: `no-cofinal` (`LadderOrdNeg`) 说单个世界的位置的秩穷尽不了 `Ordᴵ`. 那边没有定义 `Ad`.
>
> **没有否定的.** 非单调的值谓词: 比如 "值恰好是某个高度行的值". `T₁` 的值是不是某个高度行的值, 没有定理. 所以这里不能说 "一切只读值的判据都分不开", 只能说单调的分不开.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLBehaveNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Free.Level using (_≺_; _⊑⁰_)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; g₀; pos; gnext)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHPsi using (NL; ns; nh)
open import OCF.Align.WorldTHMain using (⊴₀→⊑⁰)
open import OCF.Align.WorldTHGrow using (T-strict; row-mono; one⊴ψ₀)
open import OCF.Align.WorldTHInst using (T₁)
open import OCF.Align.ValueJudgeBase using (_≼_; z≼; s≼s; l≼; ≼-trans; ≺→s≼; ⊑→≼; _≺ᵛ_; ≺→≼)
open import OCF.Align.TLBehaveDef
open import OCF.Align.TLBehaveThm using (rk; next-≺; abs-val; rows-not-ad; top-ad)
```

## §1 行的值盖住下标

```agda
dom-ht : ∀ a {u₀} (g : Gw u₀) (e : LB (ht a) azero u₀) → rk a ≼ Tψ (ht a) azero u₀ g e
dom-suc : ∀ b (nl : NL (ht b) azero) {u₀} (g : Gw u₀) (e : LB (ht (asuc b)) azero u₀) → rk (asuc b) ≼ Tψ (ht (asuc b)) azero u₀ g e

dom-ht azero g e = z≼
dom-ht (asuc azero) {u₀} g e = ⊑→≼ (FL.suc FL.zero) (⊴₀→⊑⁰ (one⊴ψ₀ (Ω̇ (ht (asuc azero)) azero) g₀ u₀ g (pos g) e))
dom-ht (asuc (asuc c)) g e = dom-suc (asuc c) ns g e
dom-ht (asuc (alim f)) g e = dom-suc (alim f) nh g e
dom-ht (alim f) g e = l≼ (λ n → ≼-trans (dom-ht (f n) g (e′ n)) (⊑→≼ _ (row-mono g g (e′ n) e (C.lim n C.self))))
  where
  e′ : ∀ n → LB (ht (f n)) azero _
  e′ n = proj₁ e , ⊲-tr (C.lim n C.self) (proj₂ e)

dom-suc b nl {u₀} g e = ≼-trans (s≼s (dom-ht b g e₀)) (≺→s≼ (abs-val b g g e₁ e (T-strict nl u₀ g e₀ u₀ g e₁)))
  where
  b⊲ : b ⊲ u₀
  b⊲ = ⊲-tr (C.suc C.self) (proj₂ e)
  e₀ : LB (ht b) azero u₀
  e₀ = proj₁ e , b⊲
  e₁ : LB (ht b) one u₀
  e₁ = pos g , b⊲
```

## §2 回灌过任何树

```agda
row-above : ∀ y → y ≺ᵛ Tψ (ht (next one y)) azero (next one y) (gnext y g₀) (z⊲ _ , C.self)
row-above y = ≼-trans (next-≺ one y) (dom-ht (next one y) (gnext y g₀) (z⊲ _ , C.self))
```

## §3 单调的值谓词

```agda
RowAll : (Ord₀ → Set) → Set
RowAll P = ∀ a {u₀} (g : Gw u₀) (e : LB (ht a) azero u₀) → P (Tψ (ht a) azero u₀ g e)

cap-trivial : (P : Ord₀ → Set) → (∀ {x y} → x ≼ y → P y → P x) → RowAll P → ∀ y → P y
cap-trivial P down all y = down (≺→≼ (row-above y)) (all _ (gnext y g₀) (z⊲ _ , C.self))

T₁-capped : (P : Ord₀ → Set) → (∀ {x y} → x ≼ y → P y → P x) → RowAll P → P T₁
T₁-capped P down all = cap-trivial P down all T₁

floor-trivial : (P : Ord₀ → Set) → (∀ {x y} → x ≼ y → P x → P y) → P T₁ →
                P (Tψ (ht (next one T₁)) azero (next one T₁) (gnext T₁ g₀) (z⊲ _ , C.self))
floor-trivial P up p = up (≺→≼ (row-above T₁)) p

-- 值的序与 Ad 没有关系
blind : Ad (Ω̇ top one) × (T₁ ≺ᵛ Tψ (ht (next one T₁)) azero (next one T₁) (gnext T₁ g₀) (z⊲ _ , C.self)) × (Ad (Ω̇ (ht (next one T₁)) azero) → ⊥)
blind = top-ad one , row-above T₁ , rows-not-ad (next one T₁) azero
```
