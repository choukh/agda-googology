# 最小亏损格上的转移: 单个结点的实例

> 验收文件. 编译定理, 对一切排中律 `lem` (条件（排中律）): tw 1 的最小亏损格 (槽位是孩子 2 里第 1 层里的第 0 层, 目标是孩子 2 里的第 1 层; 同 P4Cell) 上, 主线走链而 `Ideal lem` 保留 (`cell-actual`, `cell-keeps`), 对任意底、底值、分支, 两边输出分别是部分和极限与 Ω 结点 (`cell-forms`).
> 单结点转移的实例: 分支取 `ι (tw 1)` (第 0 层的树原样嵌入, 非退化) 时, 对任意底值 β, 现输出的值 ≼ ψ★ 输出的值 (`cell-transfer-ι`); 证法是 `chain≼keep` 加吸收, 吸收要的是 "ψ★ 在这族分支上对分支参数的值单调" (`mono-ι`).
> 不涉及外层: 外层的链点在两边不同, 本文件不处理. 常值分支在同类格上不成立见 [YiPSNeg](YiPSNeg.lagda.md) 的 `k6-lower`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPSCell where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
import OCF.Lean.YiTBRow as T
open import OCF.Lean.YiTBRow using (nat)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiPSStar
open import OCF.Lean.YiPSNeg using (one; chain≼keep)
open import OCF.Lean.YiVWVal using (val; _≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; lim⁻; _⊹_; ≼⊹; ⊹-mono; ⊹-monoˡ; val-+)
import OCF.Lean.YiVWVal as W
```

## 格

```agda
slot : Pos (tw 1)
slot = inj₂ (nat 2 , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))

w : one ≤ tw 1
w = inc (nat 2) (inc tt self)

cell-actual : kp (tw 1) (Ok-tw 1) slot w ≡ nothing
cell-actual = refl

cell-keeps : ∀ lem → Σ _ λ K → Keep★.kp★ (cmpᴵ lem) (tw 1) (Ok-tw 1) slot w ≡ just K
cell-keeps lem = _ , refl

cell-forms : ∀ lem (B : Base (tw 1)) (β : Tr⁺ one) (g : Br (tw 1) slot → Tr (tw 1))
  → (Σ _ λ f → Σ _ λ a → proj₁ (T.ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B one w β (Ω slot g)) ≡ lim f a)
  × (Σ _ λ q → Σ _ λ G → proj₁ (Ideal.ψ★ lem (tw 1) (Ok-tw 1) B one w β (Ω slot g)) ≡ Ω q G)
cell-forms lem B β g = (_ , _ , refl) , (_ , _ , refl)
```

## 分支取 ι 时的单结点转移

`ψA`, `ψI` 是两边在这一格的目标上对 `ι` 的像的折叠; 在 ι 的像上两边逐行相同 (`same`). 吸收: 第 n 个部分和不高于 ψ★ 在 `Wz zs n` 处的分支.

```agda
≼⊹ʳ : (a b : W.V zero) → b ≼ a ⊹ b
≼⊹ʳ a W.zero    = z≼
≼⊹ʳ a (W.suc b) = s≼s (≼⊹ʳ a b)
≼⊹ʳ a (W.lim f) = l≼ (λ n → ≼l n (≼⊹ʳ a (f n)))
≼⊹ʳ a (W.Ω () g)

next-mono : ∀ {j} (b b★ : Tr⁺ j) → val j (proj₁ b) ≼ val j (proj₁ b★)
          → val j (proj₁ (next⁺ b)) ≼ val j (proj₁ (next⁺ b★))
next-mono {j} b b★ d = l≼ (λ n → ≼l n (it n))
  where
  it : ∀ n → val j (iter (proj₁ b +_) (proj₁ b) n) ≼ val j (iter (proj₁ b★ +_) (proj₁ b★) n)
  it zero    = d
  it (suc n) = ≼-trans (proj₁ (val-+ (proj₁ b) (iter (proj₁ b +_) (proj₁ b) n)))
    (≼-trans (⊹-monoˡ d _)
    (≼-trans (⊹-mono (val j (proj₁ b★)) (it n))
             (proj₂ (val-+ (proj₁ b★) (iter (proj₁ b★ +_) (proj₁ b★) n)))))

module _ (lem : LEM) (β : Tr⁺ one) where
  ψA ψI : Tr zero → Tr⁺ one
  ψA z = T.ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) one w β (ι (tw 1) z)
  ψI z = Ideal.ψ★ lem (tw 1) (Ok-tw 1) (B₀ (tw 1)) one w β (ι (tw 1) z)

  same : ∀ z → val one (proj₁ (ψA z)) ≼ val one (proj₁ (ψI z))
  same zero      = ≼-refl _
  same (suc z)   = next-mono (ψA z) (ψI z) (same z)
  same (lim f a) = l≼ (λ n → ≼l n (same (f n)))
  same (Ω () g)
  same (up x () y e)

  base : ∀ b → val one (proj₁ β) ≼ val one (proj₁ (ψI b))
  base zero      = ≼-refl _
  base (suc b)   = ≼-trans (base b) (≼l 0 (≼-refl _))
  base (lim f a) = ≼-trans (base (f 0)) (≼l 0 (≼-refl _))
  base (Ω () g)
  base (up x () y e)

  mono-ι : ∀ a b → val zero a ≼ val zero b → val one (proj₁ (ψI a)) ≼ val one (proj₁ (ψI b))
  mono-ι zero      b         d          = base b
  mono-ι (suc a)   zero      ()
  mono-ι (suc a)   (suc b)   (s≼s d)    = next-mono (ψI a) (ψI b) (mono-ι a b d)
  mono-ι (suc a)   (lim g r) (≼l n d)   = ≼-trans (mono-ι (suc a) (g n) d) (≼l n (≼-refl _))
  mono-ι (suc a)   (Ω () g)  d
  mono-ι (suc a)   (up x () y e) d
  mono-ι (lim f r) b         d          = l≼ (λ n → mono-ι (f n) b (lim⁻ n d))
  mono-ι (Ω () g)  b         d
  mono-ι (up x () y e) b     d

  Wz : (ℕ → Tr zero) → ℕ → Tr zero
  Wz zs zero    = suc (zs zero)
  Wz zs (suc n) = suc (Wz zs n + zs (suc n))

  absorb : (zs : ℕ → Tr zero) → ∀ n
         → val one (cum (λ k → proj₁ (ψA (zs k))) n) ≼ val one (proj₁ (ψI (Wz zs n)))
  absorb zs zero = ≼-trans (same (zs 0)) (mono-ι (zs 0) (suc (zs 0)) (≼-suc (≼-refl _)))
  absorb zs (suc n) =
    ≼-trans (proj₁ (val-+ (cum (λ k → proj₁ (ψA (zs k))) n) (proj₁ (ψA (zs (suc n))))))
    (≼-trans (⊹-monoˡ (≼-trans (absorb zs n) (mono-ι (Wz zs n) S le₁)) _)
    (≼-trans (⊹-mono (val one (proj₁ (ψI S))) (≼-trans (same (zs (suc n))) (mono-ι (zs (suc n)) S le₂)))
    (≼-trans (proj₂ (val-+ (proj₁ (ψI S)) (proj₁ (ψI S))))
             (≼l 1 (≼-refl _)))))
    where
    S : Tr zero
    S = Wz zs n + zs (suc n)
    le₁ : val zero (Wz zs n) ≼ val zero S
    le₁ = ≼-trans (≼⊹ (val zero (Wz zs n)) (val zero (zs (suc n)))) (proj₂ (val-+ (Wz zs n) (zs (suc n))))
    le₂ : val zero (zs (suc n)) ≼ val zero S
    le₂ = ≼-trans (≼⊹ʳ (val zero (Wz zs n)) (val zero (zs (suc n)))) (proj₂ (val-+ (Wz zs n) (zs (suc n))))

sA : Tr zero → Tr zero
sA z = proj₁ (T.ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (posW (tw 1) slot) (Ωt zero) (ι (tw 1) z))

cell-transfer-ι : ∀ (lem : LEM) (β : Tr⁺ one)
  → val one (proj₁ (T.ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) one w β (Ω slot (ι (tw 1)))))
  ≼ val one (proj₁ (Ideal.ψ★ lem (tw 1) (Ok-tw 1) (B₀ (tw 1)) one w β (Ω slot (ι (tw 1)))))
cell-transfer-ι lem β =
  chain≼keep (λ k → ψA lem β (iter sA zero k)) (inj₂ (tt , inj₁ tt)) (ψI lem β)
    (λ n → Wz lem β (iter sA zero) n , absorb lem β (iter sA zero) n)
```
