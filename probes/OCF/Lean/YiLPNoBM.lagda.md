# 合法块: 对一切树的基底单调不成立

> 验收文件 (否定). 编译定理, 无前提: 第 1 层上有一棵树 `xbad` 与两个底 `B₀ one ⊴ B′` (只把目标第 0 层的分量从 1 换成 2), 前者的折叠值不低于 ω+1, 后者的不超过 ω (`no-bm`); 所以 `(ℓ : L) (x : Tr ℓ) → BM⊥ ℓ x` 不成立 (`no-bm-all`).
> 机制: 底变了, 回灌链的第 1 个坐标从 1 变成 2, 而 `xbad` 的分支函数在 1 处大, 在 2 处是零 (分支对坐标不单调). 所以基底单调只能对规范域陈述 (`YiLPMono.BaseMonoΩt`, `CoordMono`).
> 不否定什么: 不涉及各层的 Ω 树与 `CoordMono`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPNoBM where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLPVal hiding (emb; emb-mono)
open import OCF.Lean.YiLPMono using (_⊴_; BM⊥)
```

## 第 0 层的有限值与 ω

```agda
natV : ℕ → V zero
natV zero    = zero
natV (suc n) = suc (natV n)

ωV : V zero
ωV = lim natV

¬s≼z : {a : V zero} → suc a ≼ zero {zero} → ⊥
¬s≼z ()

¬ss : (n : ℕ) → natV (suc n) ≼ natV n → ⊥
¬ss zero    ()
¬ss (suc n) (s≼s d) = ¬ss n d

¬ω≼n : (n : ℕ) → ωV ≼ natV n → ⊥
¬ω≼n zero    (l≼ h) = ¬ss zero (h 1)
¬ω≼n (suc n) (l≼ h) = ¬ss (suc n) (h (suc (suc n)))

¬sω≼n : (n : ℕ) → suc ωV ≼ natV n → ⊥
¬sω≼n zero    ()
¬sω≼n (suc n) (s≼s d) = ¬ω≼n n d

¬sω≼ω : suc ωV ≼ ωV → ⊥
¬sω≼ω (≼l n d) = ¬sω≼n n d

≼⊹ʳ : ∀ {ℓ} (a b : V ℓ) → b ≼ a ⊹ b
≼⊹ʳ a zero    = z≼
≼⊹ʳ a (suc b) = s≼s (≼⊹ʳ a b)
≼⊹ʳ a (lim f) = l≼ (λ n → ≼l n (≼⊹ʳ a (f n)))
≼⊹ʳ a (Ω p g) = Ω≼ (λ z → ≼Ω z (≼⊹ʳ a (g z)))
```

## 第 1 层, 两个底, 坏树

```agda
one : L
one = suc zero

𝟏 : Tr zero
𝟏 = suc zero

bsB : (j : L) → j ≤ one → Tr j
bsB .one  self       = Ωt one
bsB .zero (ins self) = suc 𝟏

nsB : (j : L) (w : j ≤ one) → j ⊢ zero ◃ bsB j w
nsB .one  self       = Ωt-nz one
nsB .zero (ins self) = ◃t ◃s ◃s

B′ : Base one
B′ = base 𝟏 ◃s bsB nsB

⊴B′ : B₀ one ⊴ B′
⊴B′ = ≼-refl _ , λ { .one self → ≼-refl _ ; .zero (ins self) → s≼s z≼ }

big : Tr one
big = suc (suc zero)

gg : Tr zero → Tr one
gg zero                 = zero
gg (suc zero)           = big
gg (suc (suc _))        = zero
gg (suc (lim _ _))      = zero
gg (suc (Ω () _))
gg (suc (up _ () _ _))
gg (lim _ _)            = zero
gg (Ω () _)
gg (up _ () _ _)

xbad : Tr one
xbad = Ω (inj₁ tt) gg
```

## 右边: 链停在 2, 每支都是 1

```agda
st′ : Tr zero → Tr zero
st′ z = ψs one tt tt B′ zero (ins self) (suc 𝟏) (◃t ◃s ◃s) (gg z)

gg-c′ : (m : ℕ) → gg (iter st′ zero m) ≡ zero
gg-c′ zero    = refl
gg-c′ (suc m) = cong (λ t → gg (ψs one tt tt B′ zero (ins self) (suc 𝟏) (◃t ◃s ◃s) t)) (gg-c′ m)

F′ : ℕ → Tr zero
F′ m = ψ⊥ one tt tt B′ (gg (iter st′ zero m))

F′≡ : (m : ℕ) → F′ m ≡ 𝟏
F′≡ m = cong (ψ⊥ one tt tt B′) (gg-c′ m)

cum≼n : (m : ℕ) → val zero (cum F′ m) ≼ natV (suc m)
cum≼n zero    = subst (λ t → val zero t ≼ natV 1) (sym (F′≡ zero)) (≼-refl _)
cum≼n (suc m) = subst (λ t → val zero (cum F′ m + t) ≼ natV (suc (suc m))) (sym (F′≡ (suc m))) (s≼s (cum≼n m))

right≼ω : val zero (ψ⊥ one tt tt B′ xbad) ≼ ωV
right≼ω = l≼ (λ m → ≼l (suc m) (cum≼n m))
```

## 左边: 第 1 支是 ψ⊥ (big), 不低于 ω+1

```agda
1⊹n : (i : ℕ) → natV (suc i) ≼ suc zero ⊹ natV i
1⊹n zero    = ≼-refl _
1⊹n (suc i) = s≼s (1⊹n i)

itn : (i : ℕ) → natV (suc i) ≼ val zero (iter (𝟏 +_) 𝟏 i)
itn zero    = ≼-refl _
itn (suc i) = ≼-trans (≼-trans (1⊹n (suc i)) (⊹-mono (suc zero) (itn i))) (proj₂ (val-+ 𝟏 (iter (𝟏 +_) 𝟏 i)))

lemN : (i : ℕ) → natV i ≼ val zero (𝟏 + iter (𝟏 +_) 𝟏 i)
lemN i = ≼-trans (≼-suc (≼-refl (natV i)))
           (≼-trans (itn i) (≼-trans (≼⊹ʳ (suc zero) (val zero (iter (𝟏 +_) 𝟏 i))) (proj₂ (val-+ 𝟏 (iter (𝟏 +_) 𝟏 i)))))

left≽ : suc ωV ≼ val zero (ψ⊥ one tt tt (B₀ one) xbad)
left≽ = ≼l 1 (≼l 1 (≼l 0 (s≼s (l≼ (λ i → ≼l i (lemN i))))))
```

## 否定

```agda
no-bm : (B₀ one ⊴ B′) × (val zero (ψ⊥ one tt tt (B₀ one) xbad) ≼ val zero (ψ⊥ one tt tt B′ xbad) → ⊥)
no-bm = ⊴B′ , λ d → ¬sω≼ω (≼-trans left≽ (≼-trans d right≼ω))

no-bm-all : ((ℓ : L) (x : Tr ℓ) → BM⊥ ℓ x) → ⊥
no-bm-all h = proj₂ no-bm (h one xbad tt tt (B₀ one) B′ ⊴B′)
```
