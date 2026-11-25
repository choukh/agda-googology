# 起点条件不能从 `KG` 去掉

> 验收文件 (否定). 编译定理, 无前提: 层号 `tw 1` 上的底 `Bbad` 满足 `OKB` (`ok-bad`), 底分量是 ω, 链起点是 1, 不满足起点条件 (`no-start`); 它的第 0 个孩子上 `G 0` 不低于 ω+1, `K 0` 读成 ω, `read (G 0) ≼ read (K 0)` 不成立 (`no-GK`), 所以 `YiEBBtbo` 的 `KG` 对这个底不成立 (`no-KG`).
> 不否定什么: 不否定 `D.BTBOᴵ ≼ read (Fn 1 Bbad)`, 只说明 `btbo-B` 的证法要起点条件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEBNoKG where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (OKB)
open import OCF.Lean.YiEBBtbo using (Start; module Chain)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
```

## 底

```agda
one : Tr zero
one = suc zero

f₁ : ℕ → Tr zero
f₁ = iter (one +_) one

ω₁ : Tr zero
ω₁ = next one ◃s

Bbad : Base (tw 1)
Bbad = base ω₁ (◃t ◃s (◃l 0)) (λ j _ → Ωt j) (λ j _ → Ωt-nz j)

ok-bad : OKB (tw 1) Bbad
ok-bad = ⊴◃ (◃l 0) , λ j w → ⊴r

no-start : Start Bbad → ⊥
no-start ()
```

## 有限树

```agda
natT : ℕ → Tr zero
natT zero    = zero
natT (suc m) = suc (natT m)

one+ : (m : ℕ) → one + natT m ≡ natT (suc m)
one+ zero    = refl
one+ (suc m) = cong suc (one+ m)

f≡ : (k : ℕ) → f₁ k ≡ natT (suc k)
f≡ zero    = refl
f≡ (suc k) = subst (λ t → one + t ≡ natT (suc (suc k))) (sym (f≡ k)) (one+ (suc k))

n≼sn : (m : ℕ) → read (natT m) ≼ read (natT (suc m))
n≼sn zero    = z≼
n≼sn (suc m) = s≼s (n≼sn m)

¬ss : (m : ℕ) → read (natT (suc m)) ≼ read (natT m) → ⊥
¬ss zero    ()
¬ss (suc m) (s≼s d) = ¬ss m d

¬ω≼n : (m : ℕ) → read ω₁ ≼ read (natT m) → ⊥
¬ω≼n zero    (l≼ h) = ¬ss zero (≼-trans (n≼sn 1) (subst (λ t → read t ≼ read (natT zero)) (f≡ 1) (h 1)))
¬ω≼n (suc m) (l≼ h) = ¬ss (suc m) (≼-trans (n≼sn (suc (suc m))) (subst (λ t → read t ≼ read (natT (suc m))) (f≡ (suc (suc m))) (h (suc (suc m)))))

¬sω≼n : (m : ℕ) → L.suc (read ω₁) ≼ read (natT m) → ⊥
¬sω≼n zero    ()
¬sω≼n (suc m) (s≼s d) = ¬ω≼n m d

¬sω≼ω : L.suc (read ω₁) ≼ read ω₁ → ⊥
¬sω≼ω (≼l k d) = ¬sω≼n (suc k) (subst (λ t → L.suc (read ω₁) ≼ read t) (f≡ k) d)
```

## `KG` 不成立

```agda
open Chain Bbad

no-GK : read (G zero) ≼ read (K zero) → ⊥
no-GK d = ¬sω≼ω (≼-trans (≼l 1 (≼l 0 (≼-refl (L.suc (read ω₁))))) d)

no-KG : read (K zero) L.≅ read (G zero) → ⊥
no-KG e = no-GK (≅→≼ (L.≅-sym e))
```
