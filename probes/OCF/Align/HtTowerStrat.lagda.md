# 高度的高度 (五): 塔的分层

> 不含记号. 入口 [HtTower](HtTower.lagda.md). 关于 [HtTowerU](HtTowerU.lagda.md) 的塔 `θ` 的两条一步定理, 对一切 $k$:
>
> 1. **`below-θ`**: `θ k` 的一切第一位置 (任意世界里) 只用到分量 $<k$ 的种类 (`KB k`).
> 2. **`indep`**: 只用到分量 $<k$ 的种类的高度, 它的第一位置不看世界的分量 $\ge k$: 两个世界在 $<k$ 的分量上相等, 第一位置就可以搬过去.
>
> 合起来 (`θ-indep`): 低于 `θ k` 的层 (折叠里的节点种类 `StH`, 目标的 `t ⊲ Λ` 都是这样的第一位置) 不依赖世界在第 $k$ 个分量及以上的界. 这是入口里折叠计划的类型层依据: 第 $k$ 个新种类的回灌在 `θ k` 及以下的目标上把升高的界丢掉 (同 `HtFeedFold` 在第 0 层用 `drp`), 不需要两个世界的并 (`no-joinᴮ` 说并不存在). 种类 $(k,\mathrm{new})$ 对应读回层 `θ k`: **种类就是层**, 这里只对塔的新种类成立.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerStrat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerU using (L; FU; U; ιU; νk; θ)
```

## §1 只用低分量的种类

```agda
KB : ℕ → HB U → Set
KB k hz = ⊤
KB k (hs x) = KB k x
KB k (hl f) = ∀ n → KB k (f n)
KB k (hΩ κ g) = (proj₁ κ <ᴺ k) × (∀ c → KB k (g c))

KB⊲ : ∀ {k a b w} → a ⊲[ w ] b → KB k b → KB k a
KB⊲ hself h = h
KB⊲ (hsuc p) h = KB⊲ p h
KB⊲ (hlim n p) h = KB⊲ p (h n)
KB⊲ (hLim e p) h = KB⊲ p (proj₂ h _)

<-tr : ∀ {i j k} → i <ᴺ j → j <ᴺ k → i <ᴺ k
<-tr p zero = suc p
<-tr p (suc q) = suc (<-tr p q)

KB↑ : ∀ {j k} → j <ᴺ k → ∀ x → KB j x → KB k x
KB↑ q hz h = tt
KB↑ q (hs x) h = KB↑ q x h
KB↑ q (hl f) h = λ n → KB↑ q (f n) (h n)
KB↑ q (hΩ κ g) (p , h) = <-tr p q , (λ c → KB↑ q (g c) (h c))

KB-ι : ∀ {j k} → j <ᴺ k → ∀ x → KB k (ιU j x)
KB-ι q hz = tt
KB-ι q (hs x) = KB-ι q x
KB-ι q (hl f) = λ n → KB-ι q (f n)
KB-ι q (hΩ κ g) = q , (λ c → KB-ι q (g c))

KB-⊞ : ∀ {k} a b → KB k a → KB k b → KB k (a ⊞ b)
KB-⊞ a hz ha hb = ha
KB-⊞ a (hs b) ha hb = KB-⊞ a b ha hb
KB-⊞ a (hl f) ha hb = λ n → KB-⊞ a (f n) ha (hb n)
KB-⊞ a (hΩ κ g) ha (p , hb) = p , (λ c → KB-⊞ a (g c) ha (hb c))
```

**一步定理**: `θ k` 只用分量 $<k$ 的种类, 推出 `θ (k+1)` 只用分量 $<k+1$ 的. 用到的字段: `θ (k+1)` 的最外种类是 $(k,\mathrm{new})$, 分支是 `θ k ⊞ ιU k (…)`.

```agda
KB-θs : ∀ k → KB k (θ k) → KB (suc k) (θ (suc k))
KB-θs k h = zero , (λ c → KB-⊞ (θ k) (ιU k (up c)) (KB↑ zero (θ k) h) (KB-ι zero (up c)))

KB-θ : ∀ k → KB k (θ k)
KB-θ zero = tt
KB-θ (suc k) = KB-θs k (KB-θ k)

below-θ : ∀ {k a w} → a ⊲[ w ] θ k → KB k a
below-θ {k} p = KB⊲ p (KB-θ k)
```

## §2 不看高分量

```agda
indep : ∀ {k a b} {w w′ : Wd U} → (∀ j → j <ᴺ k → w j ≡ w′ j) → KB k b → a ⊲[ w ] b → a ⊲[ w′ ] b
indep eq h hself = hself
indep eq h (hsuc p) = hsuc (indep eq h p)
indep eq h (hlim n p) = hlim n (indep eq (h n) p)
indep {w = w} {w′} eq (q , h) (hLim {κ = κ} {c = c} e p) =
  hLim (subst (λ v → Bd (FU (proj₁ κ)) (proj₂ κ) c v) (eq (proj₁ κ) q) e) (indep eq (h c) p)

θ-indep : ∀ {k a} {w w′ : Wd U} → (∀ j → j <ᴺ k → w j ≡ w′ j) → a ⊲[ w ] θ k → a ⊲[ w′ ] θ k
θ-indep {k} eq p = indep eq (KB-θ k) p
```
