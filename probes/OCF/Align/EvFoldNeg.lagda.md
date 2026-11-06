# 事件世界上的真折叠 (六): 离散的序, 两个事件种类的耦合

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 三条关于 `evKS₀` (外层 $0$, 界 $1$) 的事实, 都是定理:
>
> 1. **`between`: 序是离散的.** 事件表 $H$ 与 $e∷H$ 之间 (后缀关系) 只有它们自己. 所以 `HtTowerFTree.Cut₁` 那种沿高度路径取遍中间世界的走法在事件世界里没有中间世界可取; `EvFoldTree.CutE` 沿新事件逐个走. **只说**: 后缀序上相邻的两张表之间没有第三张; 不说连续的走法在别的世界上不能写.
> 2. **`rp-κ₀-skip`: κ₁ 的事件不进 κ₀ 的界** (`refl`). `drp₂` 丢掉 κ₁ 的事件时, 第 2 层的树关心的 κ₀ 的界不变 (对单个事件; 对一切只含 κ₁ 事件的表由 `skip*`).
> 3. **`rp-κ₁-up`: κ₀ 的事件以 `up δ` 进 κ₁ 的界** (`refl`). 这是事件世界与积世界 (`step S₁` 的成对世界) 的差: 在积世界里升 $H_0$ 分量不动 `HB S₁` 分量的界; 在事件世界里 κ₀ 的增量同时接到 κ₁ 的界上 (`emb⊲ (hsuc hself) δ = up δ`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldNeg where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree using (Hist; Suf; here; there; Ev; ev; rp)
```

## §1 后缀序是离散的

```agda
private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step z≤n = z≤n
  ≤-step (s≤s p) = s≤s (≤-step p)

  ≤-tr : ∀ {k m n} → k ≤ m → m ≤ n → k ≤ n
  ≤-tr z≤n q = z≤n
  ≤-tr (s≤s p) (s≤s q) = s≤s (≤-tr p q)

  ¬s≤ : ∀ n → suc n ≤ n → ⊥
  ¬s≤ zero ()
  ¬s≤ (suc n) (s≤s p) = ¬s≤ n p

  ≤-refl : ∀ {n} → n ≤ n
  ≤-refl {n = zero} = z≤n
  ≤-refl {n = suc n} = s≤s ≤-refl

suf-len : ∀ {H X} → Suf H X → length H ≤ length X
suf-len here = ≤-refl
suf-len (there e s) = ≤-step (suf-len s)

suf-anti : ∀ {H X} → Suf H X → Suf X H → X ≡ H
suf-anti here t = refl
suf-anti (there e s) t = ⊥-elim (¬s≤ _ (≤-tr (suf-len t) (suf-len s)))

between : ∀ {H X e} → Suf H X → Suf X (e ∷ H) → (X ≡ H) ⊎ (X ≡ e ∷ H)
between s here = inj₂ refl
between s (there e t) = inj₁ (suf-anti s t)
```

## §2 两个事件种类之间

```agda
rp-κ₀-skip : ∀ δ lδ (H : Hist) → rp (ev (hs hz) hself δ lδ ∷ H) hz (hsuc hself) ≡ rp H hz (hsuc hself)
rp-κ₀-skip δ lδ H = refl

rp-κ₁-up : ∀ δ lδ (H : Hist) → rp (ev hz (hsuc hself) δ lδ ∷ H) (hs hz) hself ≡ rp H (hs hz) hself ⊞ up δ
rp-κ₁-up δ lδ H = refl

-- 只含 κ₁ 事件的表不动 κ₀ 的界
data Only₁ : Hist → Set where
  o[] : Only₁ []
  o∷  : ∀ δ lδ {H} → Only₁ H → Only₁ (ev (hs hz) hself δ lδ ∷ H)

_++ᴴ_ : Hist → Hist → Hist
[] ++ᴴ H = H
(e ∷ E) ++ᴴ H = e ∷ (E ++ᴴ H)

skip* : ∀ {E} → Only₁ E → ∀ H → rp (E ++ᴴ H) hz (hsuc hself) ≡ rp H hz (hsuc hself)
skip* o[] H = refl
skip* (o∷ δ lδ o) H = skip* o H
```
