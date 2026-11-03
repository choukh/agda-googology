# 终局 (一): 阶段接口 `Stage` 与不动点上的条件闭项

> 不含记号, 不含具体折叠, 只导入标准库. 结论写在 [EBOTop](EBOTop.lagda.md). `Stage` 的每个字段都是**假设**; `Top` 里的一切都是 `Stage` 之下的条件定理. 对角线只有一个定义: `L 0 = seed`, `L (n+1) = feed (Ω (L n))`, `Λ = lub L`, `x n = ψ₀ (Ω (L n))`, 不按阶段定制.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.EBOTopStage where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
```

## §1 第 0 层: 具体的树, FGH, 遗传步进

第 0 层是唯一具体的东西: 大数在这里算出来. `HS` 是树语言里的合法性: 每个 ℕ-极限的相邻两项步进, 步进指前驱包含, 叶子是结构互模拟. 它不提任何记号.

```agda
data O₀ : Set where
  zero : O₀
  suc  : O₀ → O₀
  lim  : (ℕ → O₀) → O₀

iterᴺ : {A : Set} → (A → A) → A → ℕ → A
iterᴺ f a zero    = a
iterᴺ f a (suc n) = f (iterᴺ f a n)

FGH : O₀ → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iterᴺ (FGH a) n n
FGH (lim f) n = FGH (f n) n

infix 4 _≅⁰_ _≺⁰_ _⊑⁰_

data _≅⁰_ : O₀ → O₀ → Set where
  z≅ : zero ≅⁰ zero
  s≅ : ∀ {a b} → a ≅⁰ b → suc a ≅⁰ suc b
  l≅ : ∀ {f g} → (∀ n → f n ≅⁰ g n) → lim f ≅⁰ lim g

data _≺⁰_ : O₀ → O₀ → Set where
  ≺z : ∀ {c b} → c ≅⁰ b → c ≺⁰ suc b
  ≺s : ∀ {c b} → c ≺⁰ b → c ≺⁰ suc b
  ≺l : ∀ {c f} n → c ≺⁰ f n → c ≺⁰ lim f

_⊑⁰_ : O₀ → O₀ → Set
a ⊑⁰ b = ∀ {c} → c ≺⁰ a → c ≺⁰ b

data HS : O₀ → Set where
  hz : HS zero
  hs : ∀ {a} → HS a → HS (suc a)
  hl : ∀ {f} → (∀ n → HS (f n)) → (∀ n → f n ⊑⁰ f (suc n)) → HS (lim f)

≅⁰-refl : ∀ a → a ≅⁰ a
≅⁰-refl zero    = z≅
≅⁰-refl (suc a) = s≅ (≅⁰-refl a)
≅⁰-refl (lim f) = l≅ (λ n → ≅⁰-refl (f n))
```

**序的基本事实.** $\prec$ 良基, 所以无自反. 这条在后面用来说 "步进不是塌缩", 也用来反驳把 `HS` 对全部层号提出的要求.

```agda
≅⁰-sym : ∀ {a b} → a ≅⁰ b → b ≅⁰ a
≅⁰-sym z≅     = z≅
≅⁰-sym (s≅ e) = s≅ (≅⁰-sym e)
≅⁰-sym (l≅ h) = l≅ (λ n → ≅⁰-sym (h n))

≅⁰-trans : ∀ {a b c} → a ≅⁰ b → b ≅⁰ c → a ≅⁰ c
≅⁰-trans z≅     z≅      = z≅
≅⁰-trans (s≅ e) (s≅ e′) = s≅ (≅⁰-trans e e′)
≅⁰-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅⁰-trans (h n) (h′ n))

≺⁰-respʳ : ∀ {c a b} → c ≺⁰ a → a ≅⁰ b → c ≺⁰ b
≺⁰-respʳ (≺z e)   (s≅ e′) = ≺z (≅⁰-trans e e′)
≺⁰-respʳ (≺s h)   (s≅ e′) = ≺s (≺⁰-respʳ h e′)
≺⁰-respʳ (≺l n h) (l≅ k)  = ≺l n (≺⁰-respʳ h (k n))

≺⁰-respˡ : ∀ {c c′ b} → c ≅⁰ c′ → c ≺⁰ b → c′ ≺⁰ b
≺⁰-respˡ e (≺z e′)   = ≺z (≅⁰-trans (≅⁰-sym e) e′)
≺⁰-respˡ e (≺s h)    = ≺s (≺⁰-respˡ e h)
≺⁰-respˡ e (≺l n h)  = ≺l n (≺⁰-respˡ e h)

data Acc⁰ (a : O₀) : Set where
  acc : (∀ {c} → c ≺⁰ a → Acc⁰ c) → Acc⁰ a

acc⁰ : ∀ a {c} → c ≺⁰ a → Acc⁰ c
acc⁰ (suc b) (≺z e)   = acc (λ q → acc⁰ b (≺⁰-respʳ q e))
acc⁰ (suc b) (≺s h)   = acc⁰ b h
acc⁰ (lim f) (≺l n h) = acc⁰ (f n) h

≺⁰-irrefl : ∀ {a} → a ≺⁰ a → ⊥
≺⁰-irrefl {a} = go (acc (acc⁰ a)) where
  go : ∀ {a} → Acc⁰ a → a ≺⁰ a → ⊥
  go (acc h) q = go (h q) (≺⁰-respʳ q (≅⁰-refl _))
```

## §2 接口

字段分五组: 世界 (层, 树, $\Omega$, 折叠), 证书, 回灌, 层序, 层极限. 证书谓词 `GoodL`, `GoodT` 完全抽象. 回灌 `feed` 要证据: 这样同时容纳 "层号内在带证据" 的设计 ([Level](Level.lagda.md) 的 `toLevel`) 与 "层号是裸树" 的设计 ([InaccTreeBase](InaccTreeBase.lagda.md) 的 `toLv`, 证据不用). 比较 (三歧, 判决) **不在接口里**: 折叠怎么派发是实例自己的事, 接口只看结果. 这是壁垒检查的要点 ([EBOTopBarrier](EBOTopBarrier.lagda.md)).

中间的定义 (`GL`, `next`, `Tow`, `L`, `x`, `Λ`) 就是**唯一的**对角线, 后面的字段只对它提要求.

```agda
tow : {A : Set} → A → (A → A) → ℕ → A
tow a f zero    = a
tow a f (suc n) = f (tow a f n)

record Stage : Set₁ where
  infix 4 _⊑_
  field
    -- 世界
    Lv   : Set
    Tr   : Lv → Set
    base : Lv
    out  : Tr base → O₀
    Ω    : (ℓ : Lv) → Tr ℓ
    ψ₀   : ∀ {ℓ} → Tr ℓ → Tr base
    -- 证书
    GoodL : Lv → Set
    GoodT : ∀ {ℓ} → Tr ℓ → Set
    seed      : Lv
    good-seed : GoodL seed
    good-Ω    : ∀ {ℓ} → GoodL ℓ → GoodT (Ω ℓ)
    cert      : ∀ {ℓ} {t : Tr ℓ} → GoodT t → HS (out (ψ₀ t))
    -- 回灌: 树到层
    feed      : ∀ {ℓ} (t : Tr ℓ) → GoodT t → Lv
    good-feed : ∀ {ℓ} (t : Tr ℓ) (g : GoodT t) → GoodL (feed t g)
    -- 层序: 前驱包含
    _⊑_  : Lv → Lv → Set
    infl : ∀ {ℓ} (g : GoodL ℓ) → ℓ ⊑ feed (Ω ℓ) (good-Ω g)
    -- 层极限
    lub   : (f : ℕ → Lv) → (∀ n → f n ⊑ f (suc n)) → Lv
    ub    : ∀ f s n → f n ⊑ lub f s
    lub-Ω : ∀ f s → out (ψ₀ (Ω (lub f s))) ≡ lim (λ n → out (ψ₀ (Ω (f n))))

  -- 唯一的对角线
  GL : Set
  GL = Σ Lv GoodL

  next : GL → GL
  next p = feed (Ω (proj₁ p)) (good-Ω (proj₂ p)) , good-feed (Ω (proj₁ p)) (good-Ω (proj₂ p))

  Tow : ℕ → GL
  Tow = tow (seed , good-seed) next

  L : ℕ → Lv
  L n = proj₁ (Tow n)

  G : ∀ n → GoodL (L n)
  G n = proj₂ (Tow n)

  x : ℕ → O₀
  x n = out (ψ₀ (Ω (L n)))

  Λ : Lv
  Λ = lub L (λ n → infl (G n))

  field
    -- 只对这条对角线的要求
    good-Λ : GoodL Λ
    Ω-Λ    : ∀ b → (∀ n → L (suc n) ⊑ b) → feed (Ω Λ) (good-Ω good-Λ) ⊑ b
```

逐字段的说明:

- `seed`: 塔的起点. EBO 取第 0 层 ($\Lambda[n]$ 从 $\Omega_0$ 算起), 低端实例可以取别的.
- `cert`: 证书的结论只有一条, 第 0 层的输出 `HS`. 中间用什么谓词是实现的事.
- `feed`: 只要 `feed (Ω ℓ)` 就够定义塔, 写成一般的树是因为分支的层号要它.
- `infl`: $\ell\sqsubseteq\Omega_\ell$. 这是塔的步进, `lub` 要它.
- `good-Λ`, `Ω-Λ`: **只对塔**. `Ω-Λ` 说 $\Omega$ 在塔的极限上连续. 塔的步进 $\psi_0(\Omega_{L_n})\sqsubseteq\psi_0(\Omega_{L_{n+1}})$ 不是字段: 它是 `good-Λ` 与 `cert` 的推论 (`spine`). 对全部好层号要求它既不需要也不对.

## §3 条件定理: 不动点上的闭项

```agda
module Top (S : Stage) where
  open Stage S

  -- 对角线的方程
  L-suc : ∀ n → L (suc n) ≡ feed (Ω (L n)) (good-Ω (G n))
  L-suc n = refl

  -- 闭项
  EBOᵀ : O₀
  EBOᵀ = out (ψ₀ (Ω Λ))

  EBO-lim : EBOᵀ ≡ lim x
  EBO-lim = lub-Ω L (λ n → infl (G n))

  x-HS : ∀ n → HS (x n)
  x-HS n = cert (good-Ω (G n))

  -- 证书
  EBO-HS : HS EBOᵀ
  EBO-HS = cert (good-Ω good-Λ)

  -- 塔的步进是推论, 不是字段
  HS-lim : HS (lim x)
  HS-lim = subst HS EBO-lim EBO-HS

  spine : ∀ n → x n ⊑⁰ x (suc n)
  spine n with HS-lim
  ... | hl _ st = st n

  -- FGH
  big : ℕ → ℕ
  big = FGH EBOᵀ

  -- 不动点: 树语言. 关系是层序 ⊑ 的两个方向, 不是结构相等.
  Λ-next : Lv
  Λ-next = feed (Ω Λ) (good-Ω good-Λ)

  fix⊑ : Λ-next ⊑ Λ
  fix⊑ = Ω-Λ Λ (λ n → ub L (λ m → infl (G m)) (suc n))

  fix⊒ : Λ ⊑ Λ-next
  fix⊒ = infl good-Λ

  fixpoint : (Λ-next ⊑ Λ) × (Λ ⊑ Λ-next)
  fixpoint = fix⊑ , fix⊒
```
