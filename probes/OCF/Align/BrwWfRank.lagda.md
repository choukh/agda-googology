# 沿 View 递归 (二): 秩的比较 (模拟序)

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 给一个类型 $T$ 和一个良基的 "直接子树" 关系 $R$ (布劳威尔树的构造子各给一种), 定义**秩的比较**:
>
> $$a\sqsubseteq b \iff \forall a'\mathrel{R}a.\ a'\sqsubset b,\qquad a'\sqsubset b\iff \exists b'\mathrel{R}b.\ a'\sqsubseteq b'.$$
>
> 这是集合论里秩的比较 (直接子树的秩加一的上确界), 不是值的比较: 常数列的极限 $\lim(0,0,\dots)$ 值是 $0$, 秩是 $1$. 为什么要它: 值前序 $\preccurlyeq$ 上的 "低于某个直接子树" 不良基 ($\lim_n\omega\preccurlyeq\omega$, 所以 $\lim_n\omega$ 低于自己的直接子树 $\omega$), 而 View 的 $\mathbb N$-极限不严格 ([BrwViewNeg](BrwViewNeg.lagda.md) `strict→LPO`), 部分的值可以等于整体的值. 秩的比较在函数上逐点, 不要 `Funext`, 并且良基 (`<ₛ-wf`).
>
> 两个关系互相归纳 (数据类型), 所以自反要 $R$ 良基 (对 `Acc` 归纳), 传递与良基对推导归纳.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfRank where

open import Induction.WellFounded using (Acc; acc; WellFounded)

module Rank {T : Set} (R : T → T → Set) (wfR : WellFounded R) where
  infix 4 _≤ₛ_ _<ₛ_
  data _≤ₛ_ : T → T → Set
  data _<ₛ_ : T → T → Set
  data _≤ₛ_ where
    sim : ∀ {a b} → (∀ {a′} → R a′ a → a′ <ₛ b) → a ≤ₛ b
  data _<ₛ_ where
    lt : ∀ {a b b′} → R b′ b → a ≤ₛ b′ → a <ₛ b
```

## §1 自反, 传递, 子树

```agda
  ≤ₛ-refl′ : ∀ a → Acc R a → a ≤ₛ a
  ≤ₛ-refl′ a (acc rs) = sim (λ {a′} r → lt r (≤ₛ-refl′ a′ (rs r)))

  ≤ₛ-refl : ∀ a → a ≤ₛ a
  ≤ₛ-refl a = ≤ₛ-refl′ a (wfR a)

  ≤ₛ-trans : ∀ {a b c} → a ≤ₛ b → b ≤ₛ c → a ≤ₛ c
  <≤-trans : ∀ {a b c} → a <ₛ b → b ≤ₛ c → a <ₛ c
  ≤ₛ-trans (sim h) k = sim (λ r → <≤-trans (h r) k)
  <≤-trans (lt rb h′) (sim k) with k rb
  ... | lt rc k′ = lt rc (≤ₛ-trans h′ k′)

  <→≤ : ∀ {a b} → a <ₛ b → a ≤ₛ b
  <→≤ (lt rb (sim h)) = sim (λ r → lt rb (<→≤ (h r)))

  -- 直接子树低于整体
  sub≤ : ∀ {a b} → R a b → a ≤ₛ b
  sub≤ {a} r = <→≤ (lt r (≤ₛ-refl a))

  ≤<-trans : ∀ {a b c} → a ≤ₛ b → b <ₛ c → a <ₛ c
  ≤<-trans h (lt rc k) = lt rc (≤ₛ-trans h k)
```

## §2 良基

$P(b)$: 一切 $a\sqsubseteq b$ 可及. 对 $b$ 的 $R$-可及性归纳: $c\sqsubset a$ 给 $c\sqsubseteq a'$, $a' R a$; $a\sqsubseteq b$ 给 $a'\sqsubseteq b'$, $b' R b$; 传递得 $c\sqsubseteq b'$, 归纳假设.

```agda
  <ₛ-acc : ∀ b → Acc R b → ∀ {a} → a ≤ₛ b → Acc _<ₛ_ a
  <ₛ-acc b (acc rs) (sim h) = acc (λ { (lt ra c≤) → step (h ra) c≤ })
    where
    step : ∀ {a′ c} → a′ <ₛ b → c ≤ₛ a′ → Acc _<ₛ_ c
    step (lt rb a′≤) c≤ = <ₛ-acc _ (rs rb) (≤ₛ-trans c≤ a′≤)

  <ₛ-wf : WellFounded _<ₛ_
  <ₛ-wf a = <ₛ-acc a (wfR a) (≤ₛ-refl a)
```
