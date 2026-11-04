> **机械改写, 验收用.** 由 [LadderLabBase](LadderLabBase.lagda.md) 经 `Survey/scripts/ordlab/mk_rebase.py` 生成: 只改模块名与导入, 克隆的证书 `LadderLabZInfW*` 换成主线 `LadderInf*`. 见 [OrdLab](OrdLab.lagda.md). 下面的文字是原文.

# 高度上的标签 (一): 前缀结构 `PxS`

> **判决: HOLDS (只有声明).** 结论写在 [OrdLab](OrdLab.lagda.md). 标签类对高度结构 `HtS` 抽象之后, 记号一侧唯一的新数据是前缀映射 `P : Ht → T → T`: 高度 $m$ 上层号 $\alpha$ (标签 $\nu$) 的节点标 $\Omega_{P\,m\,\nu}$. 实例在 [LadderLabInst](LadderLabInst.lagda.md): $\mathtt{fin}\,n\mapsto\Omega\cdot(n+1)+\nu$, $\mathtt{top}\,n\mapsto\psi_1(1)+\Omega\cdot n+\nu$. 字段都是记号上的等式, 证明都是 `refl` 级或对 $n$ 的小归纳; 闭包定理不看实例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.EBO as E
open E using (T; natT; fsn; fsT; cof; pred; cω; cΩ; sucT; cmpᵀ; lt; gt) renaming (ψ to ψᵗ)
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderLabZStandardOmega using (Ω₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; TailOf)
open import OCF.Align.OrdLabZDecouple using (Idx)

module _ (𝕊 : HtS) where
  open HtS 𝕊

  -- 第 0 行的三种写法各自要的记号事实
  data Row₀ (P : Ht → T → T) : (m : Ht) → View _<ᴸ_ h₀ m → Set where
    rb : P h₀ [] ≡ Ω₁ ∷ [] → Row₀ P h₀ base
    rc : ∀ {m n} (q : n <ᴸ m) → cof (P m []) ≡ cΩ [] → (∀ θ → fsT (P m []) θ ≡ P n θ) → Row₀ P m (clos q)
    rl : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs)

  record PxS : Set where
    field
      P       : Ht → T → T
      P-cof   : ∀ m w ws → cof (P m (w ∷ ws)) ≡ cof (w ∷ ws)
      P-pred  : ∀ m w ws → pred (P m (w ∷ ws)) ≡ P m (pred (w ∷ ws))
      P-fsn   : ∀ m w ws k → fsn (P m (w ∷ ws)) k ≡ P m (fsn (w ∷ ws) k)
      P-tail  : ∀ m τ → TailOf τ (P m τ)
      P-occ   : ∀ m τ → Occ (natT 1) (P m τ)
      -- 可数对前缀恒 lt, 反之恒 gt
      P-lt    : ∀ m τ {ν} → Idx ν → cmpᵀ (sucT ν) (P m τ) ≡ lt
      P-gt    : ∀ m ν {w} → Idx w → cmpᵀ (sucT (P m ν)) w ≡ gt
      -- 同高度比较尾巴, 不同高度由高度定
      P-cmp≡  : ∀ m ν τ → cmpᵀ (sucT (P m ν)) (P m τ) ≡ cmpᵀ (sucT ν) τ
      P-cmp-lt : ∀ {n H ν} τ → n <ᴸ H → Idx ν → cmpᵀ (sucT (P n ν)) (P H τ) ≡ lt
      P-cmp-gt : ∀ {n H} ν {τ} → H <ᴸ n → Idx τ → cmpᵀ (sucT (P n ν)) (P H τ) ≡ gt
      -- 第 0 行
      P-row   : ∀ m → Row₀ P m (view m)
```
