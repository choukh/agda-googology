# 共同上下文重定位保持既有值关系

值侧定理，不改变 ContextPullback 的构造。比较的是同一源类型中的
两棵树，不是对不同分量下标作全局比较。实际有界分量族可直接实例化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ContextPullbackValue where
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.LHRecLeg using (Ctx; toC; frC; frto)
open import OCF.Lean.ContextPullback using (module Pull)

module Value {I : Set} (F : I → KS) (T : KS) (ctx : ∀ i → Ctx T (F i)) where
  open Pull F T ctx

  embed-mono : ∀ {a b} → a ≤ᵛ b → embed a ≤ᵛ embed b
  embed-mono z≤ = z≤
  embed-mono (s≤s p) = s≤s (embed-mono p)
  embed-mono (≤s p) = ≤s (embed-mono p)
  embed-mono (l≤ p) = l≤ (λ n → embed-mono (p n))
  embed-mono (≤l n p) = ≤l n (embed-mono p)
  embed-mono {a} {hΩ (i , κ) g} (≤Ω c p) =
    ≤Ω (toC (ctx i) κ c)
      (subst (λ d → embed a ≤ᵛ embed (g d))
        (sym (frto (ctx i) κ c)) (embed-mono p))
  embed-mono {hΩ (i , κ) g} (Ω≤Ω p) =
    Ω≤Ω (λ c → embed-mono (p (frC (ctx i) κ c)))
```

本篇只证明保序，不声称反映值序或不同分量合并后的单射性。
它也不赋予任何新闭项 ψ 的读法；完整强度仍须对终点参照证明。
