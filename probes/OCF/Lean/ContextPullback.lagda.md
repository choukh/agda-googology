# 从共同包含结构拉回分量世界

给定每个分量在同一结构 T 内的上下文，把分量世界定义为 T 世界的
投影，而不先允许任意独立分量世界、再要求拷贝相干。下标 I 不作判等
或比较；应用时由有字面公共界的包含上下文提供本模块的参数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ContextPullback where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC; toC; frto; pw; lgpw; bdTo; bdFr; prFr)

world-mono : ∀ {T S} (c : Ctx T S) {w v} → _≤w_ T w v → _≤w_ S (pw c w) (pw c v)
world-mono here p = p
world-mono (viaS c) p = proj₁ (world-mono c p)
world-mono (viaL c i) p = world-mono c p i

module Pull {I : Set} (F : I → KS) (T : KS) (ctx : ∀ i → Ctx T (F i)) where
  S : KS
  S = record
    { K = Σ I (λ i → K (F i))
    ; E = λ k → E (F (proj₁ k)) (proj₂ k)
    ; Wd = Wd T ; LgW = LgW T
    ; _≤w_ = _≤w_ T ; ≤w-tr = ≤w-tr T
    ; Bd = λ k e W → Bd (F (proj₁ k)) (proj₂ k) e (pw (ctx (proj₁ k)) W)
    ; Pr = λ k W → Pr (F (proj₁ k)) (proj₂ k) (pw (ctx (proj₁ k)) W)
    ; Bd↑ = λ {k} p b → Bd↑ (F (proj₁ k)) (world-mono (ctx (proj₁ k)) p) b
    ; cmpK = λ {k} b b′ l → cmpK (F (proj₁ k)) b b′ (lgpw (ctx (proj₁ k)) l)
    ; bot = λ k → bot (F (proj₁ k)) (proj₂ k)
    ; botBd = λ k W → botBd (F (proj₁ k)) (proj₂ k) (pw (ctx (proj₁ k)) W) }

  embed : HB S → HB T
  embed hz = hz
  embed (hs a) = hs (embed a)
  embed (hl f) = hl (λ n → embed (f n))
  embed (hΩ (i , κ) g) = hΩ (ek (ctx i) κ) (λ c → embed (g (frC (ctx i) κ c)))

  embed-position : ∀ {a b W} → a ⊲[ W ] b → embed a ⊲[ W ] embed b
  embed-position hself = hself
  embed-position (hsuc p) = hsuc (embed-position p)
  embed-position (hlim n p) = hlim n (embed-position p)
  embed-position {a} {hΩ (i , κ) g} {W} (hLim {c = c} b p) =
    hLim (bdTo (ctx i) κ b)
      (subst (λ d → embed a ⊲[ W ] embed (g d))
        (sym (frto (ctx i) κ c)) (embed-position p))

  embed-legal : ∀ a → LgB a → LgB (embed a)
  embed-legal hz l = l
  embed-legal (hs a) l = embed-legal a l
  embed-legal (hl f) (st , l) =
    (λ n → embed-position (st n)) , (λ n → embed-legal (f n) (l n))
  embed-legal (hΩ (i , κ) g) (mo , l) =
    (λ lw b b′ p → embed-position
      (mo lw (bdFr (ctx i) κ b) (bdFr (ctx i) κ b′) (prFr (ctx i) κ p))) ,
    (λ lw b → embed-legal (g _) (l lw (bdFr (ctx i) κ b)))
```

结论包括任意返回整个合并类型的分支，不把分支伪装成返回自身分量。
源/目标世界字面相同，Bd/Pr 搬运由已有 Ctx 定理给出；没有升界更新。
这不是任意积世界的替代同构，也没有证明随着共同界改变的相容性。
本模块的合法性结果不包含序数强度；实际参数实例由 BoundedContext 系列交付。
