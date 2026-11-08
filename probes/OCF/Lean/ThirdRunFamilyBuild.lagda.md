# 真实有界运行族与逐目标反馈世界

本篇先实填原 Φ 的参数族，再以该族的实际输出计算反馈界。
这不是新折叠：原 Er 的坐标损失仍在。新增接线不需要界外目标，不以
预给地板填充输出。结果是按 (目标、路径、种子) 索引的局部世界族，
不是已经组装成原 Sb 下一底的一个全组件世界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRunFamilyBuild where
open import Data.Nat using (ℕ; zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
open import OCF.Lean.ThirdLeg using (wT; lwT)
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.ThirdRichWorldSections as Worlds
import OCF.Lean.ThirdRunFamilyIf as Shared
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.ThirdSan as San

module Run (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w)
  (fb : HB (Sb n)) (M : HB (Sb n)) (lm : LgB M)
  (h : HB (Tw (Sb n) M)) (nd : Fold.Gd (Sb n) w lw M h) where
  module F = Fold (Sb n) w lw
  module E = San (Sb n) w lw fb
  module R = F.F E.Er
  module I = Shared.Source n w lw fb M lm

  actual : I.RunFamily h nd
  actual = record
    { run = λ t pt b → R.Φ M (R.wfC M) lm t pt b h nd
    ; exact = λ t pt b → refl
    ; shape = λ t pt b → R.Sh-Φ M (R.wfC M) lm t pt b h nd }
  open I.RunFamily actual public

  output : ∀ t → t ⊲[ w ] M → F.GT t → HB (Tw (Sb n) t)
  output t pt b = proj₁ (run t pt b)

  focus : ∀ t pt b → output t pt b ≡ proj₁ (R.Φ M (R.wfC M) lm t pt b h nd)
  focus t pt b = refl

  -- 不是把 Sh 当高层合法性：明确调用同类型的富合法化。
  normal : ∀ t → t ⊲[ w ] M → F.GT t → HB (Tw (Sb n) t)
  normal t pt b = Rich.legT n t (output t pt b)
  legal-normal : ∀ t pt b → LgB (normal t pt b)
  legal-normal t pt b = Rich.Lg-legT n t (output t pt b)

  module At (t : HB (Sb n)) (pt : t ⊲[ w ] M) (b : F.GT t)
    (B : HB (Tw (Sb n) t)) (lB : LgB B) where
    feedback : HB (Tw (Sb n) t)
    feedback = B ⊞ normal t pt b
    legal-feedback : LgB feedback
    legal-feedback = Lg-⊞ B (normal t pt b) lB (legal-normal t pt b)
    before after : Wd (step (Tw (Sb n) t))
    before = wT (Sb n) w t , B
    after = wT (Sb n) w t , hs feedback
    legal-before : LgW (step (Tw (Sb n) t)) before
    legal-before = lwT (Sb n) w lw t , lB
    legal-after : LgW (step (Tw (Sb n) t)) after
    legal-after = lwT (Sb n) w lw t , legal-feedback
    grows : _≤w_ (step (Tw (Sb n) t)) before after
    grows = Worlds.rfT (Sb n) (Worlds.rfS n) t (wT (Sb n) w t) , hsuc (⊞-fst B (normal t pt b))
    admitted : Bd (step (Tw (Sb n) t)) (inj₂ tt) feedback after
    admitted = hsuc hself

-- 底 n=0 的目标零，才可由 Sh 直接得到标准 Cd 合法性。
module Countable (M : Cd) (lm : LgB M)
  (h : HB (Tw S⊥ M)) (nd : Fold.Gd S⊥ tt tt M h) where
  module A = Run zero tt tt hz M lm h nd
  sh-legal : ∀ (a : Cd) → A.R.Sh a → LgB a
  sh-legal hz sa = tt
  sh-legal (hs a) sa = sh-legal a sa
  sh-legal (hl f) (st , sf) = (λ n → st n) , (λ n → sh-legal (f n) (sf n))
  sh-legal (hΩ () _) sa
  output-legal : ∀ (pt : hz ⊲ M) b → LgB (A.output hz pt b)
  output-legal pt b = sh-legal _ (A.shape hz pt b)

-- 全底的真实非零原输入；输出仍逐字由旧 Φ 计算，而非给定地板。
module SuccessorInput (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w) where
  module A = Run n w lw hz (hs hz) tt (hs hz) tt
  seed : A.F.GT hz
  seed = hz , tt
  output = A.output hz (hsuc hself) seed
  module Updated = A.At hz (hsuc hself) seed hz tt
  actual-feedback-admitted = Updated.admitted
  actual-world-legal = Updated.legal-after
```

剩余类型义务是把这些带路径的局部世界组装回原源的世界，并给出
原运行证书在新世界中的搬运。这里没有 `t⊲M` 的判定，也没有
`∀m` 的界外输出；故不能直接满足上一轮不受限 `Section`。
尤其原 `GT` 只有 `Gd`，不是 LgB；若下一次仍用旧 Φ，需要为合法化后的
输出另证 Gd/路径搬运，当前准入定理没有偷含这一结论。
