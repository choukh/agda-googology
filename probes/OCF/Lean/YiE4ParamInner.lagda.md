# 参数表下的实际内层整行
验收文件；对任意 r，实际q1输出与输运后的内层整行相等。
孩子0的表取 r 的对应分量；来源：YiE4Inner；不改变树、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4ParamInner where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4Inner as I
module At (r : TB.Rb B.Λ) where
  module D = R.At r
  k = B.tw 2
  -- perf: S-1，孩子0的表必须来自 table 3 的孩子分量，不换成 table 2。
  opaque
    base₀ : F.Base k
    base₀ = D.restricted B.zero
    base₀-eq : base₀ ≡ D.restricted B.zero
    base₀-eq = refl
    branch : B.Tr (B.tw 1) → B.Tr k
    branch d = proj₁ (TB.ψ k (P.Ok-tw 2) (D.Step.child-table 2 B.zero) base₀ k P.self
      (D.baseᴱ 3 k (P.ink P.self)) (D.Step.g 1 d))
    branch-eq : branch ≡ (λ d → proj₁ (TB.ψ k (P.Ok-tw 2) (D.Step.child-table 2 B.zero) base₀ k P.self
      (D.baseᴱ 3 k (P.ink P.self)) (D.Step.g 1 d)))
    branch-eq = refl
  a : B.Tr (B.tw 1) → B.L
  a d = k B.⊕ B.↑ k (branch d)
  h = B.nd (B.sΩ (B.tw 1)) a
  -- perf: C-24/S-13，形状只在一处开放函数体，折叠底仍封装。
  opaque
    unfolding D.c₁ D.Step.feed D.Step.g D.restricted base₀ branch
    c₁-shape : D.c₁ ≡ B.Ω (inj₁ (inj₁ tt)) branch
    c₁-shape = refl
  h-eq : D.Step.child 2 D.c₁ ≡ h
  h-eq = cong (D.Step.child 2) c₁-shape
  -- perf: S-1，形状输运后的底也是函数出生处；表同样输运自 r 的孩子分量。
  opaque
    o : P.Ok h
    o = subst P.Ok h-eq (proj₂ (P.Ok-tw 3) D.c₁)
    rr : TB.Rb h
    rr = subst TB.Rb h-eq (D.Step.child-table 2 D.c₁)
    base₁ : F.Base h
    base₁ = subst F.Base h-eq (D.restricted D.c₁)
    base₁-eq : base₁ ≡ subst F.Base h-eq (D.restricted D.c₁)
    base₁-eq = refl
    ctx-shape : D.make D.c₁ ≡ (h , o , rr , base₁)
    ctx-shape = I.shift-ctx (D.Step.child 2 D.c₁) h h-eq (proj₂ (P.Ok-tw 3) D.c₁)
      (D.Step.child-table 2 D.c₁) (D.restricted D.c₁)
  module Inner = I.Inner (B.tw 1) a o rr base₁ D.β
  -- perf: C-9，输出经环境等式输运，后段只使用已封装对象。
  first-row : D.output ≡ O.limc⁺ (λ n → Inner.out (Inner.chain n))
  first-row = trans D.output-eq (trans (cong (λ d → Q.collapse d D.β) D.ctx-eq)
    (trans (cong (λ d → Q.collapse d D.β) ctx-shape) Inner.row))
```
