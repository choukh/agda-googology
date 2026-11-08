# 只沿原运行器实际访问的路径

源对象可在不同LH层中；每条边明确是后继输出、ℕ分支、真实Ω采样、
原左前缀或已证明的Coded嵌入。没有任意源第一位置或可入坐标规则。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaVisitIf where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.GeneralOmegaEmbedIf using (Coded)
import OCF.Lean.GeneralOmegaSampleRun as S
import OCF.Lean.GeneralOmegaConsumeRun as R

record Object : Set where
  constructor object
  field
    layer : LH
    tree : HB (Lv layer)
value : Object → Cd
value (object x a) = R.run x a

data Visit : Object → Object → Set₁ where
  here : ∀ a → Visit a a
  successor : ∀ {x a child} → Visit child (object x a) → Visit child (object x (hs a))
  natural : ∀ {x f child} n → Visit child (object x (f n)) → Visit child (object x (hl f))
  sampled : ∀ {x κ f child} n → Visit child (object x (S.Node.sample x κ f n)) →
    Visit child (object x (hΩ κ f))
  prefix : ∀ {x a child} b → Visit child (object x a) → Visit child (object x (a ⊞ b))
  embedded : ∀ {x y a b child} → Coded x y a b → Visit child (object x a) → Visit child (object y b)
  composed : ∀ {a b c} → Visit a b → Visit b c → Visit a c
  all-natural : ∀ {x f target} → (∀ n → Visit (object x (f n)) target) → Visit (object x (hl f)) target
```

sampled只接受原Node.sample的自然数索引，不能以任意code反馈代入。
prefix保留左端的整个原运行值，未提供从a⊞b删除a而得到b的规则。
sound须由原run证明，不是Visit字段，也没有把待证值关系当构造子。
