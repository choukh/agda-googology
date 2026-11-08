# 实际决定的两份目标拷贝不能共用一套输入世界

只否定冻结的 View 接口。共同高度 B=t=lim(const 1)，源分量为 1，
其路径使用第1项；实际新种类沿此路径保留到第1拷贝，而底种类由
base-kind 保留到第0拷贝。两目标拷贝的底界分别是0和1。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeViewNegCopies where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecFl using (Lg-up)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeViewIf

one : Cd
one = hs hz
B : Cd
B = hl (λ _ → one)
legal-B : LgB B
legal-B = (λ n → hself) , (λ n → tt)
pc : one ⊲ B
pc = hlim 1 hself

D : HB (Native hz)
D = hΩ (inj₂ tt) up
legal-D : LgB D
legal-D =
  (λ lw b b′ p → up-path p) ,
  (λ lw b → Lg-up _ (lgB⊲ b (proj₁ lw) (proj₂ lw)))
  where
  up-path : ∀ {a b : Cd} {w} → a ⊲ b → up a ⊲[ w ] up b
  up-path hself = hself
  up-path (hsuc p) = hsuc (up-path p)
  up-path (hlim n p) = hlim n (up-path p)

W : Wd (Native B)
W zero = (tt , hz) , hz
W (suc n) = (tt , one) , D
legal-W : LgW (Native B) W
legal-W zero = (tt , tt) , tt
legal-W (suc n) = (tt , tt) , legal-D

one-to-D : hs {S = Native hz} hz ⊲[ (tt , one) ] D
one-to-D = hLim hself hself

no-one-zero : ∀ {w : Wd (Native hz)} → hs {S = Native hz} hz ⊲[ w ] hz → ⊥
no-one-zero ()

no-view : View legal-B one pc B hself W → ⊥
no-view view = impossible path
  where
  V = View.input-world view
  old-law = View.node-laws view (inj₁ (inj₂ tt))
  new-law = View.node-laws view (inj₂ tt)

  path : hs {S = Native hz} hz ⊲[ proj₁ V ] D
  path = proj₁ (proj₂ new-law) (hs hz) D one-to-D hself one-to-D

  impossible : hs {S = Native hz} hz ⊲[ proj₁ V ] D → ⊥
  impossible (hLim {c = e} b p) with proj₂ (proj₂ old-law) e b
  ... | .hz , refl , hself = no-one-zero p
```

legal-B、pc、hself 与 legal-W 给出全部实际前提。证明只使用实际 keep 的
Pr 律和反向 Bd 律，不要求两条路径相等，也不要求任意两个裸下标可比。
本定理不否定 NativeRun 输出合法、目标0特例、或采用更窄视图的下降路线。
翻译账：新增已有决定规则的世界律否定，未改变种类选择、树或运行器。
