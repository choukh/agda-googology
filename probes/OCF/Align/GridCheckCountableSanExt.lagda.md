# 可数高度洗法的条件恒等诊断

这是第 4 层验收，**以函数外延为前提**，不进入树、折叠或合法性证书。
该前提在外延函数等式解释中成立；本文件没有给出无条件的 Agda 实例。
底为 `S⊥` 时，任意可数高度的原 `san` 只是逐构造子重建；
因此不能把目前缺少内涵相容证明读成数学上的分支缩水。
以下覆盖所有高度和所有裸树，并非只覆盖实际有限采样。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.GridCheckCountableSanExt where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
import OCF.Lean.ThirdSan as S
import OCF.Align.GridCheckCountableSan as Check

Funext : Set₁
Funext = ∀ {A B : Set} {f g : A → B} →
  (∀ x → f x ≡ g x) → f ≡ g

module Conditional (fe : Funext) (fb : Cd) where
  open S S⊥ tt tt fb using (san)
  module C = Check.At fb

  identity : ∀ (m : Cd) (a : HB (Tw S⊥ m)) → san m a ≡ a
  identity m hz = refl
  identity m (hs a) = cong hs (identity m a)
  identity m (hl f) = cong hl (fe (λ n → identity m (f n)))
  identity m (hΩ κ g) with C.sf-success m κ
  ... | p , eq rewrite eq =
    cong (hΩ κ) (fe (λ e → identity m (g e)))

  branch : ∀ (m : Cd) {A : Set} (g : HB (Tw S⊥ m) → A) a →
    g (san m a) ≡ g a
  branch m g a = cong g (identity m a)

-- 原 first 使用的地板参数，不另造运行器。
module Actual (fe : Funext) = Conditional fe hz
```

`branch` 仅在上述显式条件下允许任意函数消费恒等式；它没有证明
无条件的高层值同余，也没有把值等价穿过原折叠。去掉函数外延后，
逐枝结构关系或实际生成函数的结构归纳仍是可研究的办法，尚未在此证明。
这里没有得到 BTBO 或 EBO 下界；零叶、累计链及 Rich 完成的整链比较仍待完成。
