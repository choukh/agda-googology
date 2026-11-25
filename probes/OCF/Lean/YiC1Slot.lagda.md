# 实际第 2 链点的 Ω 截段与未填分支关系
验收文件；编译定理：指定极限路径的截段不高于 child-feed，分支关系的量化域非空。
头构造子为 Ω、其第 0 分支为 ℕ 极限是指定闭项形状测试；BranchNeed 尚未构造。
不声称 NextSlot、零层 RowOneAtTwo 或新的序数值下界；构造子重建等式试验在同限改写后仍耗尽，依停止条件停报。
来源：对象复用 YiC0Next，⊴ 传递复用 YiKCStep；cut-below 对指定极限路径递归。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC1Slot where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiKCStep as KC
import OCF.Align.EboLeanDef as E
cut : ∀ {ℓ} → List ℕ → B.Tr ℓ → B.Tr ℓ
cut [] x = x
cut (n ∷ ns) (B.lim f a) = cut ns (f n)
cut (n ∷ ns) x = x
Steps : ∀ {ℓ} → List ℕ → B.Tr ℓ → Set
Steps [] x = ⊤
Steps (n ∷ ns) (B.lim f a) = Steps ns (f n)
Steps (n ∷ ns) B.zero = ⊥
Steps (n ∷ ns) (B.suc x) = ⊥
Steps (n ∷ ns) (B.Ω p g) = ⊥
Steps (n ∷ ns) (B.up x c y e) = ⊥
cut-below : ∀ {ℓ} (ns : List ℕ) (x : B.Tr ℓ) → Steps ns x → K._⊴_ (cut ns x) x
cut-below [] x s = K.⊴r
cut-below (n ∷ ns) (B.lim f a) s = KC.⊴-trans (cut-below ns (f n) s) (K.⊴◃ (B.◃l n))
cut-below (n ∷ ns) B.zero ()
cut-below (n ∷ ns) (B.suc x) ()
cut-below (n ∷ ns) (B.Ω p g) ()
cut-below (n ∷ ns) (B.up x c y e) ()
path : List ℕ
path = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
br : B.Tr K.one → B.Tr B.zero → B.Tr K.one
br (B.Ω (inj₂ (tt , inj₁ tt)) g) d = g d
br (B.Ω (inj₁ ()) g) d
br (B.Ω (inj₂ (tt , inj₂ ())) g) d
br x d = B.zero
-- perf: S-1/C-10，实际截段及分支函数在出生处封装；不以大树等式比较两种颈结点写法。
opaque
  unfolding C.neck-path C.c₁ U.Inner.feed U.Inner.g
  kept : B.Tr K.one
  kept = cut path (proj₁ N.child-feed)
  branch : B.Tr B.zero → B.Tr K.one
  branch d = br kept d
  valid : Steps path (proj₁ N.child-feed)
  valid = tt
data Head : Set where
  hz hs hl hΩ hu : Head
head : ∀ {ℓ} → B.Tr ℓ → Head
head B.zero = hz
head (B.suc x) = hs
head (B.lim f a) = hl
head (B.Ω p g) = hΩ
head (B.up x c y e) = hu
opaque
  unfolding C.c₁ U.Inner.feed U.Inner.g
  cut-isΩ : head (cut path (proj₁ N.child-feed)) ≡ hΩ
  cut-isΩ = refl
  branch-zero-head : head (br (cut path (proj₁ N.child-feed)) B.zero) ≡ hl
  branch-zero-head = refl
actual-below : K._⊴_ (cut path (proj₁ N.child-feed)) (proj₁ N.child-feed)
actual-below = cut-below path (proj₁ N.child-feed) valid
BranchNeed : Set
BranchNeed = ∀ η d → K.M⁰ η d → H.M 1 (E.fsT N.slot η) (branch d)
domain₀ : K.M⁰ [] B.zero
domain₀ = K.mz
domain₁ : K.M⁰ (E.natT 1) (B.suc B.zero)
domain₁ = K.m1 refl K.mz
```
