# γ 接线所需的坐标包与 InvD 局部保持

本篇只补本轮要用的树侧接口，不定义 ψ。γ 的点从构造起就是当前层的
Raw 坐标，带原 Gd 守卫；它的合法树读回与 InvD 另存于同一包。
因此不先生成任意 Level，再要求把它编码回固定 Raw 层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGammaBase where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.LevelFixCore using (Raw; Gd)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxStep as S
open import OCF.Align.YiDBase

same-tree-inv : ∀ {D E} (x y : Y.Level) → Y.tree x ≡ Y.tree y →
  InvD D E x → InvD D E y
same-tree-inv (Y.level x lx) (Y.level .x ly) refl i =
  demanded (context i) (needed i)

start : ∀ D → InvD D (Y.zero ∷ []) S.Ω₁
start D = demanded (K.context S.start) λ where
  f (here refl) d → zero-common (dispatch S.Ω₁ f)
  f (there ()) d

pred-inv : ∀ {D E} (x : Y.Level) → InvD D E (Y.suc x) → InvD D E x
pred-inv x i = demanded (context i) (λ f p d → needed i (K.in-suc f) p d)

suc-inv : ∀ {D E} (x : Y.Level) → InvD D E x → InvD D E (Y.suc x)
suc-inv x i = demanded (context i) λ where
  (K.in-suc f) p d → needed i f p d

branch-lawful : ∀ {k c t g} → V.Legal (F.lc k c t g) → ∀ η e → V.Legal (g η e)
branch-lawful (lk , first , mono , same , lt , lg) η e = lg η e

enter-inv : ∀ {D E k c t g} (lawful : V.Legal (F.lc k c t g)) →
  InvD D E (Y.level (F.lc k c t g) lawful) → ∀ η e →
  InvD D E (Y.level (g η e) (branch-lawful lawful η e))
enter-inv lawful i η e = demanded (context i)
  (λ f p d → needed i (K.in-branch η e f) p d)

record Point (ν : Y.Level) : Set where
  constructor point
  field
    raw : Raw (Y.tree ν)
    admitted : Gd (Y.tree ν) (V.cO (Y.tree ν)) raw
open Point public

read-point : ∀ ν → Point ν → Y.Level
read-point ν p = Y.level (V.up (Y.tree ν) (raw p))
  (V.lgl→Legal (Y.tree ν) (Y.legal ν) (raw p) (proj₂ (admitted p)))

record Certified (D : Demand) (E : List Y.Level) (ν : Y.Level) : Set where
  constructor certified
  field
    coordinate : Point ν
    invariant : InvD D E (read-point ν coordinate)
open Certified public

seed : ∀ ν → Point ν
seed ν = point (V.cO (Y.tree ν)) (inj₁ refl , V.Lgl-cO (Y.tree ν))

seed-read : ∀ ν → Y.tree (read-point ν (seed ν)) ≡ Y.tree (Y.Ω ν)
seed-read (Y.level F.zero lawful) = refl
seed-read (Y.level (F.suc x) lawful) = refl
seed-read (Y.level (F.lim f) lawful) = refl
seed-read (Y.level (F.lc k c t g) lawful) = refl

certify-seed : ∀ {D E} ν → InvD D E (Y.Ω ν) → Certified D E ν
certify-seed ν i = certified (seed ν)
  (same-tree-inv (Y.Ω ν) (read-point ν (seed ν))
    (sym (seed-read ν)) i)
```

Certified 只固定 γ 点必须交付的东西，不假设“存在下一包”，也没有把这个记录
或迭代一个已保 InvD 的任意函数当成 γ 保持定理。下一步仍须真正构造 Raw 输出、
守卫及新需求下的 InvD；本篇只有起点、前驱、进入原分支与种子包装。
