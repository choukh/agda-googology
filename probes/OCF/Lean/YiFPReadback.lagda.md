# 下界读回不能直接代替精确对应
验收文件；编译否定：把 YiLSFold.notBelow 的 Corr 逐字换成 Rd，在同一规范层号 one 的 self 路径上即失败。
reads0、reads1 实填两条读回前提；只否定本项替换，不否定带局部证据的源关系、一般 NoΩ 主引理或原目标。
第一处受阻是 kpF⁼ 的默认分支所需 notBelow；状态执行与 Gd 本身已在 YiFPFrames 通过。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFPReadback where
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiGIRel as G
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiNRHit as N
import OCF.Lean.YiRWPath as P
import OCF.Align.EboLeanDef as E
one-noΩ : N.NoΩ K.one
one-noΩ = λ _ → tt
shared-bound : P._≤_ K.one K.one
shared-bound = P.self
reads0 : G.Rd K.one []
reads0 = G.c0 refl
reads1 : G.Rd K.one (E.natT 1)
reads1 = G.ca (inj₂ (refl , G.c0 refl))
read-premises : G.Rd K.one [] × G.Rd K.one (E.natT 1)
read-premises = reads0 , reads1
NotBelowAtOne : Set
NotBelowAtOne = G.Rd K.one (E.natT 1) → G.Rd K.one [] → ([] E.<ᵀ E.natT 1 → ⊥)
no-rd-notBelow : NotBelowAtOne → ⊥
no-rd-notBelow nb = nb reads1 reads0 E.[]<
```
