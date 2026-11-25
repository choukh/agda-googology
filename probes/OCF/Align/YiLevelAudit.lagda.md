# 树层号位置接口的范围：结点的层号字段不自动是第一位置

只审查本轮 `YiLevelBase` 的位置域，不写 ψ，也不改既有树或 CP。
CP 只沿后继、ℕ-分支和 Ω 结点的第一支下降；数据字段 k 与任意 g 分支
没有自动进入这个位置域。下面给整体合法的原 Ω₃ 的一个具体反例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLevelAudit where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open import OCF.Align.LevelFixVal using (CP; Legal)
import OCF.Align.YiLevelBase as Y

two three Ωthree : Y.Level
two = Y.suc (Y.suc Y.zero)
three = Y.suc two
Ωthree = Y.Ω three

two-tree : Y.tree two ≡ V.natF 2
two-tree = refl

Ωthree-tree : Y.tree Ωthree ≡ V.Ω̂ (V.natF 3)
Ωthree-tree = refl

Ωthree-form : Y.tree Ωthree ≡
  F.lc (Y.tree two) (V.cO (Y.tree two)) (V.Ω̂ (Y.tree two))
    (λ η e → V.up (Y.tree two) η)
Ωthree-form = refl

Ωthree-legal : Legal (Y.tree Ωthree)
Ωthree-legal = Y.legal Ωthree

-- 连续三个 fst 后只能到 1；再沿 suc 也到不了作为源的 2。
no-layer-field-position : CP (Y.tree two) (Y.tree Ωthree) → ⊥
no-layer-field-position (V.fst (V.fst (V.fst (V.suc ()))))

-- Position 没有把树相同的另一份合法性证明当成不同结论处理。
no-located-layer-field : (p : Y.Position Ωthree) →
  Y.tree (Y.part p) ≡ Y.tree two → ⊥
no-located-layer-field (Y.located x p) e = no-layer-field-position
  (subst (λ a → CP a (Y.tree Ωthree)) e p)
```

否定的范围仅是“lc 的任意层号字段自动成为该 lc 树的 CP 位置”。
它没有否定 Ω₃ 合法，没有否定本轮公共界比较，更没有否定未来的派发方案。
原 `Raw` 的 `Pre` 还包含层号字段和一般分支子层；将来若要比较这些下标，
须另给它们进入某个合法公共界的证据，不能把 CP 比较的量词范围扩大。

本轮不含世界更新、跨世界的界运输、高度坐标收缩、ψ 回灌或留下结点的
下层路径规则，因此没有实填交接所列五堵墙的前提，也不声称已经越过它们。
