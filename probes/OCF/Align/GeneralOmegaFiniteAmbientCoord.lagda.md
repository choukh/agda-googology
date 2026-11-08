# 固定ambient坐标读回的源同形闭包

验收辅助。只在同一原kind所指定的有限低层内运输源Ord同形；不更换
右端HB坐标，不假定坐标函数同余。具体分派的rank相等与keep/collapse
坐标映射仍由FiniteCompare提供，本篇不重做它们。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteAmbientCoord where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaFiniteAmbientIf
open import OCF.Align.GeneralOmegaFiniteRank using (nat)

coord-cong : ∀ B κ {x y c} → x L.≅ y → Coord B κ y c → Coord B κ x c
coord-cong zero () e p
coord-cong (suc B) (inj₁ κ) e p = coord-cong B κ e p
coord-cong (suc B) (inj₂ _) e p = rc e p

coord-self : ∀ B κ {x c} → Coord B κ x c → x L.≅ x
coord-self zero () p
coord-self (suc B) (inj₁ κ) p = coord-self B κ p
coord-self (suc B) (inj₂ _) p = self p

coord-cong-right : ∀ B κ {x y c} → x L.≅ y → Coord B κ x c → Coord B κ y c
coord-cong-right B κ e p = coord-cong B κ (L.≅-sym e) p

coord-tr⁻ : ∀ B κ {x c} → Coord B κ x c →
  Coord B κ (L.tr⁻ (L.≅ᴵ-refl (nat (rank B κ))) x) c
coord-tr⁻ B κ p = coord-cong B κ
  (L.tr⁻-≅ (L.≅ᴵ-refl (nat (rank B κ))) (coord-self B κ p)) p
```

前提可满足性来自AmbientIf.floor-read以及新kind处的Coord定义；
这里只消除原源坐标运输产生的同形差，不扩张任意raw输入域。
