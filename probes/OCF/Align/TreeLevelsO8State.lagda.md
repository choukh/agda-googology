# TreeLevels O8：整格模拟停在原实际高层状态

`TreeLevelsO8Cell.cell-in-context` 已经展开 `nκ`，并模拟它的一整格
（包括极限世界）。接到原闭项时仍不能只用这个精确模拟：下一外层
运行的初始状态是原 Y₁ = Y₀ ⊕ Δ₀，其目标 1 分量保留 `nκ`。
本篇证明这个**实际状态**不具有旧 `SumOneSim.Inv`，即使右边允许
任取旧树 b : O M。因此停止点是状态关系的表达范围，不是
`Walk` 的后继或极限行没写。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO8State where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; O; Lg; _⊲_; self)
open import OCF.Align.SumOneTree using (Dl; Zy; cnt; nκ; _⨾_)
open import OCF.Align.SumOneRel using (Rl; rc; rb; rr)
open import OCF.Align.SumOneSim using (Inv; un)
import OCF.Align.SumOneClosed as S

data Hasκ {ly} : ∀ {W} → Dl ly W → Set where
  hit : ∀ {W} {u : ∀ {c} → W ⊲ c → Lg c → Dl ly c} {zz : Zy ly} → Hasκ (nκ {W = W} zz u)
  left : ∀ {W} {a b : Dl ly W} → Hasκ a → Hasκ (a ⨾ b)
  right : ∀ {W} {a b : Dl ly W} → Hasκ b → Hasκ (a ⨾ b)

reject-κ-trace : ∀ {ly M W b y} {x : Dl ly W} → Hasκ x → Rl ly M b x y → ⊥
reject-κ-trace (left h) (rc d e) = reject-κ-trace h d
reject-κ-trace (right h) (rc d e) = reject-κ-trace h e
reject-κ-trace h (rb _ _ d) = reject-κ-trace h d
reject-κ-trace h (rr d _ _) = reject-κ-trace h d

seed-has-κ : Hasκ {cnt S.one} (S.yc (S.d S.Y₁) (inj₁ self) tt)
seed-has-κ = right (right (right hit))

no-seed-old-Inv : ∀ {M} → S.one ⊲ M → Lg M → (b : O M) → ¬ Inv S.Y₁ b
no-seed-old-Inv p lM b inv =
  reject-κ-trace seed-has-κ (un inv (inj₁ self) tt (inj₁ p) lM)
```

前提可满足：取 M = one、位置 `self`、合法性 tt、b = o0。
原 `Y₁` 是现成构造，不是假设出来的状态。定理仅否定旧 `Inv` 的
这一次实填；没有否定新的单向值模拟、不同步取参照链项或吸收。
它不是 `T₁` 的序数值上界，也没有给出 `T₁` 超过所求上界的反例。
