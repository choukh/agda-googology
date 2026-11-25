# 实际第 1 前缀的两次剥后继
不读记号；编译定理：目标第 1 前缀的实际上下文从第 4 层剥到第 2 层，β 值界成立。
来源：YiOGState 的保持律与 YiOGPeel；两个 Anchor 都已实填。
SameLevelMissing 是未填的跨底值界，不声明 ActualMissing、Offset 或 Cover。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGActual where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOGState as St
import OCF.Lean.YiOGPeel as Peel
module G = St.G
module T = St.T
module D₃ = Peel.At (C.h 0) (proj₂ St.oh 1) (T.base-at 1) (T.start-at 1) (P.z≤ (C.h 0))
module D₂ = Peel.At (C.g 1) (proj₂ (proj₂ St.oh 1) tt)
  (λ i u → T.base-at 1 i (P.inc tt u)) (T.start-at 1) (P.z≤ (C.g 1))
anchor₃ : D₃.Anchor
anchor₃ = B.◃t (St.target-base-growth 0 (C.h 0) (P.inc tt P.self)) (B.◃t (B.◃l 0) B.◃s)
anchor₂ : D₂.Anchor
anchor₂ = B.◃t (St.target-base-growth 0 (C.g 1) (P.inc tt (P.inc tt P.self))) (B.◃t (B.◃l 0) B.◃s)
second-prefix-peel : V.val B.zero (proj₁ D₂.low) V.≼ V.val B.zero (proj₁ (T.piece 1))
second-prefix-peel = subst (λ y → V.val B.zero (proj₁ D₂.low) V.≼ V.val B.zero (proj₁ y))
  (sym (T.state-row 1)) (V.≼-trans (D₂.peel anchor₂) (D₃.peel anchor₃))
beta-one : V.val B.zero (proj₁ (G.start-at 1)) V.≼ V.val B.zero (proj₁ (T.start-at 1))
beta-one = subst₂ (λ x y → V.val B.zero (proj₁ x) V.≼ V.val B.zero (proj₁ y))
  (sym (St.source-start-next 0)) (sym (St.target-start-next 0)) St.A.first

SameLevelMissing : Set
SameLevelMissing = V.val B.zero (proj₁ (G.piece 1)) V.≼ V.val B.zero (proj₁ D₂.low)
second-from-same : SameLevelMissing → V.val B.zero (proj₁ (G.piece 1)) V.≼ V.val B.zero (proj₁ (T.piece 1))
second-from-same p = V.≼-trans p second-prefix-peel
```
