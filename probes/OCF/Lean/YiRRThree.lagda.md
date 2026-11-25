# 前缀 3 的第一个未填分量
不读记号；工具：源前缀 3 的底在（第 3 层，`inc tt self`）的分量与拉回的目标分量的形状（`g3-self`、`t3-self`、`qs3-self`、`ps3-self`、`qt3-self`、`pt3-self`，`refl`），以及照 `YiRRTwo` 的做法这个分量的 `climb` 要的起点关系 `Obl3`（未证，也未否定）。
`Obl3` 左边是两级上折 `Up L2 … (Up L1 … (Ωt L3) (Ωt L1)) (Ωt L2)`，右边是第 4 层 Ω 树的折叠，起点是第 3 层 Ω 树的 self 折叠 `SF₃`；与前缀 2 的 `left ≼ right` 不同，右边分支里是 "折叠后的上折"，`YiRRUp.ladder` 只管 "纯上折"。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRThree where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiOGState as St
import OCF.Lean.YiTNShape as H
open import OCF.Lean.YiRRRel using (N)
```

`Qs3`, `Qt3`: 前缀 1 的折叠在前缀 3 的孩子路径上; `Ps3`, `Pt3`: 前缀 0 的. 源底在 (第 3 层, `inc tt self`) 的分量是第 3 层的 self 折叠, 起点 `Qs3`; 目标的对应分量是第 5 层的折叠, 起点 `Qt3`.

```agda

Qs3 : (i : L) → i ≤ C.g 3 → Tr⁺ i
Qs3 i w = TB.ψ St.G.ℓ C.og (MT.rbᶻ St.G.ℓ) (F.B₀ St.G.ℓ) i (inc 3 w) (Ωt i) (St.G.prefix 1)
Ps3 : (i : L) → i ≤ C.g 3 → Tr⁺ i
Ps3 i w = TB.ψ St.G.ℓ C.og (MT.rbᶻ St.G.ℓ) (F.B₀ St.G.ℓ) i (inc 3 w) (Ωt i) (St.G.prefix 0)
Qt3 : (i : L) → i ≤ C.h 3 → Tr⁺ i
Qt3 i w = TB.ψ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 3 w) (Ωt i) (St.T.prefix 1)
Pt3 : (i : L) → i ≤ C.h 3 → Tr⁺ i
Pt3 i w = TB.ψ St.T.ℓ St.oh (MT.rbᶻ St.T.ℓ) (F.B₀ St.T.ℓ) i (inc 3 w) (Ωt i) (St.T.prefix 0)
B3s : F.Base (C.g 2)
B3s i u = Qs3 i (inc tt u)
B3t : F.Base (C.h 2)
B3t i u = Qt3 i (inc tt u)
Bp : F.Base (C.h 1)
Bp i u = Pt3 i (inc tt (inc tt u))

SF₃ : Tr⁺ (C.g 2)
SF₃ = TB.ψ (C.g 2) (proj₂ St.oh 0) (MT.rbᶻ (C.g 2)) (F.B₀ (C.g 2)) (C.g 2) self (Ωt (C.g 2)) (proj₁ (Ωt (C.g 2)))

opaque
  unfolding St.G.base-at St.G.previous St.G.prefix St.G.part
  g3-self : St.G.base-at 3 (C.g 2) (inc tt self)
    ≡ TB.ψ (C.g 2) (proj₂ C.og 2) (MT.rbᶻ (C.g 2)) B3s (C.g 2) self (Qs3 (C.g 2) (inc tt self)) (proj₁ (Ωt (C.g 2)))
  g3-self = refl
  qs3-self : Qs3 (C.g 2) (inc tt self) ≡ Up (C.g 1) (down stop tt) (Ps3 (C.g 2) (inc tt self)) (proj₁ (Ωt (C.g 1)))
  qs3-self = refl
  ps3-self : Ps3 (C.g 2) (inc tt self) ≡ Up (C.g 0) (down (down stop tt) tt) (Ωt (C.g 2)) (proj₁ (Ωt (C.g 0)))
  ps3-self = refl
  qs3-full : Qs3 (C.g 2) (inc tt self)
    ≡ Up (C.g 1) (down stop tt) (Up (C.g 0) (down (down stop tt) tt) (Ωt (C.g 2)) (proj₁ (Ωt (C.g 0)))) (proj₁ (Ωt (C.g 1)))
  qs3-full = refl

opaque
  unfolding St.T.base-at St.T.previous St.T.prefix St.T.part H.first H.curve H.line
  t3-self : St.T.base-at 3 (C.g 2) (inc tt (inc tt (inc tt self)))
    ≡ TB.ψ (C.h 2) (proj₂ St.oh 2) (MT.rbᶻ (C.h 2)) B3t (C.g 2) (inc tt (inc tt self)) (Qt3 (C.g 2) (inc tt (inc tt (inc tt self)))) (proj₁ (Ωt (C.h 2)))
  t3-self = refl
  qt3-self : Qt3 (C.g 2) (inc tt (inc tt (inc tt self)))
    ≡ TB.ψ (C.h 1) (proj₂ St.oh 1) (MT.rbᶻ (C.h 1)) Bp (C.g 2) (inc tt self) (Pt3 (C.g 2) (inc tt (inc tt (inc tt self)))) (proj₁ (Ωt (C.h 1)))
  qt3-self = refl
  pt3-self : Pt3 (C.g 2) (inc tt (inc tt (inc tt self))) ≡ SF₃
  pt3-self = refl
  qt3-full : Qt3 (C.g 2) (inc tt (inc tt (inc tt self)))
    ≡ TB.ψ (C.h 1) (proj₂ St.oh 1) (MT.rbᶻ (C.h 1)) Bp (C.g 2) (inc tt self) SF₃ (proj₁ (Ωt (C.h 1)))
  qt3-full = refl
```

## 起点关系

```agda
Obl3 : Set
Obl3 = N (C.g 2) (proj₁ (Up (C.g 1) (down stop tt) (Up (C.g 0) (down (down stop tt) tt) (Ωt (C.g 2)) (proj₁ (Ωt (C.g 0)))) (proj₁ (Ωt (C.g 1)))))
             (proj₁ (TB.ψ (C.h 1) (proj₂ St.oh 1) (MT.rbᶻ (C.h 1)) Bp (C.g 2) (inc tt self) SF₃ (proj₁ (Ωt (C.h 1)))))

obl3-start : Obl3 → N (C.g 2) (proj₁ (Qs3 (C.g 2) (inc tt self))) (proj₁ (Qt3 (C.g 2) (inc tt (inc tt (inc tt self)))))
obl3-start d = subst₂ (λ x y → N (C.g 2) (proj₁ x) (proj₁ y)) (sym qs3-full) (sym qt3-full) d
```
