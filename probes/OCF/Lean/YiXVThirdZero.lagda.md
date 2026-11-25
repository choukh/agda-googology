# YiXV：实际更新底的目标层零上界
> 验收文件。编译定理 actual-upper：B3 的实际目标层 0 分量不高于 ψ₀(Ω₂)；没有 pre 2 或全链上界。
> Bound 复用 YiXVSlotSrc 的实际回灌链、YiXVSim 的第 1 层保持及部分和吸收，输入仍带 U 与字面起点证据。
> Head 在任意孩子 y 上只展开前缀派发，再代回 Ω 树，避免把整条闭链的字面相等作为值界的前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVThirdZero where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (limc≼lim)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVCarry as K
import OCF.Lean.YiXVThird as T
open import OCF.Lean.YiXVStart using (fg; e1; r1)
import OCF.Lean.YiXVSlotSrc as V
open import OCF.Lean.YiOverTwo using (Gd-γ; Inv-γ)
module Move (Comp Src : Base (suc zero))
  (b : read (b⊥ Src) ≼ L.ψ⁰ O.Ω₁)
  (s : read (bs Src zero (ins self)) ≼ L.ψ⁰ O.Ω₁) where
  module A = S.Sim Comp
  module B = S.Sim Src
  module C = H.Anchor Comp
  map : ∀ {x X} (h : A.U x X) → C.Closed h → B.U x X
  map (A.uz p q) refl = B.uz b s
  map (A.us h) c = B.us (map h c)
  map (A.uw gd h q) c = B.uw gd (map h c) q
  map (A.ul h) c = B.ul (λ n → map (h n) (c n))
  map (A.un h) c = B.un (λ a y q → map (h a y q) (c a y q))
  map (A.uu gd h q) c = B.uu gd (map h c) q


module Bound (Q : Base (suc (suc zero))) (Comp : Base (suc zero))
  (seed : S.Sim.U Comp (bs Q (suc zero) (ins self)) (O.ψ₁ (O.Ω₁ L.+ O.Ω₁)))
  (seedC : H.Anchor.Closed Comp seed)
  (zeroU : S.Sim.U Comp zero O.Ω₁) (zeroC : H.Anchor.Closed Comp zeroU)
  (b : read (b⊥ (dS (suc zero) tt tt Q zero)) ≼ L.ψ⁰ O.Ω₁)
  (s : read (bs (dS (suc zero) tt tt Q zero) zero (ins self)) ≼ L.ψ⁰ O.Ω₁) where
  Src = dS (suc zero) tt tt Q zero
  module M = Move Comp Src b s
  module A = S.Sim Src
  module C = V.Slot Q Comp seed seedC zeroU zeroC
  β = bs Q zero (ins (ins self))
  nβ = ns Q zero (ins (ins self))
  δ : Tr zero
  δ = ψs (suc (suc zero)) tt tt Q zero (ins (ins self)) β nβ (Ωt (suc (suc zero)))
  rows : ℕ → Tr zero
  rows n = ψs (suc zero) tt tt Src zero (ins self) β nβ (suc (C.c n))
  nrows : ∀ n → zero ⊢ zero ◃ rows n
  nrows n = nzs (suc zero) tt tt Src zero (ins self) β nβ (suc (C.c n))
  rowU : ∀ n → A.U (suc (C.c n)) (L.suc (C.Ref.Γ (C.Ref.ix n)))
  rowU n = A.us {x = C.c n} {X = C.Ref.Γ (C.Ref.ix n)}
    (M.map {x = C.c n} {X = C.Ref.Γ (C.Ref.ix n)} (proj₁ (C.bounds n)) (proj₂ (C.bounds n)))
  row-bound : ∀ n → read (rows n) ≼ L.ψ⁰ (C.Ref.Γ (suc (C.Ref.ix n)))
  row-bound n = ≼-trans
    (proj₂ (A.upper {x = suc (C.c n)} {X = L.suc (C.Ref.Γ (C.Ref.ix n))}
      (O.gs (Gd-γ (C.Ref.ix n))) (rowU n)))
    (R.mono⁰ (Inv-γ (C.Ref.ix n)))
  upper : read δ ≼ L.ψ⁰ (L.Ω (L.suc (L.suc L.zero)))
  upper = ≼-trans
    (limc≼lim rows nrows C.Ref.Gr row-bound C.Ref.Gr-mono C.Ref.Gr-abs)
    (l≼ (λ n → ≼l (suc (C.Ref.ix n)) (≼-refl (C.Ref.Gr n))))

module Head (B : Base (lim fg)) where
  B31 : Base (suc (suc (suc zero)))
  B31 = dL fg e1 r1 B 2 (cumΩ fg 0)
  Q : Base (suc (suc zero))
  Q = dS (suc (suc zero)) tt tt B31 zero
  w : zero ≤ lim fg
  w = inl 2 (ins (ins (ins self)))
  head : (y : Tr (suc (suc zero))) (ny : suc (suc zero) ⊢ zero ◃ y) →
    ψs (lim fg) e1 r1 B zero w (bs B zero w) (ns B zero w) (up (cumΩ fg 0) 1 y ny) ≡
    ψs (suc (suc zero)) tt tt Q zero (ins (ins self))
      (bs Q zero (ins (ins self))) (ns Q zero (ins (ins self))) y
  head y ny = refl

module Actual = Bound V.Q I.D1 K.γ₁U H.γ₁-closed I.zeroU refl I.b2 I.s2
η₀ : Tr zero
η₀ = bs T.B3 zero (ins (ins (ins self)))
partial-form : read η₀ ≡ read Actual.δ
partial-form = cong read (Head.head (B₀ (lim fg)) (Ωt (suc (suc zero))) (Ωt-nz (suc (suc zero))))
actual-upper : read η₀ ≼ L.ψ⁰ (L.Ω (L.suc (L.suc L.zero)))
actual-upper = subst (λ z → z ≼ L.ψ⁰ (L.Ω (L.suc (L.suc L.zero)))) (sym partial-form) Actual.upper
```
