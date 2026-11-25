# 对齐布劳威尔树壁垒（验收定理）
编译条件定理：精确的 Ordᴰ 初始段与其共尾顶元，加有界全派发即推出 LPO；全域及结点覆盖版均由它导出。
复用 `Barrier.barrier`，不重证开关序列。每个字段逐字填入 `Ω-Extension`。
不带派发的前提由 `Barrier.Naive` 实填，先在临时文件编译；联合派发前提不在本路无条件实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDBarrier where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiTDIface
import OCF.Barrier as B
open import OCF.BTBO using (module BoundedTrich)
module D = BoundedTrich

record ExactTop (F : Frame) : Set where
  open Frame F
  field
    ι : D.Ordᴰ → A
    ι-mono : ∀ {a b} → a D.< b → ι a < ι b
    ι-exact : ∀ {f : ℕ → D.Ordᴰ} {mono : D.monotonic f} {z} →
      z < ι (D.lim f mono) → Σ ℕ λ n → z < ι (f n)
    top : A
    ι<top : ∀ a → ι a < top

naive-frame : Frame
naive-frame = record
  { A = B.Naive.Ord₁
  ; _<_ = B.Naive._<₁_
  ; trans = B.Naive.<₁-trans
  ; irrefl = B.Naive.<₁-irrefl }

naive-base : ExactTop naive-frame
naive-base = record
  { ι = B.Naive.embed
  ; ι-mono = B.Naive.embed-mono
  ; ι-exact = B.Naive.embed-exact
  ; top = B.Naive.top
  ; ι<top = B.Naive.embed<top }

module Gate (F : Frame) where
  open Frame F
  open On F

  Bounded : A → A → Set
  Bounded x y = Σ A λ u → (x < u) × (y < u)

  reorder : ∀ {x y} → Answer x y → (x < y) ⊎ ((y < x) ⊎ (x ≡ y))
  reorder (inj₁ p) = inj₁ p
  reorder (inj₂ (inj₁ e)) = inj₂ (inj₂ e)
  reorder (inj₂ (inj₂ q)) = inj₂ (inj₁ q)

  extension : ExactTop F → Evidence Bounded → B.Ω-Extension
  extension X C = record
    { I = A
    ; _<ᴵ_ = _<_
    ; <ᴵ-trans = trans
    ; <ᴵ-irrefl = irrefl
    ; ι = ExactTop.ι X
    ; ι-mono = ExactTop.ι-mono X
    ; ι-exact = ExactTop.ι-exact X
    ; top = ExactTop.top X
    ; ι<top = ExactTop.ι<top X
    ; <ᴵ-dec = λ {a} {b} {c} p q → reorder (Evidence.answer C a b (Evidence.provide C a b (c , p , q))) }

  bounded→LPO : ExactTop F → Evidence Bounded → B.LPO
  bounded→LPO X C = B.barrier (extension X C)

  global→LPO : ExactTop F → Evidence Global → B.LPO
  global→LPO X C = bounded→LPO X record
    { E = Evidence.E C
    ; answer = Evidence.answer C
    ; provide = λ x y _ → Evidence.provide C x y tt }

  BoundedCovers : Nodes → Set
  BoundedCovers N = ∀ {x y u} → x < u → y < u → Scope N x y

  covered→LPO : ExactTop F → (N : Nodes) → Evidence (Scope N) → BoundedCovers N → B.LPO
  covered→LPO X N C cover = bounded→LPO X record
    { E = Evidence.E C
    ; answer = Evidence.answer C
    ; provide = λ x y → λ { (u , p , q) → Evidence.provide C x y (cover p q) } }

```
