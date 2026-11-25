# 统一读回域 (三): 塔第 1 项上的读法条件, 与走链一格在域内的形状

> 验收文件 (读记号). 判决: 编译定理. 第 0 层的树读回的层号 (`zero ⊕ ↑ zero x`) 与它们的槽位层上 `Raise` 无前提成立 (`raise-L⁰`, `slot-L⁰`), 所以塔第 1 项的 `SlotRaise` 无前提 (`raise-tw1`); 于是这一项上 `YiSOLow.NodeMis` 的 `kept-gt` 与 `YiSOUp.UpMis` 不再是前提, 余下 `NodeDrop`, `RebRowᵘ` 与出口条件 (`folded₁`).
> 形状档 (不是值的否定): 最小域里有一个结点, 使 `NodeDrop` 的各条关于形状与读法的前提都成立 (`drop-shape`: 层号 2 的 Ω 树, 槽位层号 1 读作 0, 目标就是槽位层, 目标读法取 1); 判断: 这一格的结论在值上成立 (同一棵树另有读法取 1 的推导), 所以它说明的是结点读法偏低, 不是掉值.
> 不给出什么: `NodeDrop`, `RebRowᵘ` 在塔第 1 项上没有实填也没有否定. 入口: [YiQVUni](YiQVUni.lagda.md), [YiQVDom](YiQVDom.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQVTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (kp)
open import OCF.Lean.YiBSBase using (rb-tw)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (cmpᵀ-refl)
open import OCF.Align.JiaAuditClosure using (cof-suc; pred-suc; cof-regular; fs-regular)
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiGTGen using (weakᴿ)
open import OCF.Lean.YiNLCtx using (prefix; rd-mono)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGLDom using (dom-top; dom-keel)
open import OCF.Lean.YiWREnd using (baseᴮ; betaᴮ; twcᴮ)
open import OCF.Lean.YiSOLow
open import OCF.Lean.YiSOEnd using (rootˢ)
open import OCF.Lean.YiSOTw1 using (root-bd1)
open import OCF.Lean.YiQVDom
open import OCF.Lean.YiQVUni
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
```

## 第 0 层的树读回的层号上的 `Raise`

`strict`: 第 0 层里 x ◃ y 时, `↑ x` 的读法 ν 给出 `↑ y` 的一个不低于 ν+1 的读法 (后继形状取 ν+1; ℕ 极限形状用树自带的相邻步进走到下一个孩子; 传递先不严格地搬一步). 递归对 y 与推导.

```agda
L⁰ : Tr zero → L
L⁰ x = zero ⊕ ↑ zero x

Up1 : L → E.T → Set
Up1 j ν = Σ E.T λ κ′ → GR.Rd j κ′ × Pen (E.cmpᵀ (E.sucT ν) κ′)

suc-rd : ∀ (b : L) {ν} → GR.Rd b ν → Up1 (nd sS (λ _ → b)) ν
suc-rd b {ν} rd = E.sucT ν , GR.ca (inj₂ (cof-suc ν , subst (GR.Rd b) (sym (pred-suc ν)) rd)) , inj₂ (cmpᵀ-refl (E.sucT ν))

strict : (y : Tr zero) {x : Tr zero} → zero ⊢ x ◃ y → ∀ {ν} → GR.Rd (L⁰ x) ν → Up1 (L⁰ y) ν
strict (suc x) ◃s rd = suc-rd (L⁰ x) rd
strict (lim f a) (◃l n) rd with strict (f (suc n)) (a n) rd
... | κ′ , rd′ , pen = κ′ , GR.rd-child sL (λ m → L⁰ (f m)) (suc n) rd′ , pen
strict y (◃t d e) rd = strict y e (rd-mono (prefix zero) (◃→⊑ zero d) rd)

raise-L⁰ : (x : Tr zero) → LvRaise (L⁰ x)
raise-L⁰ zero ()
raise-L⁰ (suc x) (inj₁ ())
raise-L⁰ (suc x) (inj₂ (tt , inj₁ tt)) nu = suc-rd (L⁰ x) nu
raise-L⁰ (suc x) (inj₂ (tt , inj₂ p)) nu with raise-L⁰ x p nu
... | κ′ , rd′ , pen = κ′ , GR.rd-child sS (λ _ → L⁰ x) tt rd′ , pen
raise-L⁰ (lim f a) (inj₁ ())
raise-L⁰ (lim f a) (inj₂ (n , inj₁ tt)) nu with strict (f (suc n)) (a n) nu
... | κ′ , rd′ , pen = κ′ , GR.rd-child sL (λ m → L⁰ (f m)) (suc n) rd′ , pen
raise-L⁰ (lim f a) (inj₂ (n , inj₂ p)) nu with raise-L⁰ (f n) p nu
... | κ′ , rd′ , pen = κ′ , GR.rd-child sL (λ m → L⁰ (f m)) n rd′ , pen
raise-L⁰ (Ω () _)
raise-L⁰ (up _ () _ _)

slot-L⁰ : (x : Tr zero) (t : Pos⁼ (L⁰ x)) → LvRaise (proj₁ (sl⁼ (L⁰ x) t))
slot-L⁰ x (inj₁ _) = raise-L⁰ x
slot-L⁰ zero (inj₂ ())
slot-L⁰ (suc x) (inj₂ (inj₁ ()))
slot-L⁰ (suc x) (inj₂ (inj₂ (tt , t))) = slot-L⁰ x t
slot-L⁰ (lim f a) (inj₂ (inj₁ ()))
slot-L⁰ (lim f a) (inj₂ (inj₂ (n , t))) = slot-L⁰ (f n) t
slot-L⁰ (Ω () _) (inj₂ _)
slot-L⁰ (up _ () _ _) (inj₂ _)

raise-tw1 : SlotRaise (tw 1)
raise-tw1 (inj₁ (inj₁ tt)) ()
raise-tw1 (inj₁ (inj₂ ()))
raise-tw1 (inj₂ (c , t)) = slot-L⁰ c t
```

## 塔第 1 项: 余下的前提

```agda
module Tw1 (𝒟 : Domˢ) (nd′ : Sysᵘ.NodeDrop 𝒟) (rr : Sysᵘ.RebRowᵘ 𝒟) (ri : Domˢ.Dm 𝒟 (rootˢ 1) (proj₁ (Ωt (tw 1)))) where
  open Sysᵘ.Mainᵘ 𝒟 nd′ rr

  folded₁ : GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ 1)) ∷ []) (twcᴮ 1)
  folded₁ = lowAllᵘ (tw 1) (Ok-tw 1) (rb-tw 1) (baseᴮ 1) (good-tw 1) raise-tw1 [] root-bd1 (dom-top (dom-keel 1)) ri
    zero (z≤ (tw 1)) (betaᴮ 1) (λ ())
    (λ κ rd → subst (λ z → GR.R zero (E.ψ z [] ∷ []) (proj₁ (betaᴮ 1))) (sym (rd0 rd)) (H.pos⁰ (proj₁ (betaᴮ 1)) (proj₂ (betaᴮ 1))))
    [] (GR.c0 refl)
```

## 走链一格在最小域里的形状

层号 2 (`a₂`), 它的 Ω 树在最小域里 (根状态嵌入孩子 2 之后的状态). 槽位是孩子侧顶槽位, 槽位层是层号 1 (`b₁`), 结点的参照取 Ω₁ (余尾 Ω₁, 即槽位层读作 0, 低于它的读法 1). 目标取槽位层自己 (路径 `inc tt self`), 目标读法取 1: `kp` 是 `nothing`, 而 0+1 ≤ 1. 这正是 `NodeDrop` 的情形.

```agda
b₁ a₂ : L
b₁ = L⁰ (suc zero)
a₂ = L⁰ (suc (suc zero))

p₂ : Pos a₂
p₂ = inj₂ (tt , inj₁ tt)

record DropShape : Set where
  field
    in-dom : Mn (stepˢ (rootˢ 1) (suc (suc zero)) zero) (proj₁ (Ωt a₂))
    cofΩ   : E.cof (E.Ωs []) ≡ E.cΩ []
    slotNu : GR.Nu a₂ p₂ []
    hyp    : ∀ η (c : Tr b₁) → GR.R b₁ η c → GR.R a₂ (E.fsT (E.Ωs []) η) (up zero tt (suc c) (z◃ c ◃s))
    dropped : kp a₂ (proj₁ (stepˢ (rootˢ 1) (suc (suc zero)) zero)) p₂ (inc tt self) ≡ nothing
    tgtRd  : GR.Rd b₁ (E.natT 1)
    pen    : Pen (E.cmpᵀ (E.sucT []) (E.natT 1))

drop-shape : DropShape
drop-shape = record
  { in-dom = Ω-child (m-rt 1) (suc (suc zero))
  ; cofΩ   = cof-regular []
  ; slotNu = GR.c0 refl
  ; hyp    = λ η c l → subst (λ z → GR.R a₂ z (up zero tt (suc c) (z◃ c ◃s))) (sym (fs-regular [] η)) (H.mU H.mz (weakᴿ b₁ l ◃s))
  ; dropped = refl
  ; tgtRd  = GR.ca (inj₂ (refl , GR.c0 refl))
  ; pen    = inj₂ refl }
```
