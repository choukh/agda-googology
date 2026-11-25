# 在 W4 实际塔中执行记号降链

第四层，无条件。给定起点的值比较，任意选择一个严格更小的可数标准项，都能从当前地址再向下走一步，并保留处理后续降链的证据。每座正塔的每个单位返回均可接收 ψ₀(Ω₂) 的整个严格初段。第 1 座完整塔还可接收至 β = D₀D₂²0，含 β 本身。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4PTODescent where

open import Data.Nat.Base using (ℕ; suc; s≤s; z≤n)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-suc; ≼-trans)
open import OCF.Align.EboLeanDef using (_<ᵀ_)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import WVOne using (T₀)
import B12EboRows as Rows
import B18ResetCellGoal as Reset
import B26Names as N
import B28OneChild as Child
import B28Branches as Branch
import B28PReference as Ref
import B20StandardGoal as Standard
import B20StandardInside as Std
import OCF.Align.Bachmann as Bach
import Survey.W4PTOAddresses as A
import Survey.W4ReturnRendezvous as Real

record Cursor (root : T₀) (b : N.Name) : Set where
  constructor cursor
  field
    path : A.Trail
    node : T₀
    reached : A.follow root path ≡ just node
    fits : N.value b ≼ node

start : ∀ root b → N.value b ≼ root → Cursor root b
start root b h = cursor [] root refl h

record Move {root a b} (old : Cursor root b) : Set where
  field
    next : Cursor root a
    valid : A.member root (just (Cursor.path next)) ≡ true
    smaller : A.kb (Cursor.path next) (Cursor.path old) ≡ true

accepted : ∀ root ps p {z} → A.follow root (ps ++ (p ∷ [])) ≡ just z →
  A.member root (just (ps ++ (p ∷ []))) ≡ true
accepted root [] p h rewrite h = refl
accepted root (x ∷ ps) p h rewrite h = refl

descend : ∀ {root a b} (old : Cursor root b) → L.suc (N.value a) ≼ Cursor.node old → Move {a = a} old
descend {root} {a} {b} (cursor ps q reached fits) strict = finish (A.pick {x = N.value a} {y = q} strict)
  where
  finish : Σ T₀ (λ z → A.Hop q z × N.value a ≼ z) → Move {a = a} (cursor {root} {b} ps q reached fits)
  finish (z , e , h) = record { next = cursor path z at h ; valid = accepted root ps ticket at ; smaller = A.extension ps ticket }
    where
    ticket = A.route e , 0
    path = ps ++ (ticket ∷ [])
    at = A.after root ps reached e 0

advance : ∀ {root} (a b : N.Name) → N.name a <ᵀ N.name b →
  (old : Cursor root b) → Move {a = a} old
advance a b lt old = descend {a = a} old (≼-trans {b = N.value b}
  (mono<ⁿ (N.nt a) (N.nt b) (N.ct b) (N.hcN a) (N.hcN b) lt) (Cursor.fits old))

two = Child.At.b 0 1

first : Cursor (Rows.child 1) two
first = start (Rows.child 1) two (≼-trans {b = L.ψ⁰ (L.Ω (Bach.lvN (Bach.snat 2)))}
  (proj₁ (Ref.At.exact (Bach.snat 2) (Branch.At.Head.at 0 1))) Rows.omega₂-in-child)

unit : ∀ n j → Cursor (Real.unit (suc n) j) two
unit n j = start (Real.unit (suc n) j) two (≼-trans {b = Std.std 1}
  (Ref.two (Branch.At.Head.at 0 1)) (≼-trans {b = L.suc (Std.std 1)}
    (≼-suc (≼-refl (Std.std 1))) (Standard.At.child n j 1 (s≤s z≤n))))

module Infinite {root} (top : N.Name) (initial : Cursor root top)
                (xs : ℕ → N.Name) (enter : N.name (xs 0) <ᵀ N.name top)
                (down : ∀ n → N.name (xs (suc n)) <ᵀ N.name (xs n)) where
  state : ∀ n → Cursor root (xs n)
  state 0 = Move.next (advance (xs 0) top enter initial)
  state (suc n) = Move.next (advance (xs (suc n)) (xs n) (down n) (state n))
  in-domain : ∀ n → A.member root (just (Cursor.path (state n))) ≡ true
  in-domain 0 = Move.valid (advance (xs 0) top enter initial)
  in-domain (suc n) = Move.valid (advance (xs (suc n)) (xs n) (down n) (state n))
  decreases : ∀ n → A.less (just (Cursor.path (state (suc n)))) (just (Cursor.path (state n))) ≡ true
  decreases n = Move.smaller (advance (xs (suc n)) (xs n) (down n) (state n))

import Survey.EboPTOFinite as Terms
import Survey.W4PTOGamma as Gamma
open import OCF.Align.EboLeanBase using (c∷; c[])

-- β 自己已占用一个通过域检查的地址，此后仍能处理任意严格下降。
module DepthTwo where
  beta = N.named (Terms.collapsed 2 2) (Terms.nf-collapsed 2 2) (c∷ c[]) (Terms.tower-h 2 2)
  root = Rows.child 1
  strict : L.suc (N.value beta) ≼ root
  strict = ≼-trans {b = Real.unit 0 2} Gamma.first-unit (Real.within 0 2)
  initial : Cursor root beta
  initial = start root beta (≼-trans {b = L.suc (N.value beta)} (≼-suc (≼-refl _)) strict)
  endpoint : Move {a = beta} initial
  endpoint = descend {a = beta} initial strict

-- 第零塔的具体地址域有一个只读自然数与短表的判定式。
module TowerZero where
  remainder : ℕ → A.Trail → Bool
  remainder n [] = true
  remainder 0 (_ ∷ _) = false
  remainder (suc n) (([] , _) ∷ ps) = remainder n ps
  remainder (suc n) (((_ ∷ _) , _) ∷ ps) = false

  finite : ∀ n ps → A.inhabited (A.follow (L.natᶜ n) ps) ≡ remainder n ps
  finite n [] = refl
  finite 0 (_ ∷ _) = refl
  finite (suc n) (([] , _) ∷ ps) = finite n ps
  finite (suc n) (((_ ∷ _) , _) ∷ ps) = refl

  gate : ∀ n ns → A.land (Rows.child 0) (n ∷ ns) ≡ A.land (L.natᶜ (suc n)) ns
  gate n ns = cong (λ x → A.land x ns) (Reset.First.branch n)

  domain : A.Node → Bool
  domain Data.Maybe.Base.nothing = true
  domain (just (((n ∷ []) , i) ∷ ps)) = remainder n ps
  domain (just _) = false

  agrees : ∀ p → A.member (Rows.child 0) p ≡ domain p
  agrees Data.Maybe.Base.nothing = refl
  agrees (just []) = refl
  agrees (just (([] , i) ∷ ps)) = refl
  agrees (just (((n ∷ []) , i) ∷ ps)) rewrite gate n [] = finite n ps
  agrees (just (((n ∷ a ∷ ns) , i) ∷ ps)) rewrite gate n (a ∷ ns) = refl
```

**经典纸面应用。** 在第一座完整塔的地址序上，以上程序逐次读入有限下降前缀，输出合法地址；扩展前缀时，新地址严格延长旧地址。有限可数标准项可按语法从可判定的标准形、可数性及比较检验恢复所需证据，HC 取仓库中的 `hc`。在标准形的守卫处只需遍历有限原项中的受守卫子项，并按项序检查它们。因而在普通自然数编码上有一个确定的递归译码过程。可将“每个合法有限下降前缀都停机，并在延长时给出合法的严格下降地址”作为一条已由上面程序证真的算术辅助句。在 ACA₀ 中结合此句，对任意假想降链作算术理解，即可得到第一塔地址序的降链。因此只使用 Tᵂ 的第一塔公理和该辅助句即可推出 WO(ψ₀(Ω₂) 的原记号严格初段)。Kreisel 定理给出辅助句保持 PTO。在同一座完整塔中，`DepthTwo.endpoint` 还给 β = D₀D₂²0 本身一个非空合法地址。首项等于 β 时从这个地址开始，首项低于 β 时先调用一次 `advance`，两种情况都能继续处理每次下降。因此一个真实的塔公理已经接收整个闭初段 ≤β。由有限层定理，ψ₀(Ω₂)<β<ψ₀(Ω₃)。更高初段的统一转换仍开放。[β 的值界](W4FixedDepth.lagda.md)[实际塔理论](W4PTOTowerTheory.lagda.md) · [初段标准项的取得](../OCF/Align/EboLeanTree.lagda.md) · [Walsh 定理 1.2](https://arxiv.org/pdf/2209.09765#page=2)

反向也有一个独立实例。第零塔的非空合法地址，第一步恰选一个极限分支 n 后取一次前驱；往后至多再走 n 步，每步都直接取前驱，副本号任意。`TowerZero.agrees` 验证整个地址域。ACA₀ 可以证明这个初等表示良序。无穷降链不能经过另加的最小元，其首键只能非增，因而最终恒定；在固定首键的尾段，链长有统一有限界。对于有界长的字典序，可对位置依次取最终恒定的键（严格前缀在后），从而排除无穷降链。等价地，固定首键的块序型至多 ωⁿ+1，各块均可显式排入 ω^ω。使用原求值记录呈现时，只需本文件已经证真的域判定一致性这一条算术句。因此 Tᴿ 连同该真算术事实能导出 Tᵂ 的第零塔公理。
