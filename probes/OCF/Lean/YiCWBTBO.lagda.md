# 新终点第 1 支的 BTBO 下界
验收文件，读记号；新支不低于 BTBO，不提供第 3 站下界。
来源：YiMTValue.rBc/rB1ᶻ/br1-Rᶻ，改用 lift-W 对应新表的路径；topΩ 已对表参数化。
rB1 与 br1-R 均无未填前提；规范实例先在临时 StationProbe 编译。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWBTBO where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiCWTable
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiSMValue as SM
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiMTRel using (topΩ; S; u0)
open import OCF.Lean.YiNRHit using (noΩ↑)
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; emb-R)
open import OCF.Lean.YiBRFold using (W→L; B₀-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; ↑-L; lift-W)
open import OCF.Lean.YiEBShape using (Fn)
open import OCF.Lean.YiBRValue using (up≼; readRW)
open import OCF.Lean.YiEBBtbo using (module Btbo)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiBtValBT using (module D)
Bc : (c : Tr zero) (j : L) → j ≤ hᵗ 0 c → Tr⁺ j
Bc c j v = ψ (hᵗ 0 c) (proj₂ (Ok-tw 1) c) (MT.rbᶻ (hᵗ 0 c)) (B₀ _) j v (Ωt j)
  (proj₁ (emb (hᵗ 0 c) (proj₂ (Ok-tw 1) c) (lift zero (↑ zero c)) MV.one⁺))
shape : ∀ c j v → C.baseᴱ 1 j (inc c v) ≡ Bc c j v
shape zero j v = refl
shape (suc c) j v = refl
shape (lim f a) j v = refl
rBc : ∀ {c c′} (rcc : RelT zero F.zero c c′) {j j′} {v : j ≤ hᵗ 0 c} {v′ : F._≤_ j′ (T1.h₁ c′)} → RelW v v′
  → RelT j j′ (proj₁ (Bc c j v)) (MV.bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ (Bc c j v)) (MV.nsᶻ j′ (F.inb c′ v′))
rBc {c} {c′} rcc {j} {j′} rv =
  let rec = SM.chE (tw-E 1) c c′ rcc
      rlj = W→L (E→L rec) rv
      em = emb-R rec (lift-W (↑-L lz rcc)) MV.one⁺ (is iz) ds
  in S rec (noΩ↑ c) (B₀ _) (F.B₀ _) (B₀-R (E→L rec)) rv (Ωt j) (Ωt-R rlj) (Ωn-R rlj) (proj₁ em)
rB1 : RelBase (tw 1) (F.tw 1) (C.baseᴱ 1) MV.Bᶻᶠ
rB1 j j′ w w′ rw@wself = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(winuΩ _) = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(wink _) = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ (wincΩ {c = c} {c′ = c′} {v = v} {v′ = v′} rcc rv) =
  subst (λ Z → RelT j j′ (proj₁ Z) (MV.bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ Z) (MV.nsᶻ j′ (F.inb c′ v′)))
    (sym (shape c j v)) (rBc rcc rv)
br1-R : RelT zero F.zero (C.station 1) (Fn 1 MV.Bᶻᶠ)
br1-R = proj₁ (topΩ {tb = rbᵗ 1} (tw-E 1) noΩ↑ (C.baseᴱ 1) MV.Bᶻᶠ rB1 (C.betaᴱ 1) (proj₁ SM.β1-R) (proj₂ SM.β1-R) (λ z → u0 z _ _) (Ωt-R (tw-L 1)))
btbo : D.BTBOᴵ ≼ readRW (C.station 1)
btbo = up≼ br1-R (Btbo.btbo-B MV.Bᶻᶠ MV.okᶻ MV.stᶻ)
```
