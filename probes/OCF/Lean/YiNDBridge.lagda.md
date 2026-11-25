# 新终点第 1 支的局部底关系
验收文件；rB1 无未填前提，连接新实际底与带表 F2 的 dB 1。
来源：YiCWBTBO.shape、YiMTValue.B1-shape 与 YiVTRel.cL；嵌入路径的变换单独证明。
不比较新旧终点，不改底或表。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNDBridge where
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiCWTable as CT
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiCWBTBO as CW
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiVTEBShape as VT
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiVTFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; cumΩ-R)
open import OCF.Lean.YiBRFold using (B₀-R)
open import OCF.Lean.YiBRTw using (Λ-E; Λ-L)
import OCF.Lean.YiVTRel as VR
emb-zlift : (a : L) (o : Ok (zero ⊕ a)) (y : Tr⁺ zero)
  → emb (zero ⊕ a) o (z≤ (zero ⊕ a)) y ≡ emb (zero ⊕ a) o (lift zero a) y
emb-zlift zero o y = refl
emb-zlift (nd s h) o y = cong (upz (c₀ s)) (emb-zlift (h (c₀ s)) (proj₂ o (c₀ s)) y)
base1-same : ∀ c j (v : j ≤ CT.hᵗ 0 c) → C.baseᴱ 1 j (inc c v) ≡ GI.baseᴱ 1 j (inc c v)
base1-same c j v = trans (CW.shape c j v)
  (trans (cong (ψ (CT.hᵗ 0 c) (proj₂ (Ok-tw 1) c) (rbᶻ (CT.hᵗ 0 c)) (B₀ _) j v (Ωt j))
    (cong proj₁ (sym (emb-zlift (↑ zero c) (proj₂ (Ok-tw 1) c) MV.one⁺))))
    (sym (MV.B1-shape c j v)))
old-rB1 : RelBase (tw 1) (F.tw 1) (GI.baseᴱ 1) (VT.dB 1)
old-rB1 = VR.cL Λ-E (B₀ _) (F.B₀ _) (B₀-R Λ-L) (cumΩ-R Λ-L 0) 1
rB1 : RelBase (tw 1) (F.tw 1) (C.baseᴱ 1) (VT.dB 1)
rB1 j j′ w w′ rw@wself = old-rB1 j j′ w w′ rw
rB1 j j′ w w′ rw@(winuΩ _) = old-rB1 j j′ w w′ rw
rB1 j j′ w w′ rw@(wink _) = old-rB1 j j′ w w′ rw
rB1 j j′ w w′ rw@(wincΩ {c = c} {v = v} rc rv) =
  subst (λ Z → RelT j j′ (proj₁ Z) (F.bs (VT.dB 1) j′ w′) × RelD j j′ (proj₂ Z) (F.ns (VT.dB 1) j′ w′))
    (sym (base1-same c j v)) (old-rB1 j j′ w w′ rw)
```
