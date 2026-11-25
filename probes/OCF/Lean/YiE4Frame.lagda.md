# 完整变量出口框架
验收文件；困难值界为显式模块参数，链点、层号、表、底、起点均为变量。
来源：YiE3Frame 重写；出口不含具体链点输出；入口见 YiE4Use。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Frame where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Cut19 as C
open import OCF.Align.Value using (_≼_)
-- perf: C-9，链点、层号、合法性、表、底、起点全部是变量；等式限定实际域。
module Frame (c : B.Tr (B.tw 2)) (c-eq : c ≡ C.c₁)
  (h : B.L) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
  (env-eq : (h , o , r , bs) ≡ Q.make c)
  (β : O.Tr⁺ B.zero) (β-eq : β ≡ A.β)
  (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , r , bs) β))) where
  context-eq : (h , o , r , bs) ≡ A.ctx
  context-eq = trans env-eq (trans (cong Q.make c-eq) (sym A.ctx-eq))
  sealed-low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ A.output)
  sealed-low e = subst (λ x → A.reference e ≼ K.readRW (proj₁ x))
    (trans (cong₂ Q.collapse context-eq β-eq) (sym A.output-eq)) (low e)
  raw-low : (e : SI.E.HC A.target) → SI.E.tree e ≼ K.readRW (proj₁ A.output)
  raw-low e = subst (λ x → x ≼ K.readRW (proj₁ A.output)) (A.reference-eq e) (sealed-low e)

-- perf: C-9/C-24，唯一调用点的出口也先对目标、输出族与证明作变量。
at-one : (t : E.T) (out : ℕ → O.Tr⁺ B.zero) (v : O.Tr⁺ B.zero) → v ≡ out 1
  → ((e : SI.E.HC t) → SI.E.tree e ≼ K.readRW (proj₁ v))
  → Σ ℕ λ q → (e : SI.E.HC t) → SI.E.tree e ≼ K.readRW (proj₁ (out q))
at-one t out v eq low = 1 , λ e → subst (λ x → SI.E.tree e ≼ K.readRW (proj₁ x)) eq (low e)
```
