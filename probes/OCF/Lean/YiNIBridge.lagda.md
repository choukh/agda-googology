# 与 Leaf、LowKeep 及语义反射的关系
验收文件；编译条件定理：旧 LowKeep 在指定请求上的实例加局部 Leaf 和出口证据给 Law。
Law 与指定零层证书、带出口证据的封闭关系互推；没有重复三条旧律。
来源：关系反射与出口分别复用 YiKCSem、YiKVRel、YiHCCheck、YiHCRel。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNIBridge where
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
import OCF.Lean.YiNIDomain as D
open import OCF.Lean.YiNIIface
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiRefTw2 as RT
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiAbsGIface using (module Laws)
module Old = Laws GI.gradedᵍ GI.domsᵍ

module Local (d : Request) where
  open Request d
  ℓ = D.Node.layer node
  Source : Set
  Source = GR.R ℓ (E.Ωt index) (proj₁ (O.Ωt ℓ))
  Kept : Set
  Kept = GR.R B.zero reference (D.output node)
  Checked : Set
  Checked = Σ Kept H.Exᴴ

  reflect : At.Value d → At.Certificate d
  reflect = CS.sem→M⁰ nonempty (D.output node)
  sound : At.Certificate d → At.Value d
  sound m = K.lower⁰ m nonempty
  check : At.Value d → Checked
  check p = HC.of⁰ (reflect p) , HC.ex-of⁰ (reflect p)
  exit : Checked → At.Value d
  exit (m , e) = H.exitᴴ m e nonempty

  restricted-lowkeep : Old.LowKeep → Source → Kept
  restricted-lowkeep lk r = subst (GR.R B.zero reference) (sym (D.output-eq node))
    (lk (D.Node.okay node , MT.rbᶻ ℓ , F.B₀ ℓ) (P.z≤ ℓ) (O.Ωt B.zero) []
      refl GI.wz (GI.startᴿ , λ i u → K.⊴r) refl r)

  leaf-low-exit : (r : Source) (keep : Source → Kept) → H.Exᴴ (keep r) → At.Value d
  leaf-low-exit r keep e = exit (keep r , e)

certificates : ∀ d → Law d → (a : Family.Member d) → At.Certificate (Family.request d a)
certificates d p a = Local.reflect (Family.request d a) (p a)

values : ∀ d → ((a : Family.Member d) → At.Certificate (Family.request d a)) → Law d
values d p a = Local.sound (Family.request d a) (p a)

all-values : ∀ d → Law d → (a : Family.Member d)
  → (h : E.HC (Request.reference (Family.request d a)))
  → RT.Rt h ≼ K.readRW (D.output (Request.node (Family.request d a)))
all-values d p a h = K.lower⁰ (certificates d p a) h
```
