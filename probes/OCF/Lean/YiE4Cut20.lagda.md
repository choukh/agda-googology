# 封装后的内层整行
验收文件；整行分解为编译定理，不把局部迭代等式充作整行。
来源：YiE3Cut20；零层消去复用 YiLTLim.nodeZ；入口见 YiE4ParamInner。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Cut20 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiLTLim as LT
open import OCF.Lean.YiE4Cut19 public

-- perf: C-9，零层节点先在变量的 Keep 上消去，避免具体路径的归约。
row0 : {X : Set} {z : X} (m : F.Keep B.zero X z) (G : X → O.Tr⁺ B.zero) (s : X → X)
  → F.node⁺ m G s ≡ O.limc⁺ (λ n → G (O.iter s z n))
row0 {z = z} m G s = LT.nodeZ m
  (λ t → t ≡ O.limc⁺ (λ n → G (O.iter s z n))) G s refl
-- perf: C-24/S-13，计算律在内层函数同时开放的一处证明。
opaque
  unfolding inner-g inner-feed inner-out
  first-row : TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (proj₁ (O.Ωt h₁))
    ≡ O.limc⁺ (λ n → inner-out (inner-chain n))
  first-row = row0 {X = B.Tr (B.tw 1)} {z = B.zero}
    (F.kp h₁ o₁ (inj₁ (inj₁ tt)) (P.z≤ h₁)) inner-out inner-feed
```
