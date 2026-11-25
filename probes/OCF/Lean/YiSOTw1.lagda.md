# 塔第 1 项根状态的 `SlotBd`; 终点的前提换成两格不一致与换基行

> 验收文件 (读记号). 判决: 编译定理. `root-bd1`: 塔第 1 项根状态的每个槽位, 每个读法 κ (`GR.Nu`, 不限域) 上底支配 Ω_κ, 无前提; 槽位层号都没有 Ω 形状, 用 `YiLLCheck.leafC`. `ebo-endᵁ`: `YiSOEnd.End.ebo-endᴬ` 的自身行前提换成 `YiSOUp.UpMis`.
> 不给出什么: 塔第 2 项起的 `RootBd` (槽位层号含 Ω 形状, `leafC` 不适用; 全域 Leaf 在 Ω 形状上有编译否定 `YiLLLeafNeg.noLeafOk`); 塔第 1 项上 `NodeMis`, `UpMis`, `RebRow` 没有实填, 所以这一项的 `LowSlot` 未走通.
> 入口: [YiSOLow](YiSOLow.lagda.md), [YiSOUp](YiSOUp.lagda.md), [YiSOEnd](YiSOEnd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSOTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([])

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath using (Ok-Λ; self; inc; posW; posW⁼)
open import OCF.Lean.YiRWFold using (B₀)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiGTGen using (weakenᴿ)
open import OCF.Lean.YiGIInst using (pre)
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ↑; NoΩ≤)
open import OCF.Lean.YiLLCheck using (leafC)
open import OCF.Lean.YiWREnd using (rbΛ; EBOᴮ; ψ-⊵ᴮ)
open import OCF.Lean.YiSOLow
open import OCF.Lean.YiSOUp
open import OCF.Lean.YiSOEnd

noΩ-tw1 : (p : Pos (tw 1)) → NoΩ (at (tw 1) p)
noΩ-tw1 (inj₁ (inj₁ _))      = tt
noΩ-tw1 (inj₂ (c , inj₁ _))  = NoΩ↑ c
noΩ-tw1 (inj₂ (c , inj₂ p))  = NoΩ≤ (posW (zero ⊕ ↑ zero c) p) (NoΩ↑ c)

root-bd1 : SlotBd (rootˢ 1) []
root-bd1 p nu = weakenᴿ (at (tw 1) p) (leafC (at (tw 1) p) (noΩ-tw1 p) (nu-rd (tw 1) p nu))
  (ψ-⊵ᴮ Λ Ok-Λ rbΛ (B₀ Λ) (at (tw 1) p) (inc 1 (posW (tw 1) p)) (O.Ωt (at (tw 1) p)) (pre 1))

module EndU (𝒟 : Domˢ) (um : UpMis) where
  open Sys 𝒟
  open End 𝒟
  open UpAll um

  ebo-endᵁ : (nm : NodeMis) (rr : RebRow) (rb : RootBd) (ri : RootIn)
    → (∀ n → H.Exᴴ (folded nm (self←up 𝒟) rr rb ri n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
  ebo-endᵁ nm rr rb ri = ebo-endᴬ nm (self←up 𝒟) rr rb ri
```
