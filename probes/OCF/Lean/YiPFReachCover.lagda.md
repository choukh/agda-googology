# 可达分支域对实际链的覆盖
验收文件；编译定理：较弱闭包 W 包含 Pre 全域及塔第 2 层实际回灌链全部项。
覆盖调用实际链输出；无任意 Ω 分支的闭包前提，不调用总域定理。
这不证明 W 为真子域，也不实填全层槽位保持律。
入口：`pre-in`、`idx₂-in`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFReachCover where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.YiRWBlock hiding (D)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiPFReach
import OCF.Lean.YiPCDom as PC

idx-in : ∀ n → W zero (PC.idx n)
idx-in zero = zero-in zero
idx-in (suc n) = output (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) (base-ok (tw 1))
  (inj₁ (inj₁ tt)) PC.G (root (tw 1)) n

pre-in : ∀ {x} → PC.Pre x → W zero x
pre-in (n , PC.⊴r) = idx-in n
pre-in (n , PC.⊴◃ d) = below (idx-in n) d

p₂ : Pos (tw 2)
p₂ = inj₁ (inj₁ tt)

G₂ : Br (tw 2) p₂ → Tr (tw 2)
G₂ c = proj₁ (upz c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))

idx₂ : ℕ → Tr (tw 1)
idx₂ = chain (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) p₂ G₂

idx₂-in : ∀ n → W (tw 1) (idx₂ n)
idx₂-in zero = zero-in (tw 1)
idx₂-in (suc n) = output (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) (base-ok (tw 2))
  p₂ G₂ (root (tw 2)) n
```
