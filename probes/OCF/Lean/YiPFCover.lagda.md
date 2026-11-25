# 闭包域对实际回灌链的覆盖
验收文件；编译定理：包含 `YiPCDom.Pre` 全部项及塔第 2 层实际回灌链全部项。
覆盖证明直接调用种子、回灌和前驱构造子，不调用 `all-in`；证明形式据第 0 步临时检查。
本文件不读记号；覆盖成立不说明该域缩小了量化范围，域的总性见 `YiPFDom`。
入口：`pre-in`、`idx₂-in`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFCover where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.YiRWBlock hiding (D)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiPFDom
import OCF.Lean.YiPCDom as PC

idx-in : ∀ n → D zero (PC.idx n)
idx-in zero = zero-in zero
idx-in (suc n) = feed-out (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1))
  (inj₁ (inj₁ tt)) PC.G (root (tw 1)) (PC.idx n)

pre-in : ∀ {x} → PC.Pre x → D zero x
pre-in (n , PC.⊴r) = idx-in n
pre-in (n , PC.⊴◃ d) = below (idx-in n) d

p₂ : Pos (tw 2)
p₂ = inj₁ (inj₁ tt)

G₂ : Br (tw 2) p₂ → Tr (tw 2)
G₂ c = proj₁ (upz c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))

idx₂ : ℕ → Tr (tw 1)
idx₂ = iter (feedᴰ (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) p₂ G₂) zero

idx₂-in : ∀ n → D (tw 1) (idx₂ n)
idx₂-in zero = zero-in (tw 1)
idx₂-in (suc n) = feed-out (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) p₂ G₂
  (root (tw 2)) (idx₂ n)

idx₂-0 : D (tw 1) (idx₂ 0)
idx₂-0 = idx₂-in 0

idx₂-1 : D (tw 1) (idx₂ 1)
idx₂-1 = idx₂-in 1

idx₂-2 : D (tw 1) (idx₂ 2)
idx₂-2 = idx₂-in 2
```
