# 实际层族的有界上下文

`prefix ⊕L upL k c` 是 ΩL 后继层实际使用的分量形状。本定理对任意
prefix、k、世界与字面路径成立，不把层号值相等当作上下文。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedContextRun where

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL)
open import OCF.Lean.BoundedContextIf

compose : ∀ {T S R} → Ctx T S → Ctx S R → Ctx T R
compose c here = c
compose c (viaS d) = viaS (compose c d)
compose c (viaL d i) = viaL (compose c d) i

node-context : ∀ P k κ (h : E (Lv k) κ → LH) e →
  Ctx (Lv (P ⊕L node k κ h)) (Lv (P ⊕L h e))
node-context P lz () h e
node-context P (ls k) (inj₁ κ) h e = node-context P k κ h e
node-context P (ls k) (inj₂ _) h e = viaL here (inj₂ e)
node-context P (ll f) (n , κ) h e = node-context P (f n) κ h e
node-context P (lΩ k g) (inj₁ _ , inj₁ κ) h e = node-context P k κ h e
node-context P (lΩ k g) (inj₁ _ , inj₂ _) h e = viaL here (inj₂ e)
node-context P (lΩ k g) (inj₂ c , κ) h e = node-context P (g c) κ h e

path-context : ∀ P k {w c B} → c ⊲[ w ] B →
  Ctx (Lv (P ⊕L upL k B)) (Lv (P ⊕L upL k c))
path-context P k hself = here
path-context P k (hsuc q) = compose (viaS here) (path-context P k q)
path-context P k (hlim n q) = compose (viaL here n) (path-context P k q)
path-context P k (hLim {κ = κ} {g = h} {c = e} b q) =
  compose (node-context P k κ (λ c → upL k (h c)) e) (path-context P k q)

bounded : ∀ P k w B → Bounded k w (λ c → P ⊕L upL k c) B
bounded P k w B = record { context = λ c p → path-context P k p }

-- ΩL (ls k) 的实际分量，包含任意高层 k，非仅可数索引。
Ω-successor : ∀ k w B → Bounded k w (λ c → ΩL k ⊕L upL k c) B
Ω-successor k = bounded (ΩL k) k
```

路径中的 Ω 分支选取已经给定的坐标 e；没有给整个函数分支寻找一个
有限支撑。分支仍可在整个混合签名里，后续树搬运应对整棵树递归。
本文件没有折叠或序数值验收结论。
