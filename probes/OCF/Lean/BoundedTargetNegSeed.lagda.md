# 配对审计：种子单调字段精确只要求一条边

固定字面界 one 的第一位置只可能是 0 或 1。因此共享 SeedMono 并不
隐藏全坐标比较；它等价于全部底世界中的 g 0 到 g 1 一条第一位置。
该结论不消除 Reg 对全部分支的递归字段，也不代替输入合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedTargetNegSeed where
open import Data.Product using (_,_; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedTargetRegIf

Edge : (HB Base → HB Layer) → Set
Edge g = ∀ {W} → g hz ⊲[ (W , one) ] g one

seed-edge : ∀ {g} → SeedMono g → Edge g
seed-edge s = s (hsuc hself) hself (hsuc hself)

edge-seed : ∀ {g} → Edge g → SeedMono g
edge-seed edge hself hself p = hself
edge-seed edge (hsuc hself) hself p = edge
edge-seed edge (hsuc hself) (hsuc hself) p = hself
edge-seed edge hself (hsuc hself) ()

characterization : ∀ g → (SeedMono g → Edge g) × (Edge g → SeedMono g)
characterization g = seed-edge , edge-seed

-- 任意前缀的常值族都满足这个字段，无合法性或正性假设。
constant : ∀ (a : HB Layer) → SeedMono (λ _ → a)
constant a = edge-seed hself
```

前提可满足性由 constant 给出；实际生成族仍须证明自己的 Edge 和递归 Reg。
此审计没有发现反例，也没有把常值实例替代实际最高反馈链的封闭证明。
翻译账：只化简已有字面共同界的字段，无新定义规则或证书条件。
