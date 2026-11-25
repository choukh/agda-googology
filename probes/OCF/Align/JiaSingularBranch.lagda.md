# 甲脚手架：打包输入域上的 Ω_Ω 分支

本篇沿输入树构造 Ω，不先计算 raw 输出再补码。
可数输入取 `JiaCountPack.Named`，每个子树在构造时已有自己的码。
这里只先生成单个分支，尚未把它接成现有 raw Ω 结点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaSingularBranch where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([])
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; Ωt; Ωs; _<ᵀ_)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-Ω)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.EboLeanClosure using (trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Align.JiaBase using (Tree; Below; below; module Layer)
open import OCF.Align.JiaFold using (lift; regular)
import OCF.Align.JiaCountPack as C

-- Ω_0 = 1；后继取低层树的全分支提升；极限逐输入树分支递归。
omega : ∀ {c} → C.Named c → (a : Acc′ c) → Tree c a
omega C.nz a = Layer.s Layer.z
omega (C.ns x) a = regular a (C.normal x)
omega (C.nl {t = c} nc cc e f) (acc h) = Layer.l branches
  where
  branches : ℕ → Tree c (acc h)
  branches n = lift ac (acc h) p (omega (f n) ac)
    where
    p = below (C.normal (f n)) (t< (trian-fsn nc e n))
    ac = h (C.normal (f n)) (t< (trian-fsn nc e n))

Ω : T
Ω = Ωs []

omegaAt : ∀ {c ℓ} → C.Named c → (a : Acc′ ℓ) → Below c ℓ → Tree ℓ a
omegaAt x a p = lift (wf (C.normal x)) a p (omega x (wf (C.normal x)))

branchTree : (a : Acc′ Ω) → C.Pack → Tree Ω a
branchTree a (c , x) = omegaAt x a (below (C.normal x) (C.countable-bound (C.countable x)))

record Generated (a : Acc′ Ω) : Set where
  constructor generated
  field
    input : C.Pack
    tree : Tree Ω a
    built : tree ≡ branchTree a input

  code : T
  code = Ωt (proj₁ input)

  code-normal : NF code
  code-normal = nf-Ω (C.normal (proj₂ input))
open Generated public

branch : (a : Acc′ Ω) → C.Pack → Generated a
branch a x = generated x (branchTree a x) refl

branch-code : ∀ a x → code (branch a x) ≡ Ωt (proj₁ x)
branch-code a x = refl

-- 有限输入的零分支确实生成 1；这只检查此分支，不估计整棵树的强度。
zero-input : C.Pack
zero-input = [] , C.nz

zero-branch : ∀ a → tree (branch a zero-input) ≡ Layer.s Layer.z
zero-branch (acc h) = refl
```

`built` 指向本篇沿输入树执行的 Ω 构造；码与其标准形一起生成，
没有把一个任意 raw 输出装进这个记录。
`branch-code` 是输出码的运算方程，**不是序数值验收定理**。
尚未证明这条分支与全部树侧 ψ 轨道的对应，更没有新闭项下界。

## 现有结点还要求什么输入

现有 `JiaBase.Layer.o` 在零层分支处接受的仍是 raw `Tree [] a₀`，
不接受 `C.Pack`。若直接用本篇分支函数续接，先要有 raw 输入到包的
转接。下列记录展示一种保留原树的事后补码接口；不是所有可能接法
的必要条件。本篇不填它，不假定它存在，也不把它当作实际生成域。

```agda
record RawRepack (a₀ : Acc′ []) : Set where
  field
    repack : Tree [] a₀ → C.Pack
    original : ∀ x → C.erase a₀ (proj₂ (repack x)) ≡ x
```

因此，把 `branchTree` 直接交给原 raw Ω 构造子时缺少的不是 NF 证据，
而是输入类型。若用 `RawRepack` 补上，就已经触及作者本轮的停止条件。
这只诊断现有 raw 接口的接线，不否定从一开始就让低层分支接受包的树族。
