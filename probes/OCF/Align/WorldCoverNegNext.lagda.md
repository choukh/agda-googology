# 下一 Ω 指标层的实际合法分支校准

这是正面实例，不是否定。当前Source只是twL2；但不能据类型名字
给它的折叠封顶。这里展示twL3的具体分量已经需要处理含Ω坐标的θ，
并给出完整合法世界与原地板分支，排除“该分支不可入”的误解。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldCoverNegNext where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecFl
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L; module New)
open import OCF.Align.BoundedDescentValueBridge using (Source)

current-source : Source ≡ Lv (twL 2)
current-source = refl

component : Cd → LH
component c = ΩL (ls lz ⊕L upL lz c)
next-shape : twL 3 ≡ lΩ lz component
next-shape = refl

k : LH
k = ls lz
g : HB (Lv k) → LH
g d = ΩL k ⊕L upL k d
higher : LH
higher = lΩ k g
selected-component : component (hs hz) ≡ higher
selected-component = refl

-- 原最低Ω地板作为下一指标层的坐标，确实不是纯Cd坐标。
coordinate : HB (Lv k)
coordinate = flL k
coordinate-legal : LgB coordinate
coordinate-legal = Lg-flL k

world : Wd (Lv higher)
world (inj₁ _) = w₀L k , coordinate
world (inj₂ d) = w₀L (g d)
world-legal : LgW (Lv higher) world
world-legal (inj₁ _) = lw₀L k , coordinate-legal
world-legal (inj₂ d) = lw₀L (g d)
admitted : Bd (Lv higher) ixK coordinate world
admitted = hself

branch : HB (Lv k) → HB (Lv higher)
branch = New.θ (cxI k g) (gcF (λ d → ι (inj₂ d) (flL (g d))))
floor-shape : flL higher ≡ hΩ ixK branch
floor-shape = refl
actual-branch-legal : LgB (branch coordinate)
actual-branch-legal = proj₂ (Lg-flL higher) world-legal admitted

-- θ在这个真实合法坐标上保留指标分量的旧Ω，并递归读取所有Cd分支。
branch-shape : branch coordinate ≡
  hΩ (inj₁ tt , inj₁ (inj₂ tt)) (λ c → branch (up c))
branch-shape = refl
```

**范围与后续义务。** 地板、上述含Ω坐标、θ分支及完整源世界都有现成
总定义和合法证书，因此下一站不是缺少树构造子。当前仅处理可数层号
与有限组件的原Native下降不能凭本篇自动扩展：需要处理此真实指标旧Ω
分支、递归层号 `upL k d` 的节点、带公共界的目标分类，以及相应回灌
坐标关系和终点值桥。这些仍是待实现义务，不是本篇否定定理。

本例也没有证明原C的值上界，没有把twL2与ΛL的类型差当成强度差。
新文件仅使用原树结构和原合法性，未引入记号字段或新的折叠规则。
