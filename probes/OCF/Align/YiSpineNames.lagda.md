# 层号码的自然命名解释：零、后继与 Ω

第 4 层诊断。先把当前树表示的三个结构方程固定下来，不给未写的
树侧 ψ 安排任意替代值。Name c 是一个明确的 EBO 层码命名证书；
本篇的 ι_L 解释这个命名域，不冒称每个正参数 ψ 码已有命名证书。
反例端点均在此域内，结论将对任意保留此域的总扩展成立。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpineNames where

open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import OCF.Align.EboLeanDef using (T; ψ; sucT; Ωt)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiSpinePrefix using (add)

data Name : T → Set where
  nz : Name []
  ns : ∀ {c} → Name c → Name (sucT c)
  no : ∀ {c} → Name c → Name (Ωt c)

interpret : (Y.Level → Y.Level) → ∀ {c} → Name c → Y.Level
interpret O nz = Y.zero
interpret O (ns x) = Y.suc (interpret O x)
interpret O (no x) = O (interpret O x)

ι_L : ∀ {c} → Name c → Y.Level
ι_L = interpret Y.Ω

two left-code : T
two = sucT (sucT [])
left-code = sucT (Ωt two)

two-name : Name two
two-name = ns (ns nz)

left-name : Name left-code
left-name = ns (no two-name)

-- 总解释的接口只固定上述自然构造方程，不预设任何 ψ 值定理。
record Extension : Set₁ where
  field
    read : T → Y.Level
    zero-law : Y.tree (read []) ≡ F.zero
    suc-law : ∀ c → Y.tree (read (sucT c)) ≡ F.suc (Y.tree (read c))
    omega-law : ∀ c → Y.tree (read (Ωt c)) ≡ V.Ω̂ (Y.tree (read c))
open Extension public

agrees : (M : Extension) → ∀ {c} (x : Name c) →
  Y.tree (read M c) ≡ Y.tree (ι_L x)
agrees M nz = zero-law M
agrees M (ns {c} x) = trans (suc-law M c) (cong F.suc (agrees M x))
agrees M (no {c} x) = trans (omega-law M c) (cong V.Ω̂ (agrees M x))

-- 只用于展示Extension合同可满足，不是S4的序数值解释。
-- 正参数ψ填一个合法层号Λ；后面的反例对所有Extension成立，不依赖此选择。
structure-model-read : T → Y.Level
structure-model-read [] = Y.zero
structure-model-read (ψ u [] ∷ xs) = add (Y.Ω (structure-model-read u)) (structure-model-read xs)
structure-model-read (ψ u (_ ∷ _) ∷ xs) = add Y.Λ (structure-model-read xs)

model-suc : ∀ c → Y.tree (structure-model-read (sucT c)) ≡ F.suc (Y.tree (structure-model-read c))
model-suc [] = refl
model-suc (ψ u [] ∷ xs) = cong (V._+ᴸ_ (V.Ω̂ (Y.tree (structure-model-read u)))) (model-suc xs)
model-suc (ψ u (_ ∷ _) ∷ xs) = cong (V._+ᴸ_ (Y.tree Y.Λ)) (model-suc xs)

structure-model : Extension
read structure-model = structure-model-read
zero-law structure-model = refl
suc-law structure-model = model-suc
omega-law structure-model c = refl

name-coherent : ∀ {c} (x y : Name c) → Y.tree (ι_L x) ≡ Y.tree (ι_L y)
name-coherent x y = trans (sym (agrees structure-model x)) (agrees structure-model y)
```

Name 的解释没有自由分支，两个端点的树因这三个方程而确定。
structure-model 只证明结构合同非空，正参数 ψ 的取值不是 EBO 值对应，
不能用它假充 S4 的全域 ι。主要反例无 Extension 参数；
对任意 Extension 的版本另列为加强，完全不读取这个模型的正 ψ 分支。
name-coherent 保证同一码在命名域内的原树表示不依赖命名证书；
它没有断言证书本身或 Level 记录相等。
Λ 本轮无需码名：它已在 YiLevelBase 中合法，且这里不向 T 加一个伪 Λ 常数。
