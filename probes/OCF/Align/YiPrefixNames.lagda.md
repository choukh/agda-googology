# 前缀表示的层号命名域

第 4 层诊断：以 Ωprefix 替换命名解释里的 Ω，保留零、后继，
增加 Ω 单项的有限和及标准 ω 极限。ω 的树为 lim natF，
其码的基本列确为 natT；不是给任意正参数 ψ 指派一个语义。
新的反例只读这些构造方程，并对所有保留这些方程的总扩展成立。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPrefixNames where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import OCF.Align.EboLeanDef using (T; ψ; sucT; Ωt; natT; fsn)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiSpinePrefix using (add; Ωprefix)
open import OCF.Align.YiPrefixLevels using (Ωp; Λp)

ω-code : T
ω-code = ψ [] (Ωt []) ∷ []

ω-fs : ∀ n → fsn ω-code n ≡ natT n
ω-fs zero = refl
ω-fs (suc n) = cong (ψ [] [] ∷_) (ω-fs n)

ω : Y.Level
ω = Y.level (F.lim V.natF) V.Legal-ω

data Name : T → Set where
  nz : Name []
  ns : ∀ {c} → Name c → Name (sucT c)
  no : ∀ {c} → Name c → Name (Ωt c)
  headΩ : ∀ {u xs} → Name u → Name xs → Name (ψ u [] ∷ xs)
  nw : Name ω-code

ι_L : ∀ {c} → Name c → Y.Level
ι_L nz = Y.zero
ι_L (ns n) = Y.suc (ι_L n)
ι_L (no n) = Ωprefix (ι_L n)
ι_L (headΩ u xs) = add (Ωprefix (ι_L u)) (ι_L xs)
ι_L nw = ω

one-code ν-code left-code : T
one-code = sucT []
ν-code = ψ one-code [] ∷ Ωt one-code
left-code = sucT ν-code

ν-name : Name ν-code
ν-name = headΩ (ns nz) (no (ns nz))

left-name : Name left-code
left-name = ns ν-name

-- 合同只规定本命名域的构造；不要求或制造树侧ψ。
record Extension : Set₁ where
  field
    read : T → Y.Level
    zero-law : Y.tree (read []) ≡ F.zero
    suc-law : ∀ c → Y.tree (read (sucT c)) ≡ F.suc (Y.tree (read c))
    omega-law : ∀ c → Y.tree (read (Ωt c)) ≡ Ωp (Y.tree (read c))
    head-law : ∀ u xs → Y.tree (read (ψ u [] ∷ xs)) ≡
      V._+ᴸ_ (Ωp (Y.tree (read u))) (Y.tree (read xs))
    omega-limit-law : Y.tree (read ω-code) ≡ F.lim V.natF
open Extension public

agrees : (M : Extension) → ∀ {c} (n : Name c) →
  Y.tree (read M c) ≡ Y.tree (ι_L n)
agrees M nz = zero-law M
agrees M (ns {c} n) = trans (suc-law M c) (cong F.suc (agrees M n))
agrees M (no {c} n) = trans (omega-law M c) (cong Ωp (agrees M n))
agrees M (headΩ {u} {xs} n m) = trans (head-law M u xs)
  (trans (cong (λ x → V._+ᴸ_ (Ωp x) (Y.tree (read M xs))) (agrees M n))
    (cong (V._+ᴸ_ (Ωp (Y.tree (ι_L n)))) (agrees M m)))
agrees M nw = omega-limit-law M

-- 居留模型只证明合同非空。未指定的正ψ仍填合法Λp；
-- 主反例不依赖这一填值，不能把此模型当S4的语义ι。
structure-model-read : T → Y.Level
principal : T → T → Y.Level
structure-model-read [] = Y.zero
structure-model-read (ψ u b ∷ xs) = add (principal u b) (structure-model-read xs)
principal u [] = Ωprefix (structure-model-read u)
principal [] (ψ [] [] ∷ []) = ω
principal u (_ ∷ _) = Λp

model-suc : ∀ c → Y.tree (structure-model-read (sucT c)) ≡
  F.suc (Y.tree (structure-model-read c))
model-suc [] = refl
model-suc (ψ u b ∷ xs) = cong (V._+ᴸ_ (Y.tree (principal u b))) (model-suc xs)

structure-model : Extension
read structure-model = structure-model-read
zero-law structure-model = refl
suc-law structure-model = model-suc
omega-law structure-model c = refl
head-law structure-model u xs = refl
omega-limit-law structure-model = refl

name-coherent : ∀ {c} (n m : Name c) → Y.tree (ι_L n) ≡ Y.tree (ι_L m)
name-coherent n m = trans (sym (agrees structure-model n)) (agrees structure-model m)
```

所有命名结果立即有 Legal；没有补码、比较合法性证明或函数外延。
本轮仍交付构造命名子域，不声称已写出全域 S4 语义解释。
Λp 由树侧前缀塔给出，不在有限记号 T 里添加伪 Λ 常数。
