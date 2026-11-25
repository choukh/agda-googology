# 乙的第一里程碑：带合法性的树层号与位置接口

本篇只准备层号，不写 ψ。复用作者指定先例 LevelFixCore／LevelFixVal
中不含记号的树、结构 Ω 与合法性闭包，不导入 LevelFixU 或旧折叠。
Level 同时保存原树与合法性；构造函数随结果给证据，不检查运行后的树。

位置明确采用 CP（字面第一位置），不是“在任意数据字段中出现”。
本接口不会自动把 Ω 结点的层号字段或任意分支认作 CP 位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLevelBase where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (Legal; CP)
import OCF.Align.LevelFixVal as V

record Level : Set where
  constructor level
  field
    tree : LF
    legal : Legal tree
open Level public

zero : Level
zero = level F.zero tt

suc : Level → Level
suc x = level (F.suc (tree x)) (legal x)

lim : (f : ℕ → Level) → (∀ n → CP (tree (f n)) (tree (f (Data.Nat.Base.suc n)))) → Level
lim f step = level (F.lim (λ n → tree (f n))) (step , (λ n → legal (f n)))

node : (k : Level) (c : Raw (tree k)) (t : Level)
  (g : (η : Raw (tree k)) → Gd (tree k) c η → Level) →
  (∀ η e → CP (tree t) (tree (g η e))) →
  (∀ η e η′ e′ → Gd (tree k) η η′ → CP (tree (g η e)) (tree (g η′ e′))) →
  (∀ η e e′ → tree (g η e) ≡ tree (g η e′)) → Level
node k c t g first mono same = level
  (F.lc (tree k) c (tree t) (λ η e → tree (g η e)))
  (legal k , first , mono , same , legal t , (λ η e → legal (g η e)))

Ω : Level → Level
Ω x = level (V.Ω̂ (tree x)) (V.Legal-Ω̂ (tree x) (legal x))

Ω-zero : tree (Ω zero) ≡ F.suc F.zero
Ω-zero = refl

Ω-suc : ∀ x → tree (Ω (suc x)) ≡
  F.lc (tree x) (V.cO (tree x)) (V.Ω̂ (tree x)) (λ η e → V.up (tree x) η)
Ω-suc x = refl

Ω-lim : ∀ f step → tree (Ω (lim f step)) ≡ F.lim (λ n → V.Ω̂ (tree (f n)))
Ω-lim f step = refl

Ω-node : ∀ k c t g first mono same → tree (Ω (node k c t g first mono same)) ≡
  F.lc (tree k) c (V.Ω̂ (tree t)) (λ η e → V.Ω̂ (tree (g η e)))
Ω-node k c t g first mono same = refl

tower : ℕ → Level
tower n = level (V.tw n) (V.Legal-tw n)

Λ : Level
Λ = lim tower V.tw-step

Λ-tree : tree Λ ≡ V.Λ
Λ-tree = refl

ΩΛ-tree : tree (Ω Λ) ≡ F.lim (λ n → V.tw (Data.Nat.Base.suc n))
ΩΛ-tree = refl

record Position (bound : Level) : Set where
  constructor located
  field
    part : Level
    place : CP (tree part) (tree bound)
open Position public

Ω-position : ∀ {bound} → Position bound → Position (Ω bound)
Ω-position (located part p) = located (Ω part) (V.Ω̂-CP p)

data Proper : LF → LF → Set where
  under-suc : ∀ {a b} → CP a b → Proper a (F.suc b)
  under-lim : ∀ {a f} n → CP a (f n) → Proper a (F.lim f)
  under-first : ∀ {a k c t g} → CP a t → Proper a (F.lc k c t g)

data Order (a b : LF) : Set where
  below : Proper a b → Order a b
  equal : a ≡ b → Order a b
  above : Proper b a → Order a b
```

Ω 的四个树投影方程均为 refl；没有识别两份合法性证据，
比较的 equal 也只返回原树相等，不返回 Level 记录相等。
Λ 及 ΩΛ 都在同一 Level 类型中合法，定义与闭包没有阶段参数。
这些是层号与位置的基础，尚不是内部 View／FGH／终点值验收的成品交付。
