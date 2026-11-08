# 富合法化与 Third 默认世界：互相独立的两个字段

本篇不改 Third。指标界族允许任意合法树，因此包含由全种类富合法化
计算地板界的替换；组件仍用原 `wT`。结论针对实际 `Sb` 全族：
组件顶种类在该世界只能读零坐标。增加外层高度界不改变这个事实。
这不是新的全局不可能性，也不是序数值上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLegNegWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw
open import OCF.Lean.ThirdLeg using (wT; lwT)
open import OCF.Lean.LHRecLeg using (here; viaL)
import OCF.Lean.ThirdRichLegIf as Rich

one : ∀ {S} → HB S
one = hs hz

module Defaults (bounds : ∀ n → HB (Sb n))
                (bounds-legal : ∀ n → LgB (bounds n)) where
  world : ∀ n → Wd (Sb n)
  world zero = tt
  world (suc n) (inj₁ _) = world n , bounds n
  world (suc n) (inj₂ c) = wT (Sb n) (world n) (hs c)

  world-legal : ∀ n → LgW (Sb n) (world n)
  world-legal zero = tt
  world-legal (suc n) (inj₁ _) = world-legal n , bounds-legal n
  world-legal (suc n) (inj₂ c) = lwT (Sb n) (world n) (world-legal n) (hs c)

  module Slot (n : ℕ) (c : HB (Sb n)) where
    U = Sb (suc n)
    V = Tw (Sb n) c

    κ : K U
    κ = inj₂ c , inj₂ tt

    only-zero : ∀ {e} → Bd U κ e (world (suc n)) → e ≡ hz
    only-zero hself = refl

    no-one : ¬ Bd U κ one (world (suc n))
    no-one ()

    height : HB U
    height = hΩ κ (λ _ → one)

    height-legal : LgB height
    height-legal = (λ _ _ _ _ → hself) , (λ _ _ → tt)

    missed-kind : K (Tw U height)
    missed-kind = one , inj₂ tt

    no-position : ¬ Pos U (world (suc n)) height missed-kind
    no-position (b , _) = no-one b

    -- 即使把外层界取成该合法高度的后继，Pos 所需的低层槽仍为零。
    common-bound : height ⊲[ world (suc n) ] hs height
    common-bound = hsuc hself

    bound-legal : LgB (hs height)
    bound-legal = height-legal

    -- 正面实例：同时提高每个组件顶槽至 1，不判任意两个组件编号相等。
    moved : Wd U
    moved (inj₁ _) = world n , bounds n
    moved (inj₂ d) = wT (Sb n) (world n) d , one

    moved-legal : LgW U moved
    moved-legal (inj₁ _) = world-legal n , bounds-legal n
    moved-legal (inj₂ d) = lwT (Sb n) (world n) (world-legal n) d , tt

    position-after-move : Pos U moved height missed-kind
    position-after-move = hself , tt

    -- 用共享接口中的真正富 θ，而非一个常值实现。源 g 本身合法。
    branch : HB V → HB U
    branch hz = hz
    branch (hs _) = one
    branch (hl _) = hz
    branch (hΩ _ _) = hz

    branch-legal : ∀ e → LgB (branch e)
    branch-legal hz = tt
    branch-legal (hs _) = tt
    branch-legal (hl _) = tt
    branch-legal (hΩ _ _) = tt

    module Θ = Rich.New (viaL {F = FX (Sb n)} here (inj₂ c)) branch

    rich-zero : Θ.θ hz ≡ hz
    rich-zero = refl

    rich-one : Θ.θ one ≡ one
    rich-one = refl

    rich-two : Θ.θ (hs one) ≡ hs (hs one)
    rich-two = refl

    rich-node : HB U
    rich-node = hΩ κ Θ.θ

    rich-node-legal : LgB rich-node
    rich-node-legal =
      (λ lw b b′ p → Θ.θ-⊲ p) ,
      (λ lw b → Θ.Lg-θ branch-legal _
        (lgB⊲ b (proj₁ (lw (inj₂ c))) (proj₂ (lw (inj₂ c)))))

    -- 富 θ 已保留非零行为，但旧世界的准入仍不能选择该坐标。
    rich-nonconstant : ¬ (Θ.θ one ≡ Θ.θ hz)
    rich-nonconstant ()
```

`only-zero` 不含合法化参数的任何计算假设；`bounds` 可以来自旧合法化、
富合法化或其他全合法函数。`rich-node-legal` 与 `rich-nonconstant` 给实际
非空正对照。`position-after-move` 只修复展示的槽，不冒称给出整个动态
折叠或所有分支的路径证书。下一步所缺的是组件 `inj₂ c` 的世界第二投影，
不是把外部高度界再加一个后继。

## 直接使用本轮完整富合法化

下列指标界逐字采用新 `Build.legS (fl n)`，可数初界仍任取合法 `c₀`。
因此不是仅有恒零合法化的反例。源节点全部分支为 1，本身合法；
实际富合法化把其坐标 0、1 的输出分别变成 1、3。
默认世界只能访问前者。此处只陈述原 `Bd` 的可入域，不称某条具体
运行链已经访问所有可入点。

```agda
import OCF.Lean.ThirdRichLegBuild as Build

module Actual (c₀ : Cd) (lc₀ : LgB c₀) where
  bounds : ∀ n → HB (Sb n)
  bounds zero = c₀
  bounds (suc n) = Build.legS (suc n) (fl (suc n))

  bounds-legal : ∀ n → LgB (bounds n)
  bounds-legal zero = lc₀
  bounds-legal (suc n) = Build.Lg-legS (suc n) (fl (suc n))

  module D = Defaults bounds bounds-legal

  module At (n : ℕ) (c : HB (Sb n)) where
    open D.Slot n c

    input : HB U
    input = hΩ κ (λ _ → one)

    input-legal : LgB input
    input-legal = (λ _ _ _ _ → hself) , (λ _ _ → tt)

    output : HB U
    output = Build.legS (suc n) input

    output-legal : LgB output
    output-legal = Build.Lg-legS (suc n) input

    output-branch : HB V → HB U
    output-branch = Build.θS (suc n) here κ (λ _ → one)

    output-head : output ≡ hΩ κ output-branch
    output-head = refl

    output-zero : output-branch hz ≡ one
    output-zero = refl

    output-one : output-branch one ≡ hs (hs one)
    output-one = refl

    output-nonconstant : ¬ (output-branch one ≡ output-branch hz)
    output-nonconstant ()

    admitted-output : ∀ {e} → Bd U κ e (D.world (suc n)) → output-branch e ≡ one
    admitted-output p with only-zero p
    ... | refl = refl

    actual-no-position : ¬ Pos U (D.world (suc n)) height missed-kind
    actual-no-position = no-position

    actual-position-after-move : Pos U moved height missed-kind
    actual-position-after-move = position-after-move
```

最后两个命题使用完全相同的高度、种类和新合法化计算的指标界。
前者失败、后者成立的差别仅在组件顶槽从 0 变为 1。
