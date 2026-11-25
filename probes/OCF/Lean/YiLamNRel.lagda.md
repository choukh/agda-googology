# `Uniᴾ` 与 `Uni` 的关系: 部分和的写法不要单调律; `YiLamFold` 不满足 `Uni` 的链行

非验收文件. 编译定理, 无前提. (一) 任意 `Uniᴾ` 的 Ω 结点 `top` 行右边合法, 只用 `Kb-br` 与各观察的 `Ψ-lgl`, 不用联系两个链点的律 (`rowᶜ-lglᴾ`); 相邻部分和总在第一位置 (`chain-upᴾ`, 对一切序列).
(二) 不写部分和时, 各项合法推不出极限合法 (`plain-needs-mono`), 这就是 `Uni` 要 `top-up` 的地方 (`YiUniForced.chain-up`). (三) 用 `Lam` 的其余字段, `Uni` 的 `top-rowᶜ` 在 `tw 2` 上不成立 (`no-plain-row`).
不否定 `Uni` 另选字段时的实例 (判断: 填不上). 接口 [YiLamIf](YiLamIf.lagda.md), 实例 [YiLamNInst](YiLamNInst.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNRel where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; Way; fold; Ext; psum; psum-lgl; plus-weak; ΩT; ΩT-lgl)
open import OCF.Lean.YiLamFold using (Lw-tw)
open import OCF.Lean.YiLamIf using (Uniᴾ)
open import OCF.Lean.YiLamNInst using (Lam)
```

## 1 部分和的写法: 链行合法不要单调律

```agda
module _ (U : Uniᴾ) where
  open Uniᴾ U

  obsᴾ : ∀ m {k g} (V : Bd (lc k g)) → Ext m (lc k g) → ℕ → Raw m
  obsᴾ m V x n = Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top

  rowᶜ-lglᴾ : ∀ m {k g} (V : Bd (lc k g)) x →
    Lgl m (ΩT m k (ωw m V x) (Kb m V x) (psum m (obsᴾ m V x)))
  rowᶜ-lglᴾ m {k} V x = ΩT-lgl m k (ωw m V x) (Kb m V x) _ (Kb-br m V x)
    (psum-lgl m _ (λ n → Ψ-lgl m (bC V (cpt V n) (cpt-lgl V n)) _ G.top tt))

  chain-upᴾ : ∀ m {k g} (V : Bd (lc k g)) x n →
    Cp m (psum m (obsᴾ m V x) n) (psum m (obsᴾ m V x) (suc n))
  chain-upᴾ m V x n = plus-weak m _ _
```

## 2 不写部分和时要单调

```agda
spike : ℕ → R
spike zero = G.suc G.zero
spike (suc n) = G.zero

spike-lgl : ∀ n → Lgl zero (spike n)
spike-lgl zero = tt
spike-lgl (suc n) = tt

plain-needs-mono : Σ (ℕ → R) λ h → (∀ n → Lgl zero (h n)) × (Lgl zero (G.lim h) → ⊥)
plain-needs-mono = spike , spike-lgl , λ { (st , _) → no (st 0) }
  where
  no : Cp zero (G.suc G.zero) G.zero → ⊥
  no (inj₁ ())
  no (inj₂ ())

spike-psum : Lgl zero (G.lim (psum zero spike))
spike-psum = psum-lgl zero spike spike-lgl
```

## 3 `Lam` 的折叠不满足 `Uni` 的链行

最左深度 `ld`: 第 0 层的加法 `a + b` 的最左深度大于 `b` 的 (当 `a` 不是 `zero`, `top`).

```agda
ld : R → ℕ
ld G.zero = 0
ld (G.suc a) = suc (ld a)
ld (G.lim f) = suc (ld (f 0))
ld (G.lc () g)
ld (G.em () a)
ld G.top = 0

ld-grow : ∀ a b → 1 ≤ ld a → ld b < ld (plus zero a b)
ld-grow a G.zero p = p
ld-grow a (G.suc b) p = s≤s (ld-grow a b p)
ld-grow a (G.lim f) p = s≤s (ld-grow a (f 0) p)
ld-grow a (G.lc () g) p
ld-grow a (G.em () d) p
ld-grow a G.top p = s≤s z≤n

plus-ne : ∀ a b → 1 ≤ ld a → plus zero a b ≡ b → ⊥
plus-ne a b p e = <-irrefl (cong ld (sym e)) (ld-grow a b p)

at1 : R → R
at1 (G.lim f) = f 1
at1 _ = G.zero

module L = Uniᴾ Lam

obs₂ : ℕ → R
obs₂ = obsᴾ Lam zero (Lw-tw 2) (λ _ → fold)

no-plain-row : L.Ψ zero (Lw-tw 2) (λ _ → fold) G.top ≡
  ΩT zero zero (L.ωw zero (Lw-tw 2) (λ _ → fold)) (L.Kb zero (Lw-tw 2) (λ _ → fold)) obs₂ → ⊥
no-plain-row e = plus-ne (obs₂ 0) (obs₂ 1) (s≤s z≤n) (cong at1 e)
```
