# `Lev` 取并 (二): 拷贝墙 `copy→⊥` 的哪一条前提不成立

> 不含记号. 入口 [ColimW](ColimW.lagda.md). 对照 [AdmWNegCopy](AdmWNegCopy.lagda.md): `copy→⊥ T C loc` 说对一切种类结构 $T$, 一个形状 `CopyShape T` (一个坐标为 `A` 的种类 $\kappa_0$, 世界 `W₂ a₀ a₁` 里 $a_0$ 之下与 $a_1$ 之下的坐标都有界, `toH` 节点合法) 加上逐分量合法 `LocalLg` 推出 $\bot$. 它的三个模型: `M1` 缺 `lgι`, `M2` 缺 `LocalLg` (合法性要求两个分量可比), `M3` 缺第二个证据的界.
>
> **在 `LevC x₀` 里: 形状成立, `LocalLg` 不成立** (`shapeA`, `¬localA`, 定理). 取底种类 `κA`. 在 `LevC` 里底种类的一切拷贝只读世界的**一个** `A` 分量 (`ColimWKS.readA`), 所以 "两个证据" 只能是同一个分量的两个第一位置: `W₂ a₀ a₁` 取 `A` 分量为 $\lim(a_0, a_1, a_1, \dots)$ (字面公共上界, 一般不合法), `bd₀`, `bd₁` 是进极限的第 0 项与第 1 项. `lgι` 成立 (第一位置就是 `A` 的 $\lhd$, 单调就是 `toH-⊲`). 由 `copy→⊥`, `LocalLg` 不成立: `W₂ X₂ X′` 不合法.
>
> **与三个模型的关系.** 同 `M2`: 缺的是逐分量合法. 区别: `M2` 有两个分量, 合法性要求它们可比; `LevC` 只有一个分量, 两份拷贝字面上就是同一个界, 不需要另加相干条件. 拷贝问题在 `LevC` 里不以 "两个证据下的两个分量" 出现 (界里没有证据的存在量词, `Bd` 是一个命题, 不是 $\Sigma$).
>
> **范围.** 只说这一个种类、这一个形状. 不说 `LevC` 上没有别的拷贝问题: 字面不同而逐点相等的层号树 (例如 `up ω₀` 与 `hl finH`) 读两个分量 (判断, 见入口).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWCopy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWNegCopy using (toH; toH-⊲; Lg-toH; CopyShape; LocalLg; copy→⊥; copy-illegal; X₂; X′; lgX₂; lgX′)
open import OCF.Align.ColimWIf
open import OCF.Align.ColimWKS
```

## §1 形状

```agda
pair : A → A → ℕ → A
pair a₀ a₁ zero = a₀
pair a₀ a₁ (suc _) = a₁

W₂C : A → A → GW S₁
W₂C a₀ a₁ = alim (pair a₀ a₁) , λ y → hz

lgιA : LgB {LevC x₀} (hΩ κA (λ e → toH e))
lgιA = (λ lw e e′ p → toH-⊲ p) , (λ c lc → Lg-toH c lc)

shapeA : CopyShape (LevC x₀)
shapeA = record
  { κ₀ = κA ; inE = λ x → x ; outE = λ x → x ; oi = λ x → refl
  ; W₂ = W₂C
  ; bd₀ = λ q → C.lim 0 q
  ; bd₁ = λ q → C.lim 1 q
  ; lgι = lgιA }
```

## §2 逐分量合法不成立

```agda
¬localA : ¬ LocalLg (LevC x₀) shapeA
¬localA loc = copy→⊥ (LevC x₀) shapeA loc

-- 具体地: 那个世界不合法, 尽管 X₂ 与 X′ 各自合法
illegal-W₂ : Lg X₂ × Lg X′ × ¬ LgW (LevC x₀) (W₂C X₂ X′)
illegal-W₂ = lgX₂ , lgX′ , copy-illegal (LevC x₀) shapeA
```

另一方面, 两份拷贝共用的合法世界是有的 (前提可满足): 公共上界取合法的 $X_2$ 本身时世界合法.

```agda
legal-same : LgW (LevC x₀) (X₂ , λ y → hz)
legal-same = lgG→ x₀ {X₂ , λ y → hz} (lgX₂ , λ y → tt)
```
