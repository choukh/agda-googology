# 只对可入层号给分量 (三): `copy→⊥` 的哪一条前提不成立

> 不含记号. 入口 [ColimA](ColimA.lagda.md). 对照 [AdmWNegCopy](AdmWNegCopy.lagda.md) (`copy→⊥ T C loc`: 形状 `CopyShape T` 加逐分量合法 `LocalLg` 推出 $\bot$) 与 [ColimWCopy](ColimWCopy.lagda.md) (`LevC x₀` 里形状成立, `LocalLg` 不成立). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **在 `LevC′ x₀ wω` 里: 形状成立, `LocalLg` 不成立** (`shapeA′`, `¬localA′`, 定理). 取底种类 `κA`: 它的界只读世界的一个 `A` 分量 (`globA`), 与 `ColimWCopy` 相同; `W₂ a₀ a₁` 取 `A` 分量为 $\lim(a_0, a_1, a_1, \dots)$, 两个 "证据" 是进极限的第 0 项与第 1 项. 由 `copy→⊥`, 逐分量合法不成立.
>
> **与拷贝的关系 (写明范围).** `CopyShape` 说的是**一个种类**的两个证据. 在 `LevC′` 里一个种类只有一条路径, 所以 `CopyShape` 的两个证据只能落在同一个分量里, 结论与 `ColimWCopy` 一样 (缺 `LocalLg`). 同一层号经两条路径出现是**两个种类** (`κ₂`, `κ₂′`), 不在 `CopyShape` 的范围里; 它们之间的问题是认同, 由 `ColimAKS.noCrossA` (不相干时读到不同的界, 定理) 与 `crossA` (相干时互推, 定理) 说清.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimACopy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmWNegCopy using (toH; toH-⊲; Lg-toH; CopyShape; LocalLg; copy→⊥; copy-illegal; X₂; X′; lgX₂; lgX′)
open import OCF.Align.ColimWIf using (x₀)
open import OCF.Align.ColimWCopy using (pair)
open import OCF.Align.ColimWNeg using (wω)
open import OCF.Align.ColimAIf
open import OCF.Align.ColimAKS
```

```agda
T′ : KS
T′ = LevC′ x₀ wω

W₂A : A → A → GWA x₀ wω
W₂A a₀ a₁ = alim (pair a₀ a₁) , λ y p → hz

lgιA′ : LgB {T′} (hΩ κA (λ e → toH e))
lgιA′ = (λ lw e e′ p → toH-⊲ p) , (λ c lc → Lg-toH c lc)

shapeA′ : CopyShape T′
shapeA′ = record
  { κ₀ = κA ; inE = λ x → x ; outE = λ x → x ; oi = λ x → refl
  ; W₂ = W₂A
  ; bd₀ = λ q → C.lim 0 q
  ; bd₁ = λ q → C.lim 1 q
  ; lgι = lgιA′ }

¬localA′ : ¬ LocalLg T′ shapeA′
¬localA′ loc = copy→⊥ T′ shapeA′ loc

illegal-W₂A : Lg X₂ × Lg X′ × ¬ LgW T′ (W₂A X₂ X′)
illegal-W₂A = lgX₂ , lgX′ , copy-illegal T′ shapeA′

-- 前提可满足: 公共上界取合法的 X₂ 时世界合法
legal-sameA : LgW T′ (X₂ , λ y p → hz)
legal-sameA = lgGA→ x₀ wω x₀ hself {X₂ , λ y p → hz} (lgX₂ , λ y p → tt)
```
