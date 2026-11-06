# Fab6: 与 CRw 闭项的对照 (有限测试)

> 不含记号. 入口 [Fab6](Fab6.lagda.md). 验收文件: 导入 [CRw](CRw.lagda.md), 不在 `Fab6` 的导入闭包里. 全文 `--safe --without-K --lossy-unification`.
>
> 两边的闭项是**不同类型**的布劳威尔树 (`Fab6Base.HB X⊥ S⊥` 与 `CRwBase.HB S⊥`), 没有跨类型的关系定理. 这里是**有限测试** (同 `CRwCmp`): 有界展开 (深度 $k$, 每个 ℕ-极限展开前 $k$ 项) 的结点数, 由 `refl` 检查. 测试不是证明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fab6Cmp where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.Fab6Base as N
open import OCF.Lean.Fab6 using (TX; TU1; TU2)
import OCF.Lean.CRwBase as C
import OCF.Lean.CRw as R

szN : ℕ → N.Cd → ℕ
szsN : ℕ → ℕ → (ℕ → N.Cd) → ℕ
szN zero x = 0
szN (suc k) N.hz = 1
szN (suc k) (N.hs x) = suc (szN (suc k) x)
szN (suc k) (N.hl f) = suc (szsN k (suc k) f)
szN (suc k) (N.hΩ () g)
szN (suc k) (N.hE () _ _)
szsN k zero f = 0
szsN k (suc i) f = szN k (f i) + szsN k i f

szC : ℕ → C.Cd → ℕ
szsC : ℕ → ℕ → (ℕ → C.Cd) → ℕ
szC zero x = 0
szC (suc k) C.hz = 1
szC (suc k) (C.hs x) = suc (szC (suc k) x)
szC (suc k) (C.hl f) = suc (szsC k (suc k) f)
szC (suc k) (C.hΩ () g)
szsC k zero f = 0
szsC k (suc i) f = szC k (f i) + szsC k i f
```

深度 4 的结点数 (数值见入口 §5).

```agda
sX : szN 4 TX ≡ 41
sX = refl

sU1 : szN 4 TU1 ≡ 41
sU1 = refl

sU2 : szN 4 TU2 ≡ 32
sU2 = refl

cX : szC 4 R.TX ≡ 41
cX = refl

cU1 : szC 4 R.TU1 ≡ 41
cU1 = refl

cU2 : szC 4 R.TU2 ≡ 32
cU2 = refl
```

层的代数 ([Fab6Lay](Fab6Lay.lagda.md)) 的闭项, 深度 4 的结点数 (只记录, 不与别处比: 两段折法的种子与地板的分支都与 CRw 不同; 深度 4 的结点数不随强度单调). 结果: `T₀` 36, `TΩΩ` 44, `TΩΩ₂` 41, `TΩ²` 45, `TΩ³` 45, `TΩ^ω` 41, `TΩ^Ω` 41.

```agda
open import OCF.Lean.Fab6Lay using (T₀; TΩΩ; TΩΩ₂; TΩ²; TΩ³; TΩ^ω; TΩ^Ω)
open import Data.Product using (_×_; _,_)

szLay : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
szLay = szN 4 T₀ , szN 4 TΩΩ , szN 4 TΩΩ₂ , szN 4 TΩ² , szN 4 TΩ³ , szN 4 TΩ^ω , szN 4 TΩ^Ω

szLay≡ : szLay ≡ (36 , 44 , 41 , 45 , 45 , 41 , 41)
szLay≡ = refl
```
