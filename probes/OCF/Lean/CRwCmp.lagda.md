# CRw: 与原闭项的对照 (有限测试)

> 不含记号. 入口 [CRw](CRw.lagda.md). 验收文件: 导入原来的 [X1Up](../Align/X1Up.lagda.md) 与 [PathOut](../Align/PathOut.lagda.md), 不在 `CRw` 的导入闭包里. 全文 `--safe --without-K --lossy-unification`.
>
> 两边的闭项是**不同类型**的布劳威尔树 (`OCF.Lean.CRwBase.HB S⊥` 与 `OCF.Align.HtTowerTy.HB LFReTy.S⊥`), 没有跨类型的关系定理. 这里是**有限测试**: 有界展开 (深度 4, 每个 ℕ-极限展开前 4 项) 的结点数, 由 `refl` 检查. 测试不是证明. 结果: `TU2`, `TU1` 两边相同 (32, 41; 数值见 `CRw` 文末); `TX` 与 PathOut 的 `TXL` **不同** (41 对 45). 原因 (判断, 读代码): PathOut 的 $X_1$ 种类结构把 $\Omega_1$ 单独放一个分量 (`κΩ`), 分量 $0$ 里的 $\Omega_1$ 拷贝不移动世界; 本路的 `XS` 没有单独的分量, $\Omega_1$ 就是分量 $0$ 的新种类, 地板 `topL` 的分支里第一个被加的 $\Omega_1$ 结点 (`gt 1` 里的 `ι 0 Ω₁`) 在本路移动世界并回灌, 在 PathOut 不移动. 深度 4 的路径指纹 (沿第 $i$ 项走) 两边都全是极限, 不区分, 所以没有列.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CRwCmp where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.CRwBase as N
open import OCF.Lean.CRw using (TX; TU1; TU2)
import OCF.Align.HtTowerTy as O
open import OCF.Align.LFReTy using (S⊥)
import OCF.Align.X1Up as X
import OCF.Align.PathOut as P

```

有界展开的结点数 (同 `LeanTCmp`): 深度 $k$, 每个 ℕ-极限只展开前 $k$ 项.

```agda
szN : ℕ → N.Cd → ℕ
szsN : ℕ → ℕ → (ℕ → N.Cd) → ℕ
szN zero x = 0
szN (suc k) N.hz = 1
szN (suc k) (N.hs x) = suc (szN (suc k) x)
szN (suc k) (N.hl f) = suc (szsN k (suc k) f)
szN (suc k) (N.hΩ () g)
szsN k zero f = 0
szsN k (suc i) f = szN k (f i) + szsN k i f

szO : ℕ → O.HB S⊥ → ℕ
szsO : ℕ → ℕ → (ℕ → O.HB S⊥) → ℕ
szO zero x = 0
szO (suc k) O.hz = 1
szO (suc k) (O.hs x) = suc (szO (suc k) x)
szO (suc k) (O.hl f) = suc (szsO k (suc k) f)
szO (suc k) (O.hΩ () g)
szsO k zero f = 0
szsO k (suc i) f = szO k (f i) + szsO k i f
```

```agda
sU2 : szN 4 TU2 ≡ szO 4 X.TU2
sU2 = refl

sU1 : szN 4 TU1 ≡ szO 4 X.TU1
sU1 = refl

-- 不同: TX 与 PathOut 的 TXL
sX : szN 4 TX ≡ 41
sX = refl

sXL : szO 4 P.TXL ≡ 45
sXL = refl
```
