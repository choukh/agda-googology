# `T-Ω` 的值验收 (三): `T-Ω` 与 `SumOne.T₀` 不互模拟

> 不含记号, 不是验收文件. 入口 [EndLowT](EndLowT.lagda.md).
>
> `SumOneAccept.T₀≈` 已证 `SumOne.T₀` 与 `BTBOᴵ` 互相 $\preccurlyeq$. 最便宜的路是证 `T-Ω` 与 `T₀` 结构互模拟 ($\cong$), 再搬. `HtFeedTest.a6` (有限测试) 说两者到深度 6 (宽 2) 相同; 本次的测试到深度 16 (宽 2) 也相同 (编译过的 `refl`, 测试档, 不在本文件). **但它们不 $\cong$** (`T-Ω≇T₀`, 定理): 沿 ℕ-分支下标 $[1,2,1,0,0,1,0,0,0,0,0]$ (后继透明) 走到的节点, 两边的构造子不同. 差在第 3 支 (宽 3), 与 [EndLowTNeg](EndLowTNeg.lagda.md) 的诊断一致: 两个折叠的可数层 $\Omega_L$ 写法不同 (`HtFeedTree.Ωd` 只看最外构造子, `SumOneTree.Ωd` 先走 `Dif`).
>
> 所以 `T-Ω` 的序数值验收不能经 $\cong$ 从 `SumOne` 搬来; 要么是值层的比较, 要么是新的对照 (见入口).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLowTShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open FL using (Ordᶜ; _≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Align.HtFeedClosed as HC
import OCF.Align.SumOneClosed as SO
```

`walk p x`: 沿下标表 $p$ 走, 后继透明, ℕ-极限取第 $i$ 支; 表走完就看构造子. 第 0 层没有 `limᵢ`, `up`. $\cong$ 保 `walk` (`walk-≅`).

```agda
data Sh : Set where
  ʷz ʷs ʷl : Sh

shape : Ordᶜ FL.zero → Sh
shape FL.zero = ʷz
shape (FL.suc _) = ʷs
shape (FL.lim _) = ʷl
shape (FL.limᵢ () _)
shape (FL.up () _)

walk : List ℕ → Ordᶜ FL.zero → Sh
walk [] x = shape x
walk (i ∷ p) FL.zero = ʷz
walk (i ∷ p) (FL.suc x) = walk (i ∷ p) x
walk (i ∷ p) (FL.lim f) = walk p (f i)
walk (i ∷ p) (FL.limᵢ () _)
walk (i ∷ p) (FL.up () _)

walk-≅ : ∀ p {x y : Ordᶜ FL.zero} → x ≅ y → walk p x ≡ walk p y
walk-≅ [] z≅ = refl
walk-≅ [] (s≅ e) = refl
walk-≅ [] (l≅ h) = refl
walk-≅ (i ∷ p) z≅ = refl
walk-≅ (i ∷ p) (s≅ {a = a} {b = b} e) = walk-≅ (i ∷ p) {a} {b} e
walk-≅ (i ∷ p) (l≅ {f = f} {g = g} h) = walk-≅ p {f i} {g i} (h i)
walk-≅ p (lᵢ≅ {p = ()} e h)
walk-≅ p (upˡ {r = ()} e)
walk-≅ p (upʳ {r = ()} e)

path : List ℕ
path = 1 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

T-Ω≇T₀ : ¬ (HC.ord HC.T-Ω ≅ SO.ord SO.T₀)
T-Ω≇T₀ e with walk-≅ path e
... | ()
```
