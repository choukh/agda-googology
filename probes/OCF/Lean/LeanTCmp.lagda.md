# LeanT 验收: 与原 `TΛ` 的对照 (有限测试)

> 验收文件, 不进成品: 导入原模块 [FabLFReGen](../Align/FabLFReGen.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.
>
> **为什么只有有限测试.** `TΛ′ : HB S⊥` 与 `TΛ : CumReadCF.A` 是不同类型上的闭项, 中间的种类结构、高度、数据树、世界也都是不同的类型 (两边各自定义). 定义相等不可能 (类型不同); 树的互模拟要对整个折叠 (`Run` 一族十几个互递归函数, 数据树含对世界的函数) 递归建立对应, 未做. 这里给的是: 沿若干条路径读出的有限指纹在两边相同 (`refl`, 检查器把两边都算出来).
>
> **指纹** `fp k i x`: 沿树走, 极限处取第 $i$ 项, 记下每两个极限之间的后继个数, 最多走 $k$ 个极限. 这是有限测试, 不是证明: 它只看见树的有限部分.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanTCmp where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase using (HB; hz; hs; hl; hΩ; S⊥)
open import OCF.Lean.LeanT using (TΛ′)
import OCF.Align.CumReadCF as C
open import OCF.Align.FabLFReGen using (TΛ)
```

```agda
fp′ : ℕ → ℕ → ℕ → HB S⊥ → List ℕ
fp′ k i s hz = s ∷ []
fp′ k i s (hs x) = fp′ k i (suc s) x
fp′ zero i s (hl f) = s ∷ []
fp′ (suc k) i s (hl f) = s ∷ fp′ k i 0 (f i)
fp′ k i s (hΩ (() , _) g)

fpA : ℕ → ℕ → ℕ → C.A → List ℕ
fpA k i s C.azero = s ∷ []
fpA k i s (C.asuc x) = fpA k i (suc s) x
fpA zero i s (C.alim f) = s ∷ []
fpA (suc k) i s (C.alim f) = s ∷ fpA k i 0 (f i)
```

沿一列下标走: 第 $j$ 个极限取列里第 $j$ 项, 列用完就停.

```agda
fpL′ : List ℕ → ℕ → HB S⊥ → List ℕ
fpL′ is s hz = s ∷ []
fpL′ is s (hs x) = fpL′ is (suc s) x
fpL′ [] s (hl f) = s ∷ []
fpL′ (i ∷ is) s (hl f) = s ∷ fpL′ is 0 (f i)
fpL′ is s (hΩ (() , _) g)

fpLA : List ℕ → ℕ → C.A → List ℕ
fpLA is s C.azero = s ∷ []
fpLA is s (C.asuc x) = fpLA is (suc s) x
fpLA [] s (C.alim f) = s ∷ []
fpLA (i ∷ is) s (C.alim f) = s ∷ fpLA is 0 (f i)
```

**有界展开的结点数** `sz k x`: 极限处展开前 $k$ 项 (各用 $k-1$ 的预算), 后继不耗预算. 一次看见 $k^k$ 量级条路径.

```agda
sz′ : ℕ → HB S⊥ → ℕ
szs′ : ℕ → ℕ → (ℕ → HB S⊥) → ℕ
sz′ zero x = 0
sz′ (suc k) hz = 1
sz′ (suc k) (hs x) = suc (sz′ (suc k) x)
sz′ (suc k) (hl f) = suc (szs′ k (suc k) f)
sz′ (suc k) (hΩ (() , _) g)
szs′ k zero f = 0
szs′ k (suc i) f = sz′ k (f i) Data.Nat.+ szs′ k i f

szA : ℕ → C.A → ℕ
szsA : ℕ → ℕ → (ℕ → C.A) → ℕ
szA zero x = 0
szA (suc k) C.azero = 1
szA (suc k) (C.asuc x) = suc (szA (suc k) x)
szA (suc k) (C.alim f) = suc (szsA k (suc k) f)
szsA k zero f = 0
szsA k (suc i) f = szA k (f i) Data.Nat.+ szsA k i f
```

## 有限测试

```agda
fp-0 : fp′ 30 0 0 TΛ′ ≡ fpA 30 0 0 TΛ
fp-0 = refl

fp-1 : fp′ 30 1 0 TΛ′ ≡ fpA 30 1 0 TΛ
fp-1 = refl

fp-2 : fp′ 30 2 0 TΛ′ ≡ fpA 30 2 0 TΛ
fp-2 = refl

fp-mix : fpL′ (1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ []) 0 TΛ′ ≡ fpLA (1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ []) 0 TΛ
fp-mix = refl

sz-5 : sz′ 5 TΛ′ ≡ szA 5 TΛ
sz-5 = refl

sz-6 : sz′ 6 TΛ′ ≡ szA 6 TΛ
sz-6 = refl

sz-7 : sz′ 7 TΛ′ ≡ 7238
sz-7 = refl

sz-7A : szA 7 TΛ ≡ 7238
sz-7A = refl
```

**结论 (有限测试, 不是证明).** 沿下标 0, 1, 2 的路径走 30 个极限的指纹, 一条混合下标路径的指纹, 与有界展开的结点数 ($k=5,6,7$; 交互模式另算到 $k=8$: 两边都是 59087) 在两边相同. `fp-1` 的指纹不平凡 (含 2), `sz` 一次覆盖 $k^k$ 量级的路径. 这支持 "同一个数学对象" 的判断, 但只看见树的有限部分.
