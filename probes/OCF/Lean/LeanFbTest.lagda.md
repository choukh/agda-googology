# LeanFb 测试: 有回灌的 `TF` 与同一折叠全有损的 `TL` (有限测试)

> 测试文件, 不进成品. 全文 `--safe --without-K --lossy-unification`. `TL`: 同一个 `T = SLs`, 同一个最高层 `ΛF`, 同一个底种类, 级回灌参数取一切有损. `fp′`, `fpL`, `sz′` 同 [LeanTCmp](LeanTCmp.lagda.md) 的指纹与有界展开. `ΨL`, `nav`, `p0` 供交互求值用 (路径取自 `NegLeanFbInst.exec-TF0`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbTest where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (TF; ΨF; bkS; Act)
import OCF.Lean.LeanTFold as Fold
open Tree SLs
open FoldTy SLs ΛF

module FL = Fold SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt)

TL : HB S⊥
TL = sum hz (n1 ⨾ yc (FL.Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself (λ p lW′ _ Y → FL.Stp Y) n0 (st FL.zeroD n0 n0)) (FL.τ₀ (lw₀ L₀)))

fp′ : ℕ → ℕ → ℕ → HB S⊥ → List ℕ
fp′ k i s hz = s ∷ []
fp′ k i s (hs x) = fp′ k i (suc s) x
fp′ zero i s (hl f) = s ∷ []
fp′ (suc k) i s (hl f) = s ∷ fp′ k i 0 (f i)
fp′ k i s (hΩ (() , _) g)

fpL : List ℕ → ℕ → HB S⊥ → List ℕ
fpL is s hz = s ∷ []
fpL is s (hs x) = fpL is (suc s) x
fpL [] s (hl f) = s ∷ []
fpL (i ∷ is) s (hl f) = s ∷ fpL is 0 (f i)
fpL is s (hΩ (() , _) g)

sz′ : ℕ → HB S⊥ → ℕ
szs′ : ℕ → ℕ → (ℕ → HB S⊥) → ℕ
sz′ zero x = 0
sz′ (suc k) hz = 1
sz′ (suc k) (hs x) = suc (sz′ (suc k) x)
sz′ (suc k) (hl f) = suc (szs′ k (suc k) f)
sz′ (suc k) (hΩ (() , _) g)
szs′ k zero f = 0
szs′ k (suc i) f = sz′ k (f i) Data.Nat.+ szs′ k i f

ΨL : D hz (w₀ L₀)
ΨL = n1 ⨾ yc (FL.Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself (λ p lW′ _ Y → FL.Stp Y) n0 (st FL.zeroD n0 n0)) (FL.τ₀ (lw₀ L₀))

data Dir : Set where
  dL dR : Dir
  dN : ℕ → Dir

nav : ∀ {W} → List Dir → D hz W → D hz W
nav [] x = x
nav (dL ∷ p) (x ⨾ y) = nav p x
nav (dR ∷ p) (x ⨾ y) = nav p y
nav (dN n ∷ p) (nl d) = nav p (d n)
nav (_ ∷ p) _ = n0

-- 头 0 的闭包结点在第 0 层目标上的输出 (路径取自 NegLeanFbInst.exec-TF0), 第 k 项
p0 : ℕ → List Dir
p0 k = dR ∷ dR ∷ dN 1 ∷ dN 0 ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ dN k ∷ []
```

**有限测试 (不是证明).** 有界展开的结点数 ($k\le7$) 在 `TF` 与 `TL` 上相同, 而且与 `TΛ′` 的 7238 (`LeanTCmp.sz-7`) 相同: 在这一深度上看不见回灌. 回灌出现在闭项计算里的位置见 `LeanFbShape.exec-TF0` 一族 (定理), 它们离根比 $k=7$ 的预算深.

```agda
sz-5 : sz′ 5 TF ≡ sz′ 5 TL
sz-5 = refl

sz-7F : sz′ 7 TF ≡ 7238
sz-7F = refl

sz-7L : sz′ 7 TL ≡ 7238
sz-7L = refl
```
