# 完整候选折叠: 带下标层证据的换基证据

> 判决: 定义与编译定理, 不读记号, 不改主线. 证据 `Rb` 比 `YiBSBase.Rb` 多带下标层 k 的证据, 所以沿任何目标路径都能降下 (`rb≤`, 含 `ink`); `Schema`, `route`, `split` 原样导入.
> 塔各项与 Λ 的证据是闭项 (`rb-tw`, `rb-Λ`; 处处无 `Schema` 的证据 `rb-no` 作对照), 且在每个 Ω 形状结点 (含下标层里的) 上都有 `Schema` (`Full`, `full-tw`, `full-Λ`); 满证据沿路径与读回偏移保持 (`full≤`, `full-rbO`).
> 不否定什么. 来源: `rbO`, `rb-tw` 改自 `YiBSBase`, `Full` 一族改自 `YiBCCover` (多一个下标层分量). 折叠在 [YiUFFold](YiUFFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUFBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiBSBase using (Schema; schema; floor; offsets; ok-floor; index-floor; ok-offsets; shape; raiseO)
```

## 证据

Ω 形状结点上: 下标层 k 的证据, 加可缺的 `Schema`. `rb≤` 沿目标路径降下, 经下标层侧时取下标层的那一份.

```agda
mutual
  Rb : L → Set
  Rb zero     = ⊤
  Rb (nd s h) = RbS s h × ((c : Ch s) → Rb (h c))
  RbS : (s : Sh) → (Ch s → L) → Set
  RbS sS     h = ⊤
  RbS sL     h = ⊤
  RbS (sΩ k) h = Rb k × Maybe (Schema k h)

rb≤ : (ℓ : L) → Rb ℓ → ∀ {j} → j ≤ ℓ → Rb j
rb≤ ℓ             r self      = r
rb≤ (nd s h)      r (inc c v) = rb≤ (h c) (proj₂ r c) v
rb≤ (nd s h)      r (inu vs)  = rb≤ (h (c₀ s)) (proj₂ r (c₀ s)) (vs (c₀ s))
rb≤ (nd (sΩ k) h) r (ink v)   = rb≤ k (proj₁ (proj₁ r)) v

rbO : (a b : L) → Rb a → Ok a → OkO a b → Rb (a ⊕ b)
rbO a zero          ra oa ob = ra
rbO a (nd sS h)     ra oa ob = tt , λ c → rbO a (h c) ra oa (proj₂ ob c)
rbO a (nd sL h)     ra oa ob = tt , λ c → rbO a (h c) ra oa (proj₂ ob c)
rbO a (nd (sΩ k) h) ra oa ob =
  (rb≤ a ra (proj₁ (proj₁ ob)) , just (schema a h oa (proj₁ (proj₁ ob)) (proj₂ ob) (λ c → refl))) ,
  λ c → rbO a (h c) ra oa (proj₂ ob c)

rb-tw : (n : ℕ) → Rb (tw n)
rb-tw zero    = tt
rb-tw (suc n) =
  (rb-tw n , just (schema (tw n) (↑ (tw n)) (Ok-tw n) self (OkO↑ (tw n) (tw n) (Ok-tw n) self) (λ c → refl))) ,
  λ c → rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

rb-Λ : Rb Λ
rb-Λ = tt , rb-tw

mutual
  rb-no : (ℓ : L) → Rb ℓ
  rb-no zero     = tt
  rb-no (nd s h) = rbS-no s h , λ c → rb-no (h c)
  rbS-no : (s : Sh) (h : Ch s → L) → RbS s h
  rbS-no sS     h = tt
  rbS-no sL     h = tt
  rbS-no (sΩ k) h = rb-no k , nothing
```

## 满证据

`Full ℓ r`: ℓ 的每个 Ω 形状结点 (孩子里的与下标层里的) 上 r 都带 `Schema`.

```agda
mutual
  Full : (ℓ : L) → Rb ℓ → Set
  Full zero     r = ⊤
  Full (nd s h) r = FullS s h (proj₁ r) × ((c : Ch s) → Full (h c) (proj₂ r c))
  FullS : (s : Sh) (h : Ch s → L) → RbS s h → Set
  FullS sS     h m = ⊤
  FullS sL     h m = ⊤
  FullS (sΩ k) h m = Full k (proj₁ m) × Σ (Schema k h) λ S → proj₂ m ≡ just S

full≤ : (ℓ : L) (r : Rb ℓ) → Full ℓ r → ∀ {j} (v : j ≤ ℓ) → Full j (rb≤ ℓ r v)
full≤ ℓ             r f self      = f
full≤ (nd s h)      r f (inc c v) = full≤ (h c) (proj₂ r c) (proj₂ f c) v
full≤ (nd s h)      r f (inu vs)  = full≤ (h (c₀ s)) (proj₂ r (c₀ s)) (proj₂ f (c₀ s)) (vs (c₀ s))
full≤ (nd (sΩ k) h) r f (ink v)   = full≤ k (proj₁ (proj₁ r)) (proj₁ (proj₁ f)) v

full-rbO : (a b : L) (ra : Rb a) (oa : Ok a) (ob : OkO a b) → Full a ra → Full (a ⊕ b) (rbO a b ra oa ob)
full-rbO a zero          ra oa ob fa = fa
full-rbO a (nd sS h)     ra oa ob fa = tt , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa
full-rbO a (nd sL h)     ra oa ob fa = tt , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa
full-rbO a (nd (sΩ k) h) ra oa ob fa =
  (full≤ a ra fa (proj₁ (proj₁ ob)) , _ , refl) , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa

full-tw : (n : ℕ) → Full (tw n) (rb-tw n)
full-tw zero    = tt
full-tw (suc n) = (full-tw n , _ , refl) , λ c →
  full-rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c) (full-tw n)

full-Λ : Full Λ rb-Λ
full-Λ = tt , full-tw
```

## 换基行里重建的层号

目标 j 的证据从孩子 c′ 的证据沿目标路径降下 (不要求路径不经下标层); 重建层号 `j ⊕ offsets S c` 的证据由 `rbO` 给出, 满证据保持.

```agda
rb-row : ∀ {k h} (S : Schema k h) (j : L) → Ok j → Rb j → floor S ≤ j → (c : Tr k) → Rb (j ⊕ offsets S c)
rb-row S j oj rj u c = rbO j (offsets S c) rj oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))

full-row : ∀ {k h} (S : Schema k h) j oj rj (u : floor S ≤ j) → Full j rj → (c : Tr k)
  → Full (j ⊕ offsets S c) (rb-row S j oj rj u c)
full-row S j oj rj u fj c = full-rbO j (offsets S c) rj oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)) fj
```
