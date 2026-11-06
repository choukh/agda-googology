# 规范形论证对树类型抽象 (三): 在 `SumOneTree.D azero` 上, 与原文对照

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). 签名实例 `σS` (方程都是 `refl`, 归纳原理是对五个构造子的模式匹配, `ni`, `nκ` 空). `FromOld`: 参数与 [`DValCanon.Gen`](DValCanon.lagda.md) **逐字相同** (部分和用原文的 `DC.pre`), 由新的 `Canon.Gen` 推出原文的两个结论, 类型与原文一字不差:
>
> - `cong0ᵒ`: 前提 `proj₁ (toA z) ≤ proj₁ (toA z′)`, 与 `DC.Gen.Two.cong0` 同型;
> - `canonᵒ`: `cw z ~ z`, 与 `DC.Gen.One.canon` 同型 (`cw` 来自 `LayerTrRound`).
>
> 反方向 `cong0ⁿ`: 原文的 `cong0` 推出新陈述 (前提换成 `sum 0 z ≤ sum 0 z′`). 两个陈述只差前提里的读法, 由 `BrwMidZero.sum₀` 互换.
>
> 本文件是对照, 导入原文与 `BrwMidZero`; 新的论证本身 ([GenAbsCanon](GenAbsCanon.lagda.md)) 不导入它们.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenAbsSO where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
import OCF.Align.SumOneTree as SO
open import OCF.Align.BrwMidZero using (toA; sum₀)
import OCF.Align.BrwMidZero as BM
open import OCF.Align.LayerTrRound using (cw)
import OCF.Align.DValCanon as DC
open import OCF.Align.GenAbsSig using (Sig; module Ops)
open import OCF.Align.GenAbsCanon using (module Canon)
```

## §1 签名实例

```agda
indS : (P : ∀ {W} → D azero W → Set) →
       (∀ {W} → P (n0 {W = W})) → (∀ {W} → P (n1 {W = W})) →
       (∀ {W} {x y : D azero W} → P x → P y → P (x ⨾ y)) →
       (∀ {W} {d : ℕ → D azero W} → (∀ n → P (d n)) → P (nl d)) →
       (∀ {W₀ W} {p : W₀ ⊲ W} {x : D azero W₀} → P x → P (nw p x)) →
       ∀ {W} (z : D azero W) → P z
indS P c0 c1 c⨾ cl cw n0 = c0
indS P c0 c1 c⨾ cl cw n1 = c1
indS P c0 c1 c⨾ cl cw (x ⨾ y) = c⨾ (indS P c0 c1 c⨾ cl cw x) (indS P c0 c1 c⨾ cl cw y)
indS P c0 c1 c⨾ cl cw (nl d) = cl (λ n → indS P c0 c1 c⨾ cl cw (d n))
indS P c0 c1 c⨾ cl cw (ni () u)
indS P c0 c1 c⨾ cl cw (nκ () u)
indS P c0 c1 c⨾ cl cw (nw p x) = cw (indS P c0 c1 c⨾ cl cw x)

σS : Sig
σS = record
  { Wd = A ; _≺_ = _⊲_ ; T = D azero
  ; n0 = n0 ; n1 = n1 ; _⨾_ = _⨾_ ; nl = nl ; nw = nw ; ind = indS
  ; sum = SO.sum ; pt = SO.pt
  ; pt-z = λ _ _ → refl ; pt-s = λ _ _ _ → refl
  ; sum-n0 = λ _ → refl ; sum-n1 = λ _ → refl ; sum-⨾ = λ _ _ _ → refl
  ; sum-nl = λ _ _ → refl ; sum-nw = λ _ _ _ → refl
  ; sum-fst = SO.sum-fst ; Lg-sum = SO.Lg-sum }
```

## §2 原文的参数推出原文的结论

```agda
module FromOld {I : Set} (Hy : I → I → Set)
  (R : I → I → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set)
  (n1⊑ : ∀ {i j} → Hy i j → ∀ {V₁ V₂} → R i j (n1 {W = V₁}) (n1 {W = V₂}))
  (infl : ∀ {i j V₁ V₂} (z : D azero V₂) → R i j (n0 {W = V₁}) z)
  (⨾-mono : ∀ {i j V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → R i j x x′ → R i j y y′ → R i j (x ⨾ y) (x′ ⨾ y′))
  (nl-mono : ∀ {i j V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → R i j (d n) (d′ n)) → R i j (nl d) (nl d′))
  (nw-l : ∀ {i j V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → R i j x z → R i j (nw p x) z)
  (nw-r : ∀ {i j V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → R i j z x → R i j z (nw p x))
  (tr⊑ : ∀ {i j V V₃} {z z′ : D azero V} {z″ : D azero V₃} → R i i z z′ → R i j z′ z″ → R i j z z″)
  (tr⊑ʳ : ∀ {i j V V₁} {z : D azero V₁} {z′ z″ : D azero V} → R i j z z′ → R j j z′ z″ → R i j z z″)
  (unit-l : ∀ {i} → Hy i i → ∀ {V} (x : D azero V) → R i i (n0 ⨾ x) x × R i i x (n0 ⨾ x))
  (unit-r : ∀ {i} → Hy i i → ∀ {V} (x : D azero V) → R i i (x ⨾ n0) x × R i i x (x ⨾ n0))
  (assoc : ∀ {i} → Hy i i → ∀ {V} (x y z : D azero V) → R i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × R i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z))
  (pre-le : ∀ {i j V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
            R i j x x′ → (∀ n → R i j (d n) (d′ n)) → ∀ k → R i j (x ⨾ DC.pre d k) (x′ ⨾ nl d′))
  (lim-leP : ∀ {i j V₁ V₂} → Hy i i → (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
             (∀ k → R i j (x ⨾ DC.pre d k) z) → R i j (x ⨾ nl d) z)
  where
  open Ops σS using (pre)

  pre≡ : ∀ {V} (d : ℕ → D azero V) k → pre d k ≡ DC.pre d k
  pre≡ d zero = refl
  pre≡ d (suc k) = cong (_⨾ d k) (pre≡ d k)

  module N = Canon.Gen σS Hy R n1⊑ infl ⨾-mono nl-mono nw-l nw-r tr⊑ tr⊑ʳ unit-l unit-r assoc
    (λ {i} {j} x x′ d d′ hx hd k → subst (λ t → R i j (x ⨾ t) (x′ ⨾ nl d′)) (sym (pre≡ d k)) (pre-le x x′ d d′ hx hd k))
    (λ {i} {j} h x d z hk → lim-leP h x d z (λ k → subst (λ t → R i j (x ⨾ t) z) (pre≡ d k) (hk k)))
  module O = DC.Gen Hy R n1⊑ infl ⨾-mono nl-mono nw-l nw-r tr⊑ tr⊑ʳ unit-l unit-r assoc pre-le lim-leP

  -- 新推旧: 原文 Two.cong0 的类型
  cong0ᵒ : ∀ {i j} → Hy i i → Hy j j → Hy i j →
           ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → proj₁ (toA z) ≤ proj₁ (toA z′) → R i j z z′
  cong0ᵒ hi hj hij z z′ le = N.Two.cong0 hi hj hij z z′ (≤-trans (proj₁ (sum₀ z)) (≤-trans le (proj₂ (sum₀ z′))))

  -- 旧推新: 前提换成读法 sum
  cong0ⁿ : ∀ {i j} → Hy i i → Hy j j → Hy i j →
           ∀ {W₀ W₀′} (z : D azero W₀) (z′ : D azero W₀′) → SO.sum azero z ≤ SO.sum azero z′ → R i j z z′
  cong0ⁿ hi hj hij z z′ le = O.Two.cong0 hi hj hij z z′ (≤-trans (proj₂ (sum₀ z)) (≤-trans le (proj₁ (sum₀ z′))))

  -- 新推旧: 原文 One.canon 的类型
  module _ {i : I} (hi : Hy i i) where
    open N.One hi using (_~_; rf~; tr~; ⨾~; nl~; ul; canon)
    open N.Two hi hi hi using (M)

    difE : ∀ {V} b {a} (p : a ⊲ b) (l : Lg b) → BM.dif {V} b p l ~ Ops.dif σS {V} b p l
    difE b C.self l = rf~ n0
    difE (OCF.Align.CumReadCF.asuc c) (C.suc p) l = ⨾~ (difE c p l) (rf~ n1)
    difE (OCF.Align.CumReadCF.alim f) (C.lim n p) (st , w) = ⨾~ (difE (f n) p (w n)) (nl~ (λ m → difE _ _ _))

    canonᵒ : ∀ {W₀} (z : D azero W₀) → R i i (cw z) z × R i i z (cw z)
    canonᵒ z =
      let (h , h′) = tr~ (difE _ (z⊲ _) (proj₂ (toA z)))
                     (tr~ (M (proj₂ (sum₀ z)) (proj₂ (toA z)) (SO.Lg-sum azero z _) ,
                           M (proj₁ (sum₀ z)) (SO.Lg-sum azero z _) (proj₂ (toA z)))
                          (canon z))
      in tr~ (ul _) (nw-l h , nw-r h′)
```
