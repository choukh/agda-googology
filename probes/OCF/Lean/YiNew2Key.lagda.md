# YiNew2 验收: 非有限孩子层的见证树, 孩子单调, 闭项

判决: 塔第 2 项里孩子层 `su (tw 1)` 的顶码 (按 `tw 1` 层的树分支) 的对角化带着 x 朝 `tw 1` 的折叠 (`key2-0`, `not-blind` 是 `refl`; `key2-diff` 是小定理).
孩子单调: 对 "孩子 1 的一切树" 的读法被编译否定 (`child-all-false`, 反例是嵌入的任意可数树, 读作量化域太宽); 对 Ω 树只有第一位置序下的实例 (`child-Ω-first`).
不否定什么: 孩子单调在布劳威尔序下对规范树是否成立没有判决; 闭项 `ebo2` 的值没有定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNew2Key where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiNewBlock
open import OCF.Lean.YiNewFold using (_+_; S; tms; iter; module Ord; module O; Le; one)
open import OCF.Lean.YiNewKey using (top)
open import OCF.Lean.YiNew2Fold
```

## 塔的字面分解

塔第 n+1 项字面上就是 `tw n ⊕ M n`: Ω 结点的每个孩子层都写成下标层之上再加一段. 这个分解是定义等式, 就是证书.

```agda
M : ℕ → Lv
M n = Om (tw n) (λ c → su (inj (tw n) c))

tw-split : ∀ n → tw (suc n) ≡ tw n ⊕ M n
tw-split n = refl
```

## 非有限孩子层的见证树

`W2 x`: x 是塔第 2 项那一层的任意树, 再嵌入孩子 `zr` 的层 `su (tw 1)` 里的顶码分支 (按 `tw 1` 层的树分支).
第一轮里这个码归 `loc`, 迭代不含底 (`loc-blind`). 现在它归 `absR 0`.

```agda
W2 : T (tw 2) → T (tw 2)
W2 x = up x zr (top (tw 1))

step₂ : T (tw 2) → RBase (tw 1) → T (tw 1) → T (tw 1)
step₂ x B ζ = Φ (tw 1) ze ζ (λ j → S (Φ (tw 1) (M 1) x B j)) 0

key2-0 : ∀ x B → Φ (tw 1) (M 1) (W2 x) B 0
               ≡ lm (λ n → Φ (tw 1) ze (iter (step₂ x B) zr n) (λ j → S (Φ (tw 1) (M 1) x B j)) 0)
key2-0 x B = refl

not-blind : ∀ x B → iter (step₂ x B) zr 1 ≡ S (Φ (tw 1) (M 1) x B 0)
not-blind x B = refl

key2-1 : ∀ x B → Φ (tw 1) (M 1) (W2 x) B 1
               ≡ Lm (inj₁ tt) (λ ζ → Φ (tw 1) ze ζ (λ j → S (Φ (tw 1) (M 1) x B j)) 1)
key2-1 x B = refl
```

两个不同的 x 给出不同的迭代第 1 项.

```agda
hd : ∀ {U B E M} → Tr U B E M → Tr U B E M
hd (lm f) = f 0
hd _      = zr

key2-diff : iter (step₂ zr (R° (tw 1))) zr 1 ≡ iter (step₂ (sc zr) (R° (tw 1))) zr 1 → ⊥
key2-diff e with cong hd e
... | ()
```

## 第 0 层上的布劳威尔序

第 0 层的树只有零, 后继, ℕ 极限. `≼` 是通常的序: 极限在右取某一项, 在左要每一项.

```agda
infix 4 _≼_
data _≼_ : T ze → T ze → Set where
  z≼  : ∀ {a} → zr ≼ a
  s≼s : ∀ {a b} → a ≼ b → sc a ≼ sc b
  ≼l  : ∀ {a f} n → a ≼ f n → a ≼ lm f
  l≼  : ∀ {f b} → (∀ n → f n ≼ b) → lm f ≼ b

≼-refl : ∀ a → a ≼ a
≼-refl zr     = z≼
≼-refl (sc a) = s≼s (≼-refl a)
≼-refl (lm f) = l≼ (λ n → ≼l n (≼-refl (f n)))

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼       _        = z≼
≼-trans (l≼ h)   q        = l≼ (λ n → ≼-trans (h n) q)
≼-trans (s≼s p)  (s≼s q)  = s≼s (≼-trans p q)
≼-trans (s≼s p)  (≼l n q) = ≼l n (≼-trans (s≼s p) q)
≼-trans (≼l n p) (≼l m q) = ≼l m (≼-trans (≼l n p) q)
≼-trans (≼l n p) (l≼ h)   = ≼-trans p (h n)

self≼sc : ∀ b → b ≼ sc b
self≼sc zr     = z≼
self≼sc (sc b) = s≼s (self≼sc b)
self≼sc (lm f) = l≼ (λ n → ≼-trans (self≼sc (f n)) (s≼s (≼l n (≼-refl (f n)))))

a≼+ : ∀ a b → a ≼ a + b
a≼+ a zr     = ≼-refl a
a≼+ a (sc b) = ≼-trans (a≼+ a b) (self≼sc (a + b))
a≼+ a (lm f) = ≼l 0 (a≼+ a (f 0))

+monoʳ : ∀ a {b b′} → b ≼ b′ → a + b ≼ a + b′
+monoʳ a {b′ = b′} z≼ = a≼+ a b′
+monoʳ a (s≼s p)  = s≼s (+monoʳ a p)
+monoʳ a (≼l n p) = ≼l n (+monoʳ a p)
+monoʳ a (l≼ h)   = l≼ (λ n → +monoʳ a (h n))

sc-irr : ∀ a → sc a ≼ a → ⊥
sc-irr (sc a) (s≼s p)  = sc-irr a p
sc-irr (lm f) (≼l n p) = sc-irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) p)

≼S : ∀ {r v} → one ≼ v → r ≼ v → sc r ≼ S v
≼S {v = v} o q = ≼l 0 (≼-trans (s≼s q) (+monoʳ v o))

one≼S : ∀ {v} → one ≼ v → one ≼ S v
one≼S {v} o = ≼l 0 (≼-trans o (a≼+ v v))
```

第 0 层的树 w 接在任何非零的底上, 朝第 0 层折叠后不低于 w 自己.

```agda
grow : ∀ (w : T ze) (B : RBase ze) → one ≼ B 0
     → (w ≼ Φ ze ze w B 0) × (one ≼ Φ ze ze w B 0)
grow zr     B o = z≼ , o
grow (sc w) B o = ≼S (proj₂ (grow w B o)) (proj₁ (grow w B o)) , one≼S (proj₂ (grow w B o))
grow (lm f) B o = l≼ (λ n → ≼l n (proj₁ (grow (f n) B o))) , ≼l 0 (proj₂ (grow (f 0) B o))
```

## 孩子单调

实例: 塔第 1 项那一层 (`tw 1 = ze ⊕ M 0`), 孩子 c = 1 (层是有限层 2) 与孩子 c + 1 = 2 (层是有限层 3).
`rhs x B` 是孩子 2 的 Ω 树嵌入后朝第 0 层的折叠.

```agda
c1 c2 : T ze
c1 = sc zr
c2 = sc (sc zr)

rhs : T (tw 1) → RBase ze → T ze
rhs x B = Φ ze (M 0) (up x c2 (top (fin 2))) B 0
```

"孩子 1 的一切树" 的读法不成立. 孩子层 2 里有嵌入的第 0 层的树, 而第 0 层含一切可数树:
取 `rhs` 的后继, 嵌两层放进孩子 1, 折叠后严格高于 `rhs`. 反例不是由折叠生成的树, 所以这条否定读作量化域太宽.

```agda
ybad : T (tw 1) → RBase ze → T (fin 2)
ybad x B = up zr tt (up zr tt (sc (rhs x B)))

child-all-false : ∀ x B → one ≼ Φ ze (M 0) x B 0
                → Φ ze (M 0) (up x c1 (ybad x B)) B 0 ≼ rhs x B → ⊥
child-all-false x B o h =
  sc-irr (rhs x B)
    (≼-trans (≼S (proj₂ (grow (rhs x B) (Φ ze (M 0) x B) o))
                 (proj₁ (grow (rhs x B) (Φ ze (M 0) x B) o))) h)
```

前提可满足: x 取零, 底取起始的底.

```agda
child-all-false° : Φ ze (M 0) (up zr c1 (ybad zr (R° ze))) (R° ze) 0 ≼ rhs zr (R° ze) → ⊥
child-all-false° = child-all-false zr (R° ze) (≼-refl one)
```

Ω 树对 Ω 树: 第一位置序下成立 (两边的第一位置相同). 这是粗序下的实例, 不是值的比较.

```agda
child-Ω-first : ∀ x B → Le ze (Φ ze (M 0) (up x c1 (top (fin 1))) B 0) (rhs x B)
child-Ω-first x B = Ord.l≤l (O.≤-refl ze _)
```

## 闭项

沿塔逐项往下折: `down n` 相对 `tw n` 朝第 0 个相对目标 (就是 `tw n` 自己) 折叠, `coll` 逐项复合到第 0 层.
`ebo2` 取各项里孩子 `zr` 的顶码分支, 再取 ℕ 极限; 形状读作 ψ₀(Λ), 值没有定理.

```agda
down : ∀ n → T (tw (suc n)) → T (tw n)
down n y = Φ (tw n) (M n) y (R° (tw n)) 0

coll : ∀ n → T (tw n) → T ze
coll zero    y = y
coll (suc n) y = coll n (down n y)

big : ∀ n → T (tw (suc n))
big n = up zr zr (top (tw n))

ebo2 : T ze
ebo2 = lm (λ n → coll (suc n) (big n))

ebo2-nz : Le ze one ebo2
ebo2-nz = Ord.≤l (rnz ze (M 0) (big 0) 0)
```
