# 验收 (形状): 换基两种写法的层号偏移

> 验收文件 (形状, 不读记号, 不涉及值), 不进成品. 塔第 n+1 项, 目标是孩子 c′ = d + m 里的第 m 层 (孩子 m 的层), 嵌入在孩子 c = b (孩子都是自然数): 兄弟孩子 (`YiRBSib.row-tw`) 在 `h (c′ + c)` 上折, 目标层 ⊕ c (`YiRDFold.row-up`) 在 `j ⊕ ↑ k c` 上折.
> 编译定理, 无前提, 对一切 n d m b (`off-all`): 兄弟孩子比孩子 c 的层高 c′ 层, 比目标层高 d + c 层; 目标层 ⊕ c 比孩子 c 的层高 m 层, 比目标层高 c 层; 兄弟孩子比目标层 ⊕ c 高 d 层. d = 0 时两层相同 (`same`), d ≥ 1 时不同 (`differ`). `refl` 实例在塔第 1, 2 项各七组; 塔第 2 项上两行的实例 `rowˢ-321`, `rowᵗ-321`.
> 不涉及 ℕ 极限或 Ω 形状的孩子.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRDLvl where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRWFold as R
open import OCF.Lean.YiAltCmp using (Ok-≤)
import OCF.Lean.YiRBSib as S
import OCF.Lean.YiRDFold as D
```

## 层号的算术

`st n a`: a 之上叠 n 层后继形状. `nk k a`: 第 k 层的自然数 a. `hk n c`: 塔第 n+1 项的孩子 c 的层.

```agda
st : ℕ → L → L
st zero    a = a
st (suc n) a = nd sS (λ _ → st n a)

nk : (k : L) → ℕ → Tr k
nk k zero    = zero
nk k (suc a) = suc (nk k a)

hk : (n : ℕ) → Tr (tw n) → L
hk n c = tw n ⊕ ↑ (tw n) c

↑nk : (k : L) (a : ℕ) → ↑ k (nk k a) ≡ st a zero
↑nk k zero    = refl
↑nk k (suc a) = cong (λ X → nd sS (λ _ → X)) (↑nk k a)

⊕st : (a : L) (n : ℕ) → a ⊕ st n zero ≡ st n a
⊕st a zero    = refl
⊕st a (suc n) = cong (λ X → nd sS (λ _ → X)) (⊕st a n)

stst : (p q : ℕ) (a : L) → st p (st q a) ≡ st (p +ℕ q) a
stst zero    q a = refl
stst (suc p) q a = cong (λ X → nd sS (λ _ → X)) (stst p q a)

nk+ : (k : L) (a b : ℕ) → nk k a + nk k b ≡ nk k (b +ℕ a)
nk+ k a zero    = refl
nk+ k a (suc b) = cong (λ (t : Tr k) → suc t) (nk+ k a b)

hst : (n a : ℕ) → hk n (nk (tw n) a) ≡ st a (tw n)
hst n a = trans (cong (tw n ⊕_) (↑nk (tw n) a)) (⊕st (tw n) a)
```

## 两种写法折的层

```agda
sibL : (n : ℕ) → Tr (tw n) → Tr (tw n) → L
sibL n c′ c = hk n (c′ + c)

tgtL : (n : ℕ) → L → Tr (tw n) → L
tgtL n j c = j ⊕ ↑ (tw n) c

sib-abs : ∀ n a b → sibL n (nk (tw n) a) (nk (tw n) b) ≡ st (b +ℕ a) (tw n)
sib-abs n a b = trans (cong (hk n) (nk+ (tw n) a b)) (hst n (b +ℕ a))

tgt-abs : ∀ n m b → tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) ≡ st (b +ℕ m) (tw n)
tgt-abs n m b =
  trans (cong (hk n (nk (tw n) m) ⊕_) (↑nk (tw n) b))
    (trans (⊕st (hk n (nk (tw n) m)) b) (trans (cong (st b) (hst n m)) (stst b m (tw n))))
```

## 偏移

`X ≡ st δ Y`: X 比 Y 高 δ 层.

```agda
off : ∀ {X Y : L} {P q : ℕ} (δ : ℕ) (a : L) → X ≡ st P a → Y ≡ st q a → P ≡ δ +ℕ q → X ≡ st δ Y
off δ a ex ey e = trans ex (trans (cong (λ r → st r a) e) (trans (sym (stst δ _ a)) (cong (st δ) (sym ey))))

Off : ℕ → ℕ → ℕ → ℕ → Set
Off n d m b =
    (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st (d +ℕ m) (hk n (nk (tw n) b)))
  × (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st (d +ℕ b) (hk n (nk (tw n) m)))
  × (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) ≡ st m (hk n (nk (tw n) b)))
  × (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) ≡ st b (hk n (nk (tw n) m)))
  × (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st d (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b)))

e₁ : ∀ d m b → b +ℕ (d +ℕ m) ≡ (d +ℕ b) +ℕ m
e₁ d m b = trans (sym (+-assoc b d m)) (cong (_+ℕ m) (+-comm b d))

off-all : ∀ n d m b → Off n d m b
off-all n d m b =
    off (d +ℕ m) (tw n) (sib-abs n (d +ℕ m) b) (hst n b) (+-comm b (d +ℕ m))
  , off (d +ℕ b) (tw n) (sib-abs n (d +ℕ m) b) (hst n m) (e₁ d m b)
  , off m (tw n) (tgt-abs n m b) (hst n b) (+-comm b m)
  , off b (tw n) (tgt-abs n m b) (hst n m) refl
  , off d (tw n) (sib-abs n (d +ℕ m) b) (tgt-abs n m b) (trans (e₁ d m b) (+-assoc d b m))

same : ∀ n m b → sibL n (nk (tw n) m) (nk (tw n) b) ≡ tgtL n (hk n (nk (tw n) m)) (nk (tw n) b)
same n m b = proj₂ (proj₂ (proj₂ (proj₂ (off-all n zero m b))))
```

d ≥ 1 时两层不同: 层号不成环.

```agda
kid : L → L
kid (nd sS h) = h tt
kid _         = zero

noncyc : ∀ n e q → st (suc e +ℕ q) (tw n) ≡ st q (tw n) → ⊥
noncyc zero    e zero    ()
noncyc (suc n) e zero    ()
noncyc n       e (suc q) eq = noncyc n e q (subst (λ r → st r (tw n) ≡ st q (tw n)) (+-suc e q) (cong kid eq))

differ : ∀ n d m b → sibL n (nk (tw n) (suc d +ℕ m)) (nk (tw n) b) ≡ tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) → ⊥
differ n d m b eq = noncyc n d (b +ℕ m)
  (trans (sym (stst (suc d) (b +ℕ m) (tw n)))
    (trans (cong (st (suc d)) (sym (tgt-abs n m b)))
      (trans (sym (proj₂ (proj₂ (proj₂ (proj₂ (off-all n (suc d) m b)))))) (trans eq (tgt-abs n m b)))))
```

`refl` 实例: (d, m, b) 依次是已知的一处 (孩子 3 里的第 2 层, 嵌入在孩子 1), d = 0, 嵌入在孩子 0, 嵌入在孩子 2, 孩子 4, 孩子 4 里的第 1 层, 孩子 5 里的第 3 层.

```agda
i₁ : Off 0 1 2 1
i₁ = refl , refl , refl , refl , refl
i₂ : Off 0 0 2 1
i₂ = refl , refl , refl , refl , refl
i₃ : Off 0 1 2 0
i₃ = refl , refl , refl , refl , refl
i₄ : Off 0 1 2 2
i₄ = refl , refl , refl , refl , refl
i₅ : Off 0 2 2 1
i₅ = refl , refl , refl , refl , refl
i₆ : Off 0 3 1 2
i₆ = refl , refl , refl , refl , refl
i₇ : Off 0 2 3 3
i₇ = refl , refl , refl , refl , refl

j₁ : Off 1 1 2 1
j₁ = refl , refl , refl , refl , refl
j₂ : Off 1 0 2 1
j₂ = refl , refl , refl , refl , refl
j₃ : Off 1 1 2 0
j₃ = refl , refl , refl , refl , refl
j₄ : Off 1 1 2 2
j₄ = refl , refl , refl , refl , refl
j₅ : Off 1 2 2 1
j₅ = refl , refl , refl , refl , refl
j₆ : Off 1 3 1 2
j₆ = refl , refl , refl , refl , refl
j₇ : Off 1 2 3 3
j₇ = refl , refl , refl , refl , refl

lvl₁ : sibL 0 (nk zero 3) (nk zero 1) ≡ st 4 zero × tgtL 0 (hk 0 (nk zero 2)) (nk zero 1) ≡ st 3 zero
lvl₁ = refl , refl

lvl₂ : sibL 1 (nk (tw 1) 3) (nk (tw 1) 1) ≡ st 4 (tw 1) × tgtL 1 (hk 1 (nk (tw 1) 2)) (nk (tw 1) 1) ≡ st 3 (tw 1)
lvl₂ = refl , refl
```

## 塔第 2 项上的两行

目标是孩子 3 里孩子 2 的层, 路径 `inc 3 (inc tt self)`, 嵌入在孩子 1: 兄弟孩子在 `st 4 (tw 1)` 上折, 目标层 ⊕ c 在 `st 3 (tw 1)` 上折.

```agda
rowˢ-321 : ∀ (B : Base (tw 2)) β x y e
  → S.ψ (tw 2) (Ok-tw 2) (S.rb-tw 2) B (hk 1 (nk (tw 1) 2)) (inc (nk (tw 1) 3) (inc tt self)) β (up x (nk (tw 1) 1) y e)
  ≡ S.ψ (st 4 (tw 1)) (proj₂ (Ok-tw 2) (nk (tw 1) 3 + nk (tw 1) 1)) (S.rb-no (st 4 (tw 1)))
      (λ i u → S.ψ (tw 2) (Ok-tw 2) (S.rb-tw 2) B i (inc (nk (tw 1) 3 + nk (tw 1) 1) u) (B i (inc (nk (tw 1) 3 + nk (tw 1) 1) u)) x)
      (hk 1 (nk (tw 1) 2))
      (inc tt self ∙ wk (⊕⊑ (tw 1) (S.pre (tw 1) (nk (tw 1) 3) (nk (tw 1) 1))))
      (S.ψ (tw 2) (Ok-tw 2) (S.rb-tw 2) B (hk 1 (nk (tw 1) 2)) (inc (nk (tw 1) 3) (inc tt self)) β x)
      (proj₁ (Ωt (st 4 (tw 1))))
    ⊞ S.ψ₀ʳ (hk 1 (nk (tw 1) 1)) (proj₂ (Ok-tw 2) (nk (tw 1) 1)) (S.rb-no (hk 1 (nk (tw 1) 1))) y
rowˢ-321 B β x y e = S.row-tw 1 B (hk 1 (nk (tw 1) 2)) (nk (tw 1) 3) (inc tt self) β x (nk (tw 1) 1) y e

rowᵗ-321 : ∀ (B : Base (tw 2)) β x y e
  → D.ψ (tw 2) (Ok-tw 2) B (hk 1 (nk (tw 1) 2)) (inc (nk (tw 1) 3) (inc tt self)) β (up x (nk (tw 1) 1) y e)
  ≡ R.ψ (st 3 (tw 1))
        (Ok⊕ (hk 1 (nk (tw 1) 2)) (↑ (tw 1) (nk (tw 1) 1))
             (Ok-≤ (hk 1 (nk (tw 1) 3)) (proj₂ (Ok-tw 2) (nk (tw 1) 3)) (inc tt self))
             (OkO↑ (hk 1 (nk (tw 1) 2)) (tw 1) (Ok-tw 1) (lift (tw 1) (↑ (tw 1) (nk (tw 1) 2))) (nk (tw 1) 1)))
        (B₀ (st 3 (tw 1))) (hk 1 (nk (tw 1) 2)) (lift (hk 1 (nk (tw 1) 2)) (↑ (tw 1) (nk (tw 1) 1)))
        (D.ψ (tw 2) (Ok-tw 2) B (hk 1 (nk (tw 1) 2)) (inc (nk (tw 1) 3) (inc tt self)) β x)
        (proj₁ (Ωt (st 3 (tw 1))))
    ⊞ D.ψ₀ᵈ (hk 1 (nk (tw 1) 1)) (proj₂ (Ok-tw 2) (nk (tw 1) 1)) y
rowᵗ-321 B β x y e = D.row-up 1 B (nk (tw 1) 3) {b′ = ↑ (tw 1) (nk (tw 1) 2)} (inc tt self) β x (nk (tw 1) 1) y e
```
