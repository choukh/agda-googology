# 追加自然数极限时，完成操作的精确值变化

对任意可数树前缀 a，完成 a⊞ω 后，值恰好为 (leg a+1) 的 ω 重复。
这是一条读取树形状的上下界公式，不由 a 的原值推出完成值，也不是
终点 C 的上界。所有重排只在可数值关系里证明，不使用函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CountableCompletionUpperOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; ⊞-≤ˡ; ⊞-≤ʳ; mul-≤)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.CountableCompletionRun using (inflation; right-add)

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)
ω : Cd
ω = hl num
legal-num : ∀ n → LgB (num n)
legal-num zero = tt
legal-num (suc n) = legal-num n
legal-ω : LgB ω
legal-ω = (λ n → hsuc hself) , legal-num

add-mono : ∀ {a b c d : Cd} → a ≤ᵛ b → c ≤ᵛ d → a ⊞ c ≤ᵛ b ⊞ d
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)
assoc : ∀ (a b c : Cd) → a ⊞ (b ⊞ c) ≤ᵛ (a ⊞ b) ⊞ c
assoc a b hz = ≤-refl _
assoc a b (hs c) = s≤s (assoc a b c)
assoc a b (hl f) = l≤ (λ n → ≤l n (assoc a b (f n)))

-- gap n m 对应 (n+1)+(m+1) 份的重复所用的最后下标。
gap : ℕ → ℕ → ℕ
gap n zero = suc n
gap n (suc m) = suc (gap n m)
mul-join : ∀ (a : Cd) n m → mul a n ⊞ mul a m ≤ᵛ mul a (gap n m)
mul-join a n zero = ≤-refl _
mul-join a n (suc m) = ≤-trans (assoc (mul a n) (mul a m) a)
  (add-mono (mul-join a n m) (≤-refl a))

tail : Cd → ℕ → Cd
tail a n = a ⊞ num n
term-upper : ∀ a n → tail a n ≤ᵛ mul (hs a) n
term-upper a zero = ≤s (≤-refl a)
term-upper a (suc n) = ≤-trans (s≤s (term-upper a n))
  (add-mono (≤-refl (mul (hs a) n)) (s≤s z≤))

budget : ℕ → ℕ
budget zero = zero
budget (suc n) = gap (budget n) (suc n)
sums-upper : ∀ a n → Σ₀ (tail a) n ≤ᵛ mul (hs a) (budget n)
sums-upper a zero = term-upper a zero
sums-upper a (suc n) = ≤-trans
  (add-mono (sums-upper a n) (term-upper a (suc n)))
  (mul-join (hs a) (budget n) (suc n))

term-positive : ∀ a n → hs a ≤ᵛ tail a (suc n)
term-positive a n = s≤s (≤⊞ a (num n))
repeat-lower : ∀ a n → mul (hs a) n ≤ᵛ Σ₀ (tail a) (suc n)
repeat-lower a zero = right-add a (hs a)
repeat-lower a (suc n) = add-mono (repeat-lower a n) (term-positive a (suc n))

leg-tail : ∀ a n → leg (tail a n) ≡ tail (leg a) n
leg-tail a zero = refl
leg-tail a (suc n) rewrite leg-tail a n = refl
leg-sums : ∀ a n → Σ₀ (λ j → leg (tail a j)) n ≡ Σ₀ (tail (leg a)) n
leg-sums a zero = refl
leg-sums a (suc n) rewrite leg-sums a n | leg-tail a n = refl

upper : ∀ a → leg (a ⊞ ω) ≤ᵛ hl (mul (hs (leg a)))
upper a = l≤ branch
  where
  branch : ∀ n → Σ₀ (λ j → leg (tail a j)) n ≤ᵛ hl (mul (hs (leg a)))
  branch n rewrite leg-sums a n = ≤l (budget n) (sums-upper (leg a) n)
lower : ∀ a → hl (mul (hs (leg a))) ≤ᵛ leg (a ⊞ ω)
lower a = l≤ branch
  where
  branch : ∀ n → mul (hs (leg a)) n ≤ᵛ leg (a ⊞ ω)
  branch n = ≤l (suc n) bound
    where
    bound : mul (hs (leg a)) n ≤ᵛ Σ₀ (λ j → leg (tail a j)) (suc n)
    bound rewrite leg-sums a (suc n) = repeat-lower (leg a) n

-- 非空实例：前缀任意，不要求它已经合法；新输出始终合法。
legal-input : ∀ a → LgB a → LgB (a ⊞ ω)
legal-input a la = Lg-⊞ a ω la legal-ω
legal-output : ∀ a → LgB (leg (a ⊞ ω))
legal-output a = Lg-leg (a ⊞ ω)
```

下面进一步在通常的合法树 ω⊞ω 上校准。完成后的值等于 ω 的 ω
重复，且严格支配输入本身；这不是以“不合法输入”解释完成的代价。

```agda
repeat-mono : ∀ {a b : Cd} → a ≤ᵛ b → hl (mul a) ≤ᵛ hl (mul b)
repeat-mono p = l≤ (λ n → ≤l n (mul-≤ p n))
mul-one : ∀ n → mul (hs hz) n ≡ num (suc n)
mul-one zero = refl
mul-one (suc n) rewrite mul-one n = refl
repeat-one≤ω : hl (mul (hs hz)) ≤ᵛ ω
repeat-one≤ω = l≤ branch
  where
  branch : ∀ n → mul (hs hz) n ≤ᵛ ω
  branch n rewrite mul-one n = ≤l (suc n) (≤-refl _)
leg-ω≤ω : leg ω ≤ᵛ ω
leg-ω≤ω = ≤-trans (l≤ branch) repeat-one≤ω
  where
  leg-num : ∀ n → leg (num n) ≡ num n
  leg-num zero = refl
  leg-num (suc n) rewrite leg-num n = refl
  zero-tail : ∀ n → tail hz n ≡ num n
  zero-tail zero = refl
  zero-tail (suc n) rewrite zero-tail n = refl
  omega-sums : ∀ n → Σ₀ (λ j → leg (num j)) n ≡ Σ₀ (tail hz) n
  omega-sums zero = refl
  omega-sums (suc n) rewrite omega-sums n | leg-num n | zero-tail n = refl
  branch : ∀ n → Σ₀ (λ j → leg (num j)) n ≤ᵛ hl (mul (hs hz))
  branch n rewrite omega-sums n = ≤l (budget n) (sums-upper hz n)
ω≤leg-ω : ω ≤ᵛ leg ω
ω≤leg-ω = inflation ω

twice : ℕ → ℕ
twice zero = 1
twice (suc n) = gap (twice n) 1
two-blocks : ∀ a n → mul (mul a 1) n ≤ᵛ mul a (twice n)
two-blocks a zero = ≤-refl _
two-blocks a (suc n) = ≤-trans
  (add-mono (two-blocks a n) (≤-refl _)) (mul-join a (twice n) 1)
repeat-successor : ∀ {a : Cd} → hs hz ≤ᵛ a → hl (mul (hs a)) ≤ᵛ hl (mul a)
repeat-successor {a} positive = l≤ (λ n → ≤l (twice n)
  (≤-trans (mul-≤ (add-mono (≤-refl a) positive) n) (two-blocks a n)))

one≤ω : hs hz ≤ᵛ ω
one≤ω = ≤l 1 (≤-refl _)
double-ω-upper : leg (ω ⊞ ω) ≤ᵛ hl (mul ω)
double-ω-upper = ≤-trans (upper ω)
  (≤-trans (repeat-successor (≤-trans one≤ω ω≤leg-ω)) (repeat-mono leg-ω≤ω))
double-ω-lower : hl (mul ω) ≤ᵛ leg (ω ⊞ ω)
double-ω-lower = ≤-trans (repeat-mono (≤s ω≤leg-ω)) (lower ω)

strict-double-ω : hs (ω ⊞ ω) ≤ᵛ leg (ω ⊞ ω)
strict-double-ω = ≤-trans
  (≤l 2 (add-mono (≤-refl (ω ⊞ ω)) one≤ω)) double-ω-lower
not-value-preserving : leg (ω ⊞ ω) ≤ᵛ ω ⊞ ω → ⊥
not-value-preserving p = ¬s≤ᵛ (ω ⊞ ω) (≤-trans strict-double-ω p)
```

两个方向都是可数序数值定理，未声称基本列一致。ω⊞ω 的合法性由
legal-input ω legal-ω 给出。结果为后续结构上界提供可复用的一步规则，
尚未覆盖 C 中所有极限形状，不能据此给 C 的上界或终点读法。
