# 折叠是和的作用 (五): 规格, 哪一步是选择

> 不含记号, 不含折叠的旧树. 入口 [TLRule](TLRule.lagda.md). 这里只有第 0 层的值 (`A` 上的前序 `≤`), 全部编译过, 无前提的都是定理.
>
> 1. `ω-spec`, `ω-uniq`: $c\cdot\omega$ 是 $c$ 之上最小的加法封闭点. 只要 "输出对加法封闭" 这一条原则, $\psi(a+1)=\psi(a)\cdot\omega$ 的**值**就被逼出, 与写法无关. 这条原则本身是选择 (`blind`, [TLRuleVar](TLRuleVar.lagda.md)).
> 2. `no-full`: 不存在对**全部**分支严格单调的折叠. 所以 $\Omega$-极限穿过目标层时只能取可数个分支: 链不是约定, 是 "$\omega$-极限的上界" 这个类型逼的. 这就是 `ψᴱ-not-mono`, `ψ-not-⊑mono` 的根.
> 3. `chain-least`: 链的上确界是对 $g$ 封闭的最小点. 起点不影响结论, 只要它在闭包里.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleSpec where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; sum; pt; sum-fst)
```

## §1 值

```agda
infix 4 _≤_
data _≤_ : A → A → Set where
  z≤ : ∀ {b} → azero ≤ b
  s≤ : ∀ {a b} → a ≤ b → asuc a ≤ asuc b
  ≤l : ∀ {a f} n → a ≤ f n → a ≤ alim f
  l≤ : ∀ {f b} → (∀ n → f n ≤ b) → alim f ≤ b

≤-refl : ∀ a → a ≤ a
≤-refl azero = z≤
≤-refl (asuc a) = s≤ (≤-refl a)
≤-refl (alim f) = l≤ (λ n → ≤l n (≤-refl (f n)))

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤ q = z≤
≤-trans p (≤l n q) = ≤l n (≤-trans p q)
≤-trans (s≤ p) (s≤ q) = s≤ (≤-trans p q)
≤-trans (≤l n p) (l≤ q) = ≤-trans p (q n)
≤-trans (l≤ p) q = l≤ (λ n → ≤-trans (p n) q)

≤-suc : ∀ {a b} → a ≤ b → a ≤ asuc b
≤-suc z≤ = z≤
≤-suc (s≤ p) = s≤ (≤-suc p)
≤-suc (≤l {f = f} n p) = ≤-trans (≤-suc p) (s≤ (≤l n (≤-refl (f n))))
≤-suc (l≤ p) = l≤ (λ n → ≤-suc (p n))

≤lim⁻ : ∀ {a f} → asuc a ≤ alim f → Σ ℕ (λ n → asuc a ≤ f n)
≤lim⁻ (≤l n p) = n , p

irr : ∀ a → ¬ (asuc a ≤ a)
irr azero ()
irr (asuc a) (s≤ p) = irr a p
irr (alim f) p with ≤lim⁻ p
... | n , q = irr (f n) (≤-trans (s≤ (≤l n (≤-refl (f n)))) q)

⊲→≤ : ∀ {a b} → a ⊲ b → a ≤ b
⊲→≤ C.self = ≤-refl _
⊲→≤ (C.suc p) = ≤-suc (⊲→≤ p)
⊲→≤ (C.lim n p) = ≤l n (⊲→≤ p)
```

## §2 加法

```agda
infixl 6 _⊞_
_⊞_ : A → A → A
a ⊞ azero = a
a ⊞ asuc b = asuc (a ⊞ b)
a ⊞ alim f = alim (λ n → a ⊞ f n)

≤⊞ : ∀ a b → a ≤ a ⊞ b
≤⊞ a azero = ≤-refl a
≤⊞ a (asuc b) = ≤-suc (≤⊞ a b)
≤⊞ a (alim f) = ≤l 0 (≤⊞ a (f 0))

⊞-mono : ∀ {a a′ b b′} → a ≤ a′ → b ≤ b′ → a ⊞ b ≤ a′ ⊞ b′
⊞-mono {b′ = b′} p z≤ = ≤-trans p (≤⊞ _ b′)
⊞-mono p (s≤ q) = s≤ (⊞-mono p q)
⊞-mono p (≤l n q) = ≤l n (⊞-mono p q)
⊞-mono p (l≤ q) = l≤ (λ n → ⊞-mono p (q n))

⊞-asso : ∀ a b c → a ⊞ (b ⊞ c) ≤ (a ⊞ b) ⊞ c
⊞-asso a b azero = ≤-refl _
⊞-asso a b (asuc c) = s≤ (⊞-asso a b c)
⊞-asso a b (alim f) = l≤ (λ n → ≤l n (⊞-asso a b (f n)))

⊞-assoʳ : ∀ a b c → (a ⊞ b) ⊞ c ≤ a ⊞ (b ⊞ c)
⊞-assoʳ a b azero = ≤-refl _
⊞-assoʳ a b (asuc c) = s≤ (⊞-assoʳ a b c)
⊞-assoʳ a b (alim f) = l≤ (λ n → ≤l n (⊞-assoʳ a b (f n)))
```

## §3 加法封闭: $\psi(a+1)$ 的值

`Clo y`: $y$ 之下对加法封闭. `mul c n` $=c\cdot n$, `ωm c` $=c\cdot\omega$.

```agda
Clo : A → Set
Clo y = ∀ {u v} → asuc u ≤ y → asuc v ≤ y → asuc (u ⊞ v) ≤ y

mul : A → ℕ → A
mul c zero = azero
mul c (suc n) = mul c n ⊞ c

ωm : A → A
ωm c = alim (mul c)

one : A
one = asuc azero

-- 最小
ω-least : ∀ {c y} → Clo y → asuc c ≤ y → ωm c ≤ y
ω-least {c} {y} C h = l≤ (λ n → ≤-trans (≤-suc (≤-refl _)) (go n))
  where
  go : ∀ n → asuc (mul c n) ≤ y
  go zero = ≤-trans (s≤ z≤) h
  go (suc n) = C (go n) h

mul+ : ∀ c n m → mul c n ⊞ mul c m ≤ mul c (n + m)
mul+ c n zero = subst (λ i → mul c n ≤ mul c i) (sym (+-identityʳ n)) (≤-refl _)
mul+ c n (suc m) = subst (λ i → mul c n ⊞ (mul c m ⊞ c) ≤ mul c i) (sym (+-suc n m))
  (≤-trans (⊞-asso (mul c n) (mul c m) c) (⊞-mono (mul+ c n m) (≤-refl c)))

-- 封闭
ω-clo : ∀ c → Clo (ωm c)
ω-clo c {u} {v} p q with ≤lim⁻ p | ≤lim⁻ q
... | n , p₁ | m , q₁ = ≤l (n + m) (≤-trans (⊞-mono (≤-trans (≤-suc (≤-refl u)) p₁) q₁) (mul+ c n m))

-- 在 c 之上
z⊞ : ∀ c → c ≤ azero ⊞ c
z⊞ azero = z≤
z⊞ (asuc c) = s≤ (z⊞ c)
z⊞ (alim f) = l≤ (λ n → ≤l n (z⊞ (f n)))

c<ω : ∀ c → one ≤ c → asuc c ≤ ωm c
c<ω c h = ≤l 2 (⊞-mono {b = one} (z⊞ c) h)

-- 规格: c·ω 是 c 之上最小的加法封闭点
ω-spec : ∀ c → one ≤ c → Clo (ωm c) × (asuc c ≤ ωm c) × (∀ {y} → Clo y → asuc c ≤ y → ωm c ≤ y)
ω-spec c h = ω-clo c , c<ω c h , ω-least

-- 任何满足规格的值都与它互相 ≤
ω-uniq : ∀ {c y} → one ≤ c → Clo y → asuc c ≤ y → (∀ {y′} → Clo y′ → asuc c ≤ y′ → y ≤ y′) → (y ≤ ωm c) × (ωm c ≤ y)
ω-uniq {c} h C s least = least (ω-clo c) (c<ω c h) , ω-least C s
```

## §4 和的一步就是 $\cdot\omega$

`step-ω`: `sum b (nl (const x))` 的值是 $b+x\cdot\omega$. 所以 `ω⋅` 这一行的值就是规格的值.

```agda
sum⊞ : ∀ a x → (a ⊞ sum azero x ≤ sum a x) × (sum a x ≤ a ⊞ sum azero x)
pt⊞  : ∀ a d n → (a ⊞ pt azero d n ≤ pt a d n) × (pt a d n ≤ a ⊞ pt azero d n)
sum⊞ a n0 = ≤-refl a , ≤-refl a
sum⊞ a n1 = ≤-refl _ , ≤-refl _
sum⊞ a (x ⨾ y) =
  ≤-trans (⊞-mono (≤-refl a) (proj₂ (sum⊞ (sum azero x) y)))
    (≤-trans (⊞-asso a (sum azero x) (sum azero y))
      (≤-trans (⊞-mono (proj₁ (sum⊞ a x)) (≤-refl _)) (proj₁ (sum⊞ (sum a x) y)))) ,
  ≤-trans (proj₂ (sum⊞ (sum a x) y))
    (≤-trans (⊞-mono (proj₂ (sum⊞ a x)) (≤-refl _))
      (≤-trans (⊞-assoʳ a (sum azero x) (sum azero y)) (⊞-mono (≤-refl a) (proj₁ (sum⊞ (sum azero x) y)))))
sum⊞ a (nl d) = l≤ (λ n → ≤l n (proj₁ (pt⊞ a d n))) , l≤ (λ n → ≤l n (proj₂ (pt⊞ a d n)))
sum⊞ a (ni () u)
pt⊞ a d zero = ≤-refl a , ≤-refl a
pt⊞ a d (suc n) =
  ≤-trans (⊞-mono (≤-refl a) (proj₂ (sum⊞ (pt azero d n) (d n))))
    (≤-trans (⊞-asso a (pt azero d n) (sum azero (d n)))
      (≤-trans (⊞-mono (proj₁ (pt⊞ a d n)) (≤-refl _)) (proj₁ (sum⊞ (pt a d n) (d n))))) ,
  ≤-trans (proj₂ (sum⊞ (pt a d n) (d n)))
    (≤-trans (⊞-mono (proj₂ (pt⊞ a d n)) (≤-refl _))
      (≤-trans (⊞-assoʳ a (pt azero d n) (sum azero (d n))) (⊞-mono (≤-refl a) (proj₁ (sum⊞ (pt azero d n) (d n))))))

pt-mul : ∀ x n → (pt azero (λ _ → x) n ≤ mul (sum azero x) n) × (mul (sum azero x) n ≤ pt azero (λ _ → x) n)
pt-mul x zero = z≤ , z≤
pt-mul x (suc n) =
  ≤-trans (proj₂ (sum⊞ (pt azero (λ _ → x) n) x)) (⊞-mono (proj₁ (pt-mul x n)) (≤-refl _)) ,
  ≤-trans (⊞-mono (proj₂ (pt-mul x n)) (≤-refl _)) (proj₁ (sum⊞ (pt azero (λ _ → x) n) x))

step-ω : ∀ b x → (sum b (nl (λ _ → x)) ≤ b ⊞ ωm (sum azero x)) × (b ⊞ ωm (sum azero x) ≤ sum b (nl (λ _ → x)))
step-ω b x =
  l≤ (λ n → ≤l n (≤-trans (proj₂ (pt⊞ b (λ _ → x) n)) (⊞-mono (≤-refl b) (proj₁ (pt-mul x n))))) ,
  l≤ (λ n → ≤l n (≤-trans (⊞-mono (≤-refl b) (proj₂ (pt-mul x n))) (proj₁ (pt⊞ b (λ _ → x) n))))
```

## §5 为什么只能走链

折叠 $f$ 把高层的分支 $z$ 送到第 0 层. 如果它对全部分支严格单调, 又有一个公共上界 $v$ ($\psi(\Omega_1)$ 就该是它), 那就矛盾: $z\le f(z)$, 取 $z=v$. 这条不依赖记号, 也不依赖折叠的任何一行.

```agda
no-full : ∀ (f : A → A) (v : A) → (∀ {a b} → a ≤ b → f a ≤ f b) → (∀ {a b} → asuc a ≤ b → asuc (f a) ≤ f b) → (∀ z → asuc (f z) ≤ v) → ⊥
no-full f v m st ub = irr v (≤-trans (s≤ (grow v)) (ub v))
  where
  grow : ∀ z → z ≤ f z
  grow azero = z≤
  grow (asuc a) = ≤-trans (s≤ (grow a)) (st (≤-refl (asuc a)))
  grow (alim h) = l≤ (λ n → ≤-trans (grow (h n)) (m (≤l n (≤-refl (h n)))))
```

## §6 链

$g$ 单调. 从任一点 $s$ 起的迭代的上确界, 是 $s$ 之上对 $g$ 封闭的最小点.

```agda
iter : (A → A) → A → ℕ → A
iter g s zero = s
iter g s (suc n) = g (iter g s n)

chain-least : ∀ {g : A → A} {s y} → s ≤ y → (∀ {u} → u ≤ y → g u ≤ y) → alim (iter g s) ≤ y
chain-least {g} {s} {y} h c = l≤ go
  where
  go : ∀ n → iter g s n ≤ y
  go zero = h
  go (suc n) = c (go n)

chain-closed : ∀ {g : A → A} {s u} → (∀ {a b} → a ≤ b → g a ≤ g b) → asuc u ≤ alim (iter g s) → g u ≤ alim (iter g s)
chain-closed {u = u} m p with ≤lim⁻ p
... | n , q = ≤l (suc n) (m (≤-trans (≤-suc (≤-refl u)) q))
```
