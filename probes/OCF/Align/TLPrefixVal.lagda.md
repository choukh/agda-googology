# 前缀 (三): 什么叫不改值的前缀

> 入口 [TLPrefix](TLPrefix.lagda.md). **判决: HOLDS (编译过, 无条件).** 导入 `LadderOrdPos`, `LadderOrdCode`, 不读记号.
>
> **定义.** `VP f f′`: 列 $f'$ 逐项与 $f$ 互相 `≼`, 且 $f'_n$ 字面在 $f'_{n+1}$ 之下. 这是 "放大 $x\mapsto y$ 满足 $x\preccurlyeq y\preccurlyeq x$ 而字面步进成立".
>
> | 前缀 | 形状 | 定理 | 结论 |
> | --- | --- | --- | --- |
> | (iii) 差分的和 | `Pv zero (G hf hr)`, 块是高于切点的部分 | `col-exact`, `VP-Lit` | **不改值, 逐项**. 对一切 `Lit` 的列 |
> | (i) 绝对的和 | $\sum_j(f_j+1)$, 即 `val ⌈ t ⌉` | `abs-overshoot` | **改值**: `ω·2ᴸ` 这一棵带证书的树上也改 |
> | (ii) 世界前缀 $u+y$ | `u ⊕ y` | `≼⊕′`, `no-⊕≼`, `1⊕≼`, `1⊕≼lim` | $y\preccurlyeq u+y$ 总成立; $u+y\preccurlyeq y$ 对 $u=y=\omega$ 假; $u=1$ 时 $1+y\preccurlyeq y+1$ 总成立, 极限的 `Lit` 上 $1+y\preccurlyeq y$ |
>
> **`graftV→LPO`.** 字面的切点不能从值的证据得到: 若 $u+1\preccurlyeq y$ (都带证书) 就有 $y'$ 与 $y$ 互相 `≼` 且 $u$ 字面在 $y'$ 之下, 则 LPO. 所以 (iii) 要字面的证据 (`NoCumLit.graft₀` 读 `⊴₀`, 也就是 `Hn`), 不能只靠 "$u$ 的值低于 $y$". 这条不否定 (ii): (ii) 不要证据, 代价是值的等式要事后证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixVal where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _⊑ᴵ_; natᴵ; ωᴵ; <ᴵ-trans)
open import OCF.Align.TLCodeShape using (Sh)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe
open import OCF.Align.TLCodeArith
open import OCF.Align.TLCodeAccept using (toC; Pv; Pv-val; plus-mono; lv₀; lv-exact)
open import OCF.Align.LadderOrdPos using (Code; plus; Sb; val; cz; cs; cl)
open import OCF.Align.LadderOrdCode using (⌈_⌉)
open import OCF.Align.LadderOrdNeg using (LPO; any; any-true; true-any)
```

## §1 定义, (iii) 不改值

差分的块形读成码, 部分和逐项就是原列.

```agda
VP : (ℕ → Ordᴵ) → (ℕ → Ordᴵ) → Set
VP f f′ = (∀ n → Eqv (f′ n) (f n)) × (∀ n → f′ n <ᴵ f′ (suc n))

-- 字面的列: 自己就是自己的不改值前缀
VP-Lit : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n <ᴵ f (suc n)) → VP f f
VP-Lit hr = (λ n → ≼-refl _ , ≼-refl _) , hr

s≼⁻ : ∀ {a b} → suc a ≼ suc b → a ≼ b
s≼⁻ (s≼ x) = x
s≼⁻ (s≼ʳ x) = ≼-trans (s≼ʳ (≼-refl _)) x

aval : ∀ {a t} (h : Lit t) (q : a <ᴵ t) → Eqv (plus (suc a) (toC (above h q))) t
aval h q = OCF.Align.TLCodeAccept.above-val h q

module Col {f : ℕ → Ordᴵ} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) where
  G : ℕ → Code
  G i = toC (tailb hf hr 0 (shape (hf 0)) i)

  -- 差分的部分和
  S-eq : ∀ i → Eqv (plus (Sb zero G i) (G i)) (f (i + 0))
  S-eq zero = OCF.Align.TLCodeAccept.Lit-val (hf 0)
  S-eq (suc i) =
    let A = aval (hf (suc i + 0)) (hr (i + 0))
        e = S-eq i
    in ≼-trans (plus-mono (G (suc i)) (s≼ (proj₁ e))) (proj₁ A)
     , ≼-trans (proj₂ A) (plus-mono (G (suc i)) (s≼ (proj₂ e)))

  -- 和式形式的列: 逐项不改值, 字面步进
  col-exact : ∀ i → Eqv (Pv zero G i) (f (i + 0))
  col-exact i = ≼-trans (proj₁ (Pv-val zero G i)) (proj₁ (S-eq i)) , ≼-trans (proj₂ (S-eq i)) (proj₂ (Pv-val zero G i))
```

## §2 (i) 绝对的和改值

$\sum_j((\omega+j)+1)$ 已经越过 $\omega\cdot2+1$, 而 `ω·2ᴸ` 是带证书的树, $\omega\cdot 2$ 的值不变 (`Lit-val`).

```agda
no-s≼ : ∀ a → suc a ≼ a → ⊥
no-s≼ zero ()
no-s≼ (suc a) (s≼ x) = no-s≼ a x
no-s≼ (suc a) (s≼ʳ x) = no-s≼ a (≼-trans (s≼ʳ (≼-refl _)) x)
no-s≼ (lim f s) (l≼ʳ n x) = no-s≼ (f n) (≼-trans (s≼ (l≼ʳ n (≼-refl _))) x)

⊕-l≼ : ∀ {a a′} y → a ≼ a′ → a ⊕ y ≼ a′ ⊕ y
⊕-l≼ zero x = x
⊕-l≼ (suc y) x = s≼ (⊕-l≼ y x)
⊕-l≼ (lim f s) x = l≼ (λ n → l≼ʳ n (⊕-l≼ (f n) x))

≼-plus′ : ∀ b c → b ≼ plus b c
≼-Sb′ : ∀ b g j → b ≼ Sb b g j
≼-plus′ b cz = ≼-refl b
≼-plus′ b (cs c) = s≼ʳ (≼-plus′ b c)
≼-plus′ b (cl g) = l≼ʳ 0 (≼-refl b)
≼-Sb′ b g zero = ≼-refl b
≼-Sb′ b g (suc j) = s≼ʳ (≼-trans (≼-Sb′ b g j) (≼-plus′ (Sb b g j) (g j)))

-- a ⊕ y ≼ a + ⌈y⌉: 放大只会更大
dom⊕ : ∀ a y → a ⊕ y ≼ plus a ⌈ y ⌉
dom⊕ a zero = ≼-refl a
dom⊕ a (suc y) = s≼ (dom⊕ a y)
dom⊕ a (lim f s) = l≼ (λ n → l≼ʳ (suc n) (s≼ʳ (≼-trans (dom⊕ a (f n)) (plus-mono ⌈ f n ⌉ (≼-Sb′ a (λ i → ⌈ f i ⌉) n)))))

addN≼ : ∀ a n → addN a n ≼ a ⊕ natᴵ n
addN≼ a zero = ≼-refl a
addN≼ a (suc n) = s≼ (addN≼ a n)

ω≼lim : ∀ {a} → a ≼ plus zero ⌈ a ⌉
ω≼lim {a} = dom⊕′ a
  where
  ze : ∀ y → y ≼ zero ⊕ y
  ze zero = z≼
  ze (suc y) = s≼ (ze y)
  ze (lim f s) = l≼ (λ n → l≼ʳ n (ze (f n)))
  dom⊕′ : ∀ y → y ≼ plus zero ⌈ y ⌉
  dom⊕′ y = ≼-trans (ze y) (dom⊕ zero y)

abs-lower : suc ω·2ᴸ ≼ val ⌈ ω·2ᴸ ⌉
abs-lower = l≼ʳ 2 (s≼ (s≼ʳ (l≼ step)))
  where
  g : ℕ → Code
  g n = ⌈ addN ωᴵ n ⌉
  S₁ : Ordᴵ
  S₁ = Sb zero g 1
  ω≼S₁ : ωᴵ ≼ S₁
  ω≼S₁ = s≼ʳ ω≼lim
  step : ∀ n → addN ωᴵ n ≼ plus S₁ ⌈ ωᴵ ⌉
  step n = ≼-trans (addN≼ ωᴵ n) (≼-trans (⊕-l≼ (natᴵ n) ω≼S₁) (≼-trans (lemma n) (dom⊕ S₁ ωᴵ)))
    where
    lemma : ∀ n → S₁ ⊕ natᴵ n ≼ S₁ ⊕ ωᴵ
    lemma n = l≼ʳ n (≼-refl _)

abs-overshoot : val ⌈ ω·2ᴸ ⌉ ≼ ω·2ᴸ → ⊥
abs-overshoot x = no-s≼ ω·2ᴸ (≼-trans abs-lower x)

-- 同一棵树上差分的和不改值
ω·2-delta : Eqv (val (toC (shape Lω·2))) ω·2ᴸ
ω·2-delta = OCF.Align.TLCodeAccept.Lit-val Lω·2
```

## §3 (ii) 世界前缀

```agda
≼⊕′ : ∀ u y → y ≼ u ⊕ y
≼⊕′ u zero = z≼
≼⊕′ u (suc y) = s≼ (≼⊕′ u y)
≼⊕′ u (lim f s) = l≼ (λ n → l≼ʳ n (≼⊕′ u (f n)))

-- u 大时 u + y 高于 y
no-⊕≼ : (∀ u y → u ⊕ y ≼ y) → ⊥
no-⊕≼ k = no-s≼ ωᴵ (≼-trans (s≼ (≼-refl ωᴵ)) (≼-trans (l≼ʳ 1 (≼-refl _)) (k ωᴵ ωᴵ)))

𝟏 : Ordᴵ
𝟏 = suc zero

-- u = 1
1⊕≼ : ∀ y → 𝟏 ⊕ y ≼ suc y
1⊕≼ zero = s≼ z≼
1⊕≼ (suc y) = s≼ (1⊕≼ y)
1⊕≼ (lim f s) = l≼ (λ n → ≼-trans (1⊕≼ (f n)) (s≼ (l≼ʳ n (≼-refl _))))

1⊕≼lim : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} → (∀ n → f n <ᴵ f (suc n)) → 𝟏 ⊕ lim f s ≼ lim f s
1⊕≼lim hr = l≼ (λ n → l≼ʳ (suc n) (≼-trans (1⊕≼ _) (<→s≼ (hr n))))
```

## §4 字面的切点不能从值的证据得到

`aₕ` 是带证书的树, 列是 $n$; 一旦 $h$ 见到 `true` 就换成 $\omega+n$. 值是 $\omega$ 或 $\omega\cdot 2$. $\omega+1\preccurlyeq a_h+1$ 无条件, 要是能把 $\omega$ 字面地接进一个同值的副本, 就判定了 $h$.

```agda
b : ℕ → Bool → Ordᴵ
b n false = natᴵ n
b n true = addN ωᴵ n

nat<ω+ : ∀ m n → natᴵ m <ᴵ addN ωᴵ (suc n)
nat<ω+ m zero = suc (lim (suc m) zero)
nat<ω+ m (suc n) = suc (nat<ω+ m n)

c : (ℕ → Bool) → ℕ → Ordᴵ
c h n = b n (any h n)

c-step : ∀ h n → c h n <ᴵ c h (suc n)
c-step h n with any h n | h (suc n)
... | false | false = zero
... | false | true = nat<ω+ n n
... | true | _ = zero

aₕ : (ℕ → Bool) → Ordᴵ
aₕ h = limᴸ (c h) (c-step h)

L-b : ∀ n x → Lit (b n x)
L-b n false = Lnat n
L-b n true = Laddn Lω n

L-aₕ : ∀ h → Lit (aₕ h)
L-aₕ h = ll (λ n → L-b n (any h n)) (c-step h)

nat≼ω+ : ∀ n → natᴵ n ≼ addN ωᴵ n
nat≼ω+ zero = z≼
nat≼ω+ (suc n) = s≼ (nat≼ω+ n)

nat≼b : ∀ n x → natᴵ n ≼ b n x
nat≼b n false = ≼-refl _
nat≼b n true = nat≼ω+ n

ω≼aₕ : ∀ h → ωᴵ ≼ aₕ h
ω≼aₕ h = l≼ (λ n → l≼ʳ n (nat≼b n (any h n)))

no-sω≼nat : ∀ n → suc ωᴵ ≼ natᴵ n → ⊥
no-sω≼nat zero ()
no-sω≼nat (suc n) (s≼ x) = no-ω n x
  where
  no-ω : ∀ n → ωᴵ ≼ natᴵ n → ⊥
  no-ω zero (l≼ k) = no-sz (k 1)
    where
    no-sz : natᴵ 1 ≼ zero → ⊥
    no-sz ()
  no-ω (suc n) (l≼ k) = no-ω n (l≼ (λ m → pred≼ (k (suc m))))
    where
    pred≼ : ∀ {m} → natᴵ (suc m) ≼ natᴵ (suc n) → natᴵ m ≼ natᴵ n
    pred≼ = s≼⁻
  no-ω (suc n) (s≼ʳ x) = no-ω n x
no-sω≼nat (suc n) (s≼ʳ x) = no-sω≼nat n x

ex : ∀ h → suc ωᴵ ≼ aₕ h → Σ ℕ λ j → h j ≡ true
ex h (l≼ʳ n y) with any h n in e
... | true = any-true h n e
... | false = ⊥-elim (no-sω≼nat n y)

ω≼ω+ : ∀ n → ωᴵ ≼ addN ωᴵ n
ω≼ω+ zero = ≼-refl _
ω≼ω+ (suc n) = s≼ʳ (ω≼ω+ n)

b-tr : ∀ n x y → x ≡ true → suc ωᴵ ≼ b (suc n) (x ∨ y)
b-tr n true y refl = s≼ (ω≼ω+ n)

fls : ∀ h → aₕ h ≼ ωᴵ → ∀ n → h n ≡ false
fls h k n with h n in e
... | false = refl
... | true = ⊥-elim (no-s≼ ωᴵ (≼-trans (l≼ʳ (suc n) (b-tr n (any h n) (h (suc n)) (true-any h n e))) k))

GraftV : Set
GraftV = ∀ {u y} → Lit u → Lit y → suc u ≼ y → Σ Ordᴵ λ y′ → Lit y′ × (Eqv y′ y × (u <ᴵ y′))

graftV→LPO : GraftV → LPO
graftV→LPO k h with k Lω (ls (L-aₕ h)) (s≼ (ω≼aₕ h))
... | _ , _ , (p₁ , p₂) , zero = inj₂ (fls h (s≼⁻ p₂))
... | _ , _ , (p₁ , p₂) , suc q = inj₁ (ex h (≼-trans (<→s≼ q) (s≼⁻ p₁)))
... | _ , ll hg hr , (p₁ , l≼ʳ m x) , lim n q =
  ⊥-elim (no-s≼ (suc (aₕ h)) (≼-trans (s≼ x) (≼-trans (<→s≼ (hr m)) (≼-trans (l≼ʳ (suc m) (≼-refl _)) p₁))))
```

字面的证据时前提成立: `NoCumLit.graft₀`. 所以这条只说证据必须是字面的.
