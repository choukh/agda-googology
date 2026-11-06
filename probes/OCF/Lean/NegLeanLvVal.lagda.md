# 头按自己的级读回, 否定一路 (二): "回灌了, 值不变" 的形状

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 本篇**不依赖**构造一路的接口 (接口定稿之前写的部分), 只导入 [LeanTBase](LeanTBase.lagda.md), [LeanTTree](LeanTTree.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路要试第一条值定理: 闭项严格高于全有损折叠. 折叠里回灌与有损只差一行 ([LeanTFold](LeanTFold.lagda.md) 的 `RKa`): 有损是 `ω⋅ c` = `nl (λ _ → c)` (当前世界的分支输出 $c$ 重复 $\omega$ 次), 回灌是 `nl (λ n → Δₙ)` ($\Delta_n$ 是分支在升高的世界 $w_{n+1}$ 里的输出). 第 0 层的数据最后经 `sum` 读成布劳威尔树. 本篇给出: **每一格都严格变大, 求和后的值仍可以相同**.
>
> - **值的序** `_≤_`: `HB S⊥` 上通常的布劳威尔树的序 (与 `TLRuleSpec._≤_` 同四个构造子); `_≈ᵥ_` 是互相 `≤`.
> - **`absorb`** (定理): $\mathrm{ptV}\,b\,f\,n = b + f_0 + \dots + f_{n-1}$. 若对一切 $n$, $c\le f_n\le c\cdot K$ (某个固定的 $K$), 则 $\sup_n \mathrm{ptV}\,b\,f\,n \approx \sup_n (b + c\cdot n)$.
> - **`absorb-D`** (定理, 对数据): 第 0 层数据 `nl d` 与有损形状 `nl (λ _ → x)` 的求和互相 `≤`, 只要每一格的值在 $[\,\mathrm{sum}\,0\,x,\ (\mathrm{sum}\,0\,x)\cdot K\,]$ 里.
> - **实例** **`succ-absorb`**: 每一格比有损多一个后继 (`x ⨾ n1`), 只要 $x$ 的值 $\ge1$, 求和的值相同. **`below-absorb`**: 每一格是有损的 $x$ 再接一段值不超过 $x$ 的数据 (回灌值落在已有界之下), 求和的值相同. **`strict-cell`**: 存在 $b, x, d$ 使每一格的值严格大于有损的那一格 ($\mathrm{hs}\,c\le f_n$), 而求和的值互相 `≤`. 前提实例 `succ-n1`, `succ-ω` ($x$ = `n1`, $x$ = $\omega$).
>
> **只否定什么.** 只否定推断 "回灌那一行每一格的输出 (值) 严格大于有损的那一格, 所以闭项的值严格变大". **不否定**: 回灌提高值 (回灌的格的值若不被有损格的固定倍数界住, 例如 $\Delta_n \ge c\cdot n$, 本篇不适用); 也不对构造一路的闭项说任何事 (它的格的值没有算). 所以一条 "严格高于全有损" 的值定理, 至少要证出回灌的格不被 $c\cdot K$ 界住 (对一切 $K$), 或者绕开这一行 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvVal where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
```

## §1 值的序

```agda
V : Set
V = HB S⊥

infix 4 _≤_ _≈ᵥ_
data _≤_ : V → V → Set where
  z≤ : ∀ {b} → hz ≤ b
  s≤ : ∀ {a b} → a ≤ b → hs a ≤ hs b
  ≤l : ∀ {a f} n → a ≤ f n → a ≤ hl f
  l≤ : ∀ {f b} → (∀ n → f n ≤ b) → hl f ≤ b

_≈ᵥ_ : V → V → Set
a ≈ᵥ b = (a ≤ b) × (b ≤ a)

≤-refl : ∀ a → a ≤ a
≤-refl hz = z≤
≤-refl (hs a) = s≤ (≤-refl a)
≤-refl (hl f) = l≤ (λ n → ≤l n (≤-refl (f n)))
≤-refl (hΩ (() , _) g)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤ q = z≤
≤-trans p (≤l n q) = ≤l n (≤-trans p q)
≤-trans (s≤ p) (s≤ q) = s≤ (≤-trans p q)
≤-trans (≤l n p) (l≤ q) = ≤-trans p (q n)
≤-trans (l≤ p) q = l≤ (λ n → ≤-trans (p n) q)

≤-suc : ∀ {a b} → a ≤ b → a ≤ hs b
≤-suc z≤ = z≤
≤-suc (s≤ p) = s≤ (≤-suc p)
≤-suc (≤l {f = f} n p) = ≤-trans (≤-suc p) (s≤ (≤l n (≤-refl (f n))))
≤-suc (l≤ p) = l≤ (λ n → ≤-suc (p n))

≈-refl : ∀ a → a ≈ᵥ a
≈-refl a = ≤-refl a , ≤-refl a

≈-trans : ∀ {a b c} → a ≈ᵥ b → b ≈ᵥ c → a ≈ᵥ c
≈-trans (p , p′) (q , q′) = ≤-trans p q , ≤-trans q′ p′

≈-sym : ∀ {a b} → a ≈ᵥ b → b ≈ᵥ a
≈-sym (p , q) = q , p

-- 两个 ℕ-极限: 逐项互相 ≤ 则互相 ≤
hl-≈ : ∀ {f g : ℕ → V} → (∀ n → f n ≈ᵥ g n) → hl f ≈ᵥ hl g
hl-≈ p = l≤ (λ n → ≤l n (proj₁ (p n))) , l≤ (λ n → ≤l n (proj₂ (p n)))
```

## §2 加法的单调与结合 (`LeanTBase._⊞_`, 右边逐构造子)

```agda
⊞-infl : ∀ a b → a ≤ a ⊞ b
⊞-infl a hz = ≤-refl a
⊞-infl a (hs b) = ≤-suc (⊞-infl a b)
⊞-infl a (hl f) = ≤l 0 (⊞-infl a (f 0))
⊞-infl a (hΩ (() , _) g)

⊞-monoʳ : ∀ a {x y} → x ≤ y → a ⊞ x ≤ a ⊞ y
⊞-monoʳ a {y = y} z≤ = ⊞-infl a y
⊞-monoʳ a (s≤ p) = s≤ (⊞-monoʳ a p)
⊞-monoʳ a (≤l n p) = ≤l n (⊞-monoʳ a p)
⊞-monoʳ a (l≤ p) = l≤ (λ n → ⊞-monoʳ a (p n))

⊞-monoˡ : ∀ {a b} x → a ≤ b → a ⊞ x ≤ b ⊞ x
⊞-monoˡ hz p = p
⊞-monoˡ (hs x) p = s≤ (⊞-monoˡ x p)
⊞-monoˡ (hl f) p = l≤ (λ n → ≤l n (⊞-monoˡ (f n) p))
⊞-monoˡ (hΩ (() , _) g) p

⊞-assoc : ∀ a b c → (a ⊞ b) ⊞ c ≈ᵥ a ⊞ (b ⊞ c)
⊞-assoc a b hz = ≈-refl (a ⊞ b)
⊞-assoc a b (hs c) = s≤ (proj₁ (⊞-assoc a b c)) , s≤ (proj₂ (⊞-assoc a b c))
⊞-assoc a b (hl f) = hl-≈ (λ n → ⊞-assoc a b (f n))
⊞-assoc a b (hΩ (() , _) g)

hz-⊞ : ∀ c → hz ⊞ c ≈ᵥ c
hz-⊞ hz = ≈-refl hz
hz-⊞ (hs c) = s≤ (proj₁ (hz-⊞ c)) , s≤ (proj₂ (hz-⊞ c))
hz-⊞ (hl f) = hl-≈ (λ n → hz-⊞ (f n))
hz-⊞ (hΩ (() , _) g)

≈-⊞ : ∀ {a a′ b b′} → a ≈ᵥ a′ → b ≈ᵥ b′ → a ⊞ b ≈ᵥ a′ ⊞ b′
≈-⊞ {a} {a′} {b} {b′} (p , p′) (q , q′) =
  ≤-trans (⊞-monoˡ b p) (⊞-monoʳ a′ q) , ≤-trans (⊞-monoˡ b′ p′) (⊞-monoʳ a q′)
```

## §3 吸收: 被有损格的固定倍数界住的格, 求和后值不变

`ptV b f n` $=b+f_0+\dots+f_{n-1}$; `C c` 是常值 $c$; `cK c K` $=c\cdot K$.

```agda
ptV : V → (ℕ → V) → ℕ → V
ptV b f zero = b
ptV b f (suc n) = ptV b f n ⊞ f n

C : V → ℕ → V
C c _ = c

cK : V → ℕ → V
cK c K = ptV hz (C c) K

add-K : ∀ b c m K → ptV b (C c) m ⊞ cK c K ≤ ptV b (C c) (K + m)
add-K b c m zero = ≤-refl (ptV b (C c) m)
add-K b c m (suc K) =
  ≤-trans (proj₂ (⊞-assoc (ptV b (C c) m) (cK c K) c)) (⊞-monoˡ c (add-K b c m K))

idx : ℕ → ℕ → ℕ
idx K zero = zero
idx K (suc n) = K + idx K n

module _ (b c : V) (f : ℕ → V) where
  upper : ∀ K → (∀ n → f n ≤ cK c K) → ∀ n → ptV b f n ≤ ptV b (C c) (idx K n)
  upper K hi zero = ≤-refl b
  upper K hi (suc n) =
    ≤-trans (⊞-monoˡ (f n) (upper K hi n))
      (≤-trans (⊞-monoʳ (ptV b (C c) (idx K n)) (hi n)) (add-K b c (idx K n) K))

  lower : (∀ n → c ≤ f n) → ∀ n → ptV b (C c) n ≤ ptV b f n
  lower lo zero = ≤-refl b
  lower lo (suc n) = ≤-trans (⊞-monoˡ c (lower lo n)) (⊞-monoʳ (ptV b f n) (lo n))

  absorb : ∀ K → (∀ n → c ≤ f n) → (∀ n → f n ≤ cK c K) → hl (ptV b f) ≈ᵥ hl (ptV b (C c))
  absorb K lo hi = l≤ (λ n → ≤l (idx K n) (upper K hi n)) , l≤ (λ n → ≤l n (lower lo n))
```

## §4 对数据: 第 0 层的 `nl` 与有损形状

`sum b x` 与 $b\boxplus\mathrm{sum}\,0\,x$ 互相 `≤` (`sum-⊞`); `nl d` 的求和就是 `ptV`.

```agda
module OnData (T : KS) where
  open Tree T using (D₀; sum; pt; n0; n1; _⨾_; nl; ni; nc; nw)

  sum-⊞ : ∀ {W} b (x : D₀ W) → sum b x ≈ᵥ b ⊞ sum hz x
  pt-⊞  : ∀ {W} b (d : ℕ → D₀ W) n → pt b d n ≈ᵥ b ⊞ pt hz d n
  sum-⊞ b n0 = ≈-refl b
  sum-⊞ b n1 = ≈-refl (hs b)
  sum-⊞ b (x ⨾ y) =
    ≈-trans (sum-⊞ (sum b x) y)
      (≈-trans (≈-⊞ (sum-⊞ b x) (≈-refl (sum hz y)))
        (≈-trans (⊞-assoc b (sum hz x) (sum hz y))
          (≈-⊞ (≈-refl b) (≈-sym (sum-⊞ (sum hz x) y)))))
  sum-⊞ b (nl d) = hl-≈ (pt-⊞ b d)
  sum-⊞ b (ni () u)
  sum-⊞ b (nc (inj₁ _) () u)
  sum-⊞ b (nc (inj₂ _) () u)
  sum-⊞ b (nw p x) = sum-⊞ b x
  pt-⊞ b d zero = ≈-refl b
  pt-⊞ b d (suc n) =
    ≈-trans (sum-⊞ (pt b d n) (d n))
      (≈-trans (≈-⊞ (pt-⊞ b d n) (≈-refl (sum hz (d n))))
        (≈-trans (⊞-assoc b (pt hz d n) (sum hz (d n)))
          (≈-⊞ (≈-refl b) (≈-sym (sum-⊞ (pt hz d n) (d n))))))

  pt-ptV : ∀ {W} b (d : ℕ → D₀ W) n → pt b d n ≈ᵥ ptV b (λ k → sum hz (d k)) n
  pt-ptV b d zero = ≈-refl b
  pt-ptV b d (suc n) = ≈-trans (sum-⊞ (pt b d n) (d n)) (≈-⊞ (pt-ptV b d n) (≈-refl (sum hz (d n))))

  sum-nl : ∀ {W} b (d : ℕ → D₀ W) → sum b (nl d) ≈ᵥ hl (ptV b (λ k → sum hz (d k)))
  sum-nl b d = hl-≈ (pt-ptV b d)

  -- 有损形状 nl (λ _ → x) 与回灌形状 nl d: 每格的值在 [c, c·K] 里则求和互相 ≤
  absorb-D : ∀ {W} b (x : D₀ W) (d : ℕ → D₀ W) K →
    (∀ n → sum hz x ≤ sum hz (d n)) → (∀ n → sum hz (d n) ≤ cK (sum hz x) K) →
    sum b (nl d) ≈ᵥ sum b (nl (λ _ → x))
  absorb-D b x d K lo hi =
    ≈-trans (sum-nl b d) (≈-trans (absorb b (sum hz x) (λ k → sum hz (d k)) K lo hi) (≈-sym (sum-nl b (λ _ → x))))
```

**实例.** 每一格多一个后继; 每一格接一段值不超过 $x$ 的数据.

```agda
  c≤cc : ∀ c → c ≤ cK c 2
  c≤cc c = ≤-trans (proj₂ (hz-⊞ c)) (⊞-infl (hz ⊞ c) c)

  -- 1 ≤ c 时, c+1 ≤ c·2
  sc≤cc : ∀ c → hs hz ≤ c → hs c ≤ cK c 2
  sc≤cc c one = ≤-trans (⊞-monoʳ c one) (⊞-monoˡ c (proj₂ (hz-⊞ c)))

  succ-absorb : ∀ {W} b (x : D₀ W) → hs hz ≤ sum hz x → sum b (nl (λ _ → x ⨾ n1)) ≈ᵥ sum b (nl (λ _ → x))
  succ-absorb b x one = absorb-D b x (λ _ → x ⨾ n1) 2 (λ _ → ≤-suc (≤-refl (sum hz x))) (λ _ → sc≤cc (sum hz x) one)

  -- 回灌值落在已有界之下: 每格是 x 再接 y n, sum hz (y n) ≤ sum hz x
  below-absorb : ∀ {W} b (x : D₀ W) (y : ℕ → D₀ W) → (∀ n → sum hz (y n) ≤ sum hz x) →
    sum b (nl (λ n → x ⨾ y n)) ≈ᵥ sum b (nl (λ _ → x))
  below-absorb b x y hy = absorb-D b x (λ n → x ⨾ y n) 2 lo hi
    where
    lo : ∀ n → sum hz x ≤ sum hz (x ⨾ y n)
    lo n = ≤-trans (⊞-infl (sum hz x) (sum hz (y n))) (proj₂ (sum-⊞ (sum hz x) (y n)))
    hi : ∀ n → sum hz (x ⨾ y n) ≤ cK (sum hz x) 2
    hi n = ≤-trans (proj₁ (sum-⊞ (sum hz x) (y n)))
             (≤-trans (⊞-monoʳ (sum hz x) (hy n)) (⊞-monoˡ (sum hz x) (proj₂ (hz-⊞ (sum hz x)))))

  -- 每格严格大于有损格, 求和的值互相 ≤
  strict-cell : ∀ {W} b (x : D₀ W) → hs hz ≤ sum hz x →
    (hs (sum hz x) ≤ sum hz (x ⨾ n1)) × (sum b (nl (λ _ → x ⨾ n1)) ≈ᵥ sum b (nl (λ _ → x)))
  strict-cell b x one = ≤-refl _ , succ-absorb b x one
```

**前提实例.** $x$ = `n1` (值 $1$) 与 $x=\omega$ (`nl (λ _ → n1)`, 值 $\omega$).

```agda
  succ-n1 : ∀ {W} b → sum {W} b (nl (λ _ → n1 ⨾ n1)) ≈ᵥ sum b (nl (λ _ → n1))
  succ-n1 b = succ-absorb b n1 (s≤ z≤)

  ωD : ∀ {W} → D₀ W
  ωD = nl (λ _ → n1)

  succ-ω : ∀ {W} b → sum {W} b (nl (λ _ → ωD ⨾ n1)) ≈ᵥ sum b (nl (λ _ → ωD))
  succ-ω b = succ-absorb b ωD (≤l 1 (s≤ z≤))
```

## §5 结论 (按档)

- **[定理]** **`absorb`**: $c\le f_n\le c\cdot K$ (对一切 $n$, 固定 $K$) ⟹ $\sup_n(b+\sum_{k<n}f_k)\approx\sup_n(b+c\cdot n)$. **`absorb-D`**: 同一件事对第 0 层数据 `nl d` 与有损形状 `nl (λ _ → x)`. 实例 **`succ-absorb`**, **`below-absorb`**, **`strict-cell`**; 前提实例 `succ-n1`, `succ-ω`.
- **[判断]** 构造一路的值定理若写成 "回灌那一行每一格严格大于有损那一格, 所以闭项严格大", 是 `strict-cell` 否定的推断; 要严格变大, 回灌的格对每个 $K$ 都要不被 $c\cdot K$ 界住 (例如回灌升出的界给出 $\Omega$-分支走得更深), 这只能对实例算.
