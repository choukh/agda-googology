# 带类型折叠到 sup 层, 否定一路 (二): 逐站独立坍缩, 保留节点的对角不合法

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 本篇**不依赖**构造一路的接口 `TySupIf`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** [Fab3Typed](Fab3Typed.lagda.md) 的折叠 `Ψ` 对一切 `T` 一条定义, 但沿后继塔折到底; `sup ℕ` 层上若**各站独立地**折 (第 $k$ 站的部分只在第 $k$ 个分量里折, 输出仍在第 $k$ 个分量里), 输出的 ℕ-对角是否合法? [HtTowerNeg](HtTowerNeg.lagda.md) 的 `no-naive-diag` 只说了逐级的 `Ωn k` 本身; 本篇对一切 `sup I G` 与一切 "与嵌入交换" 的逐站映射陈述.
>
> **结果.**
>
> 1. **`no-cross` (定理, 对一切 `I`, `G`).** 在 `sup I G` 里, 第 $j$ 个分量里带 $\Omega$-结点的高度, 不是第 $j'\neq j$ 个分量里任何高度的第一位置 (任一世界). 证明同 `no-naive-diag`: 第一位置保持 "一切结点的种类都在第 $j'$ 个分量".
> 2. **`indep-illegal` (定理).** 一列 $k\mapsto\iota_{\sigma k}(y_k)$, 若某处相邻两站不同 ($\sigma k\neq\sigma(k+1)$) 且 $y_k$ 带 $\Omega$-结点, 则它的 ℕ-极限不合法 (要一个世界).
> 3. **`sw-illegal` (定理).** 逐站映射 $\Phi$ (满足 $\Phi(\iota_j x)\equiv\iota_j(\varphi_j x)$, 与嵌入交换) 把这样一列的输出也送成不合法的 ℕ-极限, 只要某处 $\varphi$ 的输出带 $\Omega$-结点.
> 4. **`typed-indep-illegal` (定理, 实例).** 带类型折叠本身: 第 $k$ 站是 Fab3Typed 塔的第 $k+2$ 层, 它的顶 `Ω (k+2)` 用 `Fold.Ψ` 折一层, 输出放回第 $k$ 个分量 ($G\,k=$ `T (k+1)`). 输出带旧种类的 $\Omega$-结点 (`has-out`, 就是 `feed-Ω` 的那个结点), 所以这列的 ℕ-极限**不合法**.
>
> **前提实例.** `sw-id`: 恒等是逐站映射, 所以 `StationWise` 可满足; 实例 4 不经 `StationWise`, 直接对折叠的输出陈述. 世界: `wT`. `has-out k`: 对一切 $k$ 成立.
>
> **只否定什么.** 只否定: 在 `sup I G` (世界是裸下标上的积, 种类带分量号) 里, 各站输出**保留自己分量的结点**, 再取 ℕ-对角. **不否定**: (i) 各站输出先接起来 (`⊞`, 如 `HtTowerU.θ`, Fab3Typed 的 `Σ⊥`); (ii) 输出不带结点 (折到底 `S⊥`, `has-out` 不成立; Fab3Typed 的 `TΩω` 就是这样); (iii) 输出的旧种类在各站之间认同 (目标不是 `sup`, 或者旧种类不带站号): 那时 `no-cross` 的前提 "不同分量" 不成立; 这正是 `sup` 层要决定的 "留在哪里". 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupDiag where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab3Typed using (T; Ω; W; module Fold)
```

## §1 结点所在的分量

`HasΩ x`: $x$ 里至少有一个 $\Omega$-结点 (沿后继, ℕ-极限的某一项). `In j x`: $x$ 里一切结点的种类都在第 $j$ 个分量.

```agda
HasΩ : ∀ {S : KS} → HB S → Set
HasΩ hz = ⊥
HasΩ (hs x) = HasΩ x
HasΩ (hl f) = Σ ℕ (λ n → HasΩ (f n))
HasΩ (hΩ κ g) = ⊤

module _ {I : Set} {G : I → KS} where
  In : I → HB (sup I G) → Set
  In j hz = ⊤
  In j (hs x) = In j x
  In j (hl f) = ∀ n → In j (f n)
  In j (hΩ κ g) = (proj₁ κ ≡ j) × (∀ c → In j (g c))

  in-ι : ∀ j x → In j (ι {I} {G} j x)
  in-ι j hz = tt
  in-ι j (hs x) = in-ι j x
  in-ι j (hl f) = λ n → in-ι j (f n)
  in-ι j (hΩ κ g) = refl , (λ c → in-ι j (g c))

  in⊲ : ∀ {j a b w} → a ⊲[ w ] b → In j b → In j a
  in⊲ hself h = h
  in⊲ (hsuc p) h = in⊲ p h
  in⊲ (hlim n p) h = in⊲ p (h n)
  in⊲ (hLim e p) h = in⊲ p (proj₂ h _)

  in-has : ∀ {j j′} x → In j (ι {I} {G} j′ x) → HasΩ x → j′ ≡ j
  in-has (hs x) h o = in-has x h o
  in-has (hl f) h (n , o) = in-has (f n) (h n) o
  in-has (hΩ κ g) h o = proj₁ h

  no-cross : ∀ {w} j j′ (a : HB (G j)) (b : HB (G j′)) → ¬ (j ≡ j′) → HasΩ a →
             ¬ (ι {I} {G} j a ⊲[ w ] ι j′ b)
  no-cross j j′ a b ne o p = ne (in-has a (in⊲ p (in-ι j′ b)) o)
```

## §2 逐站的对角

```agda
  indep-illegal : (w : Wd (sup I G)) (σ : ℕ → I) (y : (k : ℕ) → HB (G (σ k))) (k : ℕ) →
                  ¬ (σ k ≡ σ (suc k)) → HasΩ (y k) → ¬ LgB (hl (λ m → ι {I} {G} (σ m) (y m)))
  indep-illegal w σ y k ne o (st , _) = no-cross (σ k) (σ (suc k)) (y k) (y (suc k)) ne o (st {w} k)
```

**逐站映射.** $\Phi$ 与嵌入交换: 第 $j$ 个分量的高度先嵌入再映射, 等于先在第 $j$ 站里用 $\varphi_j$ 再嵌入. 输入可以来自任一 `sup I F`.

```agda
module _ {I : Set} {F G : I → KS} where
  StationWise : (HB (sup I F) → HB (sup I G)) → ((j : I) → HB (F j) → HB (G j)) → Set
  StationWise Φ φ = ∀ j x → Φ (ι {I} {F} j x) ≡ ι {I} {G} j (φ j x)

  sw-illegal : (w : Wd (sup I G)) (Φ : HB (sup I F) → HB (sup I G)) (φ : (j : I) → HB (F j) → HB (G j)) →
               StationWise Φ φ → (σ : ℕ → I) (x : (k : ℕ) → HB (F (σ k))) (k : ℕ) →
               ¬ (σ k ≡ σ (suc k)) → HasΩ (φ (σ k) (x k)) →
               ¬ LgB (hl (λ m → Φ (ι {I} {F} (σ m) (x m))))
  sw-illegal w Φ φ sw σ x k ne o (st , _) =
    no-cross {I} {G} (σ k) (σ (suc k)) (φ (σ k) (x k)) (φ (σ (suc k)) (x (suc k))) ne o
      (subst (λ z → z ⊲[ w ] ι (σ (suc k)) (φ (σ (suc k)) (x (suc k)))) (sw (σ k) (x k))
        (subst (λ z → Φ (ι (σ k) (x k)) ⊲[ w ] z) (sw (σ (suc k)) (x (suc k))) (st {w} k)))
```

前提实例 `sw-id`: 恒等是逐站映射, 所以 `StationWise` 可满足. 注意 `StationWise` 对**一切** $j$ 陈述, 而 $\iota_j\,0=0$ 对一切 $j$ 相同, 所以它逼 $\varphi_j$ 在不带结点的高度上与 $j$ 无关 (Fab3Typed 的 `Ψ` 在 $0$ 上给 $1$, 与站无关); 只用到 `sw-illegal` 时也可以只对那一列要求交换, 证明不变.

```agda
sw-id : {I : Set} {G : I → KS} → StationWise {I} {G} {G} (λ h → h) (λ j x → x)
sw-id j x = refl
```


## §3 实例: 带类型折叠的各站顶

第 $k$ 站的输入是 Fab3Typed 塔第 $k+2$ 层 (`T (k+2)`) 的顶 `Ω (k+2)`, 折一层 (`Fold.Ψ (T (k+1))`, 世界 `W (k+2)`) 到 `T (k+1)`, 放回第 $k$ 个分量. 输出的链的第 0 点是旧种类 $\Omega_{k+1}$ 的结点 (`feed-Ω` 的一般形), 所以 `HasΩ`.

```agda
G₁ : ℕ → KS
G₁ k = T (suc k)

out : (k : ℕ) → HB (G₁ k)
out k = Fold.Ψ (T (suc k)) (W (suc (suc k))) (Ω (suc (suc k)))

has-out : ∀ k → HasΩ (out k)
has-out k = 0 , tt

wT : Wd (sup ℕ G₁)
wT k = W (suc k)

suc≢ : ∀ k → ¬ (k ≡ suc k)
suc≢ zero ()
suc≢ (suc k) e = suc≢ k (cong pred′ e)
  where
  pred′ : ℕ → ℕ
  pred′ zero = zero
  pred′ (suc n) = n

typed-indep-illegal : ¬ LgB (hl (λ k → ι {ℕ} {G₁} k (out k)))
typed-indep-illegal = indep-illegal {ℕ} {G₁} wT (λ k → k) out 0 (suc≢ 0) (has-out 0)
```

## 结论 (按档)

- **[定理]** `HasΩ`, `In`, `in-ι`, `in⊲`, `in-has`, `no-cross`, `indep-illegal`, `StationWise`, `sw-illegal`, `sw-id`, `has-out`, `typed-indep-illegal`.
- **[判断]** "sup 层的 '留' 要把旧种类在各站之间认同, 否则对角不合法" 是本篇对构造一路的提示; 认同的代价 (拷贝, `CohWNeg.no-cross`) 不在本篇.
