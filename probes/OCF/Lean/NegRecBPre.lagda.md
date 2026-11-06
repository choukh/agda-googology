# CRw 上底做成递归, 否定一路 (一): 接口之前 (世界塔, 公共上界, 对角)

> 不含记号. 入口 [NegRecB](NegRecB.lagda.md). 本篇**不依赖**构造一路 RecB 的接口 (接口定稿之前写的部分). 只导入 [CRwBase](CRwBase.lagda.md) (构造一路的前身 CRw 的底座, 不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **问题** (作者本轮选定 "CRw 上底做成递归"). 构造一路要让 CRw 的底对层号递归, 世界做成塔, 一个定义覆盖 $X_2$ 及以上各站. 本篇在接口之前问三件事, 都对 `CRwBase` 的一切种类结构 `S` 陈述:
>
> 1. **世界塔里跨层的移动 (§1, §2).** `step S` 的世界是 $(w, B)$: 下一层的世界 $w$ 加上新种类的界 $B$. 正面 (**`up-⊲`, `Lg-up`, `ι-⊲`, `Lg-ι`**): 把低层的值嵌进高层 (`up`, `ι`) 在**一切**世界里保第一位置与合法; 世界往大移动保第一位置是 `CRwBase.⊲ᴮ↑`. 否定 (**`wdep-top`**): 对一切 `S` 与一切合法的 $w$, $1\lhd\Omega$ 在 $(w,1)$ 里成立, 在 $(w,0)$ 里不成立 (推广 `NegCRwWorld.wdep₁` 到一切层). **`wdep-low`**: 第 2 层上, 顶部的界相同 (都是 $\Omega$), 只把**下一层**世界的界从 $1$ 换成 $0$, $1\lhd\Omega_2$ 就从成立变成不成立. 所以塔式世界的移动若只改顶部、把低层世界重置, 证据会丢; 跨层的移动必须把低层世界一起带着 (不缩小).
> 2. **坐标层在第 1 层及以上时的公共上界 (§3).** **`bound-wdep`**: 第 1 层 (任一 `S` 上的 `step S`) 的两个合法值 $1$ 与 $\Omega$, 在合法世界 $(w,1)$ 里有合法的字面公共上界 ($\Omega$ 自己), 在合法世界 $(w,0)$ 里**没有**. 所以坐标层不是第 0 层时, "比较有公共上界" 不是坐标对的性质, 是坐标对加低层世界的性质. 对照: 第 0 层的第一位置与世界无关 (`NegCRwWorld.wfree-S⊥`); 不合法的坐标在任何合法世界里没有合法的界 (`NegX2Bd.no-bd`, `no-bd-o₁`), 第 1 层的合法化 `leg₁` 是构造 (`NegX2Bd.Lg-leg₁`).
> 3. **一个定义覆盖一切站时的对角 (§4, §5).** **`sup-diag`** (对一切下标集 $I$ 与 $F : I\to$ `KS`): 并 `sup I F` 里, 从分量 $i$ 嵌入且含 $\Omega$-结点的值, 不是从另一个分量 $j\neq i$ 嵌入的值的第一位置. 推论 **`sup-diag-illegal`**: 各站在各自的分量里写 (第 $n$ 项是 $\iota_{\sigma n}\,x_n$, $x_0$ 含 $\Omega$-结点, $\sigma 0\neq\sigma 1$), 对角不合法 (`HtTowerNeg.no-naive-diag` 在 `CRwBase` 上对一切 `sup` 的版本). 前提实例 **`naive-ex`**. 对照 (正面) **`Lg-Σᴬ`**: 同样的项按部分和累加 ($P_{n+1}=P_n\boxplus x_{n+1}$), 对角合法; 实例 **`acc-ex`**. **`no-retract`** (对一切 `S`, `CRwBase` 版): 没有种类的坐标装着全部高度的收缩; 所以 "一个种类结构装下一切站并在 $\Lambda$ 上封口" 不可能, 层号类型必须在种类结构之外 (同 `HtTowerNeg.no-retract`).
>
> **前提实例.** 1: 世界 $(w,1)$, $(w,0)$, $((w,1),\Omega)$, $((w,0),\Omega)$ 都合法 (`lgW-top1`, `lgW-top0`, `lgW-low1`, `lgW-low0`), 只要 $w$ 合法; $w$ 合法的实例: `S⊥` 的 `tt`. 2: 同上; $\Omega$ 合法 (`Lg-Ωˢ`). 3: `naive-ex` 给出满足 `sup-diag-illegal` 全部前提的实例 ($I=\mathbb N$, $F\,n=$ `step S⊥`, $x_n=\Omega$, $\sigma=$ 恒等, 世界 $\lambda n.(\mathrm{tt},0)$).
>
> **只否定什么.** `wdep-top`, `wdep-low` 只否定: 第 $k\geq 1$ 层的第一位置与世界无关; 塔式世界的低层分量可以在移动时重置. **不否定**带塔的世界设计, 也不否定 "移动时低层世界不缩小" 的写法 (`⊲ᴮ↑` 是它的正面). `bound-wdep` 只否定: 第 1 层坐标对的公共上界的存在与世界无关. **不否定**在合法世界里带证据比较 (`cmpB` 是构造). `sup-diag-illegal` 只否定**各站在各自分量里写, 再取对角**; **不否定**累加的对角 (`Lg-Σᴬ` 是正面), 也不否定闭项 (第 0 层) 上的对角. `no-retract` 只否定种类结构在自身上封口. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegRecBPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.CRwBase
```

## §1 嵌到高层: 在一切世界里保第一位置与合法

`up`: 第 $k$ 层的值嵌进 `step` (第 $k+1$ 层), 种类 $\kappa\mapsto$ `inj₁ κ`. 新世界 $(w,B)$ 里, 旧种类的界只看 $w$ (`Bd⁺ (inj₁ κ)` 的定义), 所以第一位置与合法都只读低层世界.

```agda
module _ {S : KS} where
  up-⊲ : ∀ {a b : HB S} {w′ : Wd (step S)} → a ⊲[ proj₁ w′ ] b → up a ⊲[ w′ ] up b
  up-⊲ hself = hself
  up-⊲ (hsuc p) = hsuc (up-⊲ p)
  up-⊲ (hlim n p) = hlim n (up-⊲ p)
  up-⊲ (hLim e p) = hLim e (up-⊲ p)

  Lg-up : ∀ (a : HB S) → LgB a → LgB (up a)
  Lg-up hz l = tt
  Lg-up (hs a) l = Lg-up a l
  Lg-up (hl f) (st , l) = (λ {w} n → up-⊲ {w′ = w} (st n)) , (λ n → Lg-up (f n) (l n))
  Lg-up (hΩ κ g) (mo , l) =
    (λ {w} lw e e′ p → up-⊲ {w′ = w} (mo (proj₁ lw) e e′ p)) ,
    (λ {w} {c} lw e → Lg-up (g c) (l (proj₁ lw) e))

module _ {I : Set} {F : I → KS} where
  ιF : (i : I) → HB (F i) → HB (sup I F)
  ιF = ι {I} {F}

  ι-⊲ : ∀ i {a b : HB (F i)} {w : Wd (sup I F)} → a ⊲[ w i ] b → ιF i a ⊲[ w ] ιF i b
  ι-⊲ i {a} {.a} hself = hself
  ι-⊲ i {a} {hs b} (hsuc p) = hsuc (ι-⊲ i {a} {b} p)
  ι-⊲ i {a} {hl f} (hlim n p) = hlim n (ι-⊲ i {a} {f n} p)
  ι-⊲ i {a} {hΩ κ g} (hLim {c = c} e p) = hLim e (ι-⊲ i {a} {g c} p)

  Lg-ι : ∀ i (a : HB (F i)) → LgB a → LgB (ιF i a)
  Lg-ι i hz l = tt
  Lg-ι i (hs a) l = Lg-ι i a l
  Lg-ι i (hl f) (st , l) = (λ {w} n → ι-⊲ i {f n} {f (suc n)} {w = w} (st n)) , (λ n → Lg-ι i (f n) (l n))
  Lg-ι i (hΩ κ g) (mo , l) =
    (λ {w} {c} {c′} lw e e′ p → ι-⊲ i {g c} {g c′} {w = w} (mo (lw i) e e′ p)) ,
    (λ {w} {c} lw e → Lg-ι i (g c) (l (lw i) e))
```

## §2 第一位置依赖世界: 顶部与低层

`Ωˢ`: `step S` 的新种类的恒等结点 (第 $k+1$ 层的 $\Omega$). 合法 (`Lg-Ωˢ`, 对一切 `S`).

```agda
Ωˢ : ∀ {S : KS} → HB (step S)
Ωˢ = hΩ (inj₂ tt) up

Lg-Ωˢ : ∀ {S : KS} → LgB (Ωˢ {S})
Lg-Ωˢ = (λ {w} lw e e′ p → up-⊲ {w′ = w} p) , (λ {w} {c} lw e → Lg-up c (lgB⊲ e (proj₁ lw) (proj₂ lw)))

module _ {S : KS} where
  hz-only : ∀ {w} {c : HB S} → c ⊲[ w ] hz → c ≡ hz
  hz-only hself = refl

  no-s⊲z : ∀ {w} {x : HB S} → ¬ (hs x ⊲[ w ] hz)
  no-s⊲z ()

  one : HB S
  one = hs hz
```

**顶部.** 对一切 `S` 与一切 $w$: $1\lhd\Omega$ 在 $(w,1)$ 里成立, 在 $(w,0)$ 里不成立.

```agda
module Top {S : KS} (w : Wd S) where
  in-top1 : one ⊲[ (w , one) ] Ωˢ {S}
  in-top1 = hLim {c = one} hself hself

  not-top0 : ¬ (one ⊲[ (w , hz) ] Ωˢ {S})
  not-top0 (hLim {c = c} e p) = no-s⊲z (subst (λ z → one ⊲[ (w , hz) ] up z) (hz-only e) p)

  -- 前提实例: 两个世界都合法 (只要 w 合法)
  lgW-top1 : LgW S w → LgW (step S) (w , one)
  lgW-top1 lw = lw , tt

  lgW-top0 : LgW S w → LgW (step S) (w , hz)
  lgW-top0 lw = lw , tt

wdep-top : ∀ {S : KS} (w : Wd S) → LgW S w →
  LgW (step S) (w , one) × LgW (step S) (w , hz) × (one ⊲[ (w , one) ] Ωˢ {S}) × ¬ (one ⊲[ (w , hz) ] Ωˢ {S})
wdep-top {S} w lw = lgW-top1 lw , lgW-top0 lw , in-top1 , not-top0
  where open Top {S} w
```

**界为 $0$ 的世界只看零分支 (对一切 `S`, 一切 $w$, 一切分支 $g$).** 在世界 $(w,0)$ 里, 新种类结点 $\Omega[g]$ 的第一位置要么是它自己, 要么是 $g\,0$ 的第一位置. 所以若跨层移动把某一层的界重置成 $0$, 那一层的一切新种类结点在比较里都退化成零分支.

```agda
zero-low : ∀ {S : KS} {w : Wd S} {a : HB (step S)} {g : HB S → HB (step S)} →
  a ⊲[ (w , hz) ] hΩ (inj₂ tt) g → (a ≡ hΩ (inj₂ tt) g) ⊎ (a ⊲[ (w , hz) ] g hz)
zero-low hself = inj₁ refl
zero-low {w = w} {a = a} {g = g} (hLim {c = c} e p) = inj₂ (subst (λ z → a ⊲[ (w , hz) ] g z) (hz-only e) p)
```

**低层.** 第 2 层 `step (step S)` 的世界是 $((w,b),B)$. 顶部的界都取 $\Omega$ (第 1 层的值), 只改低层的界 $b$: $1\lhd\Omega_2$ 在 $((w,1),\Omega)$ 里成立 (经坐标 $1$, 它在第 1 层世界 $(w,1)$ 里在 $\Omega$ 之下), 在 $((w,0),\Omega)$ 里不成立 (第 1 层世界 $(w,0)$ 里在 $\Omega$ 之下的坐标只有 $\Omega$ 与 $0$, 两者经 `up` 后都不在 $1$ 之上).

```agda
module Low {S : KS} (w : Wd S) where
  open Top {S} w

  S₂ : KS
  S₂ = step (step S)

  W1 W0 : Wd S₂
  W1 = (w , one) , Ωˢ {S}
  W0 = (w , hz) , Ωˢ {S}

  in-low1 : one ⊲[ W1 ] Ωˢ {step S}
  in-low1 = hLim {c = one} in-top1 hself

  below0 : ∀ {c : HB (step S)} → c ⊲[ (w , hz) ] Ωˢ {S} → (c ≡ Ωˢ) ⊎ (c ≡ hz)
  below0 hself = inj₁ refl
  below0 (hLim {c = d} e q) = inj₂ (hz-only (subst (λ z → _ ⊲[ (w , hz) ] up z) (hz-only e) q))

  no1-upΩ : ¬ (one ⊲[ W0 ] up (Ωˢ {S}))
  no1-upΩ (hLim {c = d} e q) = no-s⊲z (subst (λ z → one ⊲[ W0 ] up (up z)) (hz-only e) q)

  not-low0 : ¬ (one ⊲[ W0 ] Ωˢ {step S})
  not-low0 (hLim {c = c} e q) with below0 e
  ... | inj₁ eq = no1-upΩ (subst (λ z → one ⊲[ W0 ] up z) eq q)
  ... | inj₂ eq = no-s⊲z (subst (λ z → one ⊲[ W0 ] up z) eq q)

  lgW-low1 : LgW S w → LgW S₂ W1
  lgW-low1 lw = (lw , tt) , Lg-Ωˢ {S}

  lgW-low0 : LgW S w → LgW S₂ W0
  lgW-low0 lw = (lw , tt) , Lg-Ωˢ {S}

wdep-low : ∀ {S : KS} (w : Wd S) → LgW S w →
  LgW (Low.S₂ {S} w) (Low.W1 w) × LgW (Low.S₂ {S} w) (Low.W0 w) ×
  proj₂ (Low.W1 {S} w) ≡ proj₂ (Low.W0 {S} w) ×
  (one ⊲[ Low.W1 w ] Ωˢ {step S}) × ¬ (one ⊲[ Low.W0 w ] Ωˢ {step S})
wdep-low {S} w lw = lgW-low1 lw , lgW-low0 lw , refl , in-low1 , not-low0
  where open Low {S} w
```

世界往大移动保第一位置是 `CRwBase.⊲ᴮ↑` (`step` 的世界序是 "低层世界变大, 且旧界是新界在新低层世界里的第一位置"). `wdep-low` 说明这条序里低层的分量不能省: 只比较顶部的界 (两者都是 $\Omega$, 字面相同) 推不出证据的搬运.

## §3 第 1 层坐标: 公共上界的存在依赖低层世界

$1$ 与 $\Omega$ 都合法 (`Lg-Ωˢ`). 在 $(w,1)$ 里 $\Omega$ 是它们的合法字面公共上界; 在 $(w,0)$ 里没有任何合法的字面公共上界: 若有, `cmpB` 给出可比, 而 $1\not\lhd\Omega$ (`not-top0`), $\Omega\not\lhd 1$.

```agda
module BoundW {S : KS} (w : Wd S) (lw : LgW S w) where
  open Top {S} w

  noΩ⊲1 : ∀ {w′ : Wd (step S)} → ¬ (Ωˢ {S} ⊲[ w′ ] one)
  noΩ⊲1 (hsuc ())

  bound-w1 : Σ (HB (step S)) (λ L → LgB L × (one ⊲[ (w , one) ] L) × (Ωˢ {S} ⊲[ (w , one) ] L))
  bound-w1 = Ωˢ {S} , Lg-Ωˢ {S} , in-top1 , hself

  no-bound-w0 : ¬ Σ (HB (step S)) (λ L → LgB L × (one ⊲[ (w , hz) ] L) × (Ωˢ {S} ⊲[ (w , hz) ] L))
  no-bound-w0 (L , lL , p , q) with cmpB p q (lgW-top0 lw) lL
  ... | inj₁ Ω⊲1 = noΩ⊲1 Ω⊲1
  ... | inj₂ 1⊲Ω = not-top0 1⊲Ω

bound-wdep : ∀ {S : KS} (w : Wd S) → LgW S w →
  LgB (one {step S}) × LgB (Ωˢ {S}) ×
  Σ (HB (step S)) (λ L → LgB L × (one ⊲[ (w , one) ] L) × (Ωˢ {S} ⊲[ (w , one) ] L)) ×
  ¬ Σ (HB (step S)) (λ L → LgB L × (one ⊲[ (w , hz) ] L) × (Ωˢ {S} ⊲[ (w , hz) ] L))
bound-wdep {S} w lw = tt , Lg-Ωˢ {S} , bound-w1 , no-bound-w0
  where open BoundW {S} w lw
```

## §4 并里的对角: 各站各写不合法, 累加合法

`AllI i x`: $x$ 的一切 $\Omega$-结点的种类都在分量 $i$. 第一位置保持它 (`allI⊲`); 从分量 $i$ 嵌入的值满足它 (`allI-ι`). `HasΩ x`: $x$ 含 $\Omega$-结点.

```agda
module _ {S : KS} where
  data HasΩ : HB S → Set where
    here : ∀ {κ g} → HasΩ (hΩ κ g)
    inS  : ∀ {a} → HasΩ a → HasΩ (hs a)
    inL  : ∀ {f} n → HasΩ (f n) → HasΩ (hl f)
    inΩ  : ∀ {κ g} c → HasΩ (g c) → HasΩ (hΩ κ g)

module _ {I : Set} {F : I → KS} where
  AllI : I → HB (sup I F) → Set
  AllI i hz = ⊤
  AllI i (hs x) = AllI i x
  AllI i (hl f) = ∀ n → AllI i (f n)
  AllI i (hΩ κ g) = (proj₁ κ ≡ i) × (∀ c → AllI i (g c))

  allI-ι : ∀ i x → AllI i (ι {I} {F} i x)
  allI-ι i hz = tt
  allI-ι i (hs x) = allI-ι i x
  allI-ι i (hl f) = λ n → allI-ι i (f n)
  allI-ι i (hΩ κ g) = refl , (λ c → allI-ι i (g c))

  allI⊲ : ∀ {j a b w} → a ⊲[ w ] b → AllI j b → AllI j a
  allI⊲ hself h = h
  allI⊲ (hsuc p) h = allI⊲ p h
  allI⊲ (hlim n p) h = allI⊲ p (h n)
  allI⊲ (hLim e p) h = allI⊲ p (proj₂ h _)

  hasΩ-ι : ∀ i {x : HB (F i)} → HasΩ x → HasΩ (ι {I} {F} i x)
  hasΩ-ι i here = here
  hasΩ-ι i (inS h) = inS (hasΩ-ι i h)
  hasΩ-ι i (inL n h) = inL n (hasΩ-ι i h)
  hasΩ-ι i (inΩ c h) = inΩ c (hasΩ-ι i h)

  two-comp : ∀ {i j x} → HasΩ x → AllI i x → AllI j x → i ≡ j
  two-comp here (ei , _) (ej , _) = trans (sym ei) ej
  two-comp (inS h) ai aj = two-comp h ai aj
  two-comp (inL n h) ai aj = two-comp h (ai n) (aj n)
  two-comp (inΩ c h) ai aj = two-comp h (proj₂ ai c) (proj₂ aj c)

  sup-diag : ∀ {i j} {x : HB (F i)} {y : HB (F j)} {w} → HasΩ x → ¬ (i ≡ j) → ¬ (ι {I} {F} i x ⊲[ w ] ι {I} {F} j y)
  sup-diag {i} {j} {x} {y} hx ne p =
    ne (two-comp (hasΩ-ι i hx) (allI-ι i x) (allI⊲ p (allI-ι j y)))

  sup-diag-illegal : ∀ (σ : ℕ → I) (x : ∀ n → HB (F (σ n))) → Wd (sup I F) →
    HasΩ (x 0) → ¬ (σ 0 ≡ σ 1) → ¬ LgB (hl (λ n → ι {I} {F} (σ n) (x n)))
  sup-diag-illegal σ x w h ne (st , _) = sup-diag h ne (st {w} 0)
```

**累加的对角 (正面, 对一切 `S`).** 部分和 $P_0=x_0$, $P_{n+1}=P_n\boxplus x_{n+1}$; 项都合法则对角合法.

```agda
module _ {S : KS} where
  Σᴬ : (ℕ → HB S) → ℕ → HB S
  Σᴬ x zero = x 0
  Σᴬ x (suc n) = Σᴬ x n ⊞ x (suc n)

  Lg-Σᴬ : ∀ x → (∀ n → LgB (x n)) → LgB (hl (Σᴬ x))
  Lg-Σᴬ x lx = (λ n → ⊞-fst (Σᴬ x n) (x (suc n))) , go
    where
    go : ∀ n → LgB (Σᴬ x n)
    go zero = lx 0
    go (suc n) = Lg-⊞ (Σᴬ x n) (x (suc n)) (go n) (lx (suc n))
```

**实例.** $I=\mathbb N$, 各分量都是 `step S⊥`, 第 $n$ 项是分量 $n$ 的 $\Omega$. 朴素的对角不合法; 累加的对角合法.

```agda
FN : ℕ → KS
FN _ = step S⊥

xN : (n : ℕ) → HB (FN n)
xN n = Ωˢ {S⊥}

wN : Wd (sup ℕ FN)
wN n = tt , hz

z≢1 : ¬ (0 ≡ 1)
z≢1 ()

naive-ex : ¬ LgB (hl (λ n → ι {ℕ} {FN} n (xN n)))
naive-ex = sup-diag-illegal {ℕ} {FN} (λ n → n) xN wN here z≢1

acc-ex : LgB (hl (Σᴬ (λ n → ι {ℕ} {FN} n (xN n))))
acc-ex = Lg-Σᴬ (λ n → ι {ℕ} {FN} n (xN n)) (λ n → Lg-ι {ℕ} {FN} n (xN n) (Lg-Ωˢ {S⊥}))
```

## §4′ 任一坐标层上新种类结点的合法化 (正面, 对一切 `U`)

挑战 "第 $k\geq1$ 层的坐标没有界是墙" 的读法. 坐标层是任一种类结构 $U$ (第 $k$ 层) 时, `step U` 的新种类 ($\Omega_{k+1}$) 的结点, 分支取 θ 式累加 `accU h` (坐标的后继处累加, ℕ-极限逐点, 坐标的 $\Omega$-结点映成输出里同种类 `inj₁ κ` 的结点), 对**一切**分支值合法的 $h$ 合法 (`Lg-ΩA`). 所以 "新种类结点的分支单调" 对一切坐标层是一条定义; 不需要按层写子句. `NegX2Bd.acc` 是 $U=$ `S⊥` 的特例 (那里没有 $\Omega$ 子句). 只覆盖新种类; 旧种类结点 (坐标是更低层的值) 的累加要把更低层的种类嵌进来, 这里没有写 (判断: 沿 `inj₁` 链可写, 未证).

```agda
module _ {U : KS} where
  accU : (HB U → HB (step U)) → HB U → HB (step U)
  accU h hz = h hz
  accU h (hs y) = accU h y ⊞ h (hs y)
  accU h (hl f) = hl (λ n → accU h (f n))
  accU h (hΩ κ g) = hΩ (inj₁ κ) (λ d → accU h (g d))

  accU-⊲ : ∀ h {y y′ : HB U} {w : Wd (step U)} → y ⊲[ proj₁ w ] y′ → accU h y ⊲[ w ] accU h y′
  accU-⊲ h hself = hself
  accU-⊲ h {y} {hs b} {w} (hsuc p) = ⊲ᴮ-tr (accU-⊲ h {w = w} p) (⊞-fst (accU h b) (h (hs b)))
  accU-⊲ h {y} {hl f} {w} (hlim n p) = hlim n (accU-⊲ h {w = w} p)
  accU-⊲ h {y} {hΩ κ g} {w} (hLim e p) = hLim e (accU-⊲ h {w = w} p)

  Lg-accU : ∀ h → (∀ d → LgB (h d)) → ∀ y → LgB y → LgB (accU h y)
  Lg-accU h lh hz l = lh hz
  Lg-accU h lh (hs y) l = Lg-⊞ (accU h y) (h (hs y)) (Lg-accU h lh y l) (lh (hs y))
  Lg-accU h lh (hl f) (st , l) = (λ {w} n → accU-⊲ h {w = w} (st n)) , (λ n → Lg-accU h lh (f n) (l n))
  Lg-accU h lh (hΩ κ g) (mo , l) =
    (λ {w} lw e e′ p → accU-⊲ h {w = w} (mo (proj₁ lw) e e′ p)) ,
    (λ {w} {c} lw e → Lg-accU h lh (g c) (l (proj₁ lw) e))

  Lg-ΩA : ∀ h → (∀ d → LgB (h d)) → LgB {step U} (hΩ (inj₂ tt) (accU h))
  Lg-ΩA h lh =
    (λ {w} lw e e′ p → accU-⊲ h {w = w} p) ,
    (λ {w} {c} lw e → Lg-accU h lh c (lgB⊲ e (proj₁ lw) (proj₂ lw)))
```

## §5 种类结构不在自身上封口 (`CRwBase` 版)

同 `HtTowerNeg.no-self`, `no-retract`, 换成 `CRwBase` 的类型. 只用高度的结构良基.

```agda
module _ {S : KS} where
  data _≺ᴮ_ : HB S → HB S → Set where
    ≺s : ∀ {x} → x ≺ᴮ hs x
    ≺l : ∀ {f} n → f n ≺ᴮ hl f
    ≺Ω : ∀ {κ g} c → g c ≺ᴮ hΩ κ g

  data Acc≺ (x : HB S) : Set where
    acc : (∀ {y} → y ≺ᴮ x → Acc≺ y) → Acc≺ x

  acc≺ : ∀ x → Acc≺ x
  acc≺ hz = acc (λ ())
  acc≺ (hs x) = acc (λ { ≺s → acc≺ x })
  acc≺ (hl f) = acc (λ { (≺l n) → acc≺ (f n) })
  acc≺ (hΩ κ g) = acc (λ { (≺Ω c) → acc≺ (g c) })

  irr≺ : ∀ {x} → Acc≺ x → ¬ (x ≺ᴮ x)
  irr≺ (acc f) p = irr≺ (f p) p

  no-self : ∀ κ (d : E S κ → HB S) c → ¬ (d c ≡ hΩ κ d)
  no-self κ d c eq = irr≺ (acc≺ (hΩ κ d)) (subst (λ z → z ≺ᴮ hΩ κ d) eq (≺Ω c))

  no-retract : ∀ κ (e : HB S → E S κ) (d : E S κ → HB S) → ¬ (∀ x → d (e x) ≡ x)
  no-retract κ e d sec = no-self κ d (e (hΩ κ d)) (sec (hΩ κ d))
```

## 结论 (按档)

- **[定理, 正面]** `up-⊲`, `Lg-up`, `ι-⊲`, `Lg-ι` (对一切 `S`, `I`, `F`, 一切世界); `Lg-Ωˢ`; `Top.in-top1`, `Low.in-low1`; `BoundW.bound-w1`; `Lg-Σᴬ`, 实例 `acc-ex`; `accU`, `accU-⊲`, `Lg-accU`, **`Lg-ΩA`** (对一切 `U`).
- **[定理, 否定]** **`wdep-top`**, `zero-low`, **`wdep-low`**, **`bound-wdep`** (对一切 `S` 与一切合法 $w$); **`sup-diag`**, **`sup-diag-illegal`** (对一切 `I`, `F`), 实例 `naive-ex`; `no-self`, **`no-retract`** (对一切 `S`).
- **[判断]** (a) 塔式世界的移动要 "低层世界不缩小" (由 `wdep-low`, 与 `⊲ᴮ↑` 的世界序一致); 构造一路若用 `step` 的世界序, 这一条自动成立. (b) 闭项 (第 0 层) 的对角总能用累加写合法 (`Lg-Σᴬ` 对 `S⊥` 的特例); 撞 `sup-diag-illegal` 的只是 "在一个装下各站的种类结构里, 各站在自己的分量里各写一项" 的写法. 构造一路是否这样写, 看接口.
