# 相干的世界 (一): 链的极限

> 不含记号. 入口 [CohW](CohW.lagda.md). [HtTowerNStage](HtTowerNStage.lagda.md) 的 `no-wmatch` 说: 逐分量的并 `sup ℕ F` 里, 同一个种类的两份拷贝 (第 $j$ 级的原件, 第 $k$ 级里它的像) 各有各的界, 一个世界投影保不住两个. 原因是 `sup` 的世界是**独立分量的积** $\prod_k \mathrm{Wd}(F\,k)$: 第 $k+1$ 个分量里装着的第 $k$ 级的世界与第 $k$ 个分量毫无关系.
>
> 这一篇换一种世界: **由扩张生成的世界.** 一条链 `Chain` 给出每一级的种类结构 `F k`, 每一级的扩张数据 `X k`, 与粘合 `gl k : Wd (F k) → X k → Wd (F (k+1))` (第 $k+1$ 级的世界由第 $k$ 级的世界加一份扩张数据得出). 极限 `colim C` 的世界是**底世界加每一级的扩张数据**:
>
> $$W^\star = \mathrm{Wd}(F\,0)\times\prod_k X\,k,\qquad \mathrm{pj}\,0\,w = w_0,\quad \mathrm{pj}\,(k+1)\,w = \mathrm{gl}\,k\,(\mathrm{pj}\,k\,w)\,(x_k).$$
>
> 第 $k$ 级的世界 `pj k w` 是**算出来的**, 不是存下来的; 第 $k+1$ 级的世界字面地含着第 $k$ 级的世界, 相干是定义相等, 不用函数外延. 种类、界、比较都经 `pj` 交给各级, 所以 `colim C` 是一个种类结构 (`KS`), `HtTowerTy` 的高度、第一位置、合法、**`cmpB`** 原样可用, 一行不新写.
>
> 一条结构定理 (对一切链): 每一级进极限有种类的对应与世界的对应 (`kmC`, `wmC`); 链若带包含 (`Incl`: 第 $k$ 级的种类进第 $k+1$ 级, 界经 `gl` 双向保持), **一切 $j\le k$, 第 $j$ 级的种类在第 $k$ 级的像与它自己在同一个世界投影 `pj j` 下界相同** (`rcoh→`, `rcoh←`). 这正是 `no-wmatch` 在 `sup` 上否定的形状.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWTy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFNeed using (KMatch; km; to; fr; fr-to)
open import OCF.Align.HtTowerNStage using (kmComp; WMatch; wm; bd→; bd←; lgw)
```

## §1 链与它的极限

```agda
record Chain : Set₁ where
  field
    F  : ℕ → KS
    X  : ℕ → Set
    gl : ∀ k → Wd (F k) → X k → Wd (F (suc k))
open Chain public

module Colim (C : Chain) where
  W⋆ : Set
  W⋆ = Wd (F C 0) × ((k : ℕ) → X C k)

  -- 第 k 级的世界: 由底世界一级一级粘出来
  pj : (k : ℕ) → W⋆ → Wd (F C k)
  pj zero w = proj₁ w
  pj (suc k) w = gl C k (pj k w) (proj₂ w k)

  K⋆ : Set
  K⋆ = Σ ℕ (λ k → K (F C k))

  E⋆ : K⋆ → Set
  E⋆ κ = E (F C (proj₁ κ)) (proj₂ κ)

open Colim public

colim : Chain → KS
colim C = record
  { K = K⋆ C ; E = E⋆ C ; Wd = W⋆ C
  ; LgW = λ w → ∀ k → LgW (F C k) (pj C k w)
  ; _≤w_ = λ w w′ → ∀ k → _≤w_ (F C k) (pj C k w) (pj C k w′)
  ; ≤w-rf = λ k → ≤w-rf (F C k)
  ; ≤w-tr = λ p q k → ≤w-tr (F C k) (p k) (q k)
  ; Bd = λ κ c w → Bd (F C (proj₁ κ)) (proj₂ κ) c (pj C (proj₁ κ) w)
  ; Pr = λ κ w c c′ → Pr (F C (proj₁ κ)) (proj₂ κ) (pj C (proj₁ κ) w) c c′
  ; Bd↑ = λ {κ} q e → Bd↑ (F C (proj₁ κ)) (q (proj₁ κ)) e
  ; cmpK = λ {κ} e e′ lw → cmpK (F C (proj₁ κ)) e e′ (lw (proj₁ κ))
  ; LgE = λ κ → LgE (F C (proj₁ κ)) (proj₂ κ)
  ; lgBd = λ {κ} e lw → lgBd (F C (proj₁ κ)) e (lw (proj₁ κ))
  ; bot = λ κ → bot (F C (proj₁ κ)) (proj₂ κ)
  ; botBd = λ κ w → botBd (F C (proj₁ κ)) (proj₂ κ) (pj C (proj₁ κ) w) }
```

**相干是定义相等.** 第 $k+1$ 级的世界就是第 $k$ 级的世界粘上第 $k$ 份扩张.

```agda
coh-pj : ∀ C k (w : W⋆ C) → pj C (suc k) w ≡ gl C k (pj C k w) (proj₂ w k)
coh-pj C k w = refl
```

## §2 每一级进极限: 种类与世界的对应

坐标映射是恒等, 世界的对应就是投影 `pj k`, 界双向是定义相等.

```agda
module _ (C : Chain) where
  kmC : ∀ k → KMatch (F C k) (colim C)
  kmC k = record { km = λ κ → k , κ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }

  wmC : ∀ k → WMatch (F C k) (colim C) (kmC k)
  wmC k = record { wm = pj C k ; bd→ = λ e → e ; bd← = λ e → e ; lgw = λ l → l k }
```

**嵌入.** 第 $k$ 级的高度原样搬进极限, 种类贴上级号. 保第一位置 (第 $k$ 级在投影世界里的第一位置), 保合法.

```agda
  ιc : ∀ k → HB (F C k) → HB (colim C)
  ιc k hz = hz
  ιc k (hs x) = hs (ιc k x)
  ιc k (hl f) = hl (λ n → ιc k (f n))
  ιc k (hΩ κ g) = hΩ (k , κ) (λ c → ιc k (g c))

  ιc-⊲ : ∀ {k a b} {w : W⋆ C} → a ⊲[ pj C k w ] b → ιc k a ⊲[ w ] ιc k b
  ιc-⊲ hself = hself
  ιc-⊲ (hsuc p) = hsuc (ιc-⊲ p)
  ιc-⊲ (hlim n p) = hlim n (ιc-⊲ p)
  ιc-⊲ (hLim e p) = hLim e (ιc-⊲ p)

  Lg-ιc : ∀ k a → LgB a → LgB (ιc k a)
  Lg-ιc k hz l = tt
  Lg-ιc k (hs a) l = Lg-ιc k a l
  Lg-ιc k (hl f) (st , l) = (λ n → ιc-⊲ (st n)) , (λ n → Lg-ιc k (f n) (l n))
  Lg-ιc k (hΩ κ g) (mo , l) = (λ lw e e′ p → ιc-⊲ (mo (lw k) e e′ p)) , (λ c lc → Lg-ιc k (g c) (l c lc))
```

## §3 带包含的链: 跨级的相干

`Incl C`: 第 $k$ 级的种类进第 $k+1$ 级 (`M k`), 界经粘合双向保持: 第 $k+1$ 级的世界 `gl k w x` 里, 像的界就是 $w$ 里原件的界. 这是 `WMatch` 限制在粘出来的世界上的形状.

```agda
record Incl (C : Chain) : Set₁ where
  field
    M    : ∀ k → KMatch (F C k) (F C (suc k))
    bdi→ : ∀ k {κ c w x} → Bd (F C (suc k)) (km (M k) κ) (to (M k) κ c) (gl C k w x) → Bd (F C k) κ c w
    bdi← : ∀ k {κ c w x} → Bd (F C k) κ c w → Bd (F C (suc k)) (km (M k) κ) (to (M k) κ c) (gl C k w x)
open Incl public

data Le (j : ℕ) : ℕ → Set where
  le-rf : Le j j
  le-st : ∀ {k} → Le j k → Le j (suc k)

kmId : ∀ {S} → KMatch S S
kmId = record { km = λ κ → κ ; to = λ κ c → c ; fr = λ κ c → c ; fr-to = λ κ c → refl }
```

`Mle q`: 第 $j$ 级进第 $k$ 级 ($j\le k$), 由 `M` 复合. **跨级的相干** (一条对 $j\le k$ 的证明递归的定理, 对一切带包含的链): 极限里第 $j$ 级的种类 $\kappa$ 与它在第 $k$ 级的像 $(k, \mathrm{km}\,\kappa)$, 在**同一个世界** $w$ 里界相同 (双向).

```agda
module _ {C : Chain} (I : Incl C) where
  Mle : ∀ {j k} → Le j k → KMatch (F C j) (F C k)
  Mle le-rf = kmId
  Mle (le-st {k} q) = kmComp (Mle q) (M I k)

  rcoh→ : ∀ {j k} (q : Le j k) {κ c} {w : W⋆ C} →
          Bd (colim C) (k , km (Mle q) κ) (to (Mle q) κ c) w → Bd (colim C) (j , κ) c w
  rcoh→ le-rf e = e
  rcoh→ (le-st {k} q) e = rcoh→ q (bdi→ I k e)

  rcoh← : ∀ {j k} (q : Le j k) {κ c} {w : W⋆ C} →
          Bd (colim C) (j , κ) c w → Bd (colim C) (k , km (Mle q) κ) (to (Mle q) κ c) w
  rcoh← le-rf e = e
  rcoh← (le-st {k} q) e = bdi← I k (rcoh← q e)
```

**同一个世界投影服务一切拷贝.** 第 $j$ 级进极限的世界对应, 种类取第 $k$ 级的像 ($k\ge j$ 任意), 世界仍是 `pj j`.

```agda
  wmLe : ∀ {j k} (q : Le j k) → WMatch (F C j) (colim C) (kmComp (Mle q) (kmC C k))
  wmLe {j} q = record
    { wm = pj C j ; bd→ = λ e → rcoh→ q e ; bd← = λ e → rcoh← q e ; lgw = λ l → l j }
```
