# 高度的高度 (一): 种类结构, 高度, 一步构造

> 不含记号. 入口 [HtTower](HtTower.lagda.md). 这一篇只有类型与对一切种类结构成立的定理; 塔在 [HtTowerU](HtTowerU.lagda.md).
>
> [HtFeedTree](HtFeedTree.lagda.md) 的高度 `H` 只有一种 $\Omega$-分支, 坐标是 `A`, 世界是 `A`. 把 "分支的坐标是什么, 坐标在什么世界里可比" 抽成一个记录 **种类结构** `KS`:
>
> - `K`: 分支的种类; `E κ`: 种类 $\kappa$ 的坐标.
> - `Wd`: 世界; `Bd κ c w`: 坐标 $c$ 字面地在世界 $w$ 的 $\kappa$-界之下; `Pr κ w c c′`: 世界 $w$ 里 $c$ 是 $c'$ 的第一位置.
> - `cmpK`: 界之下的两个坐标可比 (这就是壁垒要的字面公共上界).
>
> `HB S`: 以 `S` 为分支种类的布劳威尔树 (高度). 第一位置 `_⊲[_]_`, 合法 `LgB`, 比较 `cmpB` 与 `HtFeedTree` 的 `⊲[_]`, `LgH`, `cmpH` 同形, **对一切 `S` 一条定义, 一条定理**. 三个构造:
>
> - `step S`: 旧种类加一种新种类, **新种类的坐标就是 `S` 上的合法高度**, 新世界是旧世界加一个高度作界. `cmpK` 的新情形就是 `cmpB` 本身. 所以 "高度的高度" 每升一级不加新定理.
> - `sup I F`: 一族种类结构的并, 世界是逐分量的族.
> - `Lev x`: 对高度 $x$ 结构递归得到的种类结构 ($0\mapsto$ 底, 后继 $\mapsto$ `step`, 极限 $\mapsto$ `sup`). 层号本身成了种类结构的下标: **种类以高度为下标.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerTy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲; cmpF)
import OCF.Align.CumReadCF as C
```

## §1 种类结构

`Pr` 只在 `Bd` 之下用 (单调与比较). `bot` 是每个种类的最小坐标, 在一切世界的界之下, 只用来让 $0$ 是一切高度的第一位置.

```agda
record KS : Set₁ where
  field
    K     : Set
    E     : K → Set
    Wd    : Set
    LgW   : Wd → Set
    _≤w_  : Wd → Wd → Set
    ≤w-rf : ∀ {w} → w ≤w w
    ≤w-tr : ∀ {u v w} → u ≤w v → v ≤w w → u ≤w w
    Bd    : (κ : K) → E κ → Wd → Set
    Pr    : (κ : K) → Wd → E κ → E κ → Set
    Bd↑   : ∀ {κ c w w′} → w ≤w w′ → Bd κ c w → Bd κ c w′
    cmpK  : ∀ {κ c c′ w} → Bd κ c w → Bd κ c′ w → LgW w → Pr κ w c′ c ⊎ Pr κ w c c′
    LgE   : (κ : K) → E κ → Set
    lgBd  : ∀ {κ c w} → Bd κ c w → LgW w → LgE κ c
    bot   : (κ : K) → E κ
    botBd : ∀ κ w → Bd κ (bot κ) w
open KS public
```

**底 `S₀`**: 一个种类, 坐标与世界都是 `A`, 界与第一位置都是 `A` 的 `⊲`, 比较是 `cmpF`. `HB S₀` 就是 `HtFeedTree.H` 的形状.

```agda
S₀ : KS
S₀ = record
  { K = ⊤ ; E = λ _ → A ; Wd = A ; LgW = Lg ; _≤w_ = _⊲_ ; ≤w-rf = C.self ; ≤w-tr = ⊲-tr
  ; Bd = λ _ c w → c ⊲ w ; Pr = λ _ _ c c′ → c ⊲ c′
  ; Bd↑ = λ q e → ⊲-tr e q ; cmpK = λ e e′ lw → cmpF e e′ lw
  ; LgE = λ _ → Lg ; lgBd = λ e lw → lg⊲ e lw ; bot = λ _ → azero ; botBd = λ _ w → z⊲ w }
```

## §2 高度

```agda
data HB (S : KS) : Set where
  hz : HB S
  hs : HB S → HB S
  hl : (ℕ → HB S) → HB S
  hΩ : (κ : K S) → (E S κ → HB S) → HB S

module _ {S : KS} where
  infix 4 _⊲[_]_
  data _⊲[_]_ : HB S → Wd S → HB S → Set where
    hself : ∀ {a w} → a ⊲[ w ] a
    hsuc  : ∀ {a b w} → a ⊲[ w ] b → a ⊲[ w ] hs b
    hlim  : ∀ {a f w} n → a ⊲[ w ] f n → a ⊲[ w ] hl f
    hLim  : ∀ {a κ g w c} → Bd S κ c w → a ⊲[ w ] g c → a ⊲[ w ] hΩ κ g

  ⊲ᴮ-tr : ∀ {a b c w} → a ⊲[ w ] b → b ⊲[ w ] c → a ⊲[ w ] c
  ⊲ᴮ-tr p hself = p
  ⊲ᴮ-tr p (hsuc q) = hsuc (⊲ᴮ-tr p q)
  ⊲ᴮ-tr p (hlim n q) = hlim n (⊲ᴮ-tr p q)
  ⊲ᴮ-tr p (hLim e q) = hLim e (⊲ᴮ-tr p q)

  ⊲ᴮ↑ : ∀ {a b w w′} → _≤w_ S w w′ → a ⊲[ w ] b → a ⊲[ w′ ] b
  ⊲ᴮ↑ q hself = hself
  ⊲ᴮ↑ q (hsuc p) = hsuc (⊲ᴮ↑ q p)
  ⊲ᴮ↑ q (hlim n p) = hlim n (⊲ᴮ↑ q p)
  ⊲ᴮ↑ q (hLim e p) = hLim (Bd↑ S q e) (⊲ᴮ↑ q p)

  z⊲ᴮ : ∀ {w} L → hz ⊲[ w ] L
  z⊲ᴮ hz = hself
  z⊲ᴮ (hs b) = hsuc (z⊲ᴮ b)
  z⊲ᴮ (hl f) = hlim 0 (z⊲ᴮ (f 0))
  z⊲ᴮ {w} (hΩ κ g) = hLim (botBd S κ w) (z⊲ᴮ (g (bot S κ)))
```

**合法.** $\mathbb N$-极限: 相邻项在一切世界里是第一位置. $\Omega$-极限 (任一种类): 在一切合法世界里, 界之下的两个坐标 $c\lhd c'$ 给出 $g\,c\lhd g\,c'$. 都遗传. 与 `LgH` 同形; `LgH` 把单调写在世界 $c'$ 上, 这里写在一切含 $c,c'$ 的世界上 (两者可互推, 因为世界可以变大).

```agda
  LgB : HB S → Set
  LgB hz = ⊤
  LgB (hs h) = LgB h
  LgB (hl f) = (∀ {w} n → f n ⊲[ w ] f (suc n)) × (∀ n → LgB (f n))
  LgB (hΩ κ g) =
    (∀ {w c c′} → LgW S w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) ×
    (∀ c → LgE S κ c → LgB (g c))

  lgB⊲ : ∀ {a b w} → a ⊲[ w ] b → LgW S w → LgB b → LgB a
  lgB⊲ hself lw l = l
  lgB⊲ (hsuc p) lw l = lgB⊲ p lw l
  lgB⊲ (hlim n p) lw l = lgB⊲ p lw (proj₂ l n)
  lgB⊲ (hLim e p) lw l = lgB⊲ p lw (proj₂ l _ (lgBd S e lw))

  stepsᴮ : ∀ {f : ℕ → HB S} → (∀ {w} n → f n ⊲[ w ] f (suc n)) → ∀ {w n m} → n <ᴺ m → f n ⊲[ w ] f m
  stepsᴮ s zero = s _
  stepsᴮ s (suc q) = ⊲ᴮ-tr (stepsᴮ s q) (s _)
```

**比较: 一条定理对一切种类结构.** 与 `cmpH` 同形; $\Omega$-分支处用种类自己的 `cmpK`, 再用单调搬.

```agda
  cmpB : ∀ {a b L w} → a ⊲[ w ] L → b ⊲[ w ] L → LgW S w → LgB L → (b ⊲[ w ] a) ⊎ (a ⊲[ w ] b)
  cmpB hself q lw l = inj₁ q
  cmpB p hself lw l = inj₂ p
  cmpB (hsuc p) (hsuc q) lw l = cmpB p q lw l
  cmpB (hlim n p) (hlim m q) lw (st , l) with <ᴺ-dec n m
  ... | injᵃ n<m = cmpB (⊲ᴮ-tr p (stepsᴮ st n<m)) q lw (l m)
  ... | injᵇ m<n = cmpB p (⊲ᴮ-tr q (stepsᴮ st m<n)) lw (l n)
  ... | injᶜ refl = cmpB p q lw (l n)
  cmpB (hLim e p) (hLim e′ q) lw (mo , l) with cmpK S e e′ lw
  ... | inj₁ c′c = cmpB p (⊲ᴮ-tr q (mo lw e′ e c′c)) lw (l _ (lgBd S e lw))
  ... | inj₂ cc′ = cmpB (⊲ᴮ-tr p (mo lw e e′ cc′)) q lw (l _ (lgBd S e′ lw))
```

**加法** (右边逐构造子), 只用来把新高度接在旧高度后面 ([HtTowerU](HtTowerU.lagda.md) 的塔).

```agda
  infixl 6 _⊞_
  _⊞_ : HB S → HB S → HB S
  a ⊞ hz = a
  a ⊞ hs b = hs (a ⊞ b)
  a ⊞ hl f = hl (λ n → a ⊞ f n)
  a ⊞ hΩ κ g = hΩ κ (λ c → a ⊞ g c)

  ⊞-fst : ∀ {w} a b → a ⊲[ w ] a ⊞ b
  ⊞-fst a hz = hself
  ⊞-fst a (hs b) = hsuc (⊞-fst a b)
  ⊞-fst a (hl f) = hlim 0 (⊞-fst a (f 0))
  ⊞-fst {w} a (hΩ κ g) = hLim (botBd S κ w) (⊞-fst a (g (bot S κ)))

  ⊞-⊲ : ∀ {w} a {x y} → x ⊲[ w ] y → a ⊞ x ⊲[ w ] a ⊞ y
  ⊞-⊲ a hself = hself
  ⊞-⊲ a (hsuc p) = hsuc (⊞-⊲ a p)
  ⊞-⊲ a (hlim n p) = hlim n (⊞-⊲ a p)
  ⊞-⊲ a (hLim e p) = hLim e (⊞-⊲ a p)

  Lg-⊞ : ∀ a b → LgB a → LgB b → LgB (a ⊞ b)
  Lg-⊞ a hz la lb = la
  Lg-⊞ a (hs b) la lb = Lg-⊞ a b la lb
  Lg-⊞ a (hl f) la (st , l) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) la (l n))
  Lg-⊞ a (hΩ κ g) la (mo , l) = (λ lw e e′ p → ⊞-⊲ a (mo lw e e′ p)) , (λ c lc → Lg-⊞ a (g c) la (l c lc))
```

## §3 一步: 坐标是高度

`step S`: 种类 `K S ⊎ ⊤`. 旧种类原样; 新种类 `inj₂ tt` 的坐标是 `HB S`, 界是新世界的第二分量 $b$ (`a ⊲[ w ] b`), 第一位置是 `HB S` 的 `⊲`, 比较是 `cmpB`, 合法是 `LgB`, 最小坐标是 $0$. 新世界 $(w,b)$ 变大: $w$ 变大且 $b$ 是新 $b'$ 的第一位置 (在新的 $w'$ 里).

```agda
module Step (S : KS) where
  K⁺ : Set
  K⁺ = K S ⊎ ⊤

  E⁺ : K⁺ → Set
  E⁺ (inj₁ κ) = E S κ
  E⁺ (inj₂ _) = HB S

  W⁺ : Set
  W⁺ = Wd S × HB S

  LgW⁺ : W⁺ → Set
  LgW⁺ w = LgW S (proj₁ w) × LgB (proj₂ w)

  _≤⁺_ : W⁺ → W⁺ → Set
  w ≤⁺ w′ = _≤w_ S (proj₁ w) (proj₁ w′) × (proj₂ w ⊲[ proj₁ w′ ] proj₂ w′)

  ≤⁺-rf : ∀ {w} → w ≤⁺ w
  ≤⁺-rf = ≤w-rf S , hself

  ≤⁺-tr : ∀ {u v w} → u ≤⁺ v → v ≤⁺ w → u ≤⁺ w
  ≤⁺-tr (p , b) (q , c) = ≤w-tr S p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c

  Bd⁺ : (κ : K⁺) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = a ⊲[ proj₁ w ] proj₂ w

  Pr⁺ : (κ : K⁺) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w c c′ = Pr S κ (proj₁ w) c c′
  Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′

  Bd↑⁺ : ∀ {κ c w w′} → w ≤⁺ w′ → Bd⁺ κ c w → Bd⁺ κ c w′
  Bd↑⁺ {inj₁ κ} (q , _) e = Bd↑ S q e
  Bd↑⁺ {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b

  cmpK⁺ : ∀ {κ c c′ w} → Bd⁺ κ c w → Bd⁺ κ c′ w → LgW⁺ w → Pr⁺ κ w c′ c ⊎ Pr⁺ κ w c c′
  cmpK⁺ {inj₁ κ} e e′ (lw , lb) = cmpK S e e′ lw
  cmpK⁺ {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb

  LgE⁺ : (κ : K⁺) → E⁺ κ → Set
  LgE⁺ (inj₁ κ) = LgE S κ
  LgE⁺ (inj₂ _) = LgB

  lgBd⁺ : ∀ {κ c w} → Bd⁺ κ c w → LgW⁺ w → LgE⁺ κ c
  lgBd⁺ {inj₁ κ} e (lw , lb) = lgBd S e lw
  lgBd⁺ {inj₂ _} e (lw , lb) = lgB⊲ e lw lb

  bot⁺ : (κ : K⁺) → E⁺ κ
  bot⁺ (inj₁ κ) = bot S κ
  bot⁺ (inj₂ _) = hz

  botBd⁺ : ∀ κ w → Bd⁺ κ (bot⁺ κ) w
  botBd⁺ (inj₁ κ) w = botBd S κ (proj₁ w)
  botBd⁺ (inj₂ _) w = z⊲ᴮ (proj₂ w)

step : KS → KS
step S = record
  { K = K⁺ ; E = E⁺ ; Wd = W⁺ ; LgW = LgW⁺ ; _≤w_ = _≤⁺_ ; ≤w-rf = ≤⁺-rf ; ≤w-tr = ≤⁺-tr
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; LgE = LgE⁺ ; lgBd = lgBd⁺ ; bot = bot⁺ ; botBd = botBd⁺ }
  where open Step S
```

**嵌入 `up`**: 旧种类的分支原样搬到 `step S` 里. 保第一位置 (世界取任意新界), 保合法.

```agda
module _ {S : KS} where
  up : HB S → HB (step S)
  up hz = hz
  up (hs x) = hs (up x)
  up (hl f) = hl (λ n → up (f n))
  up (hΩ κ g) = hΩ (inj₁ κ) (λ c → up (g c))

  up-⊲ : ∀ {a b w β} → a ⊲[ w ] b → up a ⊲[ (w , β) ] up b
  up-⊲ hself = hself
  up-⊲ (hsuc p) = hsuc (up-⊲ p)
  up-⊲ (hlim n p) = hlim n (up-⊲ p)
  up-⊲ (hLim e p) = hLim e (up-⊲ p)

  Lg-up : ∀ a → LgB a → LgB (up a)
  Lg-up hz l = tt
  Lg-up (hs a) l = Lg-up a l
  Lg-up (hl f) (st , l) = (λ n → up-⊲ (st n)) , (λ n → Lg-up (f n) (l n))
  Lg-up (hΩ κ g) (mo , l) = (λ lw e e′ p → up-⊲ (mo (proj₁ lw) e e′ p)) , (λ c lc → Lg-up (g c) (l c lc))
```

## §4 并

`sup I F`: 种类是 $\Sigma_i K(F\,i)$, 世界是逐分量的族 $w:\prod_i \mathrm{Wd}(F\,i)$, 第 $i$ 个分量的种类只看世界的第 $i$ 个分量. $I$ 可以是 $\mathbb N$, 也可以是坐标类型 (下面的 `Lev`).

```agda
module Sup (I : Set) (F : I → KS) where
  Kˢ : Set
  Kˢ = Σ I (λ i → K (F i))

  Eˢ : Kˢ → Set
  Eˢ κ = E (F (proj₁ κ)) (proj₂ κ)

  Wˢ : Set
  Wˢ = (i : I) → Wd (F i)

sup : (I : Set) → (I → KS) → KS
sup I F = record
  { K = Kˢ ; E = Eˢ ; Wd = Wˢ
  ; LgW = λ w → ∀ i → LgW (F i) (w i)
  ; _≤w_ = λ w w′ → ∀ i → _≤w_ (F i) (w i) (w′ i)
  ; ≤w-rf = λ i → ≤w-rf (F i)
  ; ≤w-tr = λ p q i → ≤w-tr (F i) (p i) (q i)
  ; Bd = λ κ c w → Bd (F (proj₁ κ)) (proj₂ κ) c (w (proj₁ κ))
  ; Pr = λ κ w c c′ → Pr (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) c c′
  ; Bd↑ = λ {κ} q e → Bd↑ (F (proj₁ κ)) (q (proj₁ κ)) e
  ; cmpK = λ {κ} e e′ lw → cmpK (F (proj₁ κ)) e e′ (lw (proj₁ κ))
  ; LgE = λ κ → LgE (F (proj₁ κ)) (proj₂ κ)
  ; lgBd = λ {κ} e lw → lgBd (F (proj₁ κ)) e (lw (proj₁ κ))
  ; bot = λ κ → bot (F (proj₁ κ)) (proj₂ κ)
  ; botBd = λ κ w → botBd (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) }
  where open Sup I F

module _ {I : Set} {F : I → KS} where
  ι : (i : I) → HB (F i) → HB (sup I F)
  ι i hz = hz
  ι i (hs x) = hs (ι i x)
  ι i (hl f) = hl (λ n → ι i (f n))
  ι i (hΩ κ g) = hΩ (i , κ) (λ c → ι i (g c))

  ι-⊲ : ∀ {i a b} {w : Wd (sup I F)} → a ⊲[ w i ] b → ι i a ⊲[ w ] ι i b
  ι-⊲ hself = hself
  ι-⊲ (hsuc p) = hsuc (ι-⊲ p)
  ι-⊲ (hlim n p) = hlim n (ι-⊲ p)
  ι-⊲ (hLim e p) = hLim e (ι-⊲ p)

  Lg-ι : ∀ i a → LgB a → LgB (ι i a)
  Lg-ι i hz l = tt
  Lg-ι i (hs a) l = Lg-ι i a l
  Lg-ι i (hl f) (st , l) = (λ n → ι-⊲ (st n)) , (λ n → Lg-ι i (f n) (l n))
  Lg-ι i (hΩ κ g) (mo , l) = (λ lw e e′ p → ι-⊲ (mo (lw i) e e′ p)) , (λ c lc → Lg-ι i (g c) (l c lc))
```

## §5 种类结构以高度为下标

`Lev x`: 对高度 $x$ 结构递归. $0$ 给底 `S₀`, 后继给 `step`, $\mathbb N$-极限与 $\Omega$-极限 (任一种类) 给 `sup`. 读法 (判断): `HB (Lev x)` 是 "第 $x$ 级的高度", 它的种类是一切低于 $x$ 的级的高度. **层号 (高度) 成了分支种类的下标**, 这是 "高度的高度" 的字面形状. 定义只看 $x$ 的构造子, 不提记号, 对一切 `S` 一条定义.

```agda
Lev : ∀ {S} → HB S → KS
Lev hz = S₀
Lev (hs x) = step (Lev x)
Lev (hl f) = sup ℕ (λ n → Lev (f n))
Lev {S} (hΩ κ g) = sup (E S κ) (λ c → Lev (g c))
```
