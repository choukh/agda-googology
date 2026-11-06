# LeanT (一): 种类结构, 高度, `step`, `sup`

> 不含记号. 入口 [LeanT](LeanT.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib.
>
> **重写, 不是拷贝删减.** 参考 `HtTowerTy`, `GenFoldIf` §3, §6, `GenFoldInst` §2–§3, `FabLFReGen` §1, `LFReTy` 的 `S⊥`, `CumReadCF` 的 `A`. 与它们的差 (都是写法与数据表示, 不改闭项的构造):
>
> 1. **种类结构自带顶坐标、基世界、向下封闭.** 原来分在三个记录里 (`KS`, `TopG`, `LgDn`) 与 `GenK` 的 `w₀`, `lw₀` 里, 每个实例要对层号再递归一遍 (`topLv`, `ldLv`, `w₀Lv`, `lw₀Lv`). 这里是 `KS` 的字段, `step`, `sup` 各给一次, 以后的一切种类结构自动有. 值与原来逐项相同 (`top`, `w₀` 在 `step`, `sup` 上的式子与 `topStepG`, `topSupG`, `w₀Lv` 一样).
> 2. **没有 `LgE`, `lgBd`.** $\Omega$-分支的合法写成 "在一个合法世界的界之下的坐标处合法" (`LgB` 的第二分量取世界与界的证据), 原来是 "对一切合法坐标". 原来这两件只被 `lgBd` 连起来用; [判断] 对由 `S⊥`, `step`, `sup` 搭出的结构两者等价 (新种类的合法坐标 $c$ 在世界 $(w_0,c)$ 的界之下). 合法性证明里被比较用到的分量 (`mo`, 相邻项的第一位置) 不变.
> 3. **底层就是 `HB S⊥`.** `S⊥ = sup ⊥ (λ ())` (没有种类); `HB S⊥` 只有 $0$, 后继, $\mathbb N$-极限, 与原来的层 `A` 逐构造子相同. 闭项与 FGH 都在 `HB S⊥` 上, 不另造 `A`, `⊲`, `Lg`, 不要逐构造子的翻译 `frE⊥`.
> 4. **自然数的比较用 stdlib** (`<-cmp`, `_<′_`), 不用 `OCF.BTBO.Trich`; 走的步数与原来相同 (`stepsᴮ` 的两个构造子对应 `Trich._<_` 的两个构造子).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanTBase where

open import Data.Nat using (ℕ; zero; suc; _<′_; ≤′-step)
open import Data.Nat.Base using (≤′-refl)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl)
```

## §1 种类结构

`K`: 种类; `E κ`: 坐标; `Wd`: 世界; `Bd κ c w`: 坐标 $c$ 在世界 $w$ 的 $\kappa$-界之下; `Pr κ w c c′`: 世界 $w$ 里 $c$ 是 $c'$ 的第一位置; `cmpK`: 界之下的两个坐标可比 (字面公共上界就是这个界). `bot`: 在一切界之下的坐标; `top κ w`: 界本身; `w₀`: 基世界; `lgDn`: 合法向下封闭.

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
    lgDn  : ∀ {u v} → u ≤w v → LgW v → LgW u
    w₀    : Wd
    lw₀   : LgW w₀
    Bd    : (κ : K) → E κ → Wd → Set
    Pr    : (κ : K) → Wd → E κ → E κ → Set
    Bd↑   : ∀ {κ c w w′} → w ≤w w′ → Bd κ c w → Bd κ c w′
    cmpK  : ∀ {κ c c′ w} → Bd κ c w → Bd κ c′ w → LgW w → Pr κ w c′ c ⊎ Pr κ w c c′
    bot   : (κ : K) → E κ
    botBd : ∀ κ w → Bd κ (bot κ) w
    top   : (κ : K) → Wd → E κ
    topBd : ∀ κ w → Bd κ (top κ w) w
open KS public
```

## §2 高度: 以 `S` 为分支种类的布劳威尔树

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

**合法.** $\mathbb N$-极限: 相邻项在一切世界里是第一位置. $\Omega$-极限: 在合法世界里, 界之下 $c\lhd c'$ 给出 $g\,c\lhd g\,c'$; 界之下的坐标处遗传.

```agda
  LgB : HB S → Set
  LgB hz = ⊤
  LgB (hs h) = LgB h
  LgB (hl f) = (∀ {w} n → f n ⊲[ w ] f (suc n)) × (∀ n → LgB (f n))
  LgB (hΩ κ g) =
    (∀ {w c c′} → LgW S w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) ×
    (∀ {w c} → LgW S w → Bd S κ c w → LgB (g c))

  lgB⊲ : ∀ {a b w} → a ⊲[ w ] b → LgW S w → LgB b → LgB a
  lgB⊲ hself lw l = l
  lgB⊲ (hsuc p) lw l = lgB⊲ p lw l
  lgB⊲ (hlim n p) lw l = lgB⊲ p lw (proj₂ l n)
  lgB⊲ (hLim e p) lw l = lgB⊲ p lw (proj₂ l lw e)

  stepsᴮ : ∀ {f : ℕ → HB S} → (∀ {w} n → f n ⊲[ w ] f (suc n)) → ∀ {w n m} → n <′ m → f n ⊲[ w ] f m
  stepsᴮ s ≤′-refl = s _
  stepsᴮ s (≤′-step q) = ⊲ᴮ-tr (stepsᴮ s q) (s _)
```

**比较.** 同一棵合法高度的两个第一位置可比 (公共上界 $L$ 是字面的). 对一切种类结构一条; $\Omega$-分支处用种类自己的 `cmpK`.

```agda
  cmpB : ∀ {a b L w} → a ⊲[ w ] L → b ⊲[ w ] L → LgW S w → LgB L → (b ⊲[ w ] a) ⊎ (a ⊲[ w ] b)
  cmpB hself q lw l = inj₁ q
  cmpB p hself lw l = inj₂ p
  cmpB (hsuc p) (hsuc q) lw l = cmpB p q lw l
  cmpB (hlim n p) (hlim m q) lw (st , l) with <-cmp n m
  ... | tri< n<m _ _ = cmpB (⊲ᴮ-tr p (stepsᴮ st (<⇒<′ n<m))) q lw (l m)
  ... | tri> _ _ m<n = cmpB p (⊲ᴮ-tr q (stepsᴮ st (<⇒<′ m<n))) lw (l n)
  ... | tri≈ _ refl _ = cmpB p q lw (l n)
  cmpB (hLim e p) (hLim e′ q) lw (mo , l) with cmpK S e e′ lw
  ... | inj₁ c′c = cmpB p (⊲ᴮ-tr q (mo lw e′ e c′c)) lw (l lw e)
  ... | inj₂ cc′ = cmpB (⊲ᴮ-tr p (mo lw e e′ cc′)) q lw (l lw e′)
```

**加法** (右边逐构造子).

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
  Lg-⊞ a (hΩ κ g) la (mo , l) = (λ lw e e′ p → ⊞-⊲ a (mo lw e e′ p)) , (λ {c = c} lw e → Lg-⊞ a (g c) la (l lw e))
```

## §3 一步: 新种类的坐标是 `S` 上的高度

旧种类原样; 新种类 `inj₂ tt` 的坐标是 `HB S`, 界是新世界的第二分量, 第一位置是 `HB S` 的 `⊲`, 比较是 `cmpB`. 基世界的新界取 $0$, 顶坐标是界本身.

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

  ≤⁺-tr : ∀ {u v w} → u ≤⁺ v → v ≤⁺ w → u ≤⁺ w
  ≤⁺-tr (p , b) (q , c) = ≤w-tr S p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c

  Bd⁺ : (κ : K⁺) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = a ⊲[ proj₁ w ] proj₂ w

  Pr⁺ : (κ : K⁺) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w = Pr S κ (proj₁ w)
  Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′

  Bd↑⁺ : ∀ {κ c w w′} → w ≤⁺ w′ → Bd⁺ κ c w → Bd⁺ κ c w′
  Bd↑⁺ {inj₁ κ} (q , _) e = Bd↑ S q e
  Bd↑⁺ {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b

  cmpK⁺ : ∀ {κ c c′ w} → Bd⁺ κ c w → Bd⁺ κ c′ w → LgW⁺ w → Pr⁺ κ w c′ c ⊎ Pr⁺ κ w c c′
  cmpK⁺ {inj₁ κ} e e′ (lw , lb) = cmpK S e e′ lw
  cmpK⁺ {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb

  bot⁺ : (κ : K⁺) → E⁺ κ
  bot⁺ (inj₁ κ) = bot S κ
  bot⁺ (inj₂ _) = hz

  botBd⁺ : ∀ κ w → Bd⁺ κ (bot⁺ κ) w
  botBd⁺ (inj₁ κ) w = botBd S κ (proj₁ w)
  botBd⁺ (inj₂ _) w = z⊲ᴮ (proj₂ w)

  top⁺ : (κ : K⁺) → W⁺ → E⁺ κ
  top⁺ (inj₁ κ) w = top S κ (proj₁ w)
  top⁺ (inj₂ _) w = proj₂ w

  topBd⁺ : ∀ κ w → Bd⁺ κ (top⁺ κ w) w
  topBd⁺ (inj₁ κ) w = topBd S κ (proj₁ w)
  topBd⁺ (inj₂ _) w = hself

step : KS → KS
step S = record
  { K = K⁺ ; E = E⁺ ; Wd = W⁺ ; LgW = LgW⁺ ; _≤w_ = _≤⁺_ ; ≤w-rf = ≤w-rf S , hself ; ≤w-tr = ≤⁺-tr
  ; lgDn = λ p l → lgDn S (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l)
  ; w₀ = w₀ S , hz ; lw₀ = lw₀ S , tt
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; bot = bot⁺ ; botBd = botBd⁺ ; top = top⁺ ; topBd = topBd⁺ }
  where open Step S
```

**嵌入 `up`**: 旧种类的分支原样搬进 `step S`.

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
  Lg-up (hΩ κ g) (mo , l) = (λ lw e e′ p → up-⊲ (mo (proj₁ lw) e e′ p)) , (λ {c = c} lw e → Lg-up (g c) (l (proj₁ lw) e))
```

## §4 并, 与空结构 `S⊥`

`sup I F`: 种类 $\Sigma_i K(F\,i)$, 世界是逐分量的族. 一切字段逐分量.

```agda
sup : (I : Set) → (I → KS) → KS
sup I F = record
  { K = Σ I (λ i → K (F i)) ; E = λ κ → E (F (proj₁ κ)) (proj₂ κ) ; Wd = (i : I) → Wd (F i)
  ; LgW = λ w → ∀ i → LgW (F i) (w i) ; _≤w_ = λ w w′ → ∀ i → _≤w_ (F i) (w i) (w′ i)
  ; ≤w-rf = λ i → ≤w-rf (F i) ; ≤w-tr = λ p q i → ≤w-tr (F i) (p i) (q i)
  ; lgDn = λ p l i → lgDn (F i) (p i) (l i) ; w₀ = λ i → w₀ (F i) ; lw₀ = λ i → lw₀ (F i)
  ; Bd = λ κ c w → Bd (F (proj₁ κ)) (proj₂ κ) c (w (proj₁ κ))
  ; Pr = λ κ w → Pr (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
  ; Bd↑ = λ {κ} q e → Bd↑ (F (proj₁ κ)) (q (proj₁ κ)) e
  ; cmpK = λ {κ} e e′ lw → cmpK (F (proj₁ κ)) e e′ (lw (proj₁ κ))
  ; bot = λ κ → bot (F (proj₁ κ)) (proj₂ κ) ; botBd = λ κ w → botBd (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
  ; top = λ κ w → top (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) ; topBd = λ κ w → topBd (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) }

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
  Lg-ι i (hΩ κ g) (mo , l) = (λ lw e e′ p → ι-⊲ (mo (lw i) e e′ p)) , (λ {c = c} lw e → Lg-ι i (g c) (l (lw i) e))
```

**空结构.** `S⊥` 没有种类. `HB S⊥` 是只有 $0$, 后继, $\mathbb N$-极限的布劳威尔树: 闭项与 FGH 的类型.

```agda
S⊥ : KS
S⊥ = sup ⊥ (λ ())
```
