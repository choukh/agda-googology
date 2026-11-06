# CRw (一): 种类结构, 高度, `step`, `sup`

> 不含记号. 入口 [CRw](CRw.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib.
>
> **重写.** 参考 `HtTowerTy` 与 `LeanTBase` (只作参考). 与 `LeanTBase` 的差: 种类结构不带顶坐标、基世界、向下封闭 (本路的折叠不用它们); 没有 `≤w-rf`; `S⊥` 是记录 (世界是 `⊤`, 闭项的世界是规范的 `tt`). 合法 `LgB` 的 $\Omega$-分支取 "在合法世界的界之下的坐标处合法" (同 `LeanTBase`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CRwBase where

open import Data.Nat using (ℕ; zero; suc; _<′_; ≤′-step)
open import Data.Nat.Base using (≤′-refl)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl)
```

## §1 种类结构

`K`: 种类; `E κ`: 坐标; `Wd`: 世界; `Bd κ c w`: 坐标 $c$ 在世界 $w$ 的界之下; `Pr`: 第一位置; `cmpK`: 界之下的两个坐标可比 (字面公共上界就是这个界); `bot`: 在一切界之下的坐标.

```agda
record KS : Set₁ where
  field
    K     : Set
    E     : K → Set
    Wd    : Set
    LgW   : Wd → Set
    _≤w_  : Wd → Wd → Set
    ≤w-tr : ∀ {u v w} → u ≤w v → v ≤w w → u ≤w w
    Bd    : (κ : K) → E κ → Wd → Set
    Pr    : (κ : K) → Wd → E κ → E κ → Set
    Bd↑   : ∀ {κ c w w′} → w ≤w w′ → Bd κ c w → Bd κ c w′
    cmpK  : ∀ {κ c c′ w} → Bd κ c w → Bd κ c′ w → LgW w → Pr κ w c′ c ⊎ Pr κ w c c′
    bot   : (κ : K) → E κ
    botBd : ∀ κ w → Bd κ (bot κ) w
open KS public
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

**比较.** 同一棵合法高度 $L$ 的两个第一位置可比: $L$ 是字面公共上界. 对一切种类结构一条.

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

```agda
module Step (S : KS) where
  W⁺ : Set
  W⁺ = Wd S × HB S

  _≤⁺_ : W⁺ → W⁺ → Set
  w ≤⁺ w′ = _≤w_ S (proj₁ w) (proj₁ w′) × (proj₂ w ⊲[ proj₁ w′ ] proj₂ w′)

  E⁺ : K S ⊎ ⊤ → Set
  E⁺ (inj₁ κ) = E S κ
  E⁺ (inj₂ _) = HB S

  Bd⁺ : (κ : K S ⊎ ⊤) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = a ⊲[ proj₁ w ] proj₂ w

  Pr⁺ : (κ : K S ⊎ ⊤) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w = Pr S κ (proj₁ w)
  Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′

  Bd↑⁺ : ∀ {κ c w w′} → w ≤⁺ w′ → Bd⁺ κ c w → Bd⁺ κ c w′
  Bd↑⁺ {inj₁ κ} (q , _) e = Bd↑ S q e
  Bd↑⁺ {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b

  cmpK⁺ : ∀ {κ c c′ w} → Bd⁺ κ c w → Bd⁺ κ c′ w → LgW S (proj₁ w) × LgB (proj₂ w) → Pr⁺ κ w c′ c ⊎ Pr⁺ κ w c c′
  cmpK⁺ {inj₁ κ} e e′ (lw , lb) = cmpK S e e′ lw
  cmpK⁺ {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb

  bot⁺ : (κ : K S ⊎ ⊤) → E⁺ κ
  bot⁺ (inj₁ κ) = bot S κ
  bot⁺ (inj₂ _) = hz

  botBd⁺ : ∀ κ w → Bd⁺ κ (bot⁺ κ) w
  botBd⁺ (inj₁ κ) w = botBd S κ (proj₁ w)
  botBd⁺ (inj₂ _) w = z⊲ᴮ (proj₂ w)

step : KS → KS
step S = record
  { K = K S ⊎ ⊤ ; E = E⁺ ; Wd = W⁺ ; LgW = λ w → LgW S (proj₁ w) × LgB (proj₂ w) ; _≤w_ = _≤⁺_
  ; ≤w-tr = λ { (p , b) (q , c) → ≤w-tr S p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c }
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; bot = bot⁺ ; botBd = botBd⁺ }
  where open Step S

module _ {S : KS} where
  up : HB S → HB (step S)
  up hz = hz
  up (hs x) = hs (up x)
  up (hl f) = hl (λ n → up (f n))
  up (hΩ κ g) = hΩ (inj₁ κ) (λ c → up (g c))
```

## §4 并, 与空结构 `S⊥`

```agda
sup : (I : Set) → (I → KS) → KS
sup I F = record
  { K = Σ I (λ i → K (F i)) ; E = λ κ → E (F (proj₁ κ)) (proj₂ κ) ; Wd = (i : I) → Wd (F i)
  ; LgW = λ w → ∀ i → LgW (F i) (w i) ; _≤w_ = λ w w′ → ∀ i → _≤w_ (F i) (w i) (w′ i)
  ; ≤w-tr = λ p q i → ≤w-tr (F i) (p i) (q i)
  ; Bd = λ κ c w → Bd (F (proj₁ κ)) (proj₂ κ) c (w (proj₁ κ))
  ; Pr = λ κ w → Pr (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
  ; Bd↑ = λ {κ} q e → Bd↑ (F (proj₁ κ)) (q (proj₁ κ)) e
  ; cmpK = λ {κ} e e′ lw → cmpK (F (proj₁ κ)) e e′ (lw (proj₁ κ))
  ; bot = λ κ → bot (F (proj₁ κ)) (proj₂ κ) ; botBd = λ κ w → botBd (F (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) }

module _ {I : Set} {F : I → KS} where
  ι : (i : I) → HB (F i) → HB (sup I F)
  ι i hz = hz
  ι i (hs x) = hs (ι i x)
  ι i (hl f) = hl (λ n → ι i (f n))
  ι i (hΩ κ g) = hΩ (i , κ) (λ c → ι i (g c))
```

`S⊥` 没有种类, 世界是 `⊤`. `Cd = HB S⊥` 是只有 $0$, 后继, $\mathbb N$-极限的布劳威尔树: 可数层号, 世界的界, 闭项与 FGH 的类型.

```agda
S⊥ : KS
S⊥ = record
  { K = ⊥ ; E = λ () ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤ ; ≤w-tr = λ _ _ → tt
  ; Bd = λ () ; Pr = λ () ; Bd↑ = λ {κ} → ⊥-elim κ ; cmpK = λ {κ} → ⊥-elim κ
  ; bot = λ () ; botBd = λ () }

Cd : Set
Cd = HB S⊥

infix 4 _⊲_
_⊲_ : Cd → Cd → Set
a ⊲ b = a ⊲[ tt ] b
```
