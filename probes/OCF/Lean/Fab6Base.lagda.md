# Fab6 (一): 带外部种类的高度树

> 不含记号. 入口 [Fab6](Fab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib.
>
> **重写** (参考 `CRwBase`, 只作参考). 与 `CRwBase` 的差只有一处: 树多一个构造子 `hE`, **外部种类**的结点. 外部种类由另一个结构 `XK` 给出: 种类 `KX`, 坐标 `EX`, 以及**分支的类型** `Br x y` (随坐标 $y$ 变, 不是本树的类型). 所以外部结点的分支是别的层上的树, 第一位置进不去 (`hEx` 只进前缀), 合法只要求每个分支在自己的层上合法 (`LgBr`). 这一个构造子取代了 CRw 的路径 (`PH`), 策略 (`Po`), 可入, 世界移动: 在 CRw 里 "坐标 $y$ 处的分支只用层号 $\le y$ 的种类" 是沿折叠搬运的证据, 这里是分支的类型.
>
> `hE x p g` 带前缀 $p$: 读 $p + \Omega_x(g)$. 前缀使 `⊞` 与 `⊞-fst` 对外部结点成立 (加到前缀上), 而分支不动.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fab6Base where

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

## §1 种类结构与外部种类

`KS` 同 CRw: 种类 `K`, 坐标 `E`, 世界 `Wd`, 界 `Bd`, 第一位置 `Pr`, 界之下可比 `cmpK`. `XK`: 外部种类, 坐标 `EX`, 分支类型 `Br`, 分支的合法 `LgBr`.

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

record XK : Set₁ where
  field
    KX   : Set
    EX   : KX → Set
    Br   : (x : KX) → EX x → Set
    LgBr : (x : KX) (y : EX x) → Br x y → Set
open XK public
```

## §2 高度

```agda
data HB (X : XK) (S : KS) : Set where
  hz : HB X S
  hs : HB X S → HB X S
  hl : (ℕ → HB X S) → HB X S
  hΩ : (κ : K S) → (E S κ → HB X S) → HB X S
  hE : (x : KX X) → HB X S → ((y : EX X x) → Br X x y) → HB X S

module _ {X : XK} {S : KS} where
  infix 4 _⊲[_]_
  data _⊲[_]_ : HB X S → Wd S → HB X S → Set where
    hself : ∀ {a w} → a ⊲[ w ] a
    hsuc  : ∀ {a b w} → a ⊲[ w ] b → a ⊲[ w ] hs b
    hlim  : ∀ {a f w} n → a ⊲[ w ] f n → a ⊲[ w ] hl f
    hLim  : ∀ {a κ g w c} → Bd S κ c w → a ⊲[ w ] g c → a ⊲[ w ] hΩ κ g
    hEx   : ∀ {a x p g w} → a ⊲[ w ] p → a ⊲[ w ] hE x p g

  ⊲ᴮ-tr : ∀ {a b c w} → a ⊲[ w ] b → b ⊲[ w ] c → a ⊲[ w ] c
  ⊲ᴮ-tr p hself = p
  ⊲ᴮ-tr p (hsuc q) = hsuc (⊲ᴮ-tr p q)
  ⊲ᴮ-tr p (hlim n q) = hlim n (⊲ᴮ-tr p q)
  ⊲ᴮ-tr p (hLim e q) = hLim e (⊲ᴮ-tr p q)
  ⊲ᴮ-tr p (hEx q) = hEx (⊲ᴮ-tr p q)

  ⊲ᴮ↑ : ∀ {a b w w′} → _≤w_ S w w′ → a ⊲[ w ] b → a ⊲[ w′ ] b
  ⊲ᴮ↑ q hself = hself
  ⊲ᴮ↑ q (hsuc p) = hsuc (⊲ᴮ↑ q p)
  ⊲ᴮ↑ q (hlim n p) = hlim n (⊲ᴮ↑ q p)
  ⊲ᴮ↑ q (hLim e p) = hLim (Bd↑ S q e) (⊲ᴮ↑ q p)
  ⊲ᴮ↑ q (hEx p) = hEx (⊲ᴮ↑ q p)

  z⊲ᴮ : ∀ {w} L → hz ⊲[ w ] L
  z⊲ᴮ hz = hself
  z⊲ᴮ (hs b) = hsuc (z⊲ᴮ b)
  z⊲ᴮ (hl f) = hlim 0 (z⊲ᴮ (f 0))
  z⊲ᴮ {w} (hΩ κ g) = hLim (botBd S κ w) (z⊲ᴮ (g (bot S κ)))
  z⊲ᴮ (hE x p g) = hEx (z⊲ᴮ p)

  LgB : HB X S → Set
  LgB hz = ⊤
  LgB (hs h) = LgB h
  LgB (hl f) = (∀ {w} n → f n ⊲[ w ] f (suc n)) × (∀ n → LgB (f n))
  LgB (hΩ κ g) =
    (∀ {w c c′} → LgW S w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) ×
    (∀ {w c} → LgW S w → Bd S κ c w → LgB (g c))
  LgB (hE x p g) = LgB p × (∀ y → LgBr X x y (g y))

  lgB⊲ : ∀ {a b w} → a ⊲[ w ] b → LgW S w → LgB b → LgB a
  lgB⊲ hself lw l = l
  lgB⊲ (hsuc p) lw l = lgB⊲ p lw l
  lgB⊲ (hlim n p) lw l = lgB⊲ p lw (proj₂ l n)
  lgB⊲ (hLim e p) lw l = lgB⊲ p lw (proj₂ l lw e)
  lgB⊲ (hEx p) lw l = lgB⊲ p lw (proj₁ l)

  stepsᴮ : ∀ {f : ℕ → HB X S} → (∀ {w} n → f n ⊲[ w ] f (suc n)) → ∀ {w n m} → n <′ m → f n ⊲[ w ] f m
  stepsᴮ s ≤′-refl = s _
  stepsᴮ s (≤′-step q) = ⊲ᴮ-tr (stepsᴮ s q) (s _)
```

**比较** (同 CRw): 同一棵合法高度的两个第一位置可比. 外部结点处两个位置都在前缀里.

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
  cmpB (hEx p) (hEx q) lw (lp , _) = cmpB p q lw lp
```

**加法** (右边逐构造子; 外部结点加到前缀).

```agda
  infixl 6 _⊞_
  _⊞_ : HB X S → HB X S → HB X S
  a ⊞ hz = a
  a ⊞ hs b = hs (a ⊞ b)
  a ⊞ hl f = hl (λ n → a ⊞ f n)
  a ⊞ hΩ κ g = hΩ κ (λ c → a ⊞ g c)
  a ⊞ hE x p g = hE x (a ⊞ p) g

  ⊞-fst : ∀ {w} a b → a ⊲[ w ] a ⊞ b
  ⊞-fst a hz = hself
  ⊞-fst a (hs b) = hsuc (⊞-fst a b)
  ⊞-fst a (hl f) = hlim 0 (⊞-fst a (f 0))
  ⊞-fst {w} a (hΩ κ g) = hLim (botBd S κ w) (⊞-fst a (g (bot S κ)))
  ⊞-fst a (hE x p g) = hEx (⊞-fst a p)

  ⊞-⊲ : ∀ {w} a {x y} → x ⊲[ w ] y → a ⊞ x ⊲[ w ] a ⊞ y
  ⊞-⊲ a hself = hself
  ⊞-⊲ a (hsuc p) = hsuc (⊞-⊲ a p)
  ⊞-⊲ a (hlim n p) = hlim n (⊞-⊲ a p)
  ⊞-⊲ a (hLim e p) = hLim e (⊞-⊲ a p)
  ⊞-⊲ a (hEx p) = hEx (⊞-⊲ a p)

  Lg-⊞ : ∀ a b → LgB a → LgB b → LgB (a ⊞ b)
  Lg-⊞ a hz la lb = la
  Lg-⊞ a (hs b) la lb = Lg-⊞ a b la lb
  Lg-⊞ a (hl f) la (st , l) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) la (l n))
  Lg-⊞ a (hΩ κ g) la (mo , l) = (λ lw e e′ p → ⊞-⊲ a (mo lw e e′ p)) , (λ {c = c} lw e → Lg-⊞ a (g c) la (l lw e))
  Lg-⊞ a (hE x p g) la (lp , lg) = Lg-⊞ a p la lp , lg
```

## §3 一步与并 (同 CRw; 外部种类 `X` 不动)

```agda
module Step (X : XK) (S : KS) where
  W⁺ : Set
  W⁺ = Wd S × HB X S

  _≤⁺_ : W⁺ → W⁺ → Set
  w ≤⁺ w′ = _≤w_ S (proj₁ w) (proj₁ w′) × (proj₂ w ⊲[ proj₁ w′ ] proj₂ w′)

  E⁺ : K S ⊎ ⊤ → Set
  E⁺ (inj₁ κ) = E S κ
  E⁺ (inj₂ _) = HB X S

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

step : XK → KS → KS
step X S = record
  { K = K S ⊎ ⊤ ; E = E⁺ ; Wd = W⁺ ; LgW = λ w → LgW S (proj₁ w) × LgB (proj₂ w) ; _≤w_ = _≤⁺_
  ; ≤w-tr = λ { (p , b) (q , c) → ≤w-tr S p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c }
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; bot = bot⁺ ; botBd = botBd⁺ }
  where open Step X S

module _ {X : XK} {S : KS} where
  up : HB X S → HB X (step X S)
  up hz = hz
  up (hs x) = hs (up x)
  up (hl f) = hl (λ n → up (f n))
  up (hΩ κ g) = hΩ (inj₁ κ) (λ c → up (g c))
  up (hE x p g) = hE x (up p) g

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

module _ {X : XK} {I : Set} {F : I → KS} where
  ι : (i : I) → HB X (F i) → HB X (sup I F)
  ι i hz = hz
  ι i (hs x) = hs (ι i x)
  ι i (hl f) = hl (λ n → ι i (f n))
  ι i (hΩ κ g) = hΩ (i , κ) (λ c → ι i (g c))
  ι i (hE x p g) = hE x (ι i p) g
```

## §4 空结构

`S⊥` 没有种类, `X⊥` 没有外部种类. `Cd = HB X⊥ S⊥` 是只有 $0$, 后继, ℕ-极限的布劳威尔树: 可数层号, 闭项与 FGH 的类型.

```agda
S⊥ : KS
S⊥ = record
  { K = ⊥ ; E = λ () ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤ ; ≤w-tr = λ _ _ → tt
  ; Bd = λ () ; Pr = λ () ; Bd↑ = λ {κ} → ⊥-elim κ ; cmpK = λ {κ} → ⊥-elim κ
  ; bot = λ () ; botBd = λ () }

X⊥ : XK
X⊥ = record { KX = ⊥ ; EX = λ () ; Br = λ () ; LgBr = λ () }

Cd : Set
Cd = HB X⊥ S⊥

infix 4 _⊲_
_⊲_ : Cd → Cd → Set
a ⊲ b = a ⊲[ tt ] b
```
