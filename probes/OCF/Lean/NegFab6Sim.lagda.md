# NegFab6 (一): 外部结点是原子 — 同底折叠对一棵普通塔的模拟

> 不含记号. 入口 [NegFab6](NegFab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib 与 `Fab6Base`, `Fab6Fold`.
>
> **这一篇证什么.** `Fab6Fold.Φ` 对外部结点只折前缀, 分支不动. 于是 "树里有多少个外部结点" 这件事, 被一棵**不含外部结点**的普通塔上的同底折叠控制: 关系 `Sim` 把带外部结点的树 $u$ (任意外部种类 `X`, 任意底 `S`) 与 `Cd` 上塔里的普通树 $v$ 对齐, 外部结点对着后继 (或对着第一项之后严格增长的 ℕ-极限), 定理 `sim` 说 `Φ` 保持 `Sim`. 这里底 `S` 的种类在 `Sim` 里没有对应 (`rT hz` 的 `KR` 是空的), 所以结论只谈不含底种类结点的输入.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFab6Sim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.Fab6Base
open import OCF.Lean.Fab6Fold
```

## §1 普通树上的序

`_≼_`: 不含外部结点的树上的布劳威尔序 ($\Omega$-结点逐分支比较; 也可以取一个分支作上界). 第 0 层 (`Cd`) 上就是通常的序. 外部种类固定成 `X⊥`.

```agda
module _ {S : KS} where
  infix 4 _≼_
  data _≼_ : HB X⊥ S → HB X⊥ S → Set where
    z≼  : ∀ {y} → hz ≼ y
    s≼s : ∀ {x y} → x ≼ y → hs x ≼ hs y
    l≼  : ∀ {f y} → (∀ n → f n ≼ y) → hl f ≼ y
    ≼l  : ∀ {x f} n → x ≼ f n → x ≼ hl f
    ≼s  : ∀ {x y} → x ≼ y → x ≼ hs y
    Ω≼Ω : ∀ {κ g g′} → (∀ c → g c ≼ g′ c) → hΩ κ g ≼ hΩ κ g′
    ≼Ω  : ∀ {x κ g} c → x ≼ g c → x ≼ hΩ κ g

  ≼-refl : ∀ x → x ≼ x
  ≼-refl hz = z≼
  ≼-refl (hs x) = s≼s (≼-refl x)
  ≼-refl (hl f) = l≼ (λ n → ≼l n (≼-refl (f n)))
  ≼-refl (hΩ κ g) = Ω≼Ω (λ c → ≼-refl (g c))
  ≼-refl (hE () _ _)

  ≼-tr : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
  ≼-tr z≼ q = z≼
  ≼-tr (l≼ k) q = l≼ (λ n → ≼-tr (k n) q)
  ≼-tr p (≼l n q) = ≼l n (≼-tr p q)
  ≼-tr p (≼s q) = ≼s (≼-tr p q)
  ≼-tr p (≼Ω c q) = ≼Ω c (≼-tr p q)
  ≼-tr (s≼s p) (s≼s q) = s≼s (≼-tr p q)
  ≼-tr (≼s p) (s≼s q) = ≼s (≼-tr p q)
  ≼-tr (≼l n p) (l≼ k) = ≼-tr p (k n)
  ≼-tr (≼Ω c p) (Ω≼Ω k) = ≼Ω c (≼-tr p (k c))
  ≼-tr (Ω≼Ω h) (Ω≼Ω k) = Ω≼Ω (λ c → ≼-tr (h c) (k c))

  ≼⊞l : ∀ x y → x ≼ x ⊞ y
  ≼⊞l x hz = ≼-refl x
  ≼⊞l x (hs y) = ≼s (≼⊞l x y)
  ≼⊞l x (hl f) = ≼l 0 (≼⊞l x (f 0))
  ≼⊞l x (hΩ κ g) = ≼Ω (bot S κ) (≼⊞l x (g (bot S κ)))
  ≼⊞l x (hE () _ _)

  ≼⊞r : ∀ x y → y ≼ x ⊞ y
  ≼⊞r x hz = z≼
  ≼⊞r x (hs y) = s≼s (≼⊞r x y)
  ≼⊞r x (hl f) = l≼ (λ n → ≼l n (≼⊞r x (f n)))
  ≼⊞r x (hΩ κ g) = Ω≼Ω (λ c → ≼⊞r x (g c))
  ≼⊞r x (hE () _ _)

  ⊞-mono : ∀ {x x′ y y′} → x ≼ x′ → y ≼ y′ → x ⊞ y ≼ x′ ⊞ y′
  ⊞-mono {x′ = x′} {y′ = y′} p z≼ = ≼-tr p (≼⊞l x′ y′)
  ⊞-mono p (s≼s q) = s≼s (⊞-mono p q)
  ⊞-mono p (l≼ k) = l≼ (λ n → ⊞-mono p (k n))
  ⊞-mono p (≼l n q) = ≼l n (⊞-mono p q)
  ⊞-mono p (≼s q) = ≼s (⊞-mono p q)
  ⊞-mono p (Ω≼Ω k) = Ω≼Ω (λ c → ⊞-mono p (k c))
  ⊞-mono p (≼Ω c q) = ≼Ω c (⊞-mono p q)

  ⊲→≼ : ∀ {a b w} → a ⊲[ w ] b → a ≼ b
  ⊲→≼ {a} hself = ≼-refl a
  ⊲→≼ (hsuc p) = ≼s (⊲→≼ p)
  ⊲→≼ (hlim n p) = ≼l n (⊲→≼ p)
  ⊲→≼ (hLim {c = c} e p) = ≼Ω c (⊲→≼ p)
  ⊲→≼ (hEx {x = ()} _)
```

## §2 度量 `er`

`er`: 把外部结点换成后继, 分支丢掉, 底种类的 $\Omega$-结点换成 $0$ (下面的定理只在没有这种结点的树上用它). `er` 的值就是 "沿前缀数外部结点与后继" 的长度.

```agda
er : ∀ {X S} → HB X S → Cd
er hz = hz
er (hs h) = hs (er h)
er (hl f) = hl (λ n → er (f n))
er (hΩ _ _) = hz
er (hE _ p _) = hs (er p)
```

## §3 对齐关系

`Rl T T′`: 两个种类结构之间的对应: 种类的对应 `KR`, 对应种类的坐标的对应 `RE`. `Sim Q u v`: $u$ 是 $T$ 上带外部种类 `X` 的树, $v$ 是 $T'$ 上不带外部种类的树, 逐构造子对齐. $\Omega$-结点按逻辑关系对齐 (对应的坐标给对应的分支). 外部结点有两条规则:

- `es`: 对着后继, 前缀对齐.
- `el`: 对着 ℕ-极限 $w$: 前缀对着第 $0$ 项, 而且 $w_0+1$ 是 $w_1$ 的第一位置 (所以这个极限严格超过 $w_0$).

`G x g`: 哪些分支是允许的, 由使用者给. 分支本身不进关系: 这就是 "外部结点是原子" 的字面写法.

```agda
record Rl (T T′ : KS) : Set₁ where
  field
    KR : K T → K T′ → Set
    RE : ∀ {κ κ′} → KR κ κ′ → E T κ → E T′ κ′ → Set
open Rl public

module Ali {X : XK} (G : (x : KX X) → ((y : EX X x) → Br X x y) → Set) where

  data Sim {T T′ : KS} (Q : Rl T T′) : HB X T → HB X⊥ T′ → Set where
    zz : Sim Q hz hz
    ss : ∀ {u v} → Sim Q u v → Sim Q (hs u) (hs v)
    ll : ∀ {f f′} → (∀ n → Sim Q (f n) (f′ n)) → Sim Q (hl f) (hl f′)
    oo : ∀ {κ κ′ g g′} (r : KR Q κ κ′) → (∀ c c′ → RE Q r c c′ → Sim Q (g c) (g′ c′)) → Sim Q (hΩ κ g) (hΩ κ′ g′)
    es : ∀ {x p g v} → G x g → Sim Q p v → Sim Q (hE x p g) (hs v)
    el : ∀ {x p g w} → G x g → Sim Q p (w 0) → (∀ {w′} → hs (w 0) ⊲[ w′ ] w 1) → Sim Q (hE x p g) (hl w)
```

一步与并上的对应; 塔上的对应 `rT`: 底的种类**没有**对应 (第 0 层 `KR` 恒空).

```agda
  KRs : ∀ {T T′} → Rl T T′ → K (step X T) → K (step X⊥ T′) → Set
  KRs Q (inj₁ κ) (inj₁ κ′) = KR Q κ κ′
  KRs Q (inj₁ κ) (inj₂ _) = ⊥
  KRs Q (inj₂ _) (inj₁ κ′) = ⊥
  KRs Q (inj₂ _) (inj₂ _) = ⊤

  REs : ∀ {T T′} (Q : Rl T T′) {κ κ′} → KRs Q κ κ′ → E (step X T) κ → E (step X⊥ T′) κ′ → Set
  REs Q {inj₁ κ} {inj₁ κ′} r = RE Q r
  REs Q {inj₂ _} {inj₂ _} r = Sim Q

  rStep : ∀ {T T′} → Rl T T′ → Rl (step X T) (step X⊥ T′)
  rStep Q = record { KR = KRs Q ; RE = REs Q }

  data KRl {F F′ : ℕ → KS} (Q : ∀ n → Rl (F n) (F′ n)) : K (sup ℕ F) → K (sup ℕ F′) → Set where
    kr : ∀ {n κ κ′} → KR (Q n) κ κ′ → KRl Q (n , κ) (n , κ′)

  REl : ∀ {F F′ : ℕ → KS} (Q : ∀ n → Rl (F n) (F′ n)) {κ κ′} → KRl Q κ κ′ → E (sup ℕ F) κ → E (sup ℕ F′) κ′ → Set
  REl Q (kr {n} r) = RE (Q n) r

  rSup : ∀ {F F′ : ℕ → KS} → (∀ n → Rl (F n) (F′ n)) → Rl (sup ℕ F) (sup ℕ F′)
  rSup Q = record { KR = KRl Q ; RE = REl Q }

  r⊥ : ∀ {S} → Rl S S⊥
  r⊥ = record { KR = λ _ _ → ⊥ ; RE = λ () }

  rT : ∀ {S} m → Rl (Tw X S m) (Tw X⊥ S⊥ m)
  rT hz = r⊥
  rT (hs x) = rStep (rT x)
  rT (hl f) = rSup (λ n → rT (f n))
  rT (hΩ () _)
  rT (hE () _ _)
```

## §4 `Sim` 对 `⊞`, 累加, `up`, `ι`, 地板的封闭

```agda
  Sim-⊞ : ∀ {T T′} {Q : Rl T T′} {a a′ u v} → Sim Q a a′ → Sim Q u v → Sim Q (a ⊞ u) (a′ ⊞ v)
  Sim-⊞ A zz = A
  Sim-⊞ A (ss p) = ss (Sim-⊞ A p)
  Sim-⊞ A (ll k) = ll (λ n → Sim-⊞ A (k n))
  Sim-⊞ A (oo r k) = oo r (λ c c′ e → Sim-⊞ A (k c c′ e))
  Sim-⊞ A (es g p) = es g (Sim-⊞ A p)
  Sim-⊞ {a′ = a′} A (el {w = w} g p gp) = el g (Sim-⊞ A p) (λ {w′} → ⊞-⊲ a′ (gp {w′}))

  Sim-mul : ∀ {T T′} {Q : Rl T T′} {x x′} → Sim Q x x′ → ∀ n → Sim Q (mul x n) (mul x′ n)
  Sim-mul s zero = s
  Sim-mul s (suc n) = Sim-⊞ (Sim-mul s n) s

  Sim-Σ : ∀ {T T′} {Q : Rl T T′} {f f′} → (∀ n → Sim Q (f n) (f′ n)) → ∀ n → Sim Q (Σ⁺ f n) (Σ⁺ f′ n)
  Sim-Σ s zero = s 0
  Sim-Σ s (suc n) = Sim-⊞ (Sim-Σ s n) (s (suc n))

  Sim-chain : ∀ {T T′} {Q : Rl T T′} {b b′ k k′} → Sim Q b b′ →
              (∀ x x′ → Sim Q x x′ → Sim Q (k x) (k′ x′)) → ∀ n → Sim Q (chain b k n) (chain b′ k′ n)
  Sim-chain B K zero = K _ _ B
  Sim-chain B K (suc n) = Sim-⊞ (Sim-chain B K n) (K _ _ (Sim-⊞ B (Sim-chain B K n)))

up-⊲ : ∀ {X S} {a b : HB X S} {w : Wd (step X S)} → a ⊲[ proj₁ w ] b → up {X} {S} a ⊲[ w ] up b
up-⊲ hself = hself
up-⊲ (hsuc p) = hsuc (up-⊲ p)
up-⊲ (hlim n p) = hlim n (up-⊲ p)
up-⊲ (hLim e p) = hLim e (up-⊲ p)
up-⊲ (hEx p) = hEx (up-⊲ p)

ι-⊲ : ∀ {X} {F : ℕ → KS} n {a b : HB X (F n)} {w : Wd (sup ℕ F)} → a ⊲[ w n ] b → ι {X} {ℕ} {F} n a ⊲[ w ] ι n b
ι-⊲ n hself = hself
ι-⊲ n (hsuc p) = hsuc (ι-⊲ n p)
ι-⊲ n (hlim m p) = hlim m (ι-⊲ n p)
ι-⊲ n (hLim e p) = hLim e (ι-⊲ n p)
ι-⊲ n (hEx p) = hEx (ι-⊲ n p)

module Ali₂ {X : XK} (G : (x : KX X) → ((y : EX X x) → Br X x y) → Set) where
  open Ali {X} G public

  Sim-up : ∀ {T T′} {Q : Rl T T′} {u v} → Sim Q u v → Sim (rStep Q) (up u) (up v)
  Sim-up zz = zz
  Sim-up (ss p) = ss (Sim-up p)
  Sim-up (ll k) = ll (λ n → Sim-up (k n))
  Sim-up (oo {κ = κ} {κ′ = κ′} r k) = oo {κ = inj₁ κ} {κ′ = inj₁ κ′} r (λ c c′ e → Sim-up (k c c′ e))
  Sim-up (es g p) = es g (Sim-up p)
  Sim-up (el g p gp) = el g (Sim-up p) (λ {w′} → up-⊲ (gp {proj₁ w′}))

  Sim-ι : ∀ {F F′ : ℕ → KS} {Q : ∀ n → Rl (F n) (F′ n)} n {u v} → Sim (Q n) u v → Sim (rSup Q) (ι n u) (ι n v)
  Sim-ι n zz = zz
  Sim-ι n (ss p) = ss (Sim-ι n p)
  Sim-ι n (ll k) = ll (λ m → Sim-ι n (k m))
  Sim-ι n (oo r k) = oo (kr r) (λ c c′ e → Sim-ι n (k c c′ e))
  Sim-ι n (es g p) = es g (Sim-ι n p)
  Sim-ι n (el g p gp) = el g (Sim-ι n p) (λ {w′} → ι-⊲ n (gp {w′ n}))

  Sim-top : ∀ {S b b′} → Sim (rT {S} hz) b b′ → ∀ m → Sim (rT {S} m) (topT X S b m) (topT X⊥ S⊥ b′ m)
  Sim-ΣT : ∀ {S b b′} → Sim (rT {S} hz) b b′ → (f : ℕ → Cd) → ∀ n →
           Sim (rT {S} (hl f)) (ΣT X S b f n) (ΣT X⊥ S⊥ b′ f n)
  Sim-top B hz = B
  Sim-top B (hs x) = oo {κ = inj₂ tt} {κ′ = inj₂ tt} tt (λ c c′ e → Sim-up e)
  Sim-top B (hl f) = ll (Sim-ΣT B f)
  Sim-top B (hΩ () _)
  Sim-top B (hE () _ _)
  Sim-ΣT B f zero = Sim-ι 0 (Sim-top B (f 0))
  Sim-ΣT B f (suc n) = Sim-⊞ (Sim-ΣT B f n) (Sim-ι (suc n) (Sim-top B (f (suc n))))
```

## §5 决定对齐

左右两边的 `cl`, `dcl` 走同一个分支: 层号 $m$, 目标 $t$, 位置都一样, 比较 `cmpB` 只看 `Cd`.

```agda
  data ClR {S : KS} {m : Cd} {κ κ′} (RA : E (Tw X S m) κ → E (Tw X⊥ S⊥ m) κ′ → Set) :
           Cl {X} {S} m κ → Cl {X⊥} {S⊥} m κ′ → Set where
    rn : ∀ {j p to to′} → (∀ c c′ → Sim (rT j) c c′ → RA (to c) (to′ c′)) → ClR RA (nw j p to) (nw j p to′)

  cS-r : ∀ {S : KS} {x κ κ′ RA c c′} → ClR {S} {x} {κ} {κ′} RA c c′ → ClR {S} {hs x} {inj₁ κ} {inj₁ κ′} RA (cS c) (cS c′)
  cS-r (rn k) = rn k

  cL-r : ∀ {S : KS} {f} n {κ κ′ RA c c′} → ClR {S} {f n} {κ} {κ′} RA c c′ → ClR {S} {hl f} {n , κ} {n , κ′} RA (cL n c) (cL n c′)
  cL-r n (rn k) = rn k

  cl-r : ∀ {S : KS} m {κ κ′} (r : KR (rT {S} m) κ κ′) → ClR {S} {m} (RE (rT {S} m) r) (cl m κ) (cl m κ′)
  cl-r (hs x) {inj₁ κ} {inj₁ κ′} r = cS-r (cl-r x r)
  cl-r (hs x) {inj₂ _} {inj₂ _} r = rn (λ c c′ e → e)
  cl-r (hl f) (kr {n} r) = cL-r n (cl-r (f n) r)
  cl-r (hΩ () _) _
  cl-r (hE () _ _) _

  data DcR {S : KS} {B t : Cd} {A A′ : Set} (RA : A → A′ → Set) :
           Dc (Tw X S) X B t A → Dc (Tw X⊥ S⊥) X⊥ B t A′ → Set where
    rk : ∀ {κ κ′ fr fr′} (r : KR (rT {S} t) κ κ′) → (∀ c c′ → RE (rT {S} t) r c c′ → RA (fr c) (fr′ c′)) →
         DcR RA (keep κ fr) (keep κ′ fr′)
    rs : ∀ {to to′} → (∀ c c′ → Sim (rT {S} t) c c′ → RA (to c) (to′ c′)) → DcR RA (same to) (same to′)
    ra : ∀ {i u q to to′} → (∀ c c′ → Sim (rT {S} i) c c′ → RA (to c) (to′ c′)) →
         DcR RA (above i u q to) (above i u q to′)

  along-r : ∀ {S : KS} {i t} (q : hs i ⊲ t) → KR (rT {S} t) (along {X} {S} q) (along {X⊥} {S⊥} q)
  along-r hself = tt
  along-r (hsuc q) = along-r q
  along-r (hlim n q) = kr (along-r q)
  along-r (hLim {κ = ()} _ _)
  along-r (hEx {x = ()} _)

  frA-r : ∀ {S : KS} {i t} (q : hs i ⊲ t) c c′ → RE (rT {S} t) (along-r q) c c′ →
          Sim (rT {S} i) (frA {X} {S} q c) (frA {X⊥} {S⊥} q c′)
  frA-r hself c c′ e = e
  frA-r (hsuc q) c c′ e = frA-r q c c′ e
  frA-r (hlim n q) c c′ e = frA-r q c c′ e
  frA-r (hLim {κ = ()} _ _) _ _ _
  frA-r (hEx {x = ()} _) _ _ _

  pick-r : ∀ {S : KS} {B t i A A′} {RA : A → A′ → Set} {to to′} →
           (∀ c c′ → Sim (rT {S} i) c c′ → RA (to c) (to′ c′)) → (u : hs i ⊲ B) → (d : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
           DcR {S} RA (pick X S to u d) (pick X⊥ S⊥ to′ u d)
  pick-r k u (inj₂ q) = rk (along-r q) (λ c c′ e → k _ _ (frA-r q c c′ e))
  pick-r k u (inj₁ hself) = rk tt k
  pick-r k u (inj₁ (hsuc hself)) = rs k
  pick-r k u (inj₁ (hsuc (hsuc q))) = ra k
  pick-r k u (inj₁ (hsuc (hlim n q))) = ra k
  pick-r k u (inj₁ (hsuc (hLim {κ = ()} _ _)))
  pick-r k u (inj₁ (hsuc (hEx {x = ()} _)))

  dcl-r : ∀ {S : KS} {m t κ κ′} {RA} (pt : t ⊲ m) (lm : LgB m) {c c′} → ClR {S} {m} {κ} {κ′} RA c c′ →
          DcR {S} RA (dcl pt lm c) (dcl pt lm c′)
  dcl-r pt lm (rn {p = p} k) = pick-r k p (cmpB p pt tt lm)
```

**`caseDc` 的消去.** 对右边, `Φ` 的值恒在 $1$ 之上 (`pos-Φ`): $\Omega$-结点取最低的坐标.

```agda
caseDc-elim : ∀ {L X B t A} {R : Set} (P : R → Set) (d : Dc L X B t A) {k s ab} →
              (∀ κ′ fr → P (k κ′ fr)) → (∀ to → P (s to)) → (∀ i u q to → P (ab i u q to)) → P (caseDc d k s ab)
caseDc-elim P (keep κ′ fr) pk ps pa = pk κ′ fr
caseDc-elim P (same to) pk ps pa = ps to
caseDc-elim P (above i u q to) pk ps pa = pa i u q to

pos-Φ : ∀ m a lm t pt b h {w} → hs hz ⊲[ w ] Φ {X⊥} {S⊥} m a lm t pt b h
pos-Φ m a lm t pt b hz = hself
pos-Φ m a lm t pt b (hs h) = hlim 0 (pos-Φ m a lm t pt b h)
pos-Φ m a lm t pt b (hl f) = hlim 0 (pos-Φ m a lm t pt b (f 0))
pos-Φ m a lm t pt b (hE () _ _)
pos-Φ m (acc rs) lm t pt b (hΩ κ g) {w} = caseDc-elim (λ r → hs hz ⊲[ w ] r) (dcl pt lm (cl m κ))
  (λ κ′ fr → hLim (botBd (Tw X⊥ S⊥ t) κ′ w) (pos-Φ m (acc rs) lm t pt b (g (fr (bot (Tw X⊥ S⊥ t) κ′)))))
  (λ to → hlim 0 (pos-Φ m (acc rs) lm t pt b (g (to b))))
  (λ i pi q to → pos-Φ i (rs i pi) (lg↓ pi lm) t q b _)
```

## §6 模拟定理

**定理 (`sim`).** 对一切外部种类 `X`, 底 `S`, 层号 $m$, 目标 $t\lhd m$: 若种子对齐, 输入对齐, 则同底折叠的输出对齐, 右边是 `Cd` 的塔上**不含外部结点**的同一个折叠, 用同一份可达性证明与同一个合法证据.

外部结点的子句是全部要点: 左边 `hE x (Φ p) g`, 右边后继变成 `hl (mul (Φ v))`, 或 ℕ-极限变成部分和; 前缀对着第 $0$ 项, 严格增长由 `pos-Φ` 给出 (`el` 规则). 分支 `g` 原样留着, 没有进关系.

```agda
module Thm {X : XK} (G : (x : KX X) → ((y : EX X x) → Br X x y) → Set) where
  open Ali₂ {X} G

  caseDc-r : ∀ {S : KS} {B t A A′} {RA : A → A′ → Set} {Rt Rt′ : Set} {RR : Rt → Rt′ → Set}
             {d : Dc (Tw X S) X B t A} {d′ : Dc (Tw X⊥ S⊥) X⊥ B t A′} {k s ab k′ s′ ab′} → DcR {S} RA d d′ →
             (∀ κ κ′ fr fr′ (r : KR (rT {S} t) κ κ′) → (∀ c c′ → RE (rT {S} t) r c c′ → RA (fr c) (fr′ c′)) → RR (k κ fr) (k′ κ′ fr′)) →
             (∀ to to′ → (∀ c c′ → Sim (rT {S} t) c c′ → RA (to c) (to′ c′)) → RR (s to) (s′ to′)) →
             (∀ i u q to to′ → (∀ c c′ → Sim (rT {S} i) c c′ → RA (to c) (to′ c′)) → RR (ab i u q to) (ab′ i u q to′)) →
             RR (caseDc d k s ab) (caseDc d′ k′ s′ ab′)
  caseDc-r (rk r e) pk ps pa = pk _ _ _ _ r e
  caseDc-r (rs e) pk ps pa = ps _ _ e
  caseDc-r (ra e) pk ps pa = pa _ _ _ _ _ e

  sim : ∀ {S : KS} m a lm t pt {b b′ h h′} → Sim (rT {S} t) b b′ → Sim (rT {S} m) h h′ →
        Sim (rT {S} t) (Φ {X} {S} m a lm t pt b h) (Φ {X⊥} {S⊥} m a lm t pt b′ h′)
  sim m a lm t pt B zz = ss zz
  sim m a lm t pt B (ss p) = ll (Sim-mul (sim m a lm t pt B p))
  sim m a lm t pt B (ll k) = ll (Sim-Σ (λ n → sim m a lm t pt B (k n)))
  sim m a lm t pt {b′ = b′} B (es {v = v} g p) =
    el g (sim m a lm t pt B p) (λ {w′} → ⊞-⊲ (Φ m a lm t pt b′ v) (pos-Φ m a lm t pt b′ v))
  sim m a lm t pt {b′ = b′} B (el {w = w} g p gp) =
    el g (sim m a lm t pt B p) (λ {w′} → ⊞-⊲ (Φ m a lm t pt b′ (w 0)) (pos-Φ m a lm t pt b′ (w 1)))
  sim {S} m (acc rc) lm t pt {b} {b′} B (oo {κ} {κ′} {g} {g′} r k) =
    caseDc-r {S} {RR = Sim (rT {S} t)}
      {k = λ κ₁ fr → hΩ κ₁ (λ c → Φ m (acc rc) lm t pt b (g (fr c)))}
      {s = λ to → hl (chain b (λ b₁ → Φ m (acc rc) lm t pt b₁ (g (to b₁))))}
      {ab = λ i pi q to → Φ i (rc i pi) (lg↓ pi lm) t q b
              (hl (chain (topT X S (topT X S hz hz) i) (λ b₁ → Φ m (acc rc) lm i (⊏⊑ pi) b₁ (g (to b₁)))))}
      {k′ = λ κ₁ fr → hΩ κ₁ (λ c → Φ m (acc rc) lm t pt b′ (g′ (fr c)))}
      {s′ = λ to → hl (chain b′ (λ b₁ → Φ m (acc rc) lm t pt b₁ (g′ (to b₁))))}
      {ab′ = λ i pi q to → Φ i (rc i pi) (lg↓ pi lm) t q b′
              (hl (chain (topT X⊥ S⊥ (topT X⊥ S⊥ hz hz) i) (λ b₁ → Φ m (acc rc) lm i (⊏⊑ pi) b₁ (g′ (to b₁)))))}
      (dcl-r pt lm (cl-r m r))
      (λ κ₁ κ₁′ fr fr′ r₁ e → oo r₁ (λ c c′ c~ → sim m (acc rc) lm t pt B (k (fr c) (fr′ c′) (e c c′ c~))))
      (λ to to′ e → ll (Sim-chain B (λ x x′ x~ → sim m (acc rc) lm t pt x~ (k (to x) (to′ x′) (e x x′ x~)))))
      (λ i pi q to to′ e → sim i (rc i pi) (lg↓ pi lm) t q B
         (ll (Sim-chain (Sim-top zz i) (λ x x′ x~ → sim m (acc rc) lm i (⊏⊑ pi) x~ (k (to x) (to′ x′) (e x x′ x~))))))
```

## §7 第 0 层: 度量的上界

第 0 层 `rT hz` 的 `KR` 是空的, 所以 `Sim (rT hz) u v` 里 $u$ 没有 $\Omega$-结点. 度量 `er u` 不超过 $v$.

```agda
  sound : ∀ {S : KS} {u v} → Sim (rT {S} hz) u v → er u ≼ v
  sound zz = z≼
  sound (ss p) = s≼s (sound p)
  sound (ll k) = l≼ (λ n → ≼l n (sound (k n)))
  sound (oo () _)
  sound (es g p) = s≼s (sound p)
  sound (el g p gp) = ≼l 1 (≼-tr (s≼s (sound p)) (⊲→≼ (gp {tt})))
```

## §8 严格树

`St`: 每个 ℕ-极限的相邻项按值严格递增 (遗传). 这是**关于具体闭项的谓词**, 不是对树类型的要求 (要求一切树这样会碰 `BrwViewNeg.strict→LPO`). 用处: 入口 §3 的条件定理的前提只对严格树要求单调. 合法 `LgB` 允许常序列 (`hself` 是第一位置), 树的值很小而 `leg` 的值很大, 所以在 `LgB` 上要求单调的前提是否可满足是可疑的 (判断); 折叠的输出都是严格树 (`St-Φ`), 不需要 `LgB` 这么宽的范围.

```agda
module _ {S : KS} where
  St : HB X⊥ S → Set
  St hz = ⊤
  St (hs h) = St h
  St (hl f) = (∀ n → hs (f n) ≼ f (suc n)) × (∀ n → St (f n))
  St (hΩ κ g) = ∀ c → St (g c)
  St (hE () _ _)

  St-⊞ : ∀ (a b : HB X⊥ S) → St a → St b → St (a ⊞ b)
  St-⊞ a hz sa sb = sa
  St-⊞ a (hs b) sa sb = St-⊞ a b sa sb
  St-⊞ a (hl f) sa (st , sf) = (λ n → ⊞-mono (≼-refl a) (st n)) , (λ n → St-⊞ a (f n) sa (sf n))
  St-⊞ a (hΩ κ g) sa sg = λ c → St-⊞ a (g c) sa (sg c)
  St-⊞ a (hE () _ _) _ _

  gap : ∀ (a : HB X⊥ S) {y} → hs hz ≼ y → hs a ≼ a ⊞ y
  gap a p = ⊞-mono (≼-refl a) p

  St-mul : ∀ (x : HB X⊥ S) → St x → hs hz ≼ x → St (hl (mul x))
  St-mul x s p = (λ n → gap (mul x n) p) , go
    where go : ∀ n → St (mul x n)
          go zero = s
          go (suc n) = St-⊞ (mul x n) x (go n) s

  St-Σ : ∀ (f : ℕ → HB X⊥ S) → (∀ n → St (f n)) → (∀ n → hs hz ≼ f n) → St (hl (Σ⁺ f))
  St-Σ f sf p = (λ n → gap (Σ⁺ f n) (p (suc n))) , go
    where go : ∀ n → St (Σ⁺ f n)
          go zero = sf 0
          go (suc n) = St-⊞ (Σ⁺ f n) (f (suc n)) (go n) (sf (suc n))

  St-chain : ∀ (b : HB X⊥ S) (k : HB X⊥ S → HB X⊥ S) → (∀ b′ → St (k b′)) → (∀ b′ → hs hz ≼ k b′) → St (hl (chain b k))
  St-chain b k sk p = (λ n → gap (chain b k n) (p (b ⊞ chain b k n))) , go
    where go : ∀ n → St (chain b k n)
          go zero = sk b
          go (suc n) = St-⊞ (chain b k n) (k (b ⊞ chain b k n)) (go n) (sk (b ⊞ chain b k n))

pos≼ : ∀ m a lm t pt b h → hs hz ≼ Φ {X⊥} {S⊥} m a lm t pt b h
pos≼ m a lm t pt b hz = ≼-refl (hs hz)
pos≼ m a lm t pt b (hs h) = ≼l 0 (pos≼ m a lm t pt b h)
pos≼ m a lm t pt b (hl f) = ≼l 0 (pos≼ m a lm t pt b (f 0))
pos≼ m a lm t pt b (hE () _ _)
pos≼ m (acc rs) lm t pt b (hΩ κ g) = caseDc-elim (λ r → hs hz ≼ r) (dcl pt lm (cl m κ))
  (λ κ′ fr → ≼Ω (bot (Tw X⊥ S⊥ t) κ′) (pos≼ m (acc rs) lm t pt b (g (fr (bot (Tw X⊥ S⊥ t) κ′)))))
  (λ to → ≼l 0 (pos≼ m (acc rs) lm t pt b (g (to b))))
  (λ i pi q to → pos≼ i (rs i pi) (lg↓ pi lm) t q b _)

St-Φ : ∀ m a lm t pt b h → St (Φ {X⊥} {S⊥} m a lm t pt b h)
St-Φ m a lm t pt b hz = tt
St-Φ m a lm t pt b (hs h) = St-mul _ (St-Φ m a lm t pt b h) (pos≼ m a lm t pt b h)
St-Φ m a lm t pt b (hl f) = St-Σ _ (λ n → St-Φ m a lm t pt b (f n)) (λ n → pos≼ m a lm t pt b (f n))
St-Φ m a lm t pt b (hE () _ _)
St-Φ m (acc rs) lm t pt b (hΩ κ g) = caseDc-elim St (dcl pt lm (cl m κ))
  (λ κ′ fr c → St-Φ m (acc rs) lm t pt b (g (fr c)))
  (λ to → St-chain b _ (λ b′ → St-Φ m (acc rs) lm t pt b′ (g (to b′))) (λ b′ → pos≼ m (acc rs) lm t pt b′ (g (to b′))))
  (λ i pi q to → St-Φ i (rs i pi) (lg↓ pi lm) t q b _)
```
