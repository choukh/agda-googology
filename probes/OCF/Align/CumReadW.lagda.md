# 带闭包的世界: 以字面下界为世界的折叠

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). 这一篇把 [CumReadCF](CumReadCF.lagda.md) 推到带闭包的层 (这里只有一种闭包: 分支是可数下标, $\Omega_1$ 共尾). 与 `NoKCertTree` 相比, 去掉了帧, 表, 地板, `≈` 上的搬运.
>
> - **世界.** `A` 里的一个字面值 $u$. `O L u`: 第 $L$ 层的元素, 它用到的所有下标都是 $u$ 的第一位置. 闭包的分支 `oc x g` 在 $v\rhd u$ 的世界上给出, 所以 **"分支下标高于外层的所有下标" 由世界保证**, 字面上界就是世界本身, 比较 (`cmpN`) 只在一个 `Lg` 的世界之下. 这是 `chain-stuck` 的解法: 不需要下界守卫, 不需要表.
> - **路径** `k < L` 可以走分支 `bra w r`, `Adm v r` 说路径上的下标都在 $v$ 之下. 节点的输入在任何更高的世界上给出.
> - **第 0 层的闭包** 直接计值 (`ψ` 的 `lz` 行): 链点由 `next` 累加, 没有证书这一步.
> - **规范世界.** 输出的世界是 $\max(u,\tau)$: $u$ 是输入的世界, $\tau$ 是目标路径的世界. 不是运行时的世界, 所以同一个项同一个目标算出的闭包字面相同 (`mx`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (Ordᶜ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲; Lg-next)
```

## §1 世界

`Gw v`: 世界合法且不低于 $1$.

```agda
one : A
one = asuc azero

record Gw (v : A) : Set where
  constructor gw
  field
    lgw : Lg v
    pos : one ⊲ v
open Gw public

g₀ : Gw one
g₀ = gw tt C.self

g⊲ : ∀ {u v} → Gw u → u ⊲ v → Lg v → Gw v
g⊲ g p w = gw w (⊲-tr (pos g) p)

gnext : ∀ {u} (y : Ord₀) → Gw u → Gw (next u y)
gnext {u} y g = gw (Lg-next u y (lgw g)) (⊲-tr (pos g) (next-⊲ u y))
```

## §2 层

`lc t g`: $\Omega_1$ 共尾, 第一支 $t$, 分支 $g$ 对一切下标有定义 (不带守卫, `Legal` 只读合法的下标).

```agda
data Lv : Set where
  lz : Lv
  ls : Lv → Lv
  ll : (ℕ → Lv) → Lv
  lc : Lv → (A → Lv) → Lv

-- 字面第一位置
infix 4 _⊳_
data _⊳_ : Lv → Lv → Set where
  self : ∀ {a} → a ⊳ a
  suc  : ∀ {a b} → a ⊳ b → a ⊳ ls b
  lim  : ∀ {a f} n → a ⊳ f n → a ⊳ ll f
  fst  : ∀ {a t g} → a ⊳ t → a ⊳ lc t g

⊳-tr : ∀ {a b c} → a ⊳ b → b ⊳ c → a ⊳ c
⊳-tr p self = p
⊳-tr p (suc q) = suc (⊳-tr p q)
⊳-tr p (lim n q) = lim n (⊳-tr p q)
⊳-tr p (fst q) = fst (⊳-tr p q)

Legal : Lv → Set
Legal lz = ⊤
Legal (ls a) = Legal a
Legal (ll f) = (∀ n → f n ⊳ f (suc n)) × (∀ n → Legal (f n))
Legal (lc t g) =
  (∀ w → Gw w → t ⊳ g w) ×
  (∀ w v → Gw w → Gw v → w ⊲ v → g w ⊳ g v) ×
  Legal t × (∀ w → Gw w → Legal (g w))
```

**路径.** `k < L` 节点的路径; `k ≤ L` 位置, 都可以走分支. `Adm v`: 路径上的下标在 $v$ 之下.

```agda
infix 4 _<_ _≤_
data _<_ : Lv → Lv → Set where
  zero : ∀ {a} → a < ls a
  suc  : ∀ {a b} → a < b → a < ls b
  lim  : ∀ {a f} n → a < f n → a < ll f
  fst  : ∀ {a t g} → a < t → a < lc t g
  bra  : ∀ {a t g} w → a < g w → a < lc t g

data _≤_ : Lv → Lv → Set where
  self : ∀ {a} → a ≤ a
  suc  : ∀ {a b} → a ≤ b → a ≤ ls b
  lim  : ∀ {a f} n → a ≤ f n → a ≤ ll f
  fst  : ∀ {a t g} → a ≤ t → a ≤ lc t g
  bra  : ∀ {a t g} w → a ≤ g w → a ≤ lc t g

Bw : A → A → Set
Bw w v = (w ⊲ v) × (one ⊲ w)

gB : ∀ {w v} → Gw v → Bw w v → Gw w
gB g (p , o) = gw (lg⊲ p (lgw g)) o

upB : ∀ {w u v} → u ⊲ v → Bw w u → Bw w v
upB q (p , o) = ⊲-tr p q , o

Adm< : ∀ {a b} → A → a < b → Set
Adm< v zero = ⊤
Adm< v (suc r) = Adm< v r
Adm< v (lim n r) = Adm< v r
Adm< v (fst r) = Adm< v r
Adm< v (bra w r) = Bw w v × Adm< v r

Adm≤ : ∀ {a b} → A → a ≤ b → Set
Adm≤ v self = ⊤
Adm≤ v (suc r) = Adm≤ v r
Adm≤ v (lim n r) = Adm≤ v r
Adm≤ v (fst r) = Adm≤ v r
Adm≤ v (bra w r) = Bw w v × Adm≤ v r

up< : ∀ {a b u v} (r : a < b) → u ⊲ v → Adm< u r → Adm< v r
up< zero p x = tt
up< (suc r) p x = up< r p x
up< (lim n r) p x = up< r p x
up< (fst r) p x = up< r p x
up< (bra w r) p (y , x) = upB p y , up< r p x

up≤ : ∀ {a b u v} (r : a ≤ b) → u ⊲ v → Adm≤ u r → Adm≤ v r
up≤ self p x = tt
up≤ (suc r) p x = up≤ r p x
up≤ (lim n r) p x = up≤ r p x
up≤ (fst r) p x = up≤ r p x
up≤ (bra w r) p (y , x) = upB p y , up≤ r p x

-- 第一位置接在后面, 不加新的下标
<⊳ : ∀ {k a b} → k < a → a ⊳ b → k < b
<⊳ r self = r
<⊳ r (suc q) = suc (<⊳ r q)
<⊳ r (lim n q) = lim n (<⊳ r q)
<⊳ r (fst q) = fst (<⊳ r q)

adm<⊳ : ∀ {k a b v} (r : k < a) (q : a ⊳ b) → Adm< v r → Adm< v (<⊳ r q)
adm<⊳ r self x = x
adm<⊳ r (suc q) x = adm<⊳ r q x
adm<⊳ r (lim n q) x = adm<⊳ r q x
adm<⊳ r (fst q) x = adm<⊳ r q x

≤⊳ : ∀ {k a b} → k ≤ a → a ⊳ b → k ≤ b
≤⊳ r self = r
≤⊳ r (suc q) = suc (≤⊳ r q)
≤⊳ r (lim n q) = lim n (≤⊳ r q)
≤⊳ r (fst q) = fst (≤⊳ r q)

adm≤⊳ : ∀ {k a b v} (r : k ≤ a) (q : a ⊳ b) → Adm≤ v r → Adm≤ v (≤⊳ r q)
adm≤⊳ r self x = x
adm≤⊳ r (suc q) x = adm≤⊳ r q x
adm≤⊳ r (lim n q) x = adm≤⊳ r q x
adm≤⊳ r (fst q) x = adm≤⊳ r q x

-- 路径接路径
<≤ : ∀ {k a b} → k < a → a ≤ b → k < b
<≤ r self = r
<≤ r (suc q) = suc (<≤ r q)
<≤ r (lim n q) = lim n (<≤ r q)
<≤ r (fst q) = fst (<≤ r q)
<≤ r (bra w q) = bra w (<≤ r q)

adm<≤ : ∀ {k a b v} (r : k < a) (q : a ≤ b) → Adm< v r → Adm≤ v q → Adm< v (<≤ r q)
adm<≤ r self x y = x
adm<≤ r (suc q) x y = adm<≤ r q x y
adm<≤ r (lim n q) x y = adm<≤ r q x y
adm<≤ r (fst q) x y = adm<≤ r q x y
adm<≤ r (bra w q) x (p , y) = p , adm<≤ r q x y

≤≤ : ∀ {k a b} → k ≤ a → a ≤ b → k ≤ b
≤≤ r self = r
≤≤ r (suc q) = suc (≤≤ r q)
≤≤ r (lim n q) = lim n (≤≤ r q)
≤≤ r (fst q) = fst (≤≤ r q)
≤≤ r (bra w q) = bra w (≤≤ r q)

adm≤≤ : ∀ {k a b v} (r : k ≤ a) (q : a ≤ b) → Adm≤ v r → Adm≤ v q → Adm≤ v (≤≤ r q)
adm≤≤ r self x y = x
adm≤≤ r (suc q) x y = adm≤≤ r q x y
adm≤≤ r (lim n q) x y = adm≤≤ r q x y
adm≤≤ r (fst q) x y = adm≤≤ r q x y
adm≤≤ r (bra w q) x (p , y) = p , adm≤≤ r q x y

<→≤ : ∀ {a b} → a < b → a ≤ b
<→≤ zero = suc self
<→≤ (suc r) = suc (<→≤ r)
<→≤ (lim n r) = lim n (<→≤ r)
<→≤ (fst r) = fst (<→≤ r)
<→≤ (bra w r) = bra w (<→≤ r)

adm<→≤ : ∀ {a b v} (r : a < b) → Adm< v r → Adm≤ v (<→≤ r)
adm<→≤ zero x = tt
adm<→≤ (suc r) x = adm<→≤ r x
adm<→≤ (lim n r) x = adm<→≤ r x
adm<→≤ (fst r) x = adm<→≤ r x
adm<→≤ (bra w r) (p , x) = p , adm<→≤ r x

lg≤ : ∀ {a b v} (r : a ≤ b) → Gw v → Adm≤ v r → Legal b → Legal a
lg≤ self g x w = w
lg≤ (suc r) g x w = lg≤ r g x w
lg≤ (lim n r) g x (_ , w) = lg≤ r g x (w n)
lg≤ (fst r) g x (_ , _ , w , _) = lg≤ r g x w
lg≤ (bra u r) g (p , x) (_ , _ , _ , w) = lg≤ r g x (w u (gB g p))

steps : ∀ {f : ℕ → Lv} → (∀ n → f n ⊳ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊳ f m
steps s zero = s _
steps s (suc q) = ⊳-tr (steps s q) (s _)
```

## §3 比较

同一棵合法层的两个位置, 一个世界之下. 两条路径都走分支时, 世界给下标的字面可比 (`C.cmpF`), `Legal` 的 `dir` 给搬运. **没有比较两个任意的下标.** `tr`: 保留时新路径的下标是原路径的下标, 所以 `Adm` 能带过去.

```agda
data Rk {k L : Lv} (τ : A) (r : k < L) (t : Lv) : Set where
  keep : (s : k < t) → (∀ {v} → τ ⊲ v → Adm< v r → Adm< v s) → Rk τ r t
  rise : t ≤ k → Rk τ r t

mapK : ∀ {k L L′ τ t} {r : k < L} {r′ : k < L′} → (∀ {v} → τ ⊲ v → Adm< v r → Adm< v r′) → Rk τ r′ t → Rk τ r t
mapK f (keep s tr) = keep s (λ p x → tr p (f p x))
mapK f (rise q) = rise q

cmpN : ∀ {k t L v τ} (r : k < L) (q : t ≤ L) → Legal L → Gw v → Adm< v r → Adm≤ v q → Rk τ r t
cmpN r self w g ar aq = keep r (λ p x → x)
cmpN zero (suc q) w g ar aq = rise q
cmpN (suc r) (suc q) w g ar aq = mapK (λ p x → x) (cmpN r q w g ar aq)
cmpN (lim n r) (lim m q) (st , w) g ar aq with <ᴺ-dec n m
... | injᵃ n<m = mapK (λ p x → adm<⊳ r (steps st n<m) x) (cmpN (<⊳ r (steps st n<m)) q (w m) g (adm<⊳ r (steps st n<m) ar) aq)
... | injᵇ m<n = mapK (λ p x → x) (cmpN r (≤⊳ q (steps st m<n)) (w n) g ar (adm≤⊳ q (steps st m<n) aq))
... | injᶜ refl = mapK (λ p x → x) (cmpN r q (w n) g ar aq)
cmpN (fst r) (fst q) (_ , _ , wt , _) g ar aq = mapK (λ p x → x) (cmpN r q wt g ar aq)
cmpN (fst r) (bra y q) (tg , _ , _ , wg) g ar (py , aq) =
  mapK (λ p x → adm<⊳ r (tg y (gB g py)) x) (cmpN (<⊳ r (tg y (gB g py))) q (wg y (gB g py)) g (adm<⊳ r (tg y (gB g py)) ar) aq)
cmpN (bra x r) (fst q) (tg , _ , _ , wg) g (px , ar) aq =
  mapK (λ p u → proj₂ u) (cmpN r (≤⊳ q (tg x (gB g px))) (wg x (gB g px)) g ar (adm≤⊳ q (tg x (gB g px)) aq))
cmpN (bra x r) (bra y q) (_ , dir , _ , wg) g (px , ar) (py , aq) with C.cmpF (proj₁ px) (proj₁ py) (lgw g)
... | inj₁ y⊲x = mapK (λ p u → proj₂ u) (cmpN r (≤⊳ q (dir y x (gB g py) (gB g px) y⊲x)) (wg x (gB g px)) g ar (adm≤⊳ q (dir y x (gB g py) (gB g px) y⊲x) aq))
... | inj₂ x⊲y = mapK (λ p u → adm<⊳ r (dir x y (gB g px) (gB g py) x⊲y) (proj₂ u)) (cmpN (<⊳ r (dir x y (gB g px) (gB g py) x⊲y)) q (wg y (gB g py)) g (adm<⊳ r (dir x y (gB g px) (gB g py) x⊲y) ar) aq)

-- 一个第一位置对一个位置. 结果: 目标在它之下, 或者它是目标的第一位置 (不走分支)
data Rp (t a : Lv) (τ : A) : Set where
  tl : (q : t ≤ a) → Adm≤ τ q → Rp t a τ
  al : a ⊳ t → Rp t a τ

⊳→≤ : ∀ {a b} → a ⊳ b → a ≤ b
⊳→≤ self = self
⊳→≤ (suc p) = suc (⊳→≤ p)
⊳→≤ (lim n p) = lim n (⊳→≤ p)
⊳→≤ (fst p) = fst (⊳→≤ p)

adm⊳ : ∀ {a b v} (p : a ⊳ b) → Adm≤ v (⊳→≤ p)
adm⊳ self = tt
adm⊳ (suc p) = adm⊳ p
adm⊳ (lim n p) = adm⊳ p
adm⊳ (fst p) = adm⊳ p

cmp⊳ : ∀ {a t L v τ} (p : a ⊳ L) (q : t ≤ L) → Legal L → Gw v → τ ⊲ v → Adm≤ τ q → Rp t a τ
cmp⊳ self q w g τv aq = tl q aq
cmp⊳ p self w g τv aq = al p
cmp⊳ (suc p) (suc q) w g τv aq = cmp⊳ p q w g τv aq
cmp⊳ (lim n p) (lim m q) (st , w) g τv aq with <ᴺ-dec n m
... | injᵃ n<m = cmp⊳ (⊳-tr p (steps st n<m)) q (w m) g τv aq
... | injᵇ m<n = cmp⊳ p (≤⊳ q (steps st m<n)) (w n) g τv (adm≤⊳ q (steps st m<n) aq)
... | injᶜ refl = cmp⊳ p q (w n) g τv aq
cmp⊳ (fst p) (fst q) (_ , _ , wt , _) g τv aq = cmp⊳ p q wt g τv aq
cmp⊳ (fst p) (bra y q) (tg , _ , _ , wg) g τv (py , aq) =
  cmp⊳ (⊳-tr p (tg y (gB g (upB τv py)))) q (wg y (gB g (upB τv py))) g τv aq
```

## §4 数据树

`St a L`: 严格位置, 给节点的输入定类型. 懒嵌入 `oe` 只走一步 (`Stp`), 所以输入就是 `O a`. 世界是索引, `oc` 的分支在更高的世界上. `ow`: 把低世界的元素放到高世界, 折叠时看它自己的世界 (这就是 "规范世界").

```agda
data St (a : Lv) : Lv → Set where
  ss : ∀ {b} → a ≤ b → St a (ls b)
  sl : ∀ {f} n → a ≤ f n → St a (ll f)
  sf : ∀ {t g} → a ≤ t → St a (lc t g)
  sb : ∀ {t g} w → a ≤ g w → St a (lc t g)

data Stp : ∀ {a L} → St a L → Set where
  es : ∀ {b} → Stp {b} {ls b} (ss self)
  el : ∀ {f} n → Stp {f n} {ll f} (sl n self)
  ef : ∀ {t g} → Stp {t} {lc t g} (sf self)
  eb : ∀ {t g} w → Stp {g w} {lc t g} (sb w self)

AdmS : ∀ {a b} → A → St a b → Set
AdmS v (ss P) = Adm≤ v P
AdmS v (sl n P) = Adm≤ v P
AdmS v (sf P) = Adm≤ v P
AdmS v (sb w P) = Bw w v × Adm≤ v P

S→≤ : ∀ {a b} → St a b → a ≤ b
S→≤ (ss P) = suc P
S→≤ (sl n P) = lim n P
S→≤ (sf P) = fst P
S→≤ (sb w P) = bra w P

admS→ : ∀ {a b v} (R : St a b) → AdmS v R → Adm≤ v (S→≤ R)
admS→ (ss P) x = x
admS→ (sl n P) x = x
admS→ (sf P) x = x
admS→ (sb w P) x = x

<S : ∀ {a b} → a < b → St a b
<S zero = ss self
<S (suc r) = ss (<→≤ r)
<S (lim n r) = sl n (<→≤ r)
<S (fst r) = sf (<→≤ r)
<S (bra w r) = sb w (<→≤ r)

module _ (L : Lv) (V : ∀ {a} → St a L → A → Set) where
  data O₊ : A → Set where
    o0 : ∀ {u} → O₊ u
    os : ∀ {u} → O₊ u → O₊ u
    ol : ∀ {u} → (ℕ → O₊ u) → O₊ u
    oi : ∀ {u k} (r : k < L) → Adm< u r → (∀ {v} → u ⊲ v → Gw v → V (<S r) v → O₊ v) → O₊ u
    oc : ∀ {u} → O₊ u → (∀ {v} → u ⊲ v → Gw v → O₊ v) → O₊ u
    oe : ∀ {u a} {R : St a L} → Stp R → AdmS u R → V R u → O₊ u
    ow : ∀ {u v} → u ⊲ v → Gw u → O₊ u → O₊ v

O  : Lv → A → Set
Vs : ∀ L {a} → St a L → A → Set
Vc : ∀ b {a} → a ≤ b → A → Set
O L = O₊ L (Vs L)
Vs (ls b) (ss P) u = Vc b P u
Vs (ll f) (sl n P) u = Vc (f n) P u
Vs (lc t g) (sf P) u = Vc t P u
Vs (lc t g) (sb w P) u = Vc (g w) P u
Vc a self u = O a u
Vc (ls b) (suc P) u = Vc b P u
Vc (ll f) (lim n P) u = Vc (f n) P u
Vc (lc t g) (fst P) u = Vc t P u
Vc (lc t g) (bra w P) u = Vc (g w) P u

outC : ∀ {b a u} (P : a ≤ b) → Vc b P u → O a u
outC self x = x
outC (suc P) x = outC P x
outC (lim n P) x = outC P x
outC (fst P) x = outC P x
outC (bra w P) x = outC P x

inC : ∀ {b a u} (P : a ≤ b) → O a u → Vc b P u
inC self x = x
inC (suc P) x = inC P x
inC (lim n P) x = inC P x
inC (fst P) x = inC P x
inC (bra w P) x = inC P x

outS : ∀ {b a u} (R : St a b) → Vs b R u → O a u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x
outS (sf P) x = outC P x
outS (sb w P) x = outC P x

inS : ∀ {b a u} (R : St a b) → O a u → Vs b R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x
inS (sf P) x = inC P x
inS (sb w P) x = inC P x

out-inC : ∀ {b a u} (P : a ≤ b) (x : O a u) → outC P (inC P x) ≡ x
out-inC self x = refl
out-inC (suc P) x = out-inC P x
out-inC (lim n P) x = out-inC P x
out-inC (fst P) x = out-inC P x
out-inC (bra w P) x = out-inC P x

out-inS : ∀ {b a u} (R : St a b) (x : O a u) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x
out-inS (sf P) x = out-inC P x
out-inS (sb w P) x = out-inC P x

in-outC : ∀ {b a u} (P : a ≤ b) (x : Vc b P u) → inC P (outC P x) ≡ x
in-outC self x = refl
in-outC (suc P) x = in-outC P x
in-outC (lim n P) x = in-outC P x
in-outC (fst P) x = in-outC P x
in-outC (bra w P) x = in-outC P x

in-outS : ∀ {b a u} (R : St a b) (x : Vs b R u) → inS R (outS R x) ≡ x
in-outS (ss P) x = in-outC P x
in-outS (sl n P) x = in-outC P x
in-outS (sf P) x = in-outC P x
in-outS (sb w P) x = in-outC P x
```

## §5 $\Omega$, 加法

`Ω̇ L`: 闭的元素, 世界是最小的 $1$. 分支处带当前世界作证据. 懒嵌入只走一步.

```agda
Ω̇ : ∀ L → O L one
Ω̇ lz = os o0
Ω̇ (ls a) = oi zero tt (λ q g z → oe es tt z)
Ω̇ (ll f) = ol (λ n → oe (el n) tt (Ω̇ (f n)))
Ω̇ (lc t h) = oc (oe ef tt (Ω̇ t)) (λ {v} q g → oe (eb v) ((C.self , pos g) , tt) (ow (pos g) g₀ (Ω̇ (h v))))

Ω̇at : ∀ L {v} → Gw v → O L v
Ω̇at L g = ow (pos g) g₀ (Ω̇ L)

add : ∀ {L a u u′} → O L u → Gw u → (P : a ≤ L) → Adm≤ u P → u′ ⊲ u → O a u′ → O L u
add W gu P ap p o0 = W
add W gu P ap p (os x) = os (add W gu P ap p x)
add W gu P ap p (ol F) = ol (λ n → add W gu P ap p (F n))
add {L} W gu P ap p (oi r ar h) =
  oi (<≤ r P) (adm<≤ r P (up< r p ar) ap)
     (λ {v} q g y → add (ow q gu W) g P (up≤ P q ap) C.self (h (⊲-tr p q) g (inS (<S r) (outS (<S (<≤ r P)) y))))
add W gu P ap p (oc x h) =
  oc (add W gu P ap p x) (λ q g → add (ow q gu W) g P (up≤ P q ap) C.self (h (⊲-tr p q) g))
add W gu P ap p (oe es ar x) = add W gu (≤≤ (suc self) P) (adm≤≤ (suc self) P tt ap) p x
add W gu P ap p (oe (el n) ar x) = add W gu (≤≤ (lim n self) P) (adm≤≤ (lim n self) P tt ap) p x
add W gu P ap p (oe ef ar x) = add W gu (≤≤ (fst self) P) (adm≤≤ (fst self) P tt ap) p x
add W gu P ap p (oe (eb w) (bw , _) x) = add W gu (≤≤ (bra w self) P) (adm≤≤ (bra w self) P (upB p bw , tt) ap) p x
add W gu P ap p (ow p′ g′ x) = add W gu P ap (⊲-tr p′ p) x

rep : ∀ {L u} → O L u → Gw u → ℕ → O L u
rep y g zero = o0
rep y g (suc zero) = y
rep y g (suc (suc m)) = add (rep y g (suc m)) g self tt C.self y
```

## §6 第 0 层

```agda
ord : ∀ {u} → O lz u → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F) = FL.lim (λ n → ord (F n))
ord (oi () _ _)
ord (oc x h) = ord x
ord (oe () _ _)
ord (ow p g x) = ord x

em : ∀ {u} → Ord₀ → O lz u
em FL.zero = o0
em (FL.suc a) = os (em a)
em (FL.lim f) = ol (λ n → em (f n))
em (FL.limᵢ () f)
em (FL.up () x)
```

## §7 折叠

`Tg τ t L`: 目标 $t$ 与层 $L$ 的位置关系, 路径的下标在 $\tau$ 之下. **目标的世界 $\tau$ 只在一种情形变大:** 走进分支 $g(w)$ 时目标不低于这个闭包 (`eb` 碰上 `q = self` 或 `inj₂`), 这时路径上真的多了 $w$. `mx`: $\max(u,\tau)$.

```agda
Tg : A → Lv → Lv → Set
Tg τ t L = (Σ (t ≤ L) (Adm≤ τ)) ⊎ (Σ (L ≤ t) (Adm≤ τ))

rkT : ∀ {k t L v τ} (r : k < L) → Tg τ t L → Legal L → Gw v → τ ⊲ v → Adm< v r → Rk τ r t
rkT r (inj₁ (q , aq)) w g τv ar = cmpN r q w g ar (up≤ q τv aq)
rkT r (inj₂ (q , aq)) w g τv ar = keep (<≤ r q) (λ p x → adm<≤ r q x (up≤ q p aq))

-- 走第一位置
tgF : ∀ {a t L v τ} (p : a ⊳ L) → Tg τ t L → Legal L → Gw v → τ ⊲ v → Tg τ t a
tgF p (inj₁ (q , aq)) w g τv with cmp⊳ p q w g τv aq
... | tl q′ x = inj₁ (q′ , x)
... | al p′ = inj₂ (⊳→≤ p′ , adm⊳ p′)
tgF p (inj₂ (q , aq)) w g τv = inj₂ (≤≤ (⊳→≤ p) q , adm≤≤ (⊳→≤ p) q (adm⊳ p) aq)

-- 走分支: 目标可能多一个下标
record Tz (t a : Lv) (τ v : A) : Set where
  constructor tz
  field
    τ′  : A
    gτ′ : Gw τ′
    ττ  : τ ⊲ τ′
    τv′ : τ′ ⊲ v
    T′  : Tg τ′ t a

record Mx (u τ v : A) : Set where
  constructor mx′
  field
    m   : A
    gm  : Gw m
    um  : u ⊲ m
    τm  : τ ⊲ m
    mv  : m ⊲ v

mx : ∀ {u τ v} → Gw u → Gw τ → Gw v → u ⊲ v → τ ⊲ v → Mx u τ v
mx {u} {τ} gu gτ gv uv τv with C.cmpF uv τv (lgw gv)
... | inj₁ τ⊲u = mx′ u gu C.self τ⊲u uv
... | inj₂ u⊲τ = mx′ τ gτ u⊲τ C.self τv

tgB : ∀ {t₀ g₀′ t τ v} (w : A) → Tg τ t (lc t₀ g₀′) → Legal (lc t₀ g₀′) → Gw τ → Gw v → τ ⊲ v → Bw w v → Tz t (g₀′ w) τ v
tgB {τ = τ} w (inj₁ (self , aq)) wl gτ g τv bw with mx (gB g bw) gτ g (proj₁ bw) τv
... | mx′ m gm um τm mv = tz m gm τm mv (inj₂ (bra w self , ((um , proj₂ bw) , tt)))
tgB {τ = τ} w (inj₁ (fst q , aq)) (tg , _ , _ , _) gτ g τv bw =
  tz τ gτ C.self τv (inj₁ (≤⊳ q (tg w (gB g bw)) , adm≤⊳ q (tg w (gB g bw)) aq))
tgB {τ = τ} w (inj₁ (bra y q , (py , aq))) (_ , dir , _ , wg) gτ g τv bw with C.cmpF (proj₁ bw) (proj₁ (upB τv py)) (lgw g)
... | inj₁ y⊲w = tz τ gτ C.self τv (inj₁ (≤⊳ q (dir y w (gB g (upB τv py)) (gB g bw) y⊲w) , adm≤⊳ q (dir y w (gB g (upB τv py)) (gB g bw) y⊲w) aq))
... | inj₂ w⊲y with cmp⊳ (dir w y (gB g bw) (gB g (upB τv py)) w⊲y) q (wg y (gB g (upB τv py))) g τv aq
...   | tl q′ x = tz τ gτ C.self τv (inj₁ (q′ , x))
...   | al p′ = tz τ gτ C.self τv (inj₂ (⊳→≤ p′ , adm⊳ p′))
tgB {τ = τ} w (inj₂ (q , aq)) wl gτ g τv bw with mx (gB g bw) gτ g (proj₁ bw) τv
... | mx′ m gm um τm mv = tz m gm τm mv (inj₂ (bra w self ≤≤′ q , adm≤≤ (bra w self) q ((um , proj₂ bw) , tt) (up≤ q τm aq)))
  where
  _≤≤′_ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  _≤≤′_ = ≤≤

chainᵒ : ∀ {k u} → Gw u → (O k u → O k u) → ℕ → O k u
chainᵒ {k} g f zero = Ω̇at k g
chainᵒ g f (suc n) = f (chainᵒ g f n)

-- 第 0 层闭包的链点
record Ix (b : A) : Set where
  constructor ix
  field
    η  : A
    gη : Gw η
    up : b ⊲ η

step : ∀ {b} → Ix b → Ord₀ → Ix b
step (ix η g u) y = ix (next η y) (gnext y g) (⊲-tr u (next-⊲ η y))

ψ   : ∀ {L u} t τ → Gw τ → Tg τ t L → Legal L → Gw u → O L u → ∀ v → Gw v → u ⊲ v → τ ⊲ v → O t v
ψ⁰  : ∀ {L u} t τ → Gw τ → Tg τ t L → Legal L → Gw u → O L u → ∀ m → Gw m → u ⊲ m → τ ⊲ m → O t m

ψ t τ gτ T w gu x v gv uv τv with mx gu gτ gv uv τv
... | mx′ m gm um τm mv = ow mv gm (ψ⁰ t τ gτ T w gu x m gm um τm)

ψ⁰ t τ gτ T w gu o0 m gm um τm = Ω̇at t gm
ψ⁰ t τ gτ T w gu (os a) m gm um τm = ol (rep (ψ t τ gτ T w gu a m gm um τm) gm)
ψ⁰ t τ gτ T w gu (ol F) m gm um τm = ol (λ n → ψ t τ gτ T w gu (F n) m gm um τm)
ψ⁰ {L} t τ gτ T w gu (oi {k = k} r ar h) m gm um τm with rkT r T w gm τm (up< r um ar)
... | keep s tr = oi s (tr τm (up< r um ar))
      (λ {v} q g y → ψ t τ gτ T w g (h (⊲-tr um q) g (inS (<S r) (outS (<S s) y))) v g C.self (⊲-tr τm q))
... | rise _ = ol (λ n → ψ t τ gτ T w gm (h um gm (inS (<S r) (z n))) m gm C.self τm)
  where
  z : ℕ → O k m
  z = chainᵒ gm (λ z₁ → ψ k m gm (inj₁ (<→≤ r , adm<→≤ r (up< r um ar))) w gm (h um gm (inS (<S r) z₁)) m gm C.self C.self)
ψ⁰ lz τ gτ T w gu (oc x h) m gm um τm = ol ys′
  where
  y₀ : O lz m
  y₀ = ψ lz τ gτ T w gu x m gm um τm
  val : Ix m → Ord₀
  val (ix η g p) = ord (ψ lz τ gτ T w g (h (⊲-tr um p) g) η g C.self (⊲-tr τm p))
  ch : ℕ → Ix m
  ch zero = step (ix m gm C.self) (ord y₀)
  ch (suc n) = step (ch n) (val (ch n))
  ys′ : ℕ → O lz m
  ys′ zero = y₀
  ys′ (suc n) = em (val (ch n))
ψ⁰ (ls t) τ gτ T w gu (oc x h) m gm um τm =
  oc (ψ (ls t) τ gτ T w gu x m gm um τm) (λ {v} q g → ψ (ls t) τ gτ T w g (h (⊲-tr um q) g) v g C.self (⊲-tr τm q))
ψ⁰ (ll f) τ gτ T w gu (oc x h) m gm um τm =
  oc (ψ (ll f) τ gτ T w gu x m gm um τm) (λ {v} q g → ψ (ll f) τ gτ T w g (h (⊲-tr um q) g) v g C.self (⊲-tr τm q))
ψ⁰ (lc t₁ g₁) τ gτ T w gu (oc x h) m gm um τm =
  oc (ψ (lc t₁ g₁) τ gτ T w gu x m gm um τm) (λ {v} q g → ψ (lc t₁ g₁) τ gτ T w g (h (⊲-tr um q) g) v g C.self (⊲-tr τm q))
ψ⁰ t τ gτ T w gu (oe es ar x) m gm um τm = ψ t τ gτ (tgF (suc self) T w gm τm) w gu x m gm um τm
ψ⁰ t τ gτ T (st , w) gu (oe (el n) ar x) m gm um τm = ψ t τ gτ (tgF (lim n self) T (st , w) gm τm) (w n) gu x m gm um τm
ψ⁰ t τ gτ T w gu (oe ef ar x) m gm um τm = ψ t τ gτ (tgF (fst self) T w gm τm) (proj₁ (proj₂ (proj₂ w))) gu x m gm um τm
ψ⁰ t τ gτ T w gu (oe (eb w₁) (bw , _) x) m gm um τm with tgB w₁ T w gτ gm τm (upB um bw)
... | tz τ′ gτ′ ττ τv′ T′ = ψ t τ′ gτ′ T′ (proj₂ (proj₂ (proj₂ w)) w₁ (gB gm (upB um bw))) gu x m gm um τv′
ψ⁰ t τ gτ T w gu (ow p g′ x) m gm um τm = ψ t τ gτ T w g′ x m gm (⊲-tr p um) τm
```

## §8 闭项

```agda
z≤ : ∀ L → lz ≤ L
z≤ lz = self
z≤ (ls a) = suc (z≤ a)
z≤ (ll f) = lim 0 (z≤ (f 0))
z≤ (lc t g) = fst (z≤ t)

az≤ : ∀ {v} L → Adm≤ v (z≤ L)
az≤ lz = tt
az≤ (ls a) = az≤ a
az≤ (ll f) = az≤ (f 0)
az≤ (lc t g) = az≤ t

-- ψ₀(Ω_L): 对任何合法的 L, 全函数, 不带证书
Tψ : ∀ L → Legal L → Ord₀
Tψ L w = ord (ψ lz one g₀ (inj₁ (z≤ L , az≤ L)) w g₀ (Ω̇ L) one g₀ C.self C.self)
```
