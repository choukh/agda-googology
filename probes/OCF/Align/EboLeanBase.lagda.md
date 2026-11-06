# EboLeanBase: 序的句法事实, 标准形, $G_u$ 的成员关系, 可数项

> **记号侧验收工作**, 读记号, 不进成品. [EboLean](EboLean.lagda.md) 第 3 层的底座. 内容逐字取自 [Closure](Closure.lagda.md) §1 与 [Bachmann](Bachmann.lagda.md) §1 (`cmpᵀ` 与 `_<ᵀ_` 的对应、传递、无自反、`<sucT`), [WfFsnBase](WfFsnBase.lagda.md) (≤, 三歧, `InG`, 归纳的 `NF`, 门槛之下 $G$ 为空, `pred` 保标准形, 大小), 与 [Standard](Standard.lagda.md) 的 `Ctbl`. **删去的:** bot 的 Bool 标准形谓词 `isOTᵉ` (在 EBOI 里) 及其与 `NF` 的互转 (`toNF`, `fromNF`, `GB-from`, `GB-to`, `LeE`, 约 70 行): 这里直接以归纳的 `NF` 为标准形的定义, τ 保标准形也对 `NF` 证 ([EboLeanTau](EboLeanTau.lagda.md)). 两者等价是 WfFsnBase 的定理, 本文不再需要.
>
> 这些对一切项成立 (字典序), 除标明要 `NF` 的. `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanBase where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-suc; +-assoc; +-comm; ≤-refl; n≤1+n)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (pred-suc; <-sucT)
```

## §1 `cmpᵀ` 与 $<^\mathsf T$

```agda
cmpᵀ-refl : ∀ a → cmpᵀ a a ≡ eq
cmpᴾ-refl : ∀ x → cmpᴾ x x ≡ eq
cmpᵀ-refl []       = refl
cmpᵀ-refl (x ∷ xs) rewrite cmpᴾ-refl x = cmpᵀ-refl xs
cmpᴾ-refl (ψ u a) rewrite cmpᵀ-refl u = cmpᵀ-refl a

<→lt  : ∀ {a b} → a <ᵀ b → cmpᵀ a b ≡ lt
<ᴾ→lt : ∀ {x y} → x <ᴾ y → cmpᴾ x y ≡ lt
<→lt []< = refl
<→lt (hd< p) rewrite <ᴾ→lt p = refl
<→lt (tl< {x = x} p) rewrite cmpᴾ-refl x = <→lt p
<ᴾ→lt (lv< p) rewrite <→lt p = refl
<ᴾ→lt (ar< {u = u} p) rewrite cmpᵀ-refl u = <→lt p

lt→<  : ∀ a b → cmpᵀ a b ≡ lt → a <ᵀ b
lt→<ᴾ : ∀ x y → cmpᴾ x y ≡ lt → x <ᴾ y
eq→≡  : ∀ a b → cmpᵀ a b ≡ eq → a ≡ b
eq→≡ᴾ : ∀ x y → cmpᴾ x y ≡ eq → x ≡ y
lt→< [] [] ()
lt→< [] (y ∷ ys) e = []<
lt→< (x ∷ xs) [] ()
lt→< (x ∷ xs) (y ∷ ys) e with cmpᴾ x y in ex
... | lt = hd< (lt→<ᴾ x y ex)
... | eq rewrite eq→≡ᴾ x y ex = tl< (lt→< xs ys e)
lt→<ᴾ (ψ u a) (ψ v b) e with cmpᵀ u v in eu
... | lt = lv< (lt→< u v eu)
... | eq rewrite eq→≡ u v eu = ar< (lt→< a b e)
eq→≡ [] [] e = refl
eq→≡ [] (y ∷ ys) ()
eq→≡ (x ∷ xs) [] ()
eq→≡ (x ∷ xs) (y ∷ ys) e with cmpᴾ x y in ex
... | eq rewrite eq→≡ᴾ x y ex | eq→≡ xs ys e = refl
eq→≡ᴾ (ψ u a) (ψ v b) e with cmpᵀ u v in eu
... | eq rewrite eq→≡ u v eu | eq→≡ a b e = refl

gt→<  : ∀ a b → cmpᵀ a b ≡ gt → b <ᵀ a
gt→<ᴾ : ∀ x y → cmpᴾ x y ≡ gt → y <ᴾ x
gt→< [] [] ()
gt→< [] (y ∷ ys) ()
gt→< (x ∷ xs) [] e = []<
gt→< (x ∷ xs) (y ∷ ys) e with cmpᴾ x y in ex
... | gt = hd< (gt→<ᴾ x y ex)
... | eq rewrite eq→≡ᴾ x y ex = tl< (gt→< xs ys e)
gt→<ᴾ (ψ u a) (ψ v b) e with cmpᵀ u v in eu
... | gt = lv< (gt→< u v eu)
... | eq rewrite eq→≡ u v eu = ar< (gt→< a b e)

<ᵀ-trans : ∀ {a b c} → a <ᵀ b → b <ᵀ c → a <ᵀ c
<ᴾ-trans : ∀ {x y z} → x <ᴾ y → y <ᴾ z → x <ᴾ z
<ᵀ-trans []< (hd< q) = []<
<ᵀ-trans []< (tl< q) = []<
<ᵀ-trans (hd< p) (hd< q) = hd< (<ᴾ-trans p q)
<ᵀ-trans (hd< p) (tl< q) = hd< p
<ᵀ-trans (tl< p) (hd< q) = hd< q
<ᵀ-trans (tl< p) (tl< q) = tl< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (lv< q) = lv< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (ar< q) = lv< p
<ᴾ-trans (ar< p) (lv< q) = lv< q
<ᴾ-trans (ar< p) (ar< q) = ar< (<ᵀ-trans p q)

<ᵀ-irrefl : ∀ {a} → a <ᵀ a → ⊥
<ᵀ-irrefl {a} p with trans (sym (<→lt p)) (cmpᵀ-refl a)
... | ()

<ᵀ-asym : ∀ {a b} → a <ᵀ b → b <ᵀ a → ⊥
<ᵀ-asym p q = <ᵀ-irrefl (<ᵀ-trans p q)

Pen : Cmp → Set
Pen m = (m ≡ lt) ⊎ (m ≡ eq)

<sucT : ∀ {a} ν → a <ᵀ sucT ν → (a <ᵀ ν) ⊎ (a ≡ ν)
<sucT [] []< = inj₂ refl
<sucT [] (hd< (lv< ()))
<sucT [] (hd< (ar< ()))
<sucT [] (tl< ())
<sucT (y ∷ ys) []< = inj₁ []<
<sucT (y ∷ ys) (hd< p) = inj₁ (hd< p)
<sucT (y ∷ ys) (tl< p) with <sucT ys p
... | inj₁ q = inj₁ (tl< q)
... | inj₂ refl = inj₂ refl

gt→≤ : ∀ ν w → cmpᵀ (sucT ν) w ≡ gt → (w <ᵀ ν) ⊎ (w ≡ ν)
gt→≤ ν w e = <sucT ν (gt→< (sucT ν) w e)

cofA≢c1 : ∀ u c → cofA u c ≡ c1 → ⊥
cofA≢c1 u c0 ()
cofA≢c1 u c1 ()
cofA≢c1 u cω ()
cofA≢c1 u (cΩ μ) e = go (cmpᵀ (sucT μ) u) e where
  go : ∀ m → cofψ₊ u μ m ≡ c1 → ⊥
  go lt ()
  go eq ()
  go gt ()
```

## §2 ≤, 三歧, $G_u$, 标准形, 大小 (取自 WfFsnBase)

`InG u z t`: $z\in G_u(t)$ (Buchholz: 沿下标 $\ge u$ 的 ψ-节点收集参数, 穿进下标与参数). `GB u t Z`: $G_u(t)<Z$. `NF`: 降序和, 每个主项 $\psi_u(a)$ 有 $u, a$ 标准且 $G_u(a)<a$.

```agda
infix 4 _≤ᵀ_ _≤ᴾ_

_≤ᵀ_ : T → T → Set
a ≤ᵀ b = (a <ᵀ b) ⊎ (a ≡ b)

_≤ᴾ_ : PT → PT → Set
x ≤ᴾ y = (x <ᴾ y) ⊎ (x ≡ y)

≤-trans′ : ∀ {a b c} → a ≤ᵀ b → b ≤ᵀ c → a ≤ᵀ c
≤-trans′ (inj₁ p) (inj₁ q)    = inj₁ (<ᵀ-trans p q)
≤-trans′ (inj₁ p) (inj₂ refl) = inj₁ p
≤-trans′ (inj₂ refl) q        = q

≤-< : ∀ {a b c} → a ≤ᵀ b → b <ᵀ c → a <ᵀ c
≤-< (inj₁ p) q    = <ᵀ-trans p q
≤-< (inj₂ refl) q = q

<-≤ : ∀ {a b c} → a <ᵀ b → b ≤ᵀ c → a <ᵀ c
<-≤ p (inj₁ q)    = <ᵀ-trans p q
<-≤ p (inj₂ refl) = p

≤ᴾ-trans : ∀ {x y z} → x ≤ᴾ y → y ≤ᴾ z → x ≤ᴾ z
≤ᴾ-trans (inj₁ p) (inj₁ q)    = inj₁ (<ᴾ-trans p q)
≤ᴾ-trans (inj₁ p) (inj₂ refl) = inj₁ p
≤ᴾ-trans (inj₂ refl) q        = q

<ᴾ-irrefl : ∀ {x} → x <ᴾ x → ⊥
<ᴾ-irrefl p = <ᵀ-irrefl {_ ∷ []} (hd< p)

≤¬> : ∀ {a b} → a ≤ᵀ b → b <ᵀ a → ⊥
≤¬> (inj₁ p) q    = <ᵀ-asym p q
≤¬> (inj₂ refl) q = <ᵀ-irrefl q


tri : ∀ a b → (a <ᵀ b) ⊎ (a ≡ b) ⊎ (b <ᵀ a)
tri a b = go (cmpᵀ a b) refl where
  go : ∀ m → cmpᵀ a b ≡ m → (a <ᵀ b) ⊎ (a ≡ b) ⊎ (b <ᵀ a)
  go lt e = inj₁ (lt→< a b e)
  go eq e = inj₂ (inj₁ (eq→≡ a b e))
  go gt e = inj₂ (inj₂ (gt→< a b e))

dec≤ : ∀ a b → (a ≤ᵀ b) ⊎ (b <ᵀ a)
dec≤ a b with tri a b
... | inj₁ p        = inj₁ (inj₁ p)
... | inj₂ (inj₁ e) = inj₁ (inj₂ e)
... | inj₂ (inj₂ p) = inj₂ p


≤[] : ∀ {a} → a ≤ᵀ [] → a ≡ []
≤[] (inj₁ ())
≤[] (inj₂ e) = e

Pen→≤ : ∀ a b → Pen (cmpᵀ a b) → a ≤ᵀ b
Pen→≤ a b (inj₁ e) = inj₁ (lt→< a b e)
Pen→≤ a b (inj₂ e) = inj₂ (eq→≡ a b e)

idx< : ∀ v a vs → v <ᵀ (ψ v a ∷ vs)
idx< [] a vs = []<
idx< (ψ v′ a′ ∷ vs′) a vs = hd< (lv< (idx< v′ a′ vs′))

sub≤ : ∀ {w a w′ a′} → ψ w′ a′ ≤ᴾ ψ w a → w′ ≤ᵀ w
sub≤ (inj₁ (lv< p)) = inj₁ p
sub≤ (inj₁ (ar< _)) = inj₂ refl
sub≤ (inj₂ refl)    = inj₂ refl

data InG  (u : T) : T → T → Set
data InGP (u : T) : T → PT → Set

data InG u where
  gp  : ∀ {z x xs} → InGP u z x → InG u z (x ∷ xs)
  gtl : ∀ {z x xs} → InG u z xs → InG u z (x ∷ xs)

data InGP u where
  gh : ∀ {w c}   → u ≤ᵀ w → InGP u c (ψ w c)
  gw : ∀ {w c z} → u ≤ᵀ w → InG u z w → InGP u z (ψ w c)
  gc : ∀ {w c z} → u ≤ᵀ w → InG u z c → InGP u z (ψ w c)

GB : T → T → T → Set
GB u t Z = ∀ {z} → InG u z t → z <ᵀ Z

GB[] : ∀ {u Z} → GB u [] Z
GB[] ()

G-mono  : ∀ {u u′ z t} → u ≤ᵀ u′ → InG u′ z t → InG u z t
GP-mono : ∀ {u u′ z x} → u ≤ᵀ u′ → InGP u′ z x → InGP u z x
G-mono l (gp p)  = gp (GP-mono l p)
G-mono l (gtl p) = gtl (G-mono l p)
GP-mono l (gh m)   = gh (≤-trans′ l m)
GP-mono l (gw m p) = gw (≤-trans′ l m) (G-mono l p)
GP-mono l (gc m p) = gc (≤-trans′ l m) (G-mono l p)

G-++ˡ : ∀ {u z} p q → InG u z p → InG u z (p ++ q)
G-++ˡ (x ∷ p) q (gp h)  = gp h
G-++ˡ (x ∷ p) q (gtl h) = gtl (G-++ˡ p q h)




G-sucT : ∀ {u z} ν → InG u z ν → InG u z (sucT ν)
G-sucT ν h = G-++ˡ ν (𝟏 ∷ []) h


G-rep : ∀ {u z x} n → InG u z (replicate n x) → InG u z (x ∷ [])
G-rep (suc n) (gp h)  = gp h
G-rep (suc n) (gtl h) = G-rep n h

HdLe : PT → T → Set
HdLe x []      = ⊤
HdLe x (y ∷ _) = y ≤ᴾ x

data NF  : T → Set
data NFP : PT → Set

data NF where
  n[] : NF []
  n∷  : ∀ {x xs} → NFP x → HdLe x xs → NF xs → NF (x ∷ xs)

data NFP where
  nψ : ∀ {u a} → NF u → NF a → GB u a a → NFP (ψ u a)

nf-hd : ∀ {x xs} → NF (x ∷ xs) → NFP x
nf-hd (n∷ p _ _) = p

nf-tl : ∀ {x xs} → NF (x ∷ xs) → NF xs
nf-tl (n∷ _ _ n) = n

nf-le : ∀ {x xs} → NF (x ∷ xs) → HdLe x xs
nf-le (n∷ _ h _) = h

nfp-u : ∀ {u a} → NFP (ψ u a) → NF u
nfp-u (nψ n _ _) = n

nfp-a : ∀ {u a} → NFP (ψ u a) → NF a
nfp-a (nψ _ n _) = n

nfp-g : ∀ {u a} → NFP (ψ u a) → GB u a a
nfp-g (nψ _ _ g) = g

nf-ψ : ∀ {u a} → NF u → NF a → GB u a a → NF (ψ u a ∷ [])
nf-ψ nu na g = n∷ (nψ nu na g) tt n[]

nf-Ω : ∀ {u} → NF u → NF (ψ u [] ∷ [])
nf-Ω nu = nf-ψ nu n[] GB[]

tail< : ∀ x t → HdLe x t → NF t → t <ᵀ (x ∷ t)
tail< x [] _ _ = []<
tail< x (y ∷ ys) (inj₁ p) _ = hd< p
tail< x (y ∷ ys) (inj₂ refl) n = tl< (tail< y ys (nf-le n) (nf-tl n))

hd-lt : ∀ {x t y} → HdLe x t → y <ᵀ t → HdLe x y
hd-lt {y = []} _ _ = tt
hd-lt {t = z ∷ zs} {y = y′ ∷ ys} h (hd< p) = ≤ᴾ-trans (inj₁ p) h
hd-lt {t = z ∷ zs} {y = y′ ∷ ys} h (tl< p) = h

noG∷ : ∀ {u w a xs z} → NF (ψ w a ∷ xs) → w <ᵀ u → InG u z (ψ w a ∷ xs) → ⊥
noG∷ _ p (gp (gh l))   = ≤¬> l p
noG∷ _ p (gp (gw l _)) = ≤¬> l p
noG∷ _ p (gp (gc l _)) = ≤¬> l p
noG∷ {xs = ψ w′ a′ ∷ xs′} n p (gtl h) = noG∷ (nf-tl n) (≤-< (sub≤ (nf-le n)) p) h

noG-le : ∀ {u X z} → NF X → X ≤ᵀ u → InG u z X → ⊥
noG-le {X = ψ w a ∷ xs} n l h = noG∷ n (<-≤ (idx< w a xs) l) h

noG-Ω : ∀ {u Y z} → NF Y → Y <ᵀ (ψ u [] ∷ []) → InG u z Y → ⊥
noG-Ω {Y = ψ w a ∷ xs} n (hd< (lv< p)) h = noG∷ n p h
noG-Ω {Y = ψ w a ∷ xs} n (hd< (ar< ())) h
noG-Ω {Y = ψ w a ∷ xs} n (tl< ()) h

hd-pred : ∀ {x} y ys → HdLe x (y ∷ ys) → HdLe x (pred (y ∷ ys))
hd-pred y (z ∷ zs) h = h
hd-pred 𝟏 [] h = tt
hd-pred (ψ [] (c ∷ cs)) [] h = h
hd-pred (ψ (w ∷ ws) a) [] h = h

nf-pred : ∀ {t} → NF t → NF (pred t)
nf-pred n[] = n[]
nf-pred (n∷ {xs = y ∷ ys} p h n) = n∷ p (hd-pred y ys h) (nf-pred n)
nf-pred (n∷ {x = 𝟏} {xs = []} p h n) = n[]
nf-pred (n∷ {x = ψ [] (c ∷ cs)} {xs = []} p h n) = n∷ p h n
nf-pred (n∷ {x = ψ (w ∷ ws) a} {xs = []} p h n) = n∷ p h n

nf-rep : ∀ {x} → NFP x → ∀ n → NF (replicate n x)
nf-rep p zero = n[]
nf-rep p (suc zero) = n∷ p tt n[]
nf-rep p (suc (suc n)) = n∷ p (inj₂ refl) (nf-rep p (suc n))

size  : T → ℕ
sizeP : PT → ℕ
size [] = 0
size (x ∷ xs) = sizeP x + size xs
sizeP (ψ u a) = suc (size u + size a)

size-sucT : ∀ ν → size (sucT ν) ≡ suc (size ν)
size-sucT [] = refl
size-sucT (x ∷ xs) = trans (cong (sizeP x +_) (size-sucT xs)) (+-suc (sizeP x) (size xs))

G-size  : ∀ {u z t} → InG u z t → size z < size t
GP-size : ∀ {u z x} → InGP u z x → size z < sizeP x
G-size {t = x ∷ xs} (gp p)  = ≤-trans (GP-size p) (m≤m+n (sizeP x) (size xs))
G-size {t = x ∷ xs} (gtl p) = ≤-trans (G-size p) (m≤n+m (size xs) (sizeP x))
GP-size {x = ψ w c} (gh l)   = s≤s (m≤n+m (size c) (size w))
GP-size {x = ψ w c} (gw l p) = ≤-trans (G-size p) (≤-trans (n≤1+n (size w)) (s≤s (m≤m+n (size w) (size c))))
GP-size {x = ψ w c} (gc l p) = ≤-trans (G-size p) (≤-trans (n≤1+n (size c)) (s≤s (m≤n+m (size c) (size w))))
```

## §3 可数项

`Ctbl t`: 和的每一项都是 $\psi_0(\cdot)$.

```agda
data Ctbl : T → Set where
  c[] : Ctbl []
  c∷  : ∀ {a xs} → Ctbl xs → Ctbl (ψ [] a ∷ xs)

Ctbl-pred : ∀ {u} → Ctbl u → Ctbl (pred u)
Ctbl-pred c[] = c[]
Ctbl-pred (c∷ {a = []} c[]) = c[]
Ctbl-pred (c∷ {a = y ∷ ys} c[]) = c∷ c[]
Ctbl-pred (c∷ (c∷ c)) = c∷ (Ctbl-pred (c∷ c))
```
