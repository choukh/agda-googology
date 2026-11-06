# WfFsnBase: 封闭性证明的基础 (序、$G$ 的成员关系、归纳的标准形)

> **记号侧验收工作**, 不是最终定义, 不进成品. 读记号 (EBO 的项、序、bot 的标准形谓词 `isOTᵉ`). 是 [WfFsn](WfFsn.lagda.md) (`cl-fsn`: EBO 标准形对基本列封闭) 的第一段. 蓝本是 koteitan/googology-lean `ExBuchholz` (`6da2de5`, MIT, 只读) 的 `Closure.lean`; 本文件对应它的 `Order`、`Std`、`Sum` 里的小引理, 但都在我方定义 (`OCF.Align.EBO`) 上重写.
>
> 内容: 非严格序 `_≤ᵀ_` 与三歧 `tri`; $G_u(t)$ 的成员关系 `InG` (Lean 的 `G` 是列表, 这里是归纳关系); 归纳的标准形 `NF` 与 Bool 谓词 `isOTᵉ` 的两向转换 (`toNF`, `fromNF`); "下标在门槛之下则 $G$ 为空" (`noG-le`, `noG-Ω`); `pred` 保标准形; 项的大小与 `G-size`. 全部是编译过的定理, 对一切项 (要标准形的地方写在类型里).
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsnBase where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-suc; +-assoc; +-comm; ≤-refl; n≤1+n)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import OCF.Align.EBO as E
open E using (T; PT; ψ; 𝟏; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<; Cmp; lt; eq; gt; cmpᵀ; cmpᴾ;
              cof; cofP; cofA; cofψ0; cofψ₊; c0; c1; cω; cΩ; pred; sucT; Ωt; Ωs; natT)
open import OCF.Align.EBOI using (isOTᵉ; isOTᵉᴾ; descᵉ; Gᵉ; Gᵉᴾ; leEᵇ; ltEᵇ; leᵇ; ltᵇ)
open import OCF.Align.Closure using (cmpᵀ-refl; cmpᴾ-refl; <→lt; <ᴾ→lt; lt→<; lt→<ᴾ; eq→≡; eq→≡ᴾ;
                                     <ᵀ-trans; <ᴾ-trans; Pen)
open import OCF.Align.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; gt→<; gt→<ᴾ; <sucT)
```

## §1 序

$\le$ 是 "$<$ 或 $=$". 三歧经 `cmpᵀ` 读出. 这些对一切项成立 (字典序), 不要标准形.

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

≤ᴾ¬> : ∀ {x y} → x ≤ᴾ y → y <ᴾ x → ⊥
≤ᴾ¬> (inj₁ p) q    = <ᴾ-irrefl (<ᴾ-trans p q)
≤ᴾ¬> (inj₂ refl) q = <ᴾ-irrefl q

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

[]≤ : ∀ a → [] ≤ᵀ a
[]≤ []       = inj₂ refl
[]≤ (_ ∷ _)  = inj₁ []<

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
```

## §2 $G_u(t)$ 的成员关系

`InG u z t`: $z\in G_u(t)$. 与 bot 的 `Gᵉ` 与 Lean 的 `G` 同义: 沿和走 (`gtl`), 在下标 $w\ge u$ 的主项 $\psi_w(c)$ 处收集 $c$ (`gh`) 并钻进 $w$ (`gw`) 与 $c$ (`gc`); 下标 $<u$ 的主项挡住一切. `GB u t Z`: $G_u(t)<Z$, 即 bot 的 `Gᵉ u t Z ≡ true` (§3 `GB-from`, `GB-to`).

```agda
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
```

**$G$ 的门槛单调** (Lean `G_subset_of_le`): $u\le u'$ 则 $G_{u'}(t)\subseteq G_u(t)$. **对和可加** (Lean `G_addT`).

```agda
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

G-++ʳ : ∀ {u z} p q → InG u z q → InG u z (p ++ q)
G-++ʳ [] q h = h
G-++ʳ (x ∷ p) q h = gtl (G-++ʳ p q h)

G-++⁻ : ∀ {u z} p q → InG u z (p ++ q) → InG u z p ⊎ InG u z q
G-++⁻ [] q h = inj₂ h
G-++⁻ (x ∷ p) q (gp h)  = inj₁ (gp h)
G-++⁻ (x ∷ p) q (gtl h) with G-++⁻ p q h
... | inj₁ h′ = inj₁ (gtl h′)
... | inj₂ h′ = inj₂ h′
```

$G_u(\nu+1)=G_u(\nu)\cup G_u(1)$ 且 $G_u(1)\subseteq\{0\}$; $G$ 在重复和 $\psi_A(B)\cdot n$ 上只看到 $\psi_A(B)$ 看到的.

```agda
G-1 : ∀ {u z} → InG u z (𝟏 ∷ []) → z ≡ []
G-1 (gp (gh _))    = refl
G-1 (gp (gw _ ()))
G-1 (gp (gc _ ()))
G-1 (gtl ())

G-sucT : ∀ {u z} ν → InG u z ν → InG u z (sucT ν)
G-sucT ν h = G-++ˡ ν (𝟏 ∷ []) h

G-sucT⁻ : ∀ {u z} ν → InG u z (sucT ν) → InG u z ν ⊎ (z ≡ [])
G-sucT⁻ ν h with G-++⁻ ν (𝟏 ∷ []) h
... | inj₁ h′ = inj₁ h′
... | inj₂ h′ = inj₂ (G-1 h′)

G-rep : ∀ {u z x} n → InG u z (replicate n x) → InG u z (x ∷ [])
G-rep (suc n) (gp h)  = gp h
G-rep (suc n) (gtl h) = G-rep n h
```

## §3 标准形

`NF`: 和的各项非增 (`HdLe x xs`: 尾巴的首项 $\le x$), 每个主项 $\psi_u(a)$ 的 $u$, $a$ 标准且 $G_u(a)<a$. 这是 bot 的 `isOTᵉ` 的归纳形式 (Lean 的 `isOT` 同), 两向转换见下.

```agda
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
```

**与 `isOTᵉ` 的转换.** 布尔一侧: `leEᵇ X w` 为真恰好当 $X\le w$ (`le?`, 视图连同布尔值).

```agda
∧-intro : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

∧₁ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
∧₁ {a = true} _ = refl

∧₂ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
∧₂ {a = true} h = h

ift : ∀ {b x y} → b ≡ true → (if b then x else y) ≡ true → x ≡ true
ift {b = true} _ h = h

ifi : ∀ {b x y} → b ≡ true → x ≡ true → (if b then x else y) ≡ true
ifi {b = true} _ h = h

iff : ∀ {b x} → b ≡ false → (if b then x else true) ≡ true
iff {b = false} _ = refl

data LeE (a b : T) : Set where
  yes : leEᵇ a b ≡ true  → a ≤ᵀ b → LeE a b
  no  : leEᵇ a b ≡ false → b <ᵀ a → LeE a b

le? : ∀ a b → LeE a b
le? a b = go (cmpᵀ a b) refl where
  go : ∀ m → cmpᵀ a b ≡ m → LeE a b
  go lt e = yes (cong leᵇ e) (inj₁ (lt→< a b e))
  go eq e = yes (cong leᵇ e) (inj₂ (eq→≡ a b e))
  go gt e = no  (cong leᵇ e) (gt→< a b e)

le→b : ∀ {a b} → a ≤ᵀ b → leEᵇ a b ≡ true
le→b (inj₁ p)            = cong leᵇ (<→lt p)
le→b {a} (inj₂ refl)     = cong leᵇ (cmpᵀ-refl a)

lt→b : ∀ {a b} → a <ᵀ b → ltEᵇ a b ≡ true
lt→b p = cong ltᵇ (<→lt p)

b→lt : ∀ a b → ltEᵇ a b ≡ true → a <ᵀ b
b→lt a b h = go (cmpᵀ a b) refl h where
  go : ∀ m → cmpᵀ a b ≡ m → ltᵇ m ≡ true → a <ᵀ b
  go lt e _ = lt→< a b e
  go eq e ()
  go gt e ()

desc→ : ∀ x y → leᵇ (cmpᴾ y x) ≡ true → y ≤ᴾ x
desc→ x y d = go (cmpᴾ y x) refl d where
  go : ∀ m → cmpᴾ y x ≡ m → leᵇ m ≡ true → y ≤ᴾ x
  go lt e _ = inj₁ (lt→<ᴾ y x e)
  go eq e _ = inj₂ (eq→≡ᴾ y x e)
  go gt e ()

→desc : ∀ x y → y ≤ᴾ x → leᵇ (cmpᴾ y x) ≡ true
→desc x y (inj₁ p)    = cong leᵇ (<ᴾ→lt p)
→desc x y (inj₂ refl) = cong leᵇ (cmpᴾ-refl x)
```

```agda
GB-from  : ∀ X Y Z → Gᵉ X Y Z ≡ true → GB X Y Z
GBP-from : ∀ X y Z → Gᵉᴾ X y Z ≡ true → ∀ {z} → InGP X z y → z <ᵀ Z
GB-from X (y ∷ ys) Z h (gp p)  = GBP-from X y Z (∧₁ h) p
GB-from X (y ∷ ys) Z h (gtl p) = GB-from X ys Z (∧₂ h) p
GBP-from X (ψ w c) Z h (gh l)   = b→lt c Z (∧₁ (ift (le→b l) h))
GBP-from X (ψ w c) Z h (gw l p) = GB-from X w Z (∧₁ (∧₂ (ift (le→b l) h))) p
GBP-from X (ψ w c) Z h (gc l p) = GB-from X c Z (∧₂ (∧₂ (ift (le→b l) h))) p

GB-to   : ∀ X Y Z → GB X Y Z → Gᵉ X Y Z ≡ true
GBP-to  : ∀ X w c Z → (∀ {z} → InGP X z (ψ w c) → z <ᵀ Z) → LeE X w → Gᵉᴾ X (ψ w c) Z ≡ true
GB-to X [] Z g = refl
GB-to X (ψ w c ∷ ys) Z g =
  ∧-intro (GBP-to X w c Z (λ p → g (gp p)) (le? X w)) (GB-to X ys Z (λ p → g (gtl p)))
GBP-to X w c Z g (yes e l) =
  ifi e (∧-intro (lt→b (g (gh l)))
          (∧-intro (GB-to X w Z (λ p → g (gw l p))) (GB-to X c Z (λ p → g (gc l p)))))
GBP-to X w c Z g (no e _) = iff e
```

```agda
toNF  : ∀ t → isOTᵉ t ≡ true → NF t
toNFP : ∀ x → isOTᵉᴾ x ≡ true → NFP x
toHd  : ∀ x xs → descᵉ x xs ≡ true → HdLe x xs
toNF [] _ = n[]
toNF (x ∷ xs) h = n∷ (toNFP x (∧₁ h)) (toHd x xs (∧₁ (∧₂ h))) (toNF xs (∧₂ (∧₂ h)))
toNFP (ψ u []) h = nψ (toNF u h) n[] GB[]
toNFP (ψ u (y ∷ ys)) h =
  nψ (toNF u (∧₁ h)) (toNF (y ∷ ys) (∧₁ (∧₂ h))) (GB-from u (y ∷ ys) (y ∷ ys) (∧₂ (∧₂ h)))
toHd x [] _ = tt
toHd x (y ∷ ys) d = desc→ x y d

fromNF  : ∀ {t} → NF t → isOTᵉ t ≡ true
fromNFP : ∀ {x} → NFP x → isOTᵉᴾ x ≡ true
fromHd  : ∀ x xs → HdLe x xs → descᵉ x xs ≡ true
fromNF n[] = refl
fromNF (n∷ {x} {xs} px hx nxs) = ∧-intro (fromNFP px) (∧-intro (fromHd x xs hx) (fromNF nxs))
fromNFP (nψ {a = []} nu _ _) = fromNF nu
fromNFP (nψ {u} {y ∷ ys} nu na g) =
  ∧-intro (fromNF nu) (∧-intro (fromNF na) (GB-to u (y ∷ ys) (y ∷ ys) g))
fromHd x [] _ = refl
fromHd x (y ∷ ys) h = →desc x y h
```

**拆标准形.**

```agda
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
```

**和的尾巴、首项沿 $<$ 下传** (Lean `tail_lt`, `headLe_of_lt`). 标准和的尾巴小于整个和; 若 $y<t$ 且 $t$ 的首项 $\le x$ 则 $y$ 的首项 $\le x$ (后者对一切项).

```agda
tail< : ∀ x t → HdLe x t → NF t → t <ᵀ (x ∷ t)
tail< x [] _ _ = []<
tail< x (y ∷ ys) (inj₁ p) _ = hd< p
tail< x (y ∷ ys) (inj₂ refl) n = tl< (tail< y ys (nf-le n) (nf-tl n))

hd-lt : ∀ {x t y} → HdLe x t → y <ᵀ t → HdLe x y
hd-lt {y = []} _ _ = tt
hd-lt {t = z ∷ zs} {y = y′ ∷ ys} h (hd< p) = ≤ᴾ-trans (inj₁ p) h
hd-lt {t = z ∷ zs} {y = y′ ∷ ys} h (tl< p) = h
```

**门槛之下 $G$ 为空** (Lean `G_eq_nil_of_le`, `G_eq_nil_of_lt_psi`). 标准和 $Y$ 的首项下标 $w<u$ 时, 由降序每一项的下标都 $<u$, 所以 $G_u(Y)=\varnothing$. 两种用法: $X\le u$ (首项下标 $<X$, `idx<`) 与 $Y<\Omega_u$.

```agda
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
```

**`pred` 与重复和保标准形.** `pred` 只剥末尾的 $\mathbf 1$ (Lean 里是 `fs X nil`, 走一般的 3.3); 这里直接证, 无 `cof` 前提.

```agda
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
```

## §4 大小

Lean 的 Bachmann 性质 (`bach_pre`) 用大小论证. `size`: 主项结点数 (每个 $\psi$ 记 1). `G-size`: $G_u(t)$ 的成员严格比 $t$ 小.

```agda
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
