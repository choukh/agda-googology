# 由 LadderNFTree 生成对高度结构参数化的 LadderInfTree. 补丁是手写的数学内容.
import re,sys
import os
R=(os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..')))+'/probes/OCF/Align/'
t=open(R+'LadderNFTree.lagda.md',encoding='utf-8').read()
def between(a,b):
    i=t.index(a); j=t.index(b,i); return t[i:j]
head='''# 高度抽象 (二): 塔的树, 对高度结构 `HtS`

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 代码从 [LadderNFTree](LadderNFTree.lagda.md) 改写. 差别只有四处: (1) ℕ 上的 `upd`, `lo` 改由 `tri` 定义, 律由 `tri`, `irr`, `tr<` 证; (2) `Vs` 由 `Rec` 给, 只经 `outV`, `intoV` 用; (3) `ι↓` 带 `n <ᴸ m`, 不再只到 `suc n`, 地板用 `cap`, 高于 $n$ 的格是平凡的 (这是 `qwk` 过 `ι↓` 所必需的: `Sub n` 对高于 $n$ 的格没有信息); (4) 第 0 行按 `view` 分三种写法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfTree (𝕊 : HtS) where

open HtS 𝕊 public
open import Agda.Primitive using (Level; Setω)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Floor using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
```

## §0 序

```agda
evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)
```

## §1 地板族

```agda
Fv : Set
Fv = Ht → Flr

updT : {A : Set} → (Ht → A) → A → ∀ i {n} → Tri _<ᴸ_ i n → A
updT χ x i (tlt _) = χ i
updT χ x i (teq _) = x
updT χ x i (tgt _) = χ i

upd : {A : Set} → (Ht → A) → Ht → A → Ht → A
upd χ n x i = updT χ x i (tri i n)

infixl 5 _∪_
_∪_ : Fv → Fv → Fv
(a ∪ b) n = a n ⊔ b n

κ : Flr → Fv
κ x _ = x

loT : Fv → ∀ i {n} → Tri _<ᴸ_ i n → Flr
loT χ i (tlt _) = χ i
loT χ i (teq _) = fz
loT χ i (tgt _) = fz

-- 高度 < H 的部分
lo : Ht → Fv → Fv
lo H χ i = loT χ i (tri i H)

-- ι↓ 的地板: 低于 n 的格读 χ, 第 n 格是 x, 高于 n 的格平凡
capT : Fv → Flr → ∀ i {n} → Tri _<ᴸ_ i n → Flr
capT χ x i (tlt _) = χ i
capT χ x i (teq _) = x
capT χ x i (tgt _) = fz

cap : Fv → Ht → Flr → Fv
cap χ n x i = capT χ x i (tri i n)

Sub : Ht → Fv → Fv → Set
Sub m a b = ∀ i → i <ᴸ m → ∀ {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

Sub∞ : Fv → Fv → Set
Sub∞ a b = ∀ i {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

⇑ : ∀ {m a b} → Sub∞ a b → Sub m a b
⇑ s i q e = s i e

-- upd 的逐点转移
upd-map : ∀ {a b : Fv} {x y} h → Sub∞ a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (upd a h x) (upd b h y)
upd-map h s f i e with tri i h
... | tlt _ = s i e
... | teq _ = f e
... | tgt _ = s i e

upd-self : {A : Set} (χ : Ht → A) → ∀ h x → upd χ h x h ≡ x
upd-self χ h x with tri h h
... | tlt r = ⊥-elim (irr r)
... | teq _ = refl
... | tgt r = ⊥-elim (irr r)

upd-lt : {A : Set} → ∀ {j n} (χ : Ht → A) x → j <ᴸ n → upd χ n x j ≡ χ j
upd-lt {j = j} {n} χ x q with tri j n
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

upd-gt : {A : Set} → ∀ {j n} (χ : Ht → A) x → n <ᴸ j → upd χ n x j ≡ χ j
upd-gt {j = j} {n} χ x q with tri j n
... | tlt r = ⊥-elim (irr (tr< r q))
... | teq refl = ⊥-elim (irr q)
... | tgt _ = refl

lo-lt : ∀ {j H} χ → j <ᴸ H → lo H χ j ≡ χ j
lo-lt {j = j} {H} χ q with tri j H
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

cap-lt : ∀ {j n} (χ : Fv) x → j <ᴸ n → cap χ n x j ≡ χ j
cap-lt {j} {n} χ x q with tri j n
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

cap-gt : ∀ {j n} (χ : Fv) x → n <ᴸ j → cap χ n x j ≡ fz
cap-gt {j} {n} χ x q with tri j n
... | tlt r = ⊥-elim (irr (tr< r q))
... | teq refl = ⊥-elim (irr q)
... | tgt _ = refl

cap-self : (χ : Fv) → ∀ h x → cap χ h x h ≡ x
cap-self χ h x with tri h h
... | tlt r = ⊥-elim (irr r)
... | teq _ = refl
... | tgt r = ⊥-elim (irr r)

case-tri : ∀ {ℓ} {P : Set ℓ} i n → (i <ᴸ n → P) → (i ≡ n → P) → (n <ᴸ i → P) → P
case-tri i n a b c with tri i n
... | tlt r = a r
... | teq e = b e
... | tgt r = c r

upd-at : {A : Set} {a b : Ht → A} {y : A} (j i : Ht) → a i ≡ b i → upd a j y i ≡ upd b j y i
upd-at j i h with tri i j
... | tlt _ = h
... | teq _ = refl
... | tgt _ = h
```

## §2 数据树

`qcl n ψ s t g`: 高度 $n$ 的闭包. `qΩ↓ q`: 高度 $n<m$ 的节点, 输入是 `Vs m q k`, 也就是 `Q n k`. `qΩ`: 字面的顶层节点. `omk`: 记号 (见 [LadderNFTree](LadderNFTree.lagda.md)).

```agda
'''
s2=between("module _ (m : ℕ) (α : Ordᴵ)","Q  : ℕ → Ordᴵ")
s2=s2.replace("(m : ℕ)","(m : Ht)")
mid='''XQ : Ht → Set₁
XQ _ = Ordᴵ → Flr → Fv → Set

QV : ∀ m → (∀ {n} → n <ᴸ m → XQ n) → XQ m
UV : ∀ m (V : ∀ {n} → n <ᴸ m → XQ n) {α} (i : Ordᴵ) → i ◃ α → Flr → Fv → Set
QV m V α φ χ = Q₊ m α (UV m V) V φ χ
UV m V i zero         φ χ = QV m V i φ χ
UV m V i (suc r)      φ χ = UV m V i r φ χ
UV m V _ (self {f} n) φ χ = QV m V (f n) φ χ
UV m V i (lim n r)    φ χ = UV m V i r φ χ

Vs : ∀ m {n} → n <ᴸ m → Ordᴵ → Flr → Fv → Set
Vs = Rec XQ QV

Q  : Ht → Ordᴵ → Flr → Fv → Set
Q m = QV m (Vs m)

Us : ∀ m {α} (i : Ordᴵ) → i ◃ α → Flr → Fv → Set
Us m = UV m (Vs m)

outU : ∀ {m i α} (r : i ◃ α) {φ χ} → Us m i r φ χ → Q m i φ χ
outU zero      x = x
outU (suc r)   x = outU r x
outU (self n)  x = x
outU (lim n r) x = outU r x

intoU : ∀ {m i α} (r : i ◃ α) {φ χ} → Q m i φ χ → Us m i r φ χ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (self n)  x = x
intoU (lim n r) x = intoU r x

outV : ∀ {m n} (q : n <ᴸ m) {k φ χ} → Vs m q k φ χ → Q n k φ χ
outV {m} q {k} {φ} {χ} x = subst (λ X → X k φ χ) (Rec-β XQ QV m q) x

intoV : ∀ {m n} (q : n <ᴸ m) {k φ χ} → Q n k φ χ → Vs m q k φ χ
intoV {m} q {k} {φ} {χ} x = subst (λ X → X k φ χ) (sym (Rec-β XQ QV m q)) x

subst-out-into : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {a b : A} (e : a ≡ b) (x : P b) → subst P e (subst P (sym e) x) ≡ x
subst-out-into refl x = refl

out-intoV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} (z : Q n k ξ ζ) → outV q (intoV q z) ≡ z
out-intoV {m} q {k} {ξ} {ζ} z = subst-out-into {P = λ X → X k ξ ζ} (Rec-β XQ QV m q) z
```

## §3 加法, 同层嵌入, 搬运

```agda
'''
s3=between("sub-id : ∀ {m a}","## §4")
s3=s3.replace('''as-upd zero    η zero    ((u , v) , w) = u , (v , w)
as-upd zero    η (suc n) e = e
as-upd (suc h) η zero    e = e
as-upd {a} {b} {ψ} (suc h) η (suc n) e = as-upd {λ m → a (suc m)} {λ m → b (suc m)} {ψ} h η n e
''','''as-upd h η i e with tri i h
... | tlt _ = e
... | teq refl = (proj₁ (proj₁ e)) , (proj₂ (proj₁ e) , proj₂ e)
... | tgt _ = e
''')
s3=s3.replace("as-upd : ∀ {a b : Fv} {ψ} h η → Sub∞ (upd (a ∪ b) h (a h ⊔ ψ ⊔ fk η)) (a ∪ upd b h (ψ ⊔ fk η))","as-upd : ∀ {a b : Fv} {ψ} h η → Sub∞ (upd (a ∪ b) h (a h ⊔ ψ ⊔ fk η)) (a ∪ upd b h (ψ ⊔ fk η))")
s3=s3.replace("record RestrQ (m : ℕ)","record RestrQ (m : Ht)")
s4='''## §4 向下一层的嵌入, $\\dot\\Omega$

```agda
lo-ev : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (lo H a j) → Ev ℓ (a j)
lo-ev a q e = subst (Ev _) (lo-lt a q) e

ev-lo : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (a j) → Ev ℓ (lo H a j)
ev-lo a q e = subst (Ev _) (sym (lo-lt a q)) e

upd-sub : ∀ {m} {a b : Fv} {x y} n → Sub n a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub m (cap a n x) (cap b n y)
upd-sub n s f i q e with tri i n
... | tlt r = s i r e
... | teq _ = f e
... | tgt _ = tt

upd-cap : ∀ {a b : Fv} {x y} n → Sub∞ a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (upd a n x) (cap b n y)
upd-cap n s f i e with tri i n
... | tlt _ = s i e
... | teq _ = f e
... | tgt _ = tt

cap-map : ∀ {χ : Fv} {x y} n → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (cap χ n x) (cap χ n y)
cap-map n f i e with tri i n
... | tlt _ = e
... | teq _ = f e
... | tgt _ = tt

κ-cap : ∀ {x} n → (∀ {ℓ} → Ev ℓ Fl → Ev ℓ x) → Sub∞ (κ Fl) (cap (κ Fl) n x)
κ-cap n f i e with tri i n
... | tlt _ = e
... | teq _ = f e
... | tgt _ = tt

-- ι↓ 的三个转换
c-∪ : ∀ {a χ : Fv} {x} n → Sub∞ (a ∪ cap χ n x) (cap (a ∪ χ) n x)
c-∪ n i e with tri i n
... | tlt _ = e
... | teq _ = proj₂ e
... | tgt _ = tt

c-sw : ∀ {χ : Fv} {x y j} n → j <ᴸ n → Sub∞ (upd (cap χ n x) j y) (cap (upd χ j y) n x)
c-sw {χ} {x} {y} {j} n q i {ℓ} e = case-tri i n
  (λ a → subst (Ev ℓ) (sym (cap-lt (upd χ j y) x a)) (subst (Ev ℓ) (upd-at j i (cap-lt χ x a)) e))
  (λ { refl → subst (Ev ℓ) (sym (cap-self (upd χ j y) n x)) (subst (Ev ℓ) (trans (upd-gt (cap χ n x) y q) (cap-self χ n x)) e) })
  (λ a → subst (Ev ℓ) (sym (cap-gt (upd χ j y) x a)) tt)

ι↓ : ∀ {n m k α φ χ} → n <ᴸ m → Q n k φ χ → Q m α φ (cap χ n (flo k))
ι↓ d q0 = q0
ι↓ d (qs a) = qs (ι↓ d a)
ι↓ d (ql F) = ql (λ i → ι↓ d (F i))
ι↓ d (qi ac f) = qi ac (λ x → ι↓ d (f x))
ι↓ d (qŝ c₀ t g) = qŝ c₀ (ι↓ d t) (λ η e → ι↓ d (g η e))
ι↓ d (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (ι↓ d o₀) (λ η e → ι↓ d (o η e))
ι↓ d (qclo t g) = qclo (ι↓ d t) (λ η → ι↓ d (g η))
ι↓ {χ = χ} d (qcl {n = j} q ψ s t g) =
  qcl (tr< q d) ψ (λ e → s (subst (Ev _) (cap-lt χ _ q) e)) (ι↓ d t) (λ η → qwk (λ e → e) (⇑ (c-sw {χ} _ q)) (ι↓ d (g η)))
ι↓ {n = n} d (qwk le le′ t) = qwk le (upd-sub n le′ (λ e → e)) (ι↓ d t)
ι↓ {χ = χ} d (qΩ↓ {n = j} q fe ac h) =
  qΩ↓ (tr< q d) fe (λ e → ac (subst (Ev _) (cap-lt χ _ q) e)) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ d (h ξ ζ (intoV q (outV (tr< q d) z)))))
ι↓ {n = n} {k = k} {χ = χ} d (qΩ fe r h) =
  qΩ↓ d fe (λ e → cvFlo k (subst (Ev _) (cap-self χ n _) e) r) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo n ζ} {χ} _)) (ι↓ d (h ξ ζ (intoU (<→◃ r) (outV d z)))))
ι↓ {n = n} {k = suc a} d (omk zero z x) = qwk (λ e → e) (⇑ (cap-map n (λ e → toFlo a (λ q → e (suc q))))) (ι↓ d z)
ι↓ {n = n} {k = lim f s} d (omk (self i) z x) = qwk (λ e → e) (⇑ (cap-map n (λ e → toFlo (f i) (λ q → e (lim i q))))) (ι↓ d z)

'''
tl=between("tl : ∀ {m c k χ} (φ : Flr)","Ω̇ : ∀ m α")
s4b='''-- 第 0 行的三种写法
XΩ : Ht → Set
XΩ m = (α : Ordᴵ) → Q m α Fl (κ Fl)

-- 闭包行
rowC : ∀ {m n} → n <ᴸ m → XΩ n → Q m zero Fl (κ Fl)
rowC {n = n} q X =
  qcl q fz (λ e → e)
      (qwk (λ e → e) (⇑ (κ-cap n proj₂)) (ι↓ q (X (suc zero))))
      (λ η → qwk (λ e → e) (⇑ (upd-cap n (λ i e → e) (λ e → toFlo η (λ q′ → proj₂ e (suc q′))))) (ι↓ q (X η)))

-- 链行: 第 0 项是 1, 其余项是低层 Ω̇ 的第 0 行
𝟏L : ∀ {m} → Q m zero Fl (κ Fl)
𝟏L = qwk (λ _ → tt) (λ i q _ → tt) (qs {φ = fz} {χ = κ fz} q0)

stepL : ∀ {m n} → n <ᴸ m → XΩ n → Q m zero Fl (κ Fl)
stepL {n = n} q X = qwk (λ e → e) (⇑ (κ-cap n (λ _ → tt))) (ι↓ q (X zero))

rowL : ∀ {m} (F : ℕ → Ht) → (∀ i → F i <ᴸ m) → (∀ i → XΩ (F i)) → ℕ → Q m zero Fl (κ Fl)
rowL F qs₁ X zero    = 𝟏L
rowL F qs₁ X (suc i) = stepL (qs₁ i) (X i)

-- 根层
rowB : ∀ {m} → Q m zero Fl (κ Fl)
rowB = qclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))

rowV : ∀ m → (∀ {n} → n <ᴸ m → XΩ n) → View _<ᴸ_ h₀ m → Q m zero Fl (κ Fl)
rowV _ I base         = rowB
rowV m I (clos q)     = rowC q (I q)
rowV m I (chain F qs₁) = ql (rowL F qs₁ (λ i → I (qs₁ i)))

FΩ : ∀ m → (∀ {n} → n <ᴸ m → XΩ n) → XΩ m
FΩ m I (suc α) = qΩ (λ e → e) zero (λ ξ ζ z → qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z)))
FΩ m I (lim f s) = ql (λ n → omk (self n) (FΩ m I (f n)) (ι (self n) (FΩ m I (f n))))
FΩ m I zero = rowV m I (view m)

ΩI : ∀ m {n} → n <ᴸ m → XΩ n
ΩI = Rec XΩ FΩ

Ω̇ : ∀ m → XΩ m
Ω̇ m = FΩ m (ΩI m)

ΩI≡ : ∀ {m n} (q : n <ᴸ m) → ΩI m q ≡ Ω̇ n
ΩI≡ {m} q = Rec-β XΩ FΩ m q
```

'''
s5=between("## §5 折叠","w₀ : ℕ → Ordᴵ")
s5=s5.replace('''Ev-lo : ∀ {a : Fv} H i {ℓ} → Ev ℓ (a i) → Ev ℓ (lo H a i)
Ev-lo zero    i e = tt
Ev-lo (suc H) zero e = e
Ev-lo {a} (suc H) (suc i) e = Ev-lo {λ m → a (suc m)} H i e
''','''Ev-lo : ∀ {a : Fv} H i {ℓ} → Ev ℓ (a i) → Ev ℓ (lo H a i)
Ev-lo H i e with tri i H
... | tlt _ = e
... | teq _ = tt
... | tgt _ = tt
''')
s5=s5.replace('''Hi : ℕ → ℕ → Set''','''Hi : Ht → Ht → Set''')
s5=s5.replace('''lo-triv {H = zero} a h = tt
lo-triv {H = suc H} {i = suc i} a (inj₁ refl) = lo-triv {H = H} {i = i} (λ m → a (suc m)) (inj₁ refl)
lo-triv {H = suc H} {i = suc i} a (inj₂ r) = lo-triv {H = H} {i = i} (λ m → a (suc m)) (inj₂ (dn r))
lo-triv {H = suc H} {i = zero} a (inj₂ ())
''','''lo-triv {H} {i} a h with tri i H
lo-triv {H} {i} a (inj₁ refl) | tlt r = ⊥-elim (irr r)
lo-triv {H} {i} a (inj₂ s) | tlt r = ⊥-elim (irr (tr< r s))
... | teq _ = tt
... | tgt _ = tt
''')
s5=s5.replace("Ok : (ℕ → Ordᴵ) → Set","Ok : (Ht → Ordᴵ) → Set")
s5=s5.replace("Eh : ℕ → ℕ → (ℕ → Ordᴵ) → Fv → Set","Eh : Ht → Ht → (Ht → Ordᴵ) → Fv → Set")
s5=s5.replace('''upd-ev : ∀ {ℓ′ z} n i (w : ℕ → Ordᴵ) (χ : Fv) → Ev ℓ′ z → Ev (w i) (χ i) → Ev (upd w n ℓ′ i) (upd χ n z i)
upd-ev zero zero w χ a b = a
upd-ev zero (suc i) w χ a b = b
upd-ev (suc n) zero w χ a b = b
upd-ev (suc n) (suc i) w χ a b = upd-ev n i (λ m → w (suc m)) (λ m → χ (suc m)) a b
''','''upd-ev : ∀ {ℓ′ z} n i (w : Ht → Ordᴵ) (χ : Fv) → Ev ℓ′ z → Ev (w i) (χ i) → Ev (upd w n ℓ′ i) (upd χ n z i)
upd-ev n i w χ a b with tri i n
... | tlt _ = b
... | teq _ = a
... | tgt _ = b
''')
s5=s5.replace('''upd-ok : ∀ {ℓ′} n (w : ℕ → Ordᴵ) → Ok w → Ev ℓ′ Fl → Ok (upd w n ℓ′)
upd-ok zero w ok a zero = a
upd-ok zero w ok a (suc i) = ok (suc i)
upd-ok (suc n) w ok a zero = ok zero
upd-ok (suc n) w ok a (suc i) = upd-ok n (λ m → w (suc m)) (λ m → ok (suc m)) a i
''','''upd-ok : ∀ {ℓ′} n (w : Ht → Ordᴵ) → Ok w → Ev ℓ′ Fl → Ok (upd w n ℓ′)
upd-ok n w ok a i with tri i n
... | tlt _ = ok i
... | teq _ = a
... | tgt _ = ok i
''')
s5=s5.replace("(n : ℕ) → Ok w","(n : Ht) → Ok w")
s5=s5.replace("cv* {χ} n i (a , b) = a , (Ev-lo {Z* χ} n i (a , b) , b)","cv* {χ} n i (a , b) = a , (Ev-lo {Z* χ} n i (a , b) , b)")
s5=s5.replace('''Hi-0 : ∀ i → Hi zero i
Hi-0 zero = inj₁ refl
Hi-0 (suc i) = inj₂ (z<s i)
''','''Hi-0 : ∀ i → Hi h₀ i
Hi-0 = bot
''')
s5=s5.replace("e↓ : ∀ {n m w} {χ : Fv} → Eh zero m w χ → Eh n m w χ","e↓ : ∀ {n m w} {χ : Fv} → Eh h₀ m w χ → Eh n m w χ")
s5=s5.replace("zr : ∀ {w} → Ok w → ∀ n → zero <ᴵ w n","zr : ∀ {w} → Ok w → ∀ n → zero <ᴵ w n")
s5=s5.replace("ψ̄ᵠ : ∀ {m c φ χ w} → Ok w → Eh zero m w χ → Q m c φ χ → Run φ","ψ̄ᵠ : ∀ {m c φ χ w} → Ok w → Eh h₀ m w χ → Q m c φ χ → Run φ")
s5=s5.replace("Run φ\n","Run φ\n")
tail='''w₀ : Ht → Ordᴵ
w₀ _ = suc zero

ok₀ : Ok w₀
ok₀ i = tt , (λ q → q)

-- ψ₀(Ω_{m+α}), m 由结构解释
Tᵠ : ∀ m α → Run Fl
Tᵠ m α = ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Ω̇ m α)
```
'''
out=head+s2+mid+s3+s4+tl.rstrip()+"\n\n"+s4b+s5+tail
# 分支 ψ̄ 第 3 行的数字 0 是 Level 的, 不动
open(R+'LadderInfTree.lagda.md','w',encoding='utf-8').write(out)
