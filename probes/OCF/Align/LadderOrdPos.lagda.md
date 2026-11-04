# 序数高度 (二): 码与位置, 实例 `HB M`

> **判决: HOLDS (实例闭合, 无假设).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 对每个码 `M : Code`, 高度是位置 `Pos (cs M)`, 即 $\le M$ 的段. `HB M : HtB` 的字段全部成立.
>
> **码.** `cl g` 的值是 $\sum_j (g_j+1)$, 所以 `cl` 自动严格递增, 没有退化极限, 头部就判定了零/后继/极限. 每个位置的表示唯一, 三歧的相等是 $\equiv$. 这就是带证书的子类型: 证书做进了结构, 字面公共上界就是 $M$. 码上的全局三歧仍然是假的 (`no-tri-code`, 见 [LadderOrdNeg](LadderOrdNeg.lagda.md)), 跨 $M$ 没有比较.
>
> **对上一轮三件事的回答.** (a) `teq refl` 不用换成高度搬运: 位置的相等就是 $\equiv$. (b) `upd`, `lo`, `cap` 不用改: `Fv = Ht → Flr` 中 `Ht` 已经是 $M$ 之下的段. (c) `Rq` 的同一个 $q$ 不用放宽: $<$ 是命题 (`<ᴾ-prop`). 三件都是由选载体消去的, 不是解决的; 用 $\cong$ 作相等的版本没有试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdPos where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _⊑ᴵ_; Sim→⊑ᴵ; <ᴵ-trans; _≅ᴵ_; _≺ᴵ_; via; ≺ᴵ-irrefl; ≅ᴵ-sym; ≅ᴵ-refl)
open import OCF.Align.LadderOrdBase
```

## §1 码与位置

```agda
data Code : Set where
  cz : Code
  cs : Code → Code
  cl : (ℕ → Code) → Code

data Pos : Code → Set where
  end : ∀ {c} → Pos (cs c)
  low : ∀ {c} → Pos c → Pos (cs c)
  blk : ∀ {g} j → Pos (cs (g j)) → Pos (cl g)
```

## §2 序

字典序. 对块号的比较把 $g$ 平移, 这样相等的情形不用 `subst`.

```agda
infix 4 _<ᴾ_
_<ᴾ_ : ∀ {c} → Pos c → Pos c → Set
ltB : (g : ℕ → Code) (j k : ℕ) → Pos (cs (g j)) → Pos (cs (g k)) → Set
end     <ᴾ y       = ⊥
low p   <ᴾ end     = ⊤
low p   <ᴾ low q   = p <ᴾ q
blk {g} j p <ᴾ blk k q = ltB g j k p q
ltB g zero    zero    p q = p <ᴾ q
ltB g zero    (suc k) p q = ⊤
ltB g (suc j) zero    p q = ⊥
ltB g (suc j) (suc k) p q = ltB (λ i → g (suc i)) j k p q

<ᴾ-prop : ∀ {c} {p q : Pos c} (x y : p <ᴾ q) → x ≡ y
ltB-prop : ∀ g j k {p q} (x y : ltB g j k p q) → x ≡ y
<ᴾ-prop {p = low p} {q = end} x y = refl
<ᴾ-prop {p = low p} {q = low q} x y = <ᴾ-prop {p = p} {q = q} x y
<ᴾ-prop {p = blk {g} j p} {q = blk k q} x y = ltB-prop g j k {p} {q} x y
ltB-prop g zero zero {p} {q} x y = <ᴾ-prop {p = p} {q = q} x y
ltB-prop g zero (suc k) x y = refl
ltB-prop g (suc j) (suc k) {p} {q} x y = ltB-prop (λ i → g (suc i)) j k {p} {q} x y

<ᴾ-trans : ∀ {c} (p q r : Pos c) → p <ᴾ q → q <ᴾ r → p <ᴾ r
ltB-trans : ∀ g j k l (p : Pos (cs (g j))) (q : Pos (cs (g k))) (r : Pos (cs (g l))) → ltB g j k p q → ltB g k l q r → ltB g j l p r
<ᴾ-trans (low p) (low q) end x y = tt
<ᴾ-trans (low p) (low q) (low r) x y = <ᴾ-trans p q r x y
<ᴾ-trans (blk {g} j p) (blk k q) (blk l r) x y = ltB-trans g j k l p q r x y
ltB-trans g zero zero zero p q r x y = <ᴾ-trans p q r x y
ltB-trans g zero zero (suc l) p q r x y = tt
ltB-trans g zero (suc k) (suc l) p q r x y = tt
ltB-trans g (suc j) (suc k) (suc l) p q r x y = ltB-trans (λ i → g (suc i)) j k l p q r x y

shB : ∀ {g} → Pos (cl (λ i → g (suc i))) → Pos (cl g)
shB (blk j p) = blk (suc j) p

<ᴾ-tri : ∀ {c} (p q : Pos c) → Tri _<ᴾ_ p q
triB : ∀ g j k (p : Pos (cs (g j))) (q : Pos (cs (g k))) → Tri _<ᴾ_ (blk {g} j p) (blk {g} k q)
<ᴾ-tri end end = teq refl
<ᴾ-tri end (low q) = tgt tt
<ᴾ-tri (low p) end = tlt tt
<ᴾ-tri (low p) (low q) with <ᴾ-tri p q
... | tlt x = tlt x
... | teq refl = teq refl
... | tgt x = tgt x
<ᴾ-tri (blk {g} j p) (blk k q) = triB g j k p q
triB g zero zero p q with <ᴾ-tri p q
... | tlt x = tlt x
... | teq refl = teq refl
... | tgt x = tgt x
triB g zero (suc k) p q = tlt tt
triB g (suc j) zero p q = tgt tt
triB g (suc j) (suc k) p q with triB (λ i → g (suc i)) j k p q
... | tlt x = tlt x
... | teq e = teq (cong shB e)
... | tgt x = tgt x

-- 对角线上是 teq refl (跨世界的模拟要用)
<ᴾ-tri-self : ∀ {c} (p : Pos c) → <ᴾ-tri p p ≡ teq refl
triB-self : ∀ g j (p : Pos (cs (g j))) → triB g j j p p ≡ teq refl
<ᴾ-tri-self end = refl
<ᴾ-tri-self (low p) rewrite <ᴾ-tri-self p = refl
<ᴾ-tri-self (blk {g} j p) = triB-self g j p
triB-self g zero p rewrite <ᴾ-tri-self p = refl
triB-self g (suc j) p rewrite triB-self (λ i → g (suc i)) j p = refl

-- 块内, 块间
ltB-same : ∀ g j {p q : Pos (cs (g j))} → p <ᴾ q → ltB g j j p q
ltB-same g zero x = x
ltB-same g (suc j) x = ltB-same (λ i → g (suc i)) j x

ltB-next : ∀ g j (p : Pos (cs (g j))) (q : Pos (cs (g (suc j)))) → ltB g j (suc j) p q
ltB-next g zero p q = tt
ltB-next g (suc j) p q = ltB-next (λ i → g (suc i)) j p q
```

## §3 秩

`plus b c` 是 $b+\lVert c\rVert$, 落在 `Ordᴵ` 里. 所有下面的元素都是字面的子项, 所以 $<$ 映到字面路径. `val M` 是 $M$ 的值.

```agda
plus : Ordᴵ → Code → Ordᴵ
Sb   : Ordᴵ → (ℕ → Code) → ℕ → Ordᴵ
le<  : ∀ b c → b <ᴵ suc (plus b c)
stepSb : ∀ b g i → Sb b g i ⊑ᴵ Sb b g (suc i)
plus b cz     = b
plus b (cs c) = suc (plus b c)
plus b (cl g) = lim (Sb b g) (stepSb b g)
Sb b g zero    = b
Sb b g (suc i) = suc (plus (Sb b g i) (g i))
stepSb b g i = Sim→⊑ᴵ (λ q → <ᴵ-trans q (le< (Sb b g i) (g i)))
le< b cz     = zero
le< b (cs c) = suc (le< b c)
le< b (cl g) = suc (lim 1 (le< b (g 0)))

val : Code → Ordᴵ
val = plus zero

rkP : ∀ {c} → Ordᴵ → Pos c → Ordᴵ
rkP b (end {c})     = plus b c
rkP b (low p)       = rkP b p
rkP b (blk {g} j p) = rkP (Sb b g j) p

Le : Ordᴵ → Ordᴵ → Set
Le a b = (a ≡ b) ⊎ (a <ᴵ b)

Le-trans : ∀ {a b c} → Le a b → Le b c → Le a c
Le-trans (inj₁ refl) y = y
Le-trans (inj₂ x) (inj₁ refl) = inj₂ x
Le-trans (inj₂ x) (inj₂ y) = inj₂ (<ᴵ-trans x y)

rkP<plus : ∀ {c} b (p : Pos c) → rkP b p <ᴵ plus b c
rkP<plus b end = zero
rkP<plus b (low p) = suc (rkP<plus b p)
rkP<plus b (blk {g} j p) = lim (suc j) (rkP<plus (Sb b g j) p)

Le-plus : ∀ b c → Le b (plus b c)
Le-plus b cz = inj₁ refl
Le-plus b (cs c) = inj₂ (le< b c)
Le-plus b (cl g) = inj₂ (lim 1 (le< b (g 0)))

Le-Sb : ∀ b g j → Le b (Sb b g j)
Le-Sb b g zero = inj₁ refl
Le-Sb b g (suc j) = Le-trans (Le-Sb b g j) (inj₂ (le< (Sb b g j) (g j)))

Le-rkP : ∀ {c} b (p : Pos c) → Le b (rkP b p)
Le-rkP {cs c} b end = Le-plus b c
Le-rkP b (low p) = Le-rkP b p
Le-rkP b (blk {g} j p) = Le-trans (Le-Sb b g j) (Le-rkP (Sb b g j) p)

-- 一般的累积序列, 使得块号平移时可以归纳
Le-S : ∀ (g : ℕ → Code) (S : ℕ → Ordᴵ) → (∀ j → S (suc j) ≡ suc (plus (S j) (g j))) → ∀ k → Le (S 1) (S (suc k))
Le-S g S hS zero = inj₁ refl
Le-S g S hS (suc k) = Le-trans (Le-S g S hS k) (inj₂ (subst (S (suc k) <ᴵ_) (sym (hS (suc k))) (le< (S (suc k)) (g (suc k)))))

rkP-mono : ∀ {c} b (p q : Pos c) → p <ᴾ q → rkP b p <ᴵ rkP b q
rkB-mono : ∀ (g : ℕ → Code) (S : ℕ → Ordᴵ) → (∀ j → S (suc j) ≡ suc (plus (S j) (g j))) → ∀ j k (p : Pos (cs (g j))) (q : Pos (cs (g k))) → ltB g j k p q → rkP (S j) p <ᴵ rkP (S k) q
rkP-mono b (low p) end x = rkP<plus b p
rkP-mono b (low p) (low q) x = rkP-mono b p q x
rkP-mono b (blk {g} j p) (blk k q) x = rkB-mono g (Sb b g) (λ _ → refl) j k p q x
rkB-mono g S hS zero zero p q x = rkP-mono (S 0) p q x
rkB-mono g S hS zero (suc k) p q x with Le-trans (Le-S g S hS k) (Le-rkP (S (suc k)) q)
... | inj₁ e = subst (rkP (S 0) p <ᴵ_) e (subst (rkP (S 0) p <ᴵ_) (sym (hS 0)) (rkP<plus (S 0) p))
... | inj₂ r = <ᴵ-trans (subst (rkP (S 0) p <ᴵ_) (sym (hS 0)) (rkP<plus (S 0) p)) r
rkB-mono g S hS (suc j) (suc k) p q x = rkB-mono (λ i → g (suc i)) (λ i → S (suc i)) (λ i → hS (suc i)) j k p q x
```

秩上的相等就是位置的相等, 秩上的比较就是 `<ᴵ-dec` 的形式. 所以 `HtB` 字段 `tri` 的 $\equiv$ 与 "相等是 $\cong$" 在一个 $M$ 之内没有差别.

```agda
rk-inj : ∀ {c} b (p q : Pos c) → rkP b p ≅ᴵ rkP b q → p ≡ q
rk-inj b p q e with <ᴾ-tri p q
... | tlt x = ⊥-elim (≺ᴵ-irrefl (via (≅ᴵ-sym e) (rkP-mono b p q x)))
... | teq x = x
... | tgt x = ⊥-elim (≺ᴵ-irrefl (via e (rkP-mono b q p x)))

rk-dec : ∀ {c} b (p q : Pos c) → (rkP b p ≺ᴵ rkP b q) ⊎ ((rkP b q ≺ᴵ rkP b p) ⊎ (rkP b p ≅ᴵ rkP b q))
rk-dec b p q with <ᴾ-tri p q
... | tlt x = inj₁ (via (≅ᴵ-refl _) (rkP-mono b p q x))
... | teq refl = inj₂ (inj₂ (≅ᴵ-refl _))
... | tgt x = inj₂ (inj₁ (via (≅ᴵ-refl _) (rkP-mono b q p x)))
```

## §4 根

```agda
fstC : ∀ c → Pos (cs c)
fstC cz     = end
fstC (cs c) = low (fstC c)
fstC (cl g) = low (blk 0 (fstC (g 0)))

botC : ∀ c (p : Pos (cs c)) → (fstC c ≡ p) ⊎ (fstC c <ᴾ p)
botC cz end = inj₁ refl
botC cz (low ())
botC (cs c) end = inj₂ tt
botC (cs c) (low p) with botC c p
... | inj₁ refl = inj₁ refl
... | inj₂ x = inj₂ x
botC (cl g) end = inj₂ tt
botC (cl g) (low (blk zero p)) with botC (g 0) p
... | inj₁ refl = inj₁ refl
... | inj₂ x = inj₂ x
botC (cl g) (low (blk (suc j) p)) = inj₂ tt

IsFst : ∀ {c} → Pos c → Set
IsFst (end {c = cz})   = ⊤
IsFst (end {cs c}) = ⊥
IsFst (end {cl g}) = ⊥
IsFst (low p)      = IsFst p
IsFst (blk zero p) = IsFst p
IsFst (blk (suc j) p) = ⊥

isf : ∀ c (x : Pos (cs c)) → IsFst x → x ≡ fstC c
isf cz end h = refl
isf cz (low ()) h
isf (cs c) (low x) h = cong low (isf c x h)
isf (cl g) (low (blk zero x)) h = cong (λ z → low (blk 0 z)) (isf (g 0) x h)
```

## §5 第 0 行的写法

`viewC` 走位置的路径, 带着上下文 $\iota$ 与 "这一段开始之前" 的信息 `St`: 要么这一段就是最开头, 要么有前一个元素 $n$. 块的结束点 `blk j end` 总在, 所以每个块的开头要么是最开头, 要么有前驱. 叶子 `end {c}` 看 $c$ 的头: $c=$ `cz` 看 `St`; `cs` 是闭包; `cl g` 是链, 第 $i$ 项是 `blk i end`.

```agda
module V (M : Code) where
  H : Set
  H = Pos (cs M)

  h₀ᴾ : H
  h₀ᴾ = fstC M

  W : H → Set
  W m = Σ (View _<ᴾ_ h₀ᴾ m) (ViewOk _<ᴾ_ h₀ᴾ m)

  data St : Set where
    sf : St
    sp : H → St

  LB : St → H → Set
  LB sf y = ⊥
  LB (sp n) y = (y ≡ n) ⊎ (y <ᴾ n)

  St0 : ∀ {c} → St → (Pos c → H) → Set
  St0 sf ι = ∀ x → IsFst x → ι x ≡ h₀ᴾ
  St0 (sp n) ι = ∀ x → n <ᴾ ι x

  record Cxt (c : Code) : Set where
    constructor mkC
    field
      ι   : Pos c → H
      ιm  : ∀ (p q : Pos c) → p <ᴾ q → ι p <ᴾ ι q
      stv : St
      ok0 : St0 stv ι
      dec : ∀ {y} x → y <ᴾ ι x → (Σ (Pos c) λ y′ → (y ≡ ι y′) × (y′ <ᴾ x)) ⊎ LB stv y
  open Cxt

  LB-lt : ∀ {c} (C : Cxt c) {y} x → LB (stv C) y → y <ᴾ ι C x
  LB-lt (mkC ι ιm sf ok0 dec) x ()
  LB-lt (mkC ι ιm (sp n) ok0 dec) x (inj₁ refl) = ok0 x
  LB-lt (mkC ι ιm (sp n) ok0 dec) x (inj₂ r) = <ᴾ-trans _ n _ r (ok0 x)

  ok-low : ∀ {c} st (ι : Pos (cs c) → H) → St0 st ι → St0 st (λ p → ι (low p))
  ok-low sf ι h = λ x f → h (low x) f
  ok-low (sp n) ι h = λ x → h (low x)

  Cl : ∀ {c} → Cxt (cs c) → Cxt c
  Cl {c} C = mkC (λ p → ι C (low p)) (λ p q x → ιm C (low p) (low q) x) (stv C) (ok-low (stv C) (ι C) (ok0 C))
    (λ x r → go (dec C (low x) r))
    where
    go : ∀ {y x} → (Σ (Pos (cs c)) λ y′ → (y ≡ ι C y′) × (y′ <ᴾ low x)) ⊎ LB (stv C) y → (Σ (Pos c) λ y′ → (y ≡ ι C (low y′)) × (y′ <ᴾ x)) ⊎ LB (stv C) y
    go (inj₁ (low y′ , e , l)) = inj₁ (y′ , e , l)
    go (inj₂ b) = inj₂ b

  -- 第 0 块的上下文
  B0dec : ∀ {g} (x : Pos (cs (g 0))) (y′ : Pos (cl g)) → y′ <ᴾ blk 0 x → Σ (Pos (cs (g 0))) λ z → (y′ ≡ blk 0 z) × (z <ᴾ x)
  B0dec x (blk zero z) l = z , refl , l

  ok-b0 : ∀ {g} st (ι : Pos (cl g) → H) → St0 st ι → St0 st (λ p → ι (blk 0 p))
  ok-b0 sf ι h = λ x f → h (blk 0 x) f
  ok-b0 (sp n) ι h = λ x → h (blk 0 x)

  Cb0 : ∀ {g} → Cxt (cl g) → Cxt (cs (g 0))
  Cb0 {g} C = mkC (λ p → ι C (blk 0 p)) (λ p q x → ιm C (blk 0 p) (blk 0 q) x) (stv C) (ok-b0 (stv C) (ι C) (ok0 C))
    (λ x r → go x (dec C (blk 0 x) r))
    where
    go : ∀ {y} x → (Σ (Pos (cl g)) λ y′ → (y ≡ ι C y′) × (y′ <ᴾ blk 0 x)) ⊎ LB (stv C) y → (Σ (Pos (cs (g 0))) λ y′ → (y ≡ ι C (blk 0 y′)) × (y′ <ᴾ x)) ⊎ LB (stv C) y
    go x (inj₁ (y′ , e , l)) with B0dec x y′ l
    ... | z , refl , l′ = inj₁ (z , e , l′)
    go x (inj₂ b) = inj₂ b

  -- 第 j+1 块: 前驱是第 j 块的结束点
  split : ∀ g k j (z : Pos (cs (g k))) (x : Pos (cs (g (suc j)))) → ltB g k (suc j) z x →
          (Σ (Pos (cs (g (suc j)))) λ z′ → (blk {g} k z ≡ blk (suc j) z′) × (z′ <ᴾ x)) ⊎ ((blk {g} k z ≡ blk j end) ⊎ (blk {g} k z <ᴾ blk j end))
  split g zero zero end x l = inj₂ (inj₁ refl)
  split g zero zero (low z) x l = inj₂ (inj₂ tt)
  split g zero (suc j) z x l = inj₂ (inj₂ tt)
  split g (suc zero) zero z x l = inj₁ (z , refl , l)
  split g (suc (suc k)) zero z x ()
  split g (suc k) (suc j) z x l with split (λ i → g (suc i)) k j z x l
  ... | inj₁ (z′ , e , l′) = inj₁ (z′ , cong shB e , l′)
  ... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong shB e))
  ... | inj₂ (inj₂ r) = inj₂ (inj₂ r)

  CbS : ∀ {g} j → Cxt (cl g) → Cxt (cs (g (suc j)))
  CbS {g} j C = mkC (λ p → ι C (blk (suc j) p))
    (λ p q x → ιm C (blk (suc j) p) (blk (suc j) q) (ltB-same g (suc j) x))
    (sp (ι C (blk j end)))
    (λ x → ιm C (blk j end) (blk (suc j) x) (ltB-next g j end x))
    go
    where
    n₁ = ι C (blk j end)
    go : ∀ {y} x → y <ᴾ ι C (blk (suc j) x) → (Σ (Pos (cs (g (suc j)))) λ y′ → (y ≡ ι C (blk (suc j) y′)) × (y′ <ᴾ x)) ⊎ ((y ≡ n₁) ⊎ (y <ᴾ n₁))
    go {y} x r with dec C (blk (suc j) x) r
    ... | inj₂ b = inj₂ (inj₂ (LB-lt C (blk j end) b))
    ... | inj₁ (blk k z , e , l) with split g k j z x l
    ...   | inj₁ (z′ , e′ , l′) = inj₁ (z′ , trans e (cong (ι C) e′) , l′)
    ...   | inj₂ (inj₁ e′) = inj₂ (inj₁ (trans e (cong (ι C) e′)))
    ...   | inj₂ (inj₂ r′) = inj₂ (inj₂ (subst (_<ᴾ n₁) (sym e) (ιm C (blk k z) (blk j end) r′)))

  -- 块内的点不超过块的结束点
  blk≤end : ∀ g j (z : Pos (cs (g j))) → (blk {g} j z ≡ blk j end) ⊎ (blk {g} j z <ᴾ blk j end)
  blk≤end g j end = inj₁ refl
  blk≤end g j (low z) = inj₂ (ltB-same g j tt)

  viewC : ∀ {c} (C : Cxt c) (p : Pos c) → W (ι C p)
  viewC {cs cz} (mkC ι ιm sf ok0 dec) end = subst W (sym (ok0 end tt)) (base , tt)
  viewC {cs cz} (mkC ι ιm (sp n) ok0 dec) end = clos (ok0 end) , go
    where
    go : ∀ {x} → x <ᴾ ι end → (x ≡ n) ⊎ (x <ᴾ n)
    go r with dec end r
    ... | inj₁ (low () , _ , _)
    ... | inj₂ b = b
  viewC {cs (cs c)} C end = clos (ιm C (low end) end tt) , go
    where
    go : ∀ {x} → x <ᴾ ι C end → (x ≡ ι C (low end)) ⊎ (x <ᴾ ι C (low end))
    go r with dec C end r
    ... | inj₁ (low end , e , _) = inj₁ e
    ... | inj₁ (low (low z) , e , _) = inj₂ (subst (_<ᴾ ι C (low end)) (sym e) (ιm C (low (low z)) (low end) tt))
    ... | inj₂ b = inj₂ (LB-lt C (low end) b)
  viewC {cs (cl g)} C end =
      chain F qs , asc , cof
    where
    F : ℕ → H
    F i = ι C (low (blk i end))
    qs : ∀ i → F i <ᴾ ι C end
    qs i = ιm C (low (blk i end)) end tt
    asc : ∀ i → F i <ᴾ F (suc i)
    asc i = ιm C (low (blk i end)) (low (blk (suc i) end)) (ltB-next g i end end)
    cof : ∀ {x} → x <ᴾ ι C end → Σ ℕ λ i → (x ≡ F i) ⊎ (x <ᴾ F i)
    cof r with dec C end r
    ... | inj₂ b = 0 , inj₂ (LB-lt C (low (blk 0 end)) b)
    ... | inj₁ (low (blk j z) , e , _) with blk≤end g j z
    ...   | inj₁ e′ = j , inj₁ (trans e (cong (λ w → ι C (low w)) e′))
    ...   | inj₂ r′ = j , inj₂ (subst (_<ᴾ F j) (sym e) (ιm C (low (blk j z)) (low (blk j end)) r′))
  viewC C (low p) = viewC (Cl C) p
  viewC C (blk zero p) = viewC (Cb0 C) p
  viewC C (blk (suc j) p) = viewC (CbS j C) p

  C₀ : Cxt (cs M)
  C₀ = mkC (λ x → x) (λ p q x → x) sf (λ x h → isf M x h) (λ x r → inj₁ (_ , refl , r))

  vw : ∀ m → W m
  vw m = viewC C₀ m
```

## §6 实例

```agda
HB : Code → HtB
HB M = record
  { Ht = Pos (cs M)
  ; _<ᴸ_ = _<ᴾ_
  ; h₀ = fstC M
  ; tr< = λ {m} {c} {d} → <ᴾ-trans m c d
  ; <-prop = <ᴾ-prop
  ; bot = botC M
  ; tri = <ᴾ-tri
  ; rk = rkP zero
  ; rk< = λ {a} {b} → rkP-mono zero a b
  ; view = λ m → proj₁ (V.vw M m)
  ; view-ok = λ m → proj₂ (V.vw M m)
  }
```
