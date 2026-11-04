# 严格列 (一): 块形与位置

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** `Sh` 只记块的形状: `sz` 空段, `ss` 上面加一个点, `sl g` 一列块. **这里没有值**: 没有 `plus`, `val`, `rk`, 也不读 `Ordᴵ`. 值和秩在 [TLCodeLit](TLCodeLit.lagda.md) 由严格列直接读出. 序, 三歧, 根, 第 0 行的写法与形状有关, 与值无关, 所以这部分和 [LadderOrdPos](LadderOrdPos.lagda.md) §1, §2, §4, §5 逐行相同, 只改了名字 (`Code` → `Sh`, `cz` → `sz`, `cs` → `ss`, `cl` → `sl`, `fstC` → `fstS`, `botC` → `botS`); 生成脚本是一次性的 `sed` 式替换, 没有留. 本文件的导入闭包不含 `LadderOrdPos`, `LadderOrdCode`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.LadderOrdBase using (Tri; tlt; teq; tgt; View; base; clos; chain; ViewOk)
```

## §1 块形与位置

```agda
data Sh : Set where
  sz : Sh
  ss : Sh → Sh
  sl : (ℕ → Sh) → Sh

data Pos : Sh → Set where
  end : ∀ {c} → Pos (ss c)
  low : ∀ {c} → Pos c → Pos (ss c)
  blk : ∀ {g} j → Pos (ss (g j)) → Pos (sl g)
```

## §2 序

字典序. 对块号的比较把 $g$ 平移, 这样相等的情形不用 `subst`.

```agda
infix 4 _<ᴾ_
_<ᴾ_ : ∀ {c} → Pos c → Pos c → Set
ltB : (g : ℕ → Sh) (j k : ℕ) → Pos (ss (g j)) → Pos (ss (g k)) → Set
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
ltB-trans : ∀ g j k l (p : Pos (ss (g j))) (q : Pos (ss (g k))) (r : Pos (ss (g l))) → ltB g j k p q → ltB g k l q r → ltB g j l p r
<ᴾ-trans (low p) (low q) end x y = tt
<ᴾ-trans (low p) (low q) (low r) x y = <ᴾ-trans p q r x y
<ᴾ-trans (blk {g} j p) (blk k q) (blk l r) x y = ltB-trans g j k l p q r x y
ltB-trans g zero zero zero p q r x y = <ᴾ-trans p q r x y
ltB-trans g zero zero (suc l) p q r x y = tt
ltB-trans g zero (suc k) (suc l) p q r x y = tt
ltB-trans g (suc j) (suc k) (suc l) p q r x y = ltB-trans (λ i → g (suc i)) j k l p q r x y

shB : ∀ {g} → Pos (sl (λ i → g (suc i))) → Pos (sl g)
shB (blk j p) = blk (suc j) p

<ᴾ-tri : ∀ {c} (p q : Pos c) → Tri _<ᴾ_ p q
triB : ∀ g j k (p : Pos (ss (g j))) (q : Pos (ss (g k))) → Tri _<ᴾ_ (blk {g} j p) (blk {g} k q)
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
triB-self : ∀ g j (p : Pos (ss (g j))) → triB g j j p p ≡ teq refl
<ᴾ-tri-self end = refl
<ᴾ-tri-self (low p) rewrite <ᴾ-tri-self p = refl
<ᴾ-tri-self (blk {g} j p) = triB-self g j p
triB-self g zero p rewrite <ᴾ-tri-self p = refl
triB-self g (suc j) p rewrite triB-self (λ i → g (suc i)) j p = refl

-- 块内, 块间
ltB-same : ∀ g j {p q : Pos (ss (g j))} → p <ᴾ q → ltB g j j p q
ltB-same g zero x = x
ltB-same g (suc j) x = ltB-same (λ i → g (suc i)) j x

ltB-next : ∀ g j (p : Pos (ss (g j))) (q : Pos (ss (g (suc j)))) → ltB g j (suc j) p q
ltB-next g zero p q = tt
ltB-next g (suc j) p q = ltB-next (λ i → g (suc i)) j p q
```

## §3 根

```agda
fstS : ∀ c → Pos (ss c)
fstS sz     = end
fstS (ss c) = low (fstS c)
fstS (sl g) = low (blk 0 (fstS (g 0)))

botS : ∀ c (p : Pos (ss c)) → (fstS c ≡ p) ⊎ (fstS c <ᴾ p)
botS sz end = inj₁ refl
botS sz (low ())
botS (ss c) end = inj₂ tt
botS (ss c) (low p) with botS c p
... | inj₁ refl = inj₁ refl
... | inj₂ x = inj₂ x
botS (sl g) end = inj₂ tt
botS (sl g) (low (blk zero p)) with botS (g 0) p
... | inj₁ refl = inj₁ refl
... | inj₂ x = inj₂ x
botS (sl g) (low (blk (suc j) p)) = inj₂ tt

IsFst : ∀ {c} → Pos c → Set
IsFst (end {c = sz})   = ⊤
IsFst (end {ss c}) = ⊥
IsFst (end {sl g}) = ⊥
IsFst (low p)      = IsFst p
IsFst (blk zero p) = IsFst p
IsFst (blk (suc j) p) = ⊥

isf : ∀ c (x : Pos (ss c)) → IsFst x → x ≡ fstS c
isf sz end h = refl
isf sz (low ()) h
isf (ss c) (low x) h = cong low (isf c x h)
isf (sl g) (low (blk zero x)) h = cong (λ z → low (blk 0 z)) (isf (g 0) x h)
```

## §4 第 0 行的写法

`viewC` 走位置的路径, 带着上下文 $\iota$ 与 "这一段开始之前" 的信息 `St`: 要么这一段就是最开头, 要么有前一个元素 $n$. 块的结束点 `blk j end` 总在, 所以每个块的开头要么是最开头, 要么有前驱. 叶子 `end {c}` 看 $c$ 的头: $c=$ `sz` 看 `St`; `ss` 是闭包; `sl g` 是链, 第 $i$ 项是 `blk i end`.

```agda
module V (M : Sh) where
  H : Set
  H = Pos (ss M)

  h₀ᴾ : H
  h₀ᴾ = fstS M

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

  record Cxt (c : Sh) : Set where
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

  ok-low : ∀ {c} st (ι : Pos (ss c) → H) → St0 st ι → St0 st (λ p → ι (low p))
  ok-low sf ι h = λ x f → h (low x) f
  ok-low (sp n) ι h = λ x → h (low x)

  Cl : ∀ {c} → Cxt (ss c) → Cxt c
  Cl {c} C = mkC (λ p → ι C (low p)) (λ p q x → ιm C (low p) (low q) x) (stv C) (ok-low (stv C) (ι C) (ok0 C))
    (λ x r → go (dec C (low x) r))
    where
    go : ∀ {y x} → (Σ (Pos (ss c)) λ y′ → (y ≡ ι C y′) × (y′ <ᴾ low x)) ⊎ LB (stv C) y → (Σ (Pos c) λ y′ → (y ≡ ι C (low y′)) × (y′ <ᴾ x)) ⊎ LB (stv C) y
    go (inj₁ (low y′ , e , l)) = inj₁ (y′ , e , l)
    go (inj₂ b) = inj₂ b

  -- 第 0 块的上下文
  B0dec : ∀ {g} (x : Pos (ss (g 0))) (y′ : Pos (sl g)) → y′ <ᴾ blk 0 x → Σ (Pos (ss (g 0))) λ z → (y′ ≡ blk 0 z) × (z <ᴾ x)
  B0dec x (blk zero z) l = z , refl , l

  ok-b0 : ∀ {g} st (ι : Pos (sl g) → H) → St0 st ι → St0 st (λ p → ι (blk 0 p))
  ok-b0 sf ι h = λ x f → h (blk 0 x) f
  ok-b0 (sp n) ι h = λ x → h (blk 0 x)

  Cb0 : ∀ {g} → Cxt (sl g) → Cxt (ss (g 0))
  Cb0 {g} C = mkC (λ p → ι C (blk 0 p)) (λ p q x → ιm C (blk 0 p) (blk 0 q) x) (stv C) (ok-b0 (stv C) (ι C) (ok0 C))
    (λ x r → go x (dec C (blk 0 x) r))
    where
    go : ∀ {y} x → (Σ (Pos (sl g)) λ y′ → (y ≡ ι C y′) × (y′ <ᴾ blk 0 x)) ⊎ LB (stv C) y → (Σ (Pos (ss (g 0))) λ y′ → (y ≡ ι C (blk 0 y′)) × (y′ <ᴾ x)) ⊎ LB (stv C) y
    go x (inj₁ (y′ , e , l)) with B0dec x y′ l
    ... | z , refl , l′ = inj₁ (z , e , l′)
    go x (inj₂ b) = inj₂ b

  -- 第 j+1 块: 前驱是第 j 块的结束点
  split : ∀ g k j (z : Pos (ss (g k))) (x : Pos (ss (g (suc j)))) → ltB g k (suc j) z x →
          (Σ (Pos (ss (g (suc j)))) λ z′ → (blk {g} k z ≡ blk (suc j) z′) × (z′ <ᴾ x)) ⊎ ((blk {g} k z ≡ blk j end) ⊎ (blk {g} k z <ᴾ blk j end))
  split g zero zero end x l = inj₂ (inj₁ refl)
  split g zero zero (low z) x l = inj₂ (inj₂ tt)
  split g zero (suc j) z x l = inj₂ (inj₂ tt)
  split g (suc zero) zero z x l = inj₁ (z , refl , l)
  split g (suc (suc k)) zero z x ()
  split g (suc k) (suc j) z x l with split (λ i → g (suc i)) k j z x l
  ... | inj₁ (z′ , e , l′) = inj₁ (z′ , cong shB e , l′)
  ... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong shB e))
  ... | inj₂ (inj₂ r) = inj₂ (inj₂ r)

  CbS : ∀ {g} j → Cxt (sl g) → Cxt (ss (g (suc j)))
  CbS {g} j C = mkC (λ p → ι C (blk (suc j) p))
    (λ p q x → ιm C (blk (suc j) p) (blk (suc j) q) (ltB-same g (suc j) x))
    (sp (ι C (blk j end)))
    (λ x → ιm C (blk j end) (blk (suc j) x) (ltB-next g j end x))
    go
    where
    n₁ = ι C (blk j end)
    go : ∀ {y} x → y <ᴾ ι C (blk (suc j) x) → (Σ (Pos (ss (g (suc j)))) λ y′ → (y ≡ ι C (blk (suc j) y′)) × (y′ <ᴾ x)) ⊎ ((y ≡ n₁) ⊎ (y <ᴾ n₁))
    go {y} x r with dec C (blk (suc j) x) r
    ... | inj₂ b = inj₂ (inj₂ (LB-lt C (blk j end) b))
    ... | inj₁ (blk k z , e , l) with split g k j z x l
    ...   | inj₁ (z′ , e′ , l′) = inj₁ (z′ , trans e (cong (ι C) e′) , l′)
    ...   | inj₂ (inj₁ e′) = inj₂ (inj₁ (trans e (cong (ι C) e′)))
    ...   | inj₂ (inj₂ r′) = inj₂ (inj₂ (subst (_<ᴾ n₁) (sym e) (ιm C (blk k z) (blk j end) r′)))

  -- 块内的点不超过块的结束点
  blk≤end : ∀ g j (z : Pos (ss (g j))) → (blk {g} j z ≡ blk j end) ⊎ (blk {g} j z <ᴾ blk j end)
  blk≤end g j end = inj₁ refl
  blk≤end g j (low z) = inj₂ (ltB-same g j tt)

  viewC : ∀ {c} (C : Cxt c) (p : Pos c) → W (ι C p)
  viewC {ss sz} (mkC ι ιm sf ok0 dec) end = subst W (sym (ok0 end tt)) (base , tt)
  viewC {ss sz} (mkC ι ιm (sp n) ok0 dec) end = clos (ok0 end) , go
    where
    go : ∀ {x} → x <ᴾ ι end → (x ≡ n) ⊎ (x <ᴾ n)
    go r with dec end r
    ... | inj₁ (low () , _ , _)
    ... | inj₂ b = b
  viewC {ss (ss c)} C end = clos (ιm C (low end) end tt) , go
    where
    go : ∀ {x} → x <ᴾ ι C end → (x ≡ ι C (low end)) ⊎ (x <ᴾ ι C (low end))
    go r with dec C end r
    ... | inj₁ (low end , e , _) = inj₁ e
    ... | inj₁ (low (low z) , e , _) = inj₂ (subst (_<ᴾ ι C (low end)) (sym e) (ιm C (low (low z)) (low end) tt))
    ... | inj₂ b = inj₂ (LB-lt C (low end) b)
  viewC {ss (sl g)} C end =
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

  C₀ : Cxt (ss M)
  C₀ = mkC (λ x → x) (λ p q x → x) sf (λ x h → isf M x h) (λ x r → inj₁ (_ , refl , r))

  vw : ∀ m → W m
  vw m = viewC C₀ m
```

