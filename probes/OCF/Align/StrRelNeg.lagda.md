# 结构关系 (六): 只由值求首对齐推出 LPO

> 不含记号, 不提折叠. 入口 [StrRel](StrRel.lagda.md). `KNest2` §3 的第三条判断 ("由值求首对齐的对应点, 要在右边的字面结构里找出与左边偏移值相等的层, 一般不可判定") 的编译形式.
>
> **`VHead`**: 一个过程, 对一切第 0 层树 $x, x'$ 与 $\mathrm{val}\,x\le\mathrm{val}\,x'$ 的证明, 把 $x$ 的每个位置 $s$ 送到 $x'$ 的一个位置 $s'$, 使 $\mathrm{rem}\,s\le\mathrm{rem}\,s'$ (只要求剩余长度, 不要求前缀; 所以比 `StrRelHead.headAdm` 给出的弱).
>
> **定理 `vhead→LPO : VHead → LPO`.** 经典地 `VHead` 成立 (取右边与左边偏移相同的位置; 判断, 未编译), 所以否定的是构造性. 反例族: 左边 $x=1⨾\omega$, 位置取开头 (剩余 $\omega$). 右边 $x'_f=A_f⨾B_f$, $A_f=\mathrm{nl}(n\mapsto f\,n\ ?\ \omega : 0)$, $B_f=\mathrm{nl}(n\mapsto (f\text{ 到 }n\text{ 全假})\ ?\ 1 : 0)$. 值上总有 $\omega\le x'_f$ (有界搜索, `prem`). 剩余 $\ge\omega$ 的位置: 若 $f$ 有真, 只在 $A_f$ 里 ($B_f$ 有限); 若 $f$ 全假, 只在 $B_f$ 里 ($A_f$ 没有位置). 所以位置落在哪一半就判定了 $f$.
>
> **范围.** 只杀 "只看值、对一切值可比的对给出对应位置" 的做法. 不杀由结构关系给出的首对齐 (`StrRelHead.head`, 构造的), 也不杀带额外数据 (推导) 的做法.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRelNeg where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊲→≤; irr; _⊞_; ⊞-mono; z⊞)
open import OCF.Align.HtFeedTree using (D; hz; n0; n1; _⨾_; nl; sum; pt; sum-fst)
open import OCF.Align.StrRelHead using (val; Sp; here; inl; inr; inn; rem; Tl; tl-cons; bmono; ≡→≤; cons≡)
```

## §1 陈述

```agda
VHead : Set
VHead = ∀ {V} (x x′ : D hz V) → val x ≤ val x′ → (s : Sp x) → Σ (Sp x′) (λ s′ → rem s ≤ rem s′)

LPO : Set
LPO = ∀ (f : ℕ → Bool) → Σ ℕ (λ n → f n ≡ true) ⊎ (∀ n → f n ≡ false)
```

## §2 小件

```agda
fin : ℕ → A
fin zero = azero
fin (suc n) = asuc (fin n)

z⊞′ : ∀ δ → azero ⊞ δ ≤ δ
z⊞′ azero = z≤
z⊞′ (asuc δ) = s≤ (z⊞′ δ)
z⊞′ (alim g) = l≤ (λ n → ≤l n (z⊞′ (g n)))

finS : ∀ m → fin m ≤ fin (suc m)
finS m = ≤-suc (≤-refl (fin m))

≤⊞ˡ : ∀ a b → b ≤ a ⊞ b
≤⊞ˡ a azero = z≤
≤⊞ˡ a (asuc b) = s≤ (≤⊞ˡ a b)
≤⊞ˡ a (alim f) = l≤ (λ n → ≤l n (≤⊞ˡ a (f n)))

-- 尾巴不超过整个
tl≤ : ∀ {V} (d : ℕ → D hz V) k → Tl d k ≤ Tl d 0
tl≤ d zero = ≤-refl _
tl≤ d (suc k) = ≤-trans (≤⊞ˡ (val (d k)) (Tl d (suc k))) (≤-trans (tl-cons d k) (tl≤ d k))

ptmono : ∀ {V} (d : ℕ → D hz V) c j k → pt c d k ≤ pt c d (j + k)
ptmono d c zero k = ≤-refl _
ptmono d c (suc j) k = ≤-trans (ptmono d c j k) (⊲→≤ (sum-fst (pt c d (j + k)) (d (j + k))))

ite : Bool → D hz azero → D hz azero → D hz azero
ite true a b = a
ite false a b = b

∧l : ∀ {x y} → x ∧ y ≡ true → x ≡ true
∧l {x = true} _ = refl
∧l {x = false} ()

∧f : ∀ x → x ∧ false ≡ false
∧f true = refl
∧f false = refl

ω₁ : D hz azero
ω₁ = nl (λ _ → n1)

c1 : ℕ → D hz azero
c1 _ = n1

finω : ∀ m → fin m ≤ pt azero c1 m
finω zero = z≤
finω (suc m) = s≤ (finω m)

-- 每项至多 1
pt≤fin : ∀ (g : ℕ → Bool) c m → pt c (λ n → ite (g n) n1 n0) m ≤ c ⊞ fin m
pt≤fin g c zero = ≤-refl c
pt≤fin g c (suc m) with g m
... | true = s≤ (pt≤fin g c m)
... | false = ≤-suc (pt≤fin g c m)

spA : ∀ bo → Sp (ite bo ω₁ n0) → bo ≡ true
spA true _ = refl
spA false ()

remB : ∀ bo (t : Sp (ite bo n1 n0)) → rem t ≡ azero
remB true here = refl
remB false ()
```

## §3 反例族

```agda
module Fam (f : ℕ → Bool) where
  allF : ℕ → Bool
  allF zero = not (f 0)
  allF (suc m) = allF m ∧ not (f (suc m))

  a b : ℕ → D hz azero
  a n = ite (f n) ω₁ n0
  b n = ite (allF n) n1 n0

  x x′ : D hz azero
  x = n1 ⨾ ω₁
  x′ = nl a ⨾ nl b

  -- 有界搜索
  search : ∀ m → Σ ℕ (λ j → f j ≡ true) ⊎ (allF m ≡ true)
  search zero with f 0 in e
  ... | true = inj₁ (0 , e)
  ... | false = inj₂ refl
  search (suc m) with search m
  ... | inj₁ w = inj₁ w
  ... | inj₂ e with f (suc m) in e′
  ...   | true = inj₁ (suc m , e′)
  ...   | false = inj₂ (subst (λ z → z ∧ true ≡ true) (sym e) refl)

  ωA : ∀ j → f j ≡ true → val ω₁ ≤ val (nl a)
  ωA j e = ≤l (suc j) (≤-trans (subst (λ bo → val ω₁ ≤ sum azero (ite bo ω₁ n0)) (sym e) (≤-refl _)) (bmono (a j) {azero} z≤))

  finB : ∀ c m → allF m ≡ true → fin (suc m) ≤ pt c b (suc m)
  finB c zero e = subst (λ bo → fin 1 ≤ sum c (ite bo n1 n0)) (sym e) (s≤ z≤)
  finB c (suc m) e =
    subst (λ bo → fin (suc (suc m)) ≤ sum (pt c b (suc m)) (ite bo n1 n0)) (sym e) (s≤ (finB c m (∧l e)))

  prem : val x ≤ val x′
  prem = l≤ (λ m → ≤-trans (≡→≤ (sym (cons≡ azero c1 m))) (≤-trans (finω′ (suc m)) (g (suc m))))
    where
    finω′ : ∀ m → pt azero c1 m ≤ fin m
    finω′ zero = z≤
    finω′ (suc m) = s≤ (finω′ m)
    X = val (nl a)
    g : ∀ m → fin m ≤ val x′
    g m with search m
    ... | inj₁ (j , e) = ≤-trans (≤-trans (≤l m (finω m)) (ωA j e)) (⊲→≤ (sum-fst X (nl b)))
    ... | inj₂ e = ≤l (suc m) (≤-trans (finS m) (finB X m e))

  -- f n 为真则 B_f 有限
  allF-false : ∀ {n} → f n ≡ true → ∀ j → allF (j + n) ≡ false
  allF-false {n = zero} e zero = cong not e
  allF-false {n = suc n} e zero = subst (λ z → allF n ∧ not z ≡ false) (sym e) (∧f (allF n))
  allF-false e (suc j) = subst (λ z → z ∧ not (f (suc (j + _))) ≡ false) (sym (allF-false e j)) refl

  stab : ∀ {n} → f n ≡ true → ∀ j → pt azero b (j + n) ≤ pt azero b n
  stab e zero = ≤-refl _
  stab {n} e (suc j) =
    subst (λ bo → sum (pt azero b (j + n)) (ite bo n1 n0) ≤ pt azero b n) (sym (allF-false e j)) (stab e j)

  boundB : ∀ {n} → f n ≡ true → val (nl b) ≤ fin n
  boundB {n} e = l≤ (λ m →
    ≤-trans (ptmono b azero n m)
      (≤-trans (≡→≤ (cong (pt azero b) (+-comm n m)))
        (≤-trans (stab e m) (≤-trans (pt≤fin allF azero n) (z⊞′ (fin n))))))
```

## §4 定理

```agda
vhead→LPO : VHead → LPO
vhead→LPO vh f with vh x x′ prem (inl here)
  where open Fam f
... | inl (inn k t₀) , r = inj₁ (k , spA (f k) t₀)
... | inr (inn k t₀) , r = inj₂ dec
  where
  open Fam f
  dec : ∀ n → f n ≡ false
  dec n with f n in e
  ... | false = refl
  ... | true = ⊥-elim (irr (fin n) (≤-trans (≤l (suc n) (finω (suc n))) (≤-trans (z⊞ (val ω₁)) (≤-trans r′ (z⊞′ (fin n))))))
    where
    r′ : azero ⊞ val ω₁ ≤ azero ⊞ fin n
    r′ = ≤-trans r (≤-trans (≡→≤ (cong (λ z → z ⊞ Tl b (suc k)) (remB (allF k) t₀)))
                     (⊞-mono (≤-refl azero) (≤-trans (tl≤ b (suc k)) (boundB e))))
```
