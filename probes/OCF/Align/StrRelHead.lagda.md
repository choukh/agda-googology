# 结构关系 (五): 首对齐

> 不含记号, 不提折叠. 入口 [StrRel](StrRel.lagda.md). 这里回答 `KNest2` §3 的接口问题: 一格之内的首对齐要两格坐标 (上一格的输出) 由不含左边极限截断的结构关系相关. 本文证: **$\sqsubseteq_0$ 推出首对齐**, 对推导归纳, 每个构造子一步, 构造性的.
>
> - `Sp x`: $x$ 里一个 `n1` 的位置 (一格里被走到的一层). `pre s`: 位置之前的前缀树; `rem s`: 位置之后剩下的长度 (值).
> - `dec`: $b+x\approx (b+\mathrm{pre}\,s)+1+\mathrm{rem}\,s$ (两个方向的 $\le$). 被走到的层是 $c=b+\mathrm{pre}\,s$, 区间的终点是 $b+x$.
> - **`head`**: $x\sqsubseteq_0 x'$ ⇒ 对 $x$ 的每个位置 $s$ 给出 $x'$ 的位置 $s'$, $\mathrm{pre}\,s\sqsubseteq_0\mathrm{pre}\,s'$ 且 $\mathrm{rem}\,s\le\mathrm{rem}\,s'$. 只有 `pr` 那一步要把右边的有限前缀换成极限里的位置 (`toNl`, 剩余变长, 方向对).
> - **`headAdm`**: 再加两个起点 $v\le v'$: 被走到的两层 $c\le c'$, 且 $\mathrm{Adm}(c,c';\,v+x,\,v'+x')$ (`KNestAdm.Adm`: 左边剩下的长度放得进右边). 这正是 `KNest2Glue.CellStep` 的格在每一层要的领先量.
>
> **为什么左边极限截断不行 (判断, 对照 [StrRelNeg](StrRelNeg.lagda.md)).** `head` 的每一步只把左边的一个位置送到右边的一个位置. 若关系里有 "$\forall k.\ x⨾\mathrm{pre}\,d\,k\sqsubseteq t$ ⇒ $x⨾\mathrm{nl}\,d\sqsubseteq t$", 左边 $d_j$ 里的位置要经某个 $k>j$ 的前缀推导送过去, 那个推导只保证前缀的剩余 ($d_{j..k-1}$) 放得进去, 左边真实的剩余是无穷的尾巴. `StrRelNeg` 把 "只由值求对应位置" 编译成否定 (推出 LPO).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRelHead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ≤⊞; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.HtFeedTree using (D; hz; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
open import OCF.Align.StrRelDef {azero} tt using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; tr; u0l; u0r; u1l; u1r; al; al′; ar; ar′;
  refl₀; val₀; prv; preL₀; preL)
```

`Adm` 与 `KNestAdm.Adm` 逐字相同 (入口里 `adm≡ : … ≡ KNestAdm.Adm …` 是 `refl`). 本地写一份, 是为了不导入 `KNestAdm` (它经 `KNestNeg` 的闭包里有 `DValCanon`).

```agda
Adm : A → A → A → A → Set
Adm α α′ ℓ ℓ′ = Σ A (λ δ → (ℓ ≤ α ⊞ δ) × (α′ ⊞ δ ≤ ℓ′))
```

## §1 值的小件

```agda
val : ∀ {V} → D hz V → A
val x = sum azero x

≡→≤ : ∀ {a b} → a ≡ b → a ≤ b
≡→≤ refl = ≤-refl _

bmono : ∀ {V} (x : D hz V) {b b′} → b ≤ b′ → sum b x ≤ sum b′ x
bmono x h = val₀ (refl₀ x) h

-- sum 与 ⊞
sum⊞ : ∀ {V} a (x : D hz V) → (a ⊞ val x ≤ sum a x) × (sum a x ≤ a ⊞ val x)
pt⊞  : ∀ {V} a (d : ℕ → D hz V) n → (a ⊞ pt azero d n ≤ pt a d n) × (pt a d n ≤ a ⊞ pt azero d n)
sum⊞ a n0 = ≤-refl a , ≤-refl a
sum⊞ a n1 = ≤-refl _ , ≤-refl _
sum⊞ a (x ⨾ y) =
  ≤-trans (⊞-mono (≤-refl a) (proj₂ (sum⊞ (val x) y)))
    (≤-trans (⊞-asso a (val x) (val y))
      (≤-trans (⊞-mono (proj₁ (sum⊞ a x)) (≤-refl _)) (proj₁ (sum⊞ (sum a x) y)))) ,
  ≤-trans (proj₂ (sum⊞ (sum a x) y))
    (≤-trans (⊞-mono (proj₂ (sum⊞ a x)) (≤-refl _))
      (≤-trans (⊞-assoʳ a (val x) (val y)) (⊞-mono (≤-refl a) (proj₁ (sum⊞ (val x) y)))))
sum⊞ a (nl d) = l≤ (λ n → ≤l n (proj₁ (pt⊞ a d n))) , l≤ (λ n → ≤l n (proj₂ (pt⊞ a d n)))
sum⊞ a (ni () u)
sum⊞ a (nκ () u)
sum⊞ a (nw p x) = sum⊞ a x
pt⊞ a d zero = ≤-refl a , ≤-refl a
pt⊞ a d (suc n) =
  ≤-trans (⊞-mono (≤-refl a) (proj₂ (sum⊞ (pt azero d n) (d n))))
    (≤-trans (⊞-asso a (pt azero d n) (val (d n)))
      (≤-trans (⊞-mono (proj₁ (pt⊞ a d n)) (≤-refl _)) (proj₁ (sum⊞ (pt a d n) (d n))))) ,
  ≤-trans (proj₂ (sum⊞ (pt a d n) (d n)))
    (≤-trans (⊞-mono (proj₂ (pt⊞ a d n)) (≤-refl _))
      (≤-trans (⊞-assoʳ a (pt azero d n) (val (d n))) (⊞-mono (≤-refl a) (proj₁ (sum⊞ (pt azero d n) (d n))))))

pt≡ : ∀ {V} b (d : ℕ → D hz V) n → pt b d n ≡ sum b (preL d n)
pt≡ b d zero = refl
pt≡ b d (suc n) = cong (λ t → sum t (d n)) (pt≡ b d n)

-- 去掉第一项
cons≡ : ∀ {V} b (d : ℕ → D hz V) m → pt b d (suc m) ≡ pt (sum b (d 0)) (λ k → d (suc k)) m
cons≡ b d zero = refl
cons≡ b d (suc m) = cong (λ t → sum t (d (suc m))) (cons≡ b d m)

-- 尾巴: 去掉前 k 项
drop : ∀ {X : Set} → (ℕ → X) → ℕ → ℕ → X
drop d zero = d
drop d (suc k) = drop (λ m → d (suc m)) k

Tl : ∀ {V} → (ℕ → D hz V) → ℕ → A
Tl d k = val (nl (drop d k))

dropR : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ k m → drop d k m ⊑₀ drop d′ k m
dropR h zero m = h m
dropR h (suc k) m = dropR (λ n → h (suc n)) k m

Tl-mono : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ k → Tl d k ≤ Tl d′ k
Tl-mono h k = val₀ (lm (dropR h k)) z≤
```

**极限的拆分.** $\lim_m(b+d_0+\dots+d_{m-1})\approx (b+d_0+\dots+d_n)+\mathrm{Tl}\,d\,(n+1)$. 对 $n$ 归纳, 每步去掉第一项 (`cons≡`); 尾巴 `drop` 的定义让 $\mathrm{Tl}\,d\,(n+2)$ 与 $\mathrm{Tl}\,(d\circ\mathrm{suc})\,(n+1)$ 定义性相同.

```agda
shift : ∀ {V} b (d : ℕ → D hz V) → (alim (pt b d) ≤ alim (pt (sum b (d 0)) (λ k → d (suc k)))) ×
                                    (alim (pt (sum b (d 0)) (λ k → d (suc k))) ≤ alim (pt b d))
shift b d = l≤ f , l≤ (λ m → ≤l (suc m) (≡→≤ (sym (cons≡ b d m))))
  where
  f : ∀ k → pt b d k ≤ alim (pt (sum b (d 0)) (λ k → d (suc k)))
  f zero = ≤l 0 (⊲→≤ (sum-fst b (d 0)))
  f (suc m) = ≤l m (≡→≤ (cons≡ b d m))

lsplit : ∀ {V} b (d : ℕ → D hz V) n → (alim (pt b d) ≤ pt b d (suc n) ⊞ Tl d (suc n)) × (pt b d (suc n) ⊞ Tl d (suc n) ≤ alim (pt b d))
lsplit b d zero =
  ≤-trans (proj₁ (shift b d)) (l≤ (λ m → ≤l m (proj₂ (pt⊞ b₁ e m)))) ,
  ≤-trans (l≤ (λ m → ≤l m (proj₁ (pt⊞ b₁ e m)))) (proj₂ (shift b d))
  where
  b₁ = sum b (d 0)
  e = λ k → d (suc k)
lsplit b d (suc n) =
  ≤-trans (proj₁ (shift b d)) (≤-trans (proj₁ (lsplit b₁ e n)) (⊞-mono (≡→≤ (sym (cons≡ b d (suc n)))) (≤-refl _))) ,
  ≤-trans (⊞-mono (≡→≤ (cons≡ b d (suc n))) (≤-refl _)) (≤-trans (proj₂ (lsplit b₁ e n)) (proj₂ (shift b d)))
  where
  b₁ = sum b (d 0)
  e = λ k → d (suc k)

-- 第 k 项加上它之后的尾巴, 不超过从第 k 项起的尾巴
tl-cons : ∀ {V} (d : ℕ → D hz V) k → val (d k) ⊞ Tl d (suc k) ≤ Tl d k
tl-cons d zero = l≤ (λ m → ≤l (suc m) (≤-trans (proj₁ (pt⊞ (val (d 0)) (λ k → d (suc k)) m)) (≡→≤ (sym (cons≡ azero d m)))))
tl-cons d (suc k) = tl-cons (λ m → d (suc m)) k
```

## §2 位置

```agda
data Sp : ∀ {V} → D hz V → Set where
  here : ∀ {V} → Sp (n1 {W = V})
  inl  : ∀ {V} {x y : D hz V} → Sp x → Sp (x ⨾ y)
  inr  : ∀ {V} {x y : D hz V} → Sp y → Sp (x ⨾ y)
  inn  : ∀ {V} {d : ℕ → D hz V} n → Sp (d n) → Sp (nl d)
  inw  : ∀ {V₀ V} {p : V₀ ⊲ V} {x : D hz V₀} → Sp x → Sp (nw p x)

pre : ∀ {V} {x : D hz V} → Sp x → D hz V
pre here = n0
pre (inl s) = pre s
pre (inr {x = x} s) = x ⨾ pre s
pre (inn {d = d} n s) = preL d n ⨾ pre s
pre (inw {p = p} s) = nw p (pre s)

rem : ∀ {V} {x : D hz V} → Sp x → A
rem here = azero
rem (inl {y = y} s) = rem s ⊞ val y
rem (inr s) = rem s
rem (inn {d = d} n s) = rem s ⊞ Tl d (suc n)
rem (inw s) = rem s
```

**拆分 `dec`.** $b+x\approx(b+\mathrm{pre}\,s+1)+\mathrm{rem}\,s$.

```agda
dec : ∀ {V} {x : D hz V} b (s : Sp x) → (sum b x ≤ asuc (sum b (pre s)) ⊞ rem s) × (asuc (sum b (pre s)) ⊞ rem s ≤ sum b x)
dec b here = ≤-refl _ , ≤-refl _
dec b (inl {x = x} {y} s) =
  let (h₁ , h₂) = dec b s
      c = asuc (sum b (pre s))
  in ≤-trans (proj₂ (sum⊞ (sum b x) y)) (≤-trans (⊞-mono h₁ (≤-refl _)) (⊞-assoʳ c (rem s) (val y))) ,
     ≤-trans (⊞-asso c (rem s) (val y)) (≤-trans (⊞-mono h₂ (≤-refl _)) (proj₁ (sum⊞ (sum b x) y)))
dec b (inr {x = x} s) = dec (sum b x) s
dec b (inn {d = d} n s) =
  let b′ = sum b (preL d n)
      (h₁ , h₂) = dec b′ s
      c = asuc (sum b′ (pre s))
      e₁ : pt b d (suc n) ≤ sum b′ (d n)
      e₁ = bmono (d n) (≡→≤ (pt≡ b d n))
      e₂ : sum b′ (d n) ≤ pt b d (suc n)
      e₂ = bmono (d n) (≡→≤ (sym (pt≡ b d n)))
  in ≤-trans (proj₁ (lsplit b d n)) (≤-trans (⊞-mono (≤-trans e₁ h₁) (≤-refl _)) (⊞-assoʳ c (rem s) (Tl d (suc n)))) ,
     ≤-trans (⊞-asso c (rem s) (Tl d (suc n))) (≤-trans (⊞-mono (≤-trans h₂ e₂) (≤-refl _)) (proj₂ (lsplit b d n)))
dec b (inw s) = dec b s
```

**有限前缀里的位置搬到极限里.** 前缀树字面不变 (`pre≡`), 剩余变长 (`remTo`).

```agda
toNl : ∀ {V} {d : ℕ → D hz V} k → Sp (preL d k) → Sp (nl d)
toNl zero ()
toNl (suc k) (inl t) = toNl k t
toNl (suc k) (inr s) = inn k s

pre≡ : ∀ {V} {d : ℕ → D hz V} k (t : Sp (preL d k)) → pre (toNl k t) ≡ pre t
pre≡ zero ()
pre≡ (suc k) (inl t) = pre≡ k t
pre≡ (suc k) (inr s) = refl

remTo : ∀ {V} {d : ℕ → D hz V} k (t : Sp (preL d k)) → rem t ⊞ Tl d k ≤ rem (toNl k t)
remTo zero ()
remTo {d = d} (suc k) (inl t) =
  ≤-trans (⊞-assoʳ (rem t) (val (d k)) (Tl d (suc k))) (≤-trans (⊞-mono (≤-refl (rem t)) (tl-cons d k)) (remTo k t))
remTo (suc k) (inr s) = ≤-refl _
```

## §3 首对齐

```agda
Al : ∀ {V V′} → D hz V → D hz V′ → Set
Al x x′ = ∀ (s : Sp x) → Σ (Sp x′) (λ s′ → (pre s ⊑₀ pre s′) × (rem s ≤ rem s′))

head  : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → Al x x′
headP : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ k → Al (preL d k) (preL d′ k)

head z0 ()
head o1 here = here , (z0 , z≤)
head (sq hx hy) (inl s) = let (s′ , p , r) = head hx s in inl s′ , (p , ⊞-mono r (val₀ hy z≤))
head (sq hx hy) (inr s) = let (s′ , p , r) = head hy s in inr s′ , (sq hx p , r)
head (lm hd) (inn n s) = let (s′ , p , r) = head (hd n) s in inn n s′ , (sq (preL₀ hd n) p , ⊞-mono r (Tl-mono hd (suc n)))
head (wl hx) (inw s) = let (s′ , p , r) = head hx s in s′ , (wl p , r)
head (wr hx) s = let (s′ , p , r) = head hx s in inw s′ , (wr p , r)
head (pr hx hd k) (inl s) = let (s′ , p , r) = head hx s in inl s′ , (p , ⊞-mono r (≤l k (prv hd z≤ k)))
head (pr {d′ = d′} hx hd k) (inr t) =
  let (t′ , p , r) = headP hd k t
  in inr (toNl k t′) , (sq hx (subst (λ u → _ ⊑₀ u) (sym (pre≡ k t′)) p) ,
                        ≤-trans r (≤-trans (≤⊞ (rem t′) (Tl d′ k)) (remTo k t′)))
head (tr h h′) s = let (s′ , p , r) = head h s ; (s″ , p′ , r′) = head h′ s′ in s″ , (tr p p′ , ≤-trans r r′)
head (u0l h) (inl ())
head (u0l h) (inr s) = let (s′ , p , r) = head h s in s′ , (u0l p , r)
head (u0r h) s = let (s′ , p , r) = head h s in inr s′ , (u0r p , r)
head (u1l h) (inl s) = head h s
head (u1l h) (inr ())
head (u1r h) s = let (s′ , p , r) = head h s in inl s′ , (p , r)
head (al {x = x} {y} {z} h) (inl (inl s)) =
  let (s′ , p , r) = head h (inl s)
  in s′ , (p , ≤-trans (≤-trans (⊞-assoʳ (rem s) (val y) (val z)) (⊞-mono (≤-refl (rem s)) (proj₁ (sum⊞ (val y) z)))) r)
head (al h) (inl (inr s)) = head h (inr (inl s))
head (al h) (inr s) = let (s′ , p , r) = head h (inr (inr s)) in s′ , (al p , r)
head (al′ {x = x} {y} {z} h) (inl s) =
  let (s′ , p , r) = head h (inl (inl s))
  in s′ , (p , ≤-trans (≤-trans (⊞-mono (≤-refl (rem s)) (proj₂ (sum⊞ (val y) z))) (⊞-asso (rem s) (val y) (val z))) r)
head (al′ h) (inr (inl s)) = head h (inl (inr s))
head (al′ h) (inr (inr s)) = let (s′ , p , r) = head h (inr s) in s′ , (al′ p , r)
head (ar {x = x} {y} {z} h) s with head h s
... | inl (inl s′) , p , r = inl s′ , (p , ≤-trans r (≤-trans (⊞-assoʳ (rem s′) (val y) (val z)) (⊞-mono (≤-refl (rem s′)) (proj₁ (sum⊞ (val y) z)))))
... | inl (inr s′) , p , r = inr (inl s′) , (p , r)
... | inr s′ , p , r = inr (inr s′) , (ar p , r)
head (ar′ {x = x} {y} {z} h) s with head h s
... | inl s′ , p , r = inl (inl s′) , (p , ≤-trans r (≤-trans (⊞-mono (≤-refl (rem s′)) (proj₂ (sum⊞ (val y) z))) (⊞-asso (rem s′) (val y) (val z))))
... | inr (inl s′) , p , r = inl (inr s′) , (p , r)
... | inr (inr s′) , p , r = inr s′ , (ar′ p , r)

headP hd zero ()
headP hd (suc k) (inl t) = let (t′ , p , r) = headP hd k t in inl t′ , (p , ⊞-mono r (val₀ (hd k) z≤))
headP hd (suc k) (inr s) = let (s′ , p , r) = head (hd k) s in inr s′ , (sq (preL₀ hd k) p , r)
```

## §4 领先量

两个起点 $v\le v'$. 被走到的层 $c=v+\mathrm{pre}\,s$, $c'=v'+\mathrm{pre}\,s'$; 区间终点 $\ell=v+x$, $\ell'=v'+x'$. 取 $\delta=1+\mathrm{rem}\,s$: $\ell\le c+\delta$ (`dec` 左边), $c'+\delta\le c'+(1+\mathrm{rem}\,s')\le\ell'$ (`dec` 右边).

```agda
headAdm : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ {v v′} → v ≤ v′ → (s : Sp x) →
          Σ (Sp x′) (λ s′ → (sum v (pre s) ≤ sum v′ (pre s′)) × Adm (sum v (pre s)) (sum v′ (pre s′)) (sum v x) (sum v′ x′))
headAdm h {v} {v′} hv s =
  let (s′ , p , r) = head h s
      c = sum v (pre s)
      c′ = sum v′ (pre s′)
  in s′ , (val₀ p hv ,
           ((asuc azero ⊞ rem s) ,
            ≤-trans (proj₁ (dec v s)) (⊞-assoʳ c (asuc azero) (rem s)) ,
            ≤-trans (⊞-mono (≤-refl c′) (⊞-mono (≤-refl (asuc azero)) r))
                    (≤-trans (⊞-asso c′ (asuc azero) (rem s′)) (proj₂ (dec v′ s′)))))
```
