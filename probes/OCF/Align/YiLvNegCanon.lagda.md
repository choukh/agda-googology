# YiLvNeg 第 3 项 (续)：槽位可以与证书无关，不要全知原理

**判决：编译构造与编译定理 (正面)。** `ccompare : Compare` 把 `YiLvIf.compare` 交出的槽位换成规范位置 (每个极限处取最小的可行分支)；
它读合法性的数据来判定，但交出的三路形状与槽位只由两个层号决定：换证书、换公共上界、沿路径搬位置都不变 (`ccompare-slot`, `ccompare-levels`, `ccompare-shift`)。最小分支是有界搜索：已知的位置给出上界，界内的可行性由有界比较判定。
没有的：`Tri` 里方程分量 (`lev i s ≡ j` 的证明) 与证书无关，没写成。接口 [YiLvIf](YiLvIf.lagda.md)，反面在 [YiLvNegCert](YiLvNegCert.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegCanon where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiLvNegCompare using (At; no-loop; no-both; no-same; lev-legal)
open import OCF.Align.YiLvNegCert
  using (Kᶜ; Kᶜ-plain; Kᶜ-legal; hiᶜ; loᶜ; Bᶜ)
```

## 1 界内的可行性可判定

`back`：`a` 是 `x` 的字面第一位置，`r` 是 `x` 的位置；判定 `r` 处的层号是不是也在 `a` 的某个位置上。
对 `x` 递归，极限处照 `compare` 把两边搬到同一个分支。这里读合法性的数据。

```agda
Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

back : ∀ x → Plain x → Legal x → ∀ {a} → CP a x → (r : Pre x) → Dec′ (At a (lev x r))
back x pl L self r = inj₁ (r , refl)
back (suc x) pl L (suc p) (inj₁ _) =
  inj₂ (λ a → no-loop x (subst (At x) (proj₂ a) (shift p (proj₁ a))))
back (suc x) pl L (suc p) (inj₂ r) = back x pl L p r
back (lim g) pl (st , lg) (lim m p) (n , r) with <-cmp m n
... | tri< m<n _ _ = back (g n) (pl n) (lg n) (CP-tr p (steps st (<⇒<′ m<n))) r
... | tri≈ _ refl _ = back (g m) (pl m) (lg m) p r
... | tri> _ _ n<m =
  subst (λ z → Dec′ (At _ z)) (proj₂ (shift (steps st (<⇒<′ n<m)) r))
    (back (g m) (pl m) (lg m) p (proj₁ (shift (steps st (<⇒<′ n<m)) r)))
back (lc k c w b t g) () L (fst p) r
```

## 2 最小的可行分支

一般的有界最小化：`P n` 成立，`n` 以下可判定，则有最小的 `m`；最小者唯一。

```agda
Least : (ℕ → Set) → ℕ → Set
Least P m = P m × (∀ k → k < m → P k → ⊥)

least : ∀ (P : ℕ → Set) n → P n → (∀ k → k < n → Dec′ (P k)) → Σ ℕ (Least P)
least P zero p dec = zero , p , (λ k ())
least P (suc n) p dec with dec zero (s≤s z≤n)
... | inj₁ p₀ = zero , p₀ , (λ k ())
... | inj₂ no with least (λ k → P (suc k)) n p (λ k lt → dec (suc k) (s≤s lt))
... | m , pm , mn = suc m , pm , (λ { zero _ → no ; (suc k) (s≤s lt) → mn k lt })

least-unique : ∀ (P : ℕ → Set) m m′ → Least P m → Least P m′ → m ≡ m′
least-unique P m m′ (pm , mn) (pm′ , mn′) with <-cmp m m′
... | tri< lt _ _ = ⊥-elim (mn′ m lt pm)
... | tri≈ _ e _ = e
... | tri> _ _ gt = ⊥-elim (mn m′ gt pm′)

occurs : ∀ (f : ℕ → LF) → (∀ n → Plain (f n)) → Legal (lim f) → ∀ j n → At (f n) j →
  ∀ k → k < n → Dec′ (At (f k) j)
occurs f pl (st , lg) j n (r , e) k lt =
  subst (λ z → Dec′ (At (f k) z)) e (back (f n) (pl n) (lg n) (steps st (<⇒<′ lt)) r)

first : ∀ (f : ℕ → LF) → (∀ n → Plain (f n)) → Legal (lim f) → ∀ j →
  At (lim f) j → Σ ℕ (Least (λ k → At (f k) j))
first f pl L j ((n , r) , e) =
  least (λ k → At (f k) j) n (r , e) (occurs f pl L j n (r , e))
```

## 3 规范位置，与它不依赖证书

`canon`：后继处位置的形状已定；极限处走到最小的可行分支，再往下递归。
`canon-const`：输入的位置与合法性证书都换掉，交出的位置不变。

```agda
in-lim : ∀ (f : ℕ → LF) j m → At (f m) j → At (lim f) j
in-lim f j m (r , e) = (m , r) , e

canon : ∀ i → Plain i → Legal i → ∀ j → At i j → At i j
canon (suc k) pl L j (inj₁ x , e) = inj₁ x , e
canon (suc k) pl L j (inj₂ r , e) =
  inj₂ (proj₁ (canon k pl L j (r , e))) , proj₂ (canon k pl L j (r , e))
canon (lim f) pl L j a =
  in-lim f j (proj₁ (first f pl L j a))
    (canon (f (proj₁ (first f pl L j a))) (pl (proj₁ (first f pl L j a)))
      (proj₂ L (proj₁ (first f pl L j a))) j (proj₁ (proj₂ (first f pl L j a))))

glue : ∀ (f : ℕ → LF) j (pl pl′ : ∀ n → Plain (f n)) (L L′ : Legal (lim f)) m m′
  (am : At (f m) j) (am′ : At (f m′) j) → m ≡ m′ →
  (∀ k (b b′ : At (f k) j) →
    proj₁ (canon (f k) (pl k) (proj₂ L k) j b) ≡ proj₁ (canon (f k) (pl′ k) (proj₂ L′ k) j b′)) →
  _≡_ {A = Pre (lim f)}
    (m , proj₁ (canon (f m) (pl m) (proj₂ L m) j am))
    (m′ , proj₁ (canon (f m′) (pl′ m′) (proj₂ L′ m′) j am′))
glue f j pl pl′ L L′ m .m am am′ refl ih = cong {B = Pre (lim f)} (λ z → m , z) (ih m am am′)

canon-const : ∀ i (pl pl′ : Plain i) (L L′ : Legal i) j (a a′ : At i j) →
  proj₁ (canon i pl L j a) ≡ proj₁ (canon i pl′ L′ j a′)
canon-const (suc k) pl pl′ L L′ j (inj₁ _ , e) (inj₁ _ , e′) = refl
canon-const (suc k) pl pl′ L L′ j (inj₁ _ , e) (inj₂ r′ , e′) = ⊥-elim (no-same (r′ , e′) e)
canon-const (suc k) pl pl′ L L′ j (inj₂ r , e) (inj₁ _ , e′) = ⊥-elim (no-same (r , e) e′)
canon-const (suc k) pl pl′ L L′ j (inj₂ r , e) (inj₂ r′ , e′) =
  cong inj₂ (canon-const k pl pl′ L L′ j (r , e) (r′ , e′))
canon-const (lim f) pl pl′ L L′ j a a′ =
  glue f j pl pl′ L L′ _ _ _ _
    (least-unique (λ k → At (f k) j) _ _
      (proj₂ (first f pl L j a)) (proj₂ (first f pl′ L′ j a′)))
    (λ k b b′ → canon-const (f k) (pl k) (pl′ k) (proj₂ L k) (proj₂ L′ k) j b b′)
```

## 4 规范比较

`Shape` 是 `Tri` 去掉方程分量。`norm` 把任何一个三路结果里的槽位换成规范位置；三路互斥 (位置关系良基)，所以形状也与证书无关。

```agda
data Shape (i j : LF) : Set where
  belowˢ : Pre i → Shape i j
  aboveˢ : Pre j → Shape i j
  sameˢ : Shape i j

shape : ∀ {i j} → Tri i j → Shape i j
shape (below s e) = belowˢ s
shape (above s e) = aboveˢ s
shape (same e) = sameˢ

norm : ∀ i j → Plain i → Plain j → Legal i → Legal j → Tri i j → Tri i j
norm i j pi pj Li Lj (below s e) =
  below (proj₁ (canon i pi Li j (s , e))) (proj₂ (canon i pi Li j (s , e)))
norm i j pi pj Li Lj (above s e) =
  above (proj₁ (canon j pj Lj i (s , e))) (proj₂ (canon j pj Lj i (s , e)))
norm i j pi pj Li Lj (same e) = same e

norm-const : ∀ i j (pi pi′ : Plain i) (pj pj′ : Plain j)
  (Li Li′ : Legal i) (Lj Lj′ : Legal j) (t t′ : Tri i j) →
  shape (norm i j pi pj Li Lj t) ≡ shape (norm i j pi′ pj′ Li′ Lj′ t′)
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (below s e) (below s′ e′) =
  cong belowˢ (canon-const i pi pi′ Li Li′ j (s , e) (s′ , e′))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (below s e) (above s′ e′) =
  ⊥-elim (no-both (s , e) (s′ , e′))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (below s e) (same e′) =
  ⊥-elim (no-same (s , e) e′)
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (above s e) (below s′ e′) =
  ⊥-elim (no-both (s′ , e′) (s , e))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (above s e) (above s′ e′) =
  cong aboveˢ (canon-const j pj pj′ Lj Lj′ i (s , e) (s′ , e′))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (above s e) (same e′) =
  ⊥-elim (no-same (s , e) (sym e′))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (same e) (below s′ e′) =
  ⊥-elim (no-same (s′ , e′) e)
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (same e) (above s′ e′) =
  ⊥-elim (no-same (s′ , e′) (sym e))
norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ (same e) (same e′) = refl

ccompare : Compare
ccompare K pl L q q′ =
  norm (lev K q) (lev K q′) (lev-plain K pl q) (lev-plain K pl q′)
    (lev-legal K pl L q) (lev-legal K pl L q′) (compare K pl L q q′)

ccompare-slot : ∀ K pl (L L′ : Legal K) q q′ →
  shape (ccompare K pl L q q′) ≡ shape (ccompare K pl L′ q q′)
ccompare-slot K pl L L′ q q′ =
  norm-const (lev K q) (lev K q′) (lev-plain K pl q) (lev-plain K pl q)
    (lev-plain K pl q′) (lev-plain K pl q′)
    (lev-legal K pl L q) (lev-legal K pl L′ q) (lev-legal K pl L q′) (lev-legal K pl L′ q′)
    (compare K pl L q q′) (compare K pl L′ q q′)
```

形状与槽位只由两个层号决定：换公共上界、换位置、换证书都不变 (沿层号的相等搬运之后)。
位置沿第一位置路径搬到更大的层号里 (`YiLvIf.shift`) 是它的特例。

```agda
shape-transport : ∀ i j i′ j′ (e₁ : i ≡ i′) (e₂ : j ≡ j′)
  (pi : Plain i) (pj : Plain j) (Li : Legal i) (Lj : Legal j)
  (pi′ : Plain i′) (pj′ : Plain j′) (Li′ : Legal i′) (Lj′ : Legal j′)
  (t : Tri i j) (t′ : Tri i′ j′) →
  subst₂ Shape e₁ e₂ (shape (norm i j pi pj Li Lj t)) ≡ shape (norm i′ j′ pi′ pj′ Li′ Lj′ t′)
shape-transport i j .i .j refl refl pi pj Li Lj pi′ pj′ Li′ Lj′ t t′ =
  norm-const i j pi pi′ pj pj′ Li Li′ Lj Lj′ t t′

ccompare-levels : ∀ K K′ (pl : Plain K) (pl′ : Plain K′) (L : Legal K) (L′ : Legal K′)
  (q₁ q₂ : Pre K) (q₁′ q₂′ : Pre K′)
  (e₁ : lev K q₁ ≡ lev K′ q₁′) (e₂ : lev K q₂ ≡ lev K′ q₂′) →
  subst₂ Shape e₁ e₂ (shape (ccompare K pl L q₁ q₂)) ≡ shape (ccompare K′ pl′ L′ q₁′ q₂′)
ccompare-levels K K′ pl pl′ L L′ q₁ q₂ q₁′ q₂′ e₁ e₂ =
  shape-transport (lev K q₁) (lev K q₂) (lev K′ q₁′) (lev K′ q₂′) e₁ e₂
    (lev-plain K pl q₁) (lev-plain K pl q₂) (lev-legal K pl L q₁) (lev-legal K pl L q₂)
    (lev-plain K′ pl′ q₁′) (lev-plain K′ pl′ q₂′)
    (lev-legal K′ pl′ L′ q₁′) (lev-legal K′ pl′ L′ q₂′)
    (compare K pl L q₁ q₂) (compare K′ pl′ L′ q₁′ q₂′)

ccompare-shift : ∀ {a} b (p : CP a b) (pa : Plain a) (pb : Plain b)
  (La : Legal a) (Lb : Legal b) (r r′ : Pre a) →
  subst₂ Shape (proj₂ (shift p r)) (proj₂ (shift p r′))
    (shape (ccompare b pb Lb (proj₁ (shift p r)) (proj₁ (shift p r′)))) ≡
  shape (ccompare a pa La r r′)
ccompare-shift {a} b p pa pb La Lb r r′ =
  ccompare-levels b a pb pa Lb La (proj₁ (shift p r)) (proj₁ (shift p r′)) r r′
    (proj₂ (shift p r)) (proj₂ (shift p r′))
```

在 [YiLvNegCert](YiLvNegCert.lagda.md) 的实例上 (两份证书让 `compare` 交出槽位 0 与 1)，`ccompare` 都交出槽位 0。这两条是计算检查。

```agda
canon₀ : shape (ccompare Kᶜ Kᶜ-plain (Kᶜ-legal 0) hiᶜ loᶜ) ≡ belowˢ (0 , inj₁ tt)
canon₀ = refl

canon₁ : shape (ccompare Kᶜ Kᶜ-plain (Kᶜ-legal 1) hiᶜ loᶜ) ≡ belowˢ (0 , inj₁ tt)
canon₁ = refl
```

范围。`ccompare-slot` 说的是形状与槽位；`below s e` 里的 `e` 取自输入，两份证书给出的 `e` 是否相等没有证明
(判断：这等于问层号的相等证明是否唯一，本仓库的选项下对含极限的层号证不出)。折叠要把结点的下界沿 `e` 搬到槽位的类型里，
所以 "换证书输出相等" 除槽位外还要两项，都没有证：方程分量相等，以及 [YiLvNegCert](YiLvNegCert.lagda.md) 的函数相等。
