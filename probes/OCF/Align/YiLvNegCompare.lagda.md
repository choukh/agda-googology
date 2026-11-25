# YiLvNeg 第 1 项：合法性只能无关地用时，有界比较给出什么

**判决：编译定理。** `CompareIrr` 推出 `IrrSearch` 与更强的 `IrrDecide`，并且与 "从无关的证据交出位置" (`PosIrr`) 等价，还推出 `Plain` 层号上相等证明的反压扁 (`EqIrr`)。
见证层号是 `tw 3` 的一个带守卫坐标的读回 (守卫相关时自带见证)；`IrrSearch → CompareIrr` 没写成。
不否定 `Compare` (合法性作数据，`YiLvIf.compare`)；互为延伸的位置对不读合法性 (`prefix→tri`)。接口 [YiLvIf](YiLvIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegCompare where

open import Data.Nat.Base using (ℕ; zero; suc; _<′_)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiIrrNegWide
  using (Found; IrrSearch; seen; seen-hit; seen-found; flag; flag-hit; dense; dense-legal;
         always; always-found)
open import OCF.Align.YiIrrNegWideDecide using (Mono; Evidence; IrrDecide)
```

## 1 见证：一个坐标，它合法当且仅当 `α` 有见证

`coordᴺ α = lim (1, suc d, suc d, …)`，`d = dense α = lim (flag (seen α m))` 总合法。
第 0 步 `1 ⊲ suc d` 要在 `d` 里选一个取值为 1 的下标。层号取它的读回，所以它在 `tw 3` 的分支域里 (§3)。

```agda
col : (ℕ → Bool) → ℕ → R
col α zero = one
col α (suc n) = G.suc (dense α)

coordᴺ : (ℕ → Bool) → R
coordᴺ α = G.lim (col α)

found→lgl : ∀ α → Found α → Lgl zero (coordᴺ α)
found→lgl α (n , p) = step , lawful
  where
  step : ∀ k → Cp zero (col α k) (col α (suc k))
  step zero = inj₂ (inj₂ (n , subst (λ z → Cp zero one (flag z))
    (sym (seen-hit α n p)) (inj₁ refl)))
  step (suc k) = inj₁ refl
  lawful : ∀ k → Lgl zero (col α k)
  lawful zero = tt
  lawful (suc k) = dense-legal α

lgl→found : ∀ α → Lgl zero (coordᴺ α) → Found α
lgl→found α (st , lf) with st zero
... | inj₁ ()
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ (m , p)) = seen-found α m (flag-hit (seen α m) p)

levelᴺ : (ℕ → Bool) → LF
levelᴺ α = read0 (coordᴺ α)

levelᴺ-plain : ∀ α → Plain (levelᴺ α)
levelᴺ-plain α = up0-plain (coordᴺ α) (raw0-Nested (coordᴺ α))

levelᴺ-legal : ∀ α → Found α → Legal (levelᴺ α)
levelᴺ-legal α s = read0-legal (coordᴺ α) (found→lgl α s)

-- 两个位置: 第 1 支的根 (层号 read0 (dense α)) 与第 0 支的根 (层号 zero).
hi lo : ∀ α → Pre (levelᴺ α)
hi α = 1 , inj₁ tt
lo α = 0 , inj₁ tt

hi-level : ∀ α → lev (levelᴺ α) (hi α) ≡ read0 (dense α)
hi-level α = refl

lo-level : ∀ α → lev (levelᴺ α) (lo α) ≡ zero
lo-level α = refl

pre-flag : ∀ x .(nb : Nested zero (flag x)) → Pre (up zero (flag x) nb) → x ≡ true
pre-flag true nb r = refl
pre-flag false nb ()
```

## 2 `CompareIrr → IrrSearch`

`Tri (read0 (dense α)) zero` 只能是 `below`：`zero` 里没有位置，极限不等于零。`below` 的槽位在 `read0 (dense α)` 的某一支里，那一支不是零。

```agda
compare-irr→irr-search : CompareIrr → IrrSearch
compare-irr→irr-search cmp α s
  with cmp (levelᴺ α) (levelᴺ-plain α) (levelᴺ-legal α s) (hi α) (lo α)
... | below (m , r) e = seen-found α m (pre-flag (seen α m) _ r)
... | above () e
... | same ()
```

只对坐标的读回陈述，结论相同。`tw 3` 根上的链点若只带无关的 `Lgl zero η`，能交给比较的就是 `CompareRead` 的前提；
坐标的合法性作数据时比较成立 (`compare-read`)。

```agda
CompareRead : Set
CompareRead = ∀ (η : R) → .(Lgl zero η) → (q q′ : Pre (read0 η)) →
  Tri (lev (read0 η) q) (lev (read0 η) q′)

compare-irr→compare-read : CompareIrr → CompareRead
compare-irr→compare-read cmp η l =
  cmp (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η l)

compare-read→irr-search : CompareRead → IrrSearch
compare-read→irr-search cmp α s with cmp (coordᴺ α) (found→lgl α s) (hi α) (lo α)
... | below (m , r) e = seen-found α m (pre-flag (seen α m) _ r)
... | above () e
... | same ()

compare-read : ∀ (η : R) → Lgl zero η → (q q′ : Pre (read0 η)) →
  Tri (lev (read0 η) q) (lev (read0 η) q′)
compare-read η l = compare (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η l)
```

更强的一条：`IrrDecide` ([YiIrrNegWideDecide](YiIrrNegWideDecide.lagda.md)；对单调的 `γ`，凭无关的 "字面全假或有真值" 判定是哪一种)。
坐标 `lim (suc ω′, suc β, suc β, …)`，`ω′ = lim (1, 1, …)`，`β = lim (tick (γ m))`，`tick` 把假送到 1、真送到 `suc ω′`。
`γ` 字面全假时 `β` 就是 `ω′`，第 0 步是相等；有真值时 `suc ω′` 是 `β` 的一项。三路里 `same` 给出全假，`below` 给出真值。

```agda
onesᴰ : R
onesᴰ = G.lim (λ _ → one)

tickᴰ : Bool → R
tickᴰ false = one
tickᴰ true = G.suc onesᴰ

tickᴰ-step : ∀ x y → (x ≡ true → y ≡ true) → Cp zero (tickᴰ x) (tickᴰ y)
tickᴰ-step false false h = inj₁ refl
tickᴰ-step false true h = inj₂ (inj₂ (zero , inj₁ refl))
tickᴰ-step true false h with h refl
... | ()
tickᴰ-step true true h = inj₁ refl

tickᴰ-lgl : ∀ x → Lgl zero (tickᴰ x)
tickᴰ-lgl false = tt
tickᴰ-lgl true = (λ _ → inj₁ refl) , (λ _ → tt)

betaᴰ : (ℕ → Bool) → R
betaᴰ γ = G.lim (λ m → tickᴰ (γ m))

colᴰ : (ℕ → Bool) → ℕ → R
colᴰ γ zero = G.suc onesᴰ
colᴰ γ (suc n) = G.suc (betaᴰ γ)

coordᴰ : (ℕ → Bool) → R
coordᴰ γ = G.lim (colᴰ γ)

evidence→lgl : ∀ γ → Mono γ → Evidence γ → Lgl zero (coordᴰ γ)
evidence→lgl γ mono ev = step ev , lawful
  where
  step : Evidence γ → ∀ n → Cp zero (colᴰ γ n) (colᴰ γ (suc n))
  step (inj₁ flat) zero =
    inj₁ (cong (λ g → G.suc (G.lim (λ m → tickᴰ (g m)))) (sym flat))
  step (inj₂ (n , p)) zero = inj₂ (inj₂ (n ,
    subst (λ z → Cp zero (G.suc onesᴰ) (tickᴰ z)) (sym p) (inj₁ refl)))
  step e (suc n) = inj₁ refl
  lawful : ∀ n → Lgl zero (colᴰ γ n)
  lawful zero = (λ _ → inj₁ refl) , (λ _ → tt)
  lawful (suc n) =
    (λ m → tickᴰ-step (γ m) (γ (suc m)) (mono m)) , (λ m → tickᴰ-lgl (γ m))

coordᴰ-guard : ∀ γ → Mono γ → Evidence γ → Gd zero raw1 (coordᴰ γ)
coordᴰ-guard γ mono ev =
  inj₂ (zero , inj₂ (inj₂ (zero , inj₁ refl))) , evidence→lgl γ mono ev , raw0-Nested (coordᴰ γ)

tick-hit : ∀ x .(nb : Nested zero (tickᴰ x)) (r : Pre (up zero (tickᴰ x) nb)) →
  lev (up zero (tickᴰ x) nb) r ≡ read0 onesᴰ → x ≡ true
tick-hit true nb r e = refl
tick-hit false nb (inj₁ _) ()
tick-hit false nb (inj₂ ()) e

tick-flat : ∀ x .(nb : Nested zero (tickᴰ x)) → up zero (tickᴰ x) nb ≡ suc zero → x ≡ false
tick-flat false nb e = refl
tick-flat true nb ()

bodyᴸ : LF → ℕ → LF
bodyᴸ (lim f) = f
bodyᴸ zero = λ _ → zero
bodyᴸ (suc x) = λ _ → zero
bodyᴸ (lc k c w b t g) = λ _ → zero

compare-read→irr-decide : CompareRead → IrrDecide
compare-read→irr-decide cmp γ mono ev
  with cmp (coordᴰ γ) (evidence→lgl γ mono ev) (1 , inj₁ tt) (0 , inj₁ tt)
... | below (m , r) e = inj₂ (m , tick-hit (γ m) _ r e)
... | above (n , inj₁ _) ()
... | above (n , inj₂ ()) e
... | same e = inj₁ (λ m → tick-flat (γ m) _ (cong (λ x → bodyᴸ x m) e))

compare-irr→irr-decide : CompareIrr → IrrDecide
compare-irr→irr-decide cmp = compare-read→irr-decide (compare-irr→compare-read cmp)
```

前提可满足：`α = always` 时合法性有闭证明，这时 `compare` 给出的正是 `below` (计算检查)。

```agda
closed-legal : Legal (levelᴺ always)
closed-legal = levelᴺ-legal always always-found

closed-compare : Tri (read0 (dense always)) zero
closed-compare = compare (levelᴺ always) (levelᴺ-plain always) closed-legal (hi always) (lo always)

IsBelow : ∀ {i j} → Tri i j → Set
IsBelow (below s e) = ⊤
IsBelow (above s e) = ⊥
IsBelow (same e) = ⊥

closed-is-below : IsBelow closed-compare
closed-is-below = tt
```

合法性这个前提不能整个去掉：不合法的层号上三路可以一条都不成立。

```agda
CompareBare : Set
CompareBare = ∀ K → Plain K → (q q′ : Pre K) → Tri (lev K q) (lev K q′)

bad : ℕ → LF
bad zero = suc zero
bad (suc n) = suc (lim (λ _ → zero))

bad-plain : ∀ n → Plain (bad n)
bad-plain zero = tt
bad-plain (suc n) = λ _ → tt

compare-bare→⊥ : CompareBare → ⊥
compare-bare→⊥ cmp with cmp (lim bad) bad-plain (0 , inj₁ tt) (1 , inj₁ tt)
... | below () e
... | above (n , ()) e
... | same ()
```

## 3 见证在不在 `tw 3` 的分支域里

`tw 3` 的第 `η` 支是 `Ω̂ (read0 η)`，守卫是 `1 ⊲ η`、`η` 合法、嵌套。`coordᴺ α` 的守卫与 `Found α` 等价：
无关地成立时它是分支域里的坐标；相关的守卫自带见证。它是不是折叠实际走到的链点，本篇没有判定
(链点是 `1` 起步逐次加上折叠输出的闭值，`tw 3` 的折叠还没有)。

```agda
branch₃ : (η : R) → .(Gd zero raw1 η) → LF
branch₃ η e = Ω̂ (up zero η (proj₂ (proj₂ e)))

tw₃-branches : tw 3 ≡ lc zero raw1 tt tt (tw 2) branch₃
tw₃-branches = refl

witness-guard : ∀ α → Found α → Gd zero raw1 (coordᴺ α)
witness-guard α s = inj₂ (zero , inj₁ refl) , found→lgl α s , raw0-Nested (coordᴺ α)

witness-branch : ∀ α .(s : Found α) →
  branch₃ (coordᴺ α) (witness-guard α s) ≡ Ω̂ (levelᴺ α)
witness-branch α s = refl

guard→found : ∀ α → Gd zero raw1 (coordᴺ α) → Found α
guard→found α e = lgl→found α (proj₁ (proj₂ e))
```

## 4 强度：与 "从无关证据交出位置" 等价

`At i j`：`j` 是 `i` 的某个位置上的层号。位置关系良基 (`wf-all`)，所以三路里至多一路成立。

```agda
At : LF → LF → Set
At i j = Σ (Pre i) λ s → lev i s ≡ j

data Wf (i : LF) : Set where
  wf : (∀ j → At i j → Wf j) → Wf i

unwf : ∀ {i} → Wf i → ∀ j → At i j → Wf j
unwf (wf h) = h

wf-all : ∀ i → Wf i
wf-all zero = wf (λ j ())
wf-all (suc k) = wf λ
  { j (inj₁ _ , refl) → wf-all k
  ; j (inj₂ r , e) → unwf (wf-all k) j (r , e) }
wf-all (lim f) = wf λ { j ((n , r) , e) → unwf (wf-all (f n)) j (r , e) }
wf-all (lc k c w b t g) = wf λ
  { j (inj₁ (inj₁ _) , refl) → wf-all k
  ; j (inj₁ (inj₂ r) , e) → unwf (wf-all k) j (r , e)
  ; j (inj₂ (inj₁ r) , e) → unwf (wf-all t) j (r , e)
  ; j (inj₂ (inj₂ (η , e′ , r)) , e) → unwf (wf-all (g η e′)) j (r , e) }

wf-asym : ∀ {i j} → Wf i → At i j → At j i → ⊥
wf-asym (wf h) a b = wf-asym (h _ a) b a

no-loop : ∀ i → At i i → ⊥
no-loop i a = wf-asym (wf-all i) a a

no-both : ∀ {i j} → At i j → At j i → ⊥
no-both {i} = wf-asym (wf-all i)

no-same : ∀ {i j} → At i j → i ≡ j → ⊥
no-same {i} a refl = no-loop i a

lev-legal : ∀ K → Plain K → Legal K → ∀ r → Legal (lev K r)
lev-legal (suc k) pl L (inj₁ _) = L
lev-legal (suc k) pl L (inj₂ r) = lev-legal k pl L r
lev-legal (lim f) pl L (n , r) = lev-legal (f n) (pl n) (proj₂ L n) r

at→cp : ∀ i → Plain i → ∀ j → At i j → CP (suc j) i
at→cp (suc k) pl j (inj₁ _ , refl) = self
at→cp (suc k) pl j (inj₂ r , e) = suc (at→cp k pl j (r , e))
at→cp (lim f) pl j ((n , r) , e) = lim n (at→cp (f n) (pl n) j (r , e))

PosIrr : Set
PosIrr = ∀ i j → Plain i → Plain j → .(Legal i) → .(At i j) → At i j
```

`CompareIrr → PosIrr`：把 `suc j` 与 `suc i` 排成极限 `lim (suc j, suc i, suc i, …)`，它合法当且仅当 `j` 在 `i` 的某个位置上。

```agda
pair : LF → LF → ℕ → LF
pair i j zero = suc j
pair i j (suc n) = suc i

pair-plain : ∀ i j → Plain i → Plain j → ∀ n → Plain (pair i j n)
pair-plain i j pi pj zero = pj
pair-plain i j pi pj (suc n) = pi

pair-legal : ∀ i j → Plain i → Legal i → At i j → Legal (lim (pair i j))
pair-legal i j pi L a = step , lawful
  where
  step : ∀ n → CP (pair i j n) (pair i j (suc n))
  step zero = suc (at→cp i pi j a)
  step (suc n) = self
  lawful : ∀ n → Legal (pair i j n)
  lawful zero = subst Legal (proj₂ a) (lev-legal i pi L (proj₁ a))
  lawful (suc n) = L

compare-irr→pos-irr : CompareIrr → PosIrr
compare-irr→pos-irr cmp i j pi pj L a
  with cmp (lim (pair i j)) (pair-plain i j pi pj) (pair-legal i j pi L a)
    (1 , inj₁ tt) (0 , inj₁ tt)
... | below s e = s , e
... | above s e = ⊥-elim-irr (no-both a (s , e))
... | same e = ⊥-elim-irr (no-same a e)
```

`PosIrr → CompareIrr`：照 `YiLvIf.compare`，极限处把编号小的位置搬到编号大的分支里；搬运后的位置只无关地知道，由 `PosIrr` 取回。

```agda
move : PosIrr → (f : ℕ → LF) → (∀ n → Plain (f n)) → .(Legal (lim f)) →
  ∀ {n m} → n <′ m → (r : Pre (f n)) → At (f m) (lev (f n) r)
move pos f pl lg {n} {m} lt r =
  pos (f m) (lev (f n) r) (pl m) (lev-plain (f n) (pl n) r) (proj₂ lg m)
    (shift (steps (proj₁ lg) lt) r)

pos-irr→compare-irr : PosIrr → CompareIrr
pos-irr→compare-irr pos zero pl lg () q′
pos-irr→compare-irr pos (suc k) pl lg (inj₁ _) (inj₁ _) = same refl
pos-irr→compare-irr pos (suc k) pl lg (inj₁ _) (inj₂ r′) = below r′ refl
pos-irr→compare-irr pos (suc k) pl lg (inj₂ r) (inj₁ _) = above r refl
pos-irr→compare-irr pos (suc k) pl lg (inj₂ r) (inj₂ r′) =
  pos-irr→compare-irr pos k pl lg r r′
pos-irr→compare-irr pos (lim f) pl lg (n , r) (m , r′) with <-cmp n m
... | tri< n<m _ _ =
  subst (λ z → Tri z (lev (f m) r′)) (proj₂ (move pos f pl lg (<⇒<′ n<m) r))
    (pos-irr→compare-irr pos (f m) (pl m) (proj₂ lg m)
      (proj₁ (move pos f pl lg (<⇒<′ n<m) r)) r′)
... | tri≈ _ refl _ = pos-irr→compare-irr pos (f n) (pl n) (proj₂ lg n) r r′
... | tri> _ _ m<n =
  subst (λ z → Tri (lev (f n) r) z) (proj₂ (move pos f pl lg (<⇒<′ m<n) r′))
    (pos-irr→compare-irr pos (f n) (pl n) (proj₂ lg n) r
      (proj₁ (move pos f pl lg (<⇒<′ m<n) r′)))
```

`PosIrr` 还给出 `Plain` 层号上相等证明的反压扁：`suc a` 里层号为 `b` 的位置只能是根。
这一条不是对可判定谓词的搜索 (层号相等不可判定)，所以 `IrrSearch → CompareIrr` 没有写成；它是否可证，本篇没有结论。

```agda
EqIrr : Set
EqIrr = ∀ a b → Plain a → Plain b → .(Legal a) → .(a ≡ b) → a ≡ b

pos-irr→eq-irr : PosIrr → EqIrr
pos-irr→eq-irr pos a b pa pb L e with pos (suc a) b pa pb L (inj₁ tt , e)
... | inj₁ _ , e′ = e′
... | inj₂ r , e′ = ⊥-elim-irr (no-loop a (r , trans e′ (sym e)))

compare-irr→eq-irr : CompareIrr → EqIrr
compare-irr→eq-irr cmp = pos-irr→eq-irr (compare-irr→pos-irr cmp)
```

## 5 哪一类位置对不读合法性

`ext K q s`：位置 `q` 往下接上 `q` 处层号里的位置 `s`。互为延伸或相同的位置对，三路直接写出，对一切层号 (含 Ω 结点的层号)，
不要 `Plain`，不要合法性。`compare` 读合法性的地方只有极限处两个位置落在不同分支 (§1 的 `hi`, `lo` 就是)。

```agda
ext : ∀ K (q : Pre K) → Pre (lev K q) → Pre K
ext (suc k) (inj₁ _) s = inj₂ s
ext (suc k) (inj₂ r) s = inj₂ (ext k r s)
ext (lim f) (n , r) s = n , ext (f n) r s
ext (lc k c w b t g) (inj₁ (inj₁ _)) s = inj₁ (inj₂ s)
ext (lc k c w b t g) (inj₁ (inj₂ r)) s = inj₁ (inj₂ (ext k r s))
ext (lc k c w b t g) (inj₂ (inj₁ r)) s = inj₂ (inj₁ (ext t r s))
ext (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) s = inj₂ (inj₂ (η , e , ext (g η e) r s))

lev-ext : ∀ K q s → lev K (ext K q s) ≡ lev (lev K q) s
lev-ext (suc k) (inj₁ _) s = refl
lev-ext (suc k) (inj₂ r) s = lev-ext k r s
lev-ext (lim f) (n , r) s = lev-ext (f n) r s
lev-ext (lc k c w b t g) (inj₁ (inj₁ _)) s = refl
lev-ext (lc k c w b t g) (inj₁ (inj₂ r)) s = lev-ext k r s
lev-ext (lc k c w b t g) (inj₂ (inj₁ r)) s = lev-ext t r s
lev-ext (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) s = lev-ext (g η e) r s

data Prefix (K : LF) (q q′ : Pre K) : Set where
  equal : q ≡ q′ → Prefix K q q′
  longer : (s : Pre (lev K q)) → ext K q s ≡ q′ → Prefix K q q′
  shorter : (s : Pre (lev K q′)) → ext K q′ s ≡ q → Prefix K q q′

prefix→tri : ∀ K (q q′ : Pre K) → Prefix K q q′ → Tri (lev K q) (lev K q′)
prefix→tri K q .q (equal refl) = same refl
prefix→tri K q .(ext K q s) (longer s refl) = below s (sym (lev-ext K q s))
prefix→tri K .(ext K q′ s) q′ (shorter s refl) = above s (sym (lev-ext K q′ s))
```
