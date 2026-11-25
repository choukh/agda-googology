# YiOmNeg 第 1 项：`SlotIrr` 与 `KidIrr` 各推出什么

**判决：编译定理。** 两者都推出 `LegalCopy` (从无关的守卫交出一棵相关合法的层号树，它无关地等于那一支根上的层号)，因而都推出 `IrrSearch` 与 `IrrDecide`；
两者都由 "守卫可以从无关变回相关" (`GdData`，排中律的实例 `GdDec` 给出) 推出，所以不可反驳。两者之间的蕴涵没有判定。
不否定守卫相关时的槽位与嵌入 (`YiOmIf.slot-rel`, `kid-rel`)；探针坐标在 `tw 3` 根上的分支域里，守卫只无关地成立，它是不是规范的链走到的坐标没有判定。接口 [YiOmIf](YiOmIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmNegSlot where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiOmIf
open import OCF.Align.YiIrrNegWide
  using (Found; IrrSearch; seen; seen-found; flag; dense; always; always-found)
open import OCF.Align.YiIrrNegWideDecide using (Mono; AllFalse; Evidence; IrrDecide)
open import OCF.Align.YiLvNegCompare
  using (coordᴺ; levelᴺ; found→lgl; hi; lo; pre-flag; lev-legal; bodyᴸ;
         onesᴰ; tickᴰ; betaᴰ; coordᴰ; coordᴰ-guard; tick-hit; tick-flat; witness-guard)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
```

## 1 `tw 2` 的每个位置上的层号都相关地合法

主干上的层号是零。支里的位置带相关的守卫，守卫里有坐标的合法性，读回后是那一支层号的合法性。

```agda
lev-legal₂ : ∀ (q : Pre K₂ω) → Legal (lev K₂ω q)
lev-legal₂ (inj₁ (inj₁ _)) = tt
lev-legal₂ (inj₁ (inj₂ ()))
lev-legal₂ (inj₂ (inj₁ (inj₁ _))) = tt
lev-legal₂ (inj₂ (inj₁ (inj₂ ())))
lev-legal₂ (inj₂ (inj₂ (η , e , r))) =
  lev-legal (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η (proj₁ (proj₂ e))) r
```

## 2 被推出的陈述

`Copy L`：一棵相关合法的层号树，无关地等于 `L`。`LegalCopy`：坐标 `suc s` 的守卫只无关地成立时，交出根上层号 `read0 s` 的这样一份拷贝。
它不提槽位，也不提嵌入，是两条接口陈述的公共后果。

```agda
record Copy (L : LF) : Set where
  constructor copy
  field
    level : LF
    legal : Legal level
    .agree : level ≡ L

use : ∀ {L} {X : Set} → Copy L → ((L′ : LF) → Legal L′ → .(L′ ≡ L) → X) → X
use (copy l g e) k = k l g e

LegalCopy : Set
LegalCopy = ∀ (s : R) → .(Gd zero raw1 (G.suc s)) → Copy (read0 s)

slot→copy : SlotIrr → LegalCopy
slot→copy si s e =
  copy (lev K₂ω (proj₁ (si (G.suc s) e (inj₁ tt))))
       (lev-legal₂ (proj₁ (si (G.suc s) e (inj₁ tt))))
       (proj₂ (si (G.suc s) e (inj₁ tt)))
```

## 3 读回是结点的树交出层号

`NodeAt L x`：`x` 是层号 `L` 的结点。`Raw (tw 2)` 的一棵树若 (无关地) 读回成层号 `L` 的结点，就能相关地交出 `L` 的一份拷贝：
树是数据，它的头要么是带位置的结点，要么经相关守卫嵌入的孩子，要么 `top`；每种情形层号都在一个相关合法的层号里。

```agda
NodeAt : LF → LF → Set
NodeAt L (lc k c w b t g) = k ≡ L
NodeAt L zero = ⊥
NodeAt L (suc x) = ⊥
NodeAt L (lim f) = ⊥

upN-level : ∀ y r c .(l : LglLow y r c) .(b : NestedLow y r c) t
  (g : (η : Low y r) → .(GdL y r c η) → LF) L →
  NodeAt L (upN y r c l b t g) → lev y r ≡ L
upN-level (suc k) (inj₁ _) c l b t g L h = h
upN-level (suc k) (inj₂ r) c l b t g L h = upN-level k r c l b t g L h
upN-level (lim f) (n , r) c l b t g L h = upN-level (f n) r c l b t g L h
upN-level (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l b t g L h = h
upN-level (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l b t g L h = upN-level k r c l b t g L h
upN-level (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l b t g L h = upN-level t₀ r c l b t g L h
upN-level (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l b t g L h =
  upN-level (g₀ η e) r c l b t g L h

upN-node : ∀ y r c .(l : LglLow y r c) .(b : NestedLow y r c) t
  (g : (η : Low y r) → .(GdL y r c η) → LF) → NodeAt (lev y r) (upN y r c l b t g)
upN-node (suc k) (inj₁ _) c l b t g = refl
upN-node (suc k) (inj₂ r) c l b t g = upN-node k r c l b t g
upN-node (lim f) (n , r) c l b t g = upN-node (f n) r c l b t g
upN-node (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l b t g = refl
upN-node (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l b t g = upN-node k r c l b t g
upN-node (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l b t g = upN-node t₀ r c l b t g
upN-node (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l b t g = upN-node (g₀ η e) r c l b t g

plain-copy : ∀ L K → Plain K → Legal K → (T : Raw K) .(nb : Nested K T) →
  .(NodeAt L (up K T nb)) → Copy L
plain-copy L K pl lg G.zero nb h = ⊥-elim-irr h
plain-copy L K pl lg (G.suc a) nb h = ⊥-elim-irr h
plain-copy L K pl lg (G.lim f) nb h = ⊥-elim-irr h
plain-copy L K pl lg (G.lc r c t g) nb h =
  copy (lev K r) (lev-legal K pl lg r)
    (upN-level K r c (proj₁ nb) (proj₁ (proj₂ nb))
      (up K t (proj₁ (proj₂ (proj₂ nb))))
      (λ η e → up K (g η e) (proj₂ (proj₂ (proj₂ nb)) η e)) L h)
plain-copy L zero pl lg (G.em () T) nb h
plain-copy L (suc k) pl lg (G.em _ T) nb h = plain-copy L k pl lg T nb h
plain-copy L (lim f) pl lg (G.em n T) nb h = plain-copy L (f n) (pl n) (proj₂ lg n) T nb h
plain-copy L zero pl lg G.top nb h = ⊥-elim-irr h
plain-copy L (suc k) pl lg G.top nb h = copy k lg h
plain-copy L (lim f) pl lg G.top nb h = ⊥-elim-irr h

node₂-copy : ∀ L (ξ : Raw K₂ω) .(nb : Nested K₂ω ξ) → .(NodeAt L (up K₂ω ξ nb)) → Copy L
node₂-copy L G.zero nb h = ⊥-elim-irr h
node₂-copy L (G.suc a) nb h = ⊥-elim-irr h
node₂-copy L (G.lim f) nb h = ⊥-elim-irr h
node₂-copy L (G.lc q c t g) nb h =
  copy (lev K₂ω q) (lev-legal₂ q)
    (upN-level K₂ω q c (proj₁ nb) (proj₁ (proj₂ nb))
      (up K₂ω t (proj₁ (proj₂ (proj₂ nb))))
      (λ η e → up K₂ω (g η e) (proj₂ (proj₂ (proj₂ nb)) η e)) L h)
node₂-copy L (G.em (inj₁ _) T) nb h = plain-copy L zero tt tt T nb h
node₂-copy L (G.em (inj₂ (inj₁ _)) T) nb h = plain-copy L (suc zero) tt tt T nb h
node₂-copy L (G.em (inj₂ (inj₂ (η , e))) T) nb h =
  plain-copy L (read0 η) (up0-plain η (raw0-Nested η)) (read0-legal η (proj₁ (proj₂ e))) T nb h
node₂-copy L G.top nb h = copy zero tt h
```

`KidIrr` 把第 `suc s` 支的 `top` 嵌进来，读回是 `Ω̂ (suc (read0 s))`，一个层号 `read0 s` 的结点。

```agda
kid→copy : KidIrr → LegalCopy
kid→copy (emb , law) s e =
  node₂-copy (read0 s) (emb (G.suc s) e G.top)
    (proj₁ (law (G.suc s) e G.top tt))
    (subst (NodeAt (read0 s)) (sym (proj₂ (law (G.suc s) e G.top tt))) refl)
```

## 4 `LegalCopy → IrrSearch`

坐标 `suc (coordᴺ α)`：守卫与 `Found α` 等价 (`YiLvNegCompare.witness-guard`, `guard→found`)。它根上的层号 `levelᴺ α` 是极限，
第 0 步的路径要在 `read0 (dense α)` 里选一个下标。拷贝只无关地等于 `levelᴺ α`，但路径是数据：沿它的构造子走，下标取出来以后，
"`seen α n` 为真" 可判定，由无关的证明变回相关的。

```agda
predᴸ : LF → LF
predᴸ (suc x) = x
predᴸ zero = zero
predᴸ (lim f) = zero
predᴸ (lc k c w b t g) = zero

bool-irr : ∀ (x y : Bool) → .(x ≡ y) → x ≡ y
bool-irr false false e = refl
bool-irr true true e = refl
bool-irr false true e = ⊥-elim-irr (no e)
  where no : false ≡ true → ⊥
        no ()
bool-irr true false e = ⊥-elim-irr (no e)
  where no : true ≡ false → ⊥
        no ()

hitᶠ : ∀ x .(nb : Nested zero (flag x)) → CP (suc zero) (up zero (flag x) nb) → x ≡ true
hitᶠ true nb p = refl
hitᶠ false nb ()

pathᶠ₃ : ∀ α n (a b : LF) → a ≡ suc zero → b ≡ read0 (flag (seen α n)) → CP a b → seen α n ≡ true
pathᶠ₃ α n a b refl refl p = hitᶠ (seen α n) _ p

pathᶠ₂ : ∀ α (a b : LF) → .(a ≡ suc zero) → .(b ≡ read0 (dense α)) → CP a b → Found α
pathᶠ₂ α a .a ea eb self = ⊥-elim-irr (no ea eb)
  where no : a ≡ suc zero → a ≡ read0 (dense α) → ⊥
        no refl ()
pathᶠ₂ α a (suc b) ea eb (suc p) = ⊥-elim-irr (no eb)
  where no : suc b ≡ read0 (dense α) → ⊥
        no ()
pathᶠ₂ α a (lim f) ea eb (lim n p) =
  seen-found α n (bool-irr (seen α n) true
    (pathᶠ₃ α n a (f n) ea (cong (λ x → bodyᴸ x n) eb) p))
pathᶠ₂ α a (lc k c w b t g) ea eb (fst p) = ⊥-elim-irr (no eb)
  where no : lc k c w b t g ≡ read0 (dense α) → ⊥
        no ()

pathᶠ₁ : ∀ α (a b : LF) → .(a ≡ suc zero) → .(b ≡ suc (read0 (dense α))) → CP a b → Found α
pathᶠ₁ α a .a ea eb self = ⊥-elim-irr (no ea eb)
  where no : a ≡ suc zero → a ≡ suc (read0 (dense α)) → ⊥
        no refl ()
pathᶠ₁ α a (suc b) ea eb (suc p) = pathᶠ₂ α a b ea (cong predᴸ eb) p
pathᶠ₁ α a (lim f) ea eb (lim n p) = ⊥-elim-irr (no eb)
  where no : lim f ≡ suc (read0 (dense α)) → ⊥
        no ()
pathᶠ₁ α a (lc k c w b t g) ea eb (fst p) = ⊥-elim-irr (no eb)
  where no : lc k c w b t g ≡ suc (read0 (dense α)) → ⊥
        no ()

legal-irr→found : ∀ α (L : LF) → .(L ≡ levelᴺ α) → Legal L → Found α
legal-irr→found α (lim f) eq (st , lg) =
  pathᶠ₁ α (f 0) (f 1) (cong (λ x → bodyᴸ x 0) eq) (cong (λ x → bodyᴸ x 1) eq) (st 0)
legal-irr→found α zero eq lg = ⊥-elim-irr (no eq)
  where no : zero ≡ levelᴺ α → ⊥
        no ()
legal-irr→found α (suc x) eq lg = ⊥-elim-irr (no eq)
  where no : suc x ≡ levelᴺ α → ⊥
        no ()
legal-irr→found α (lc k c w b t g) eq lg = ⊥-elim-irr (no eq)
  where no : lc k c w b t g ≡ levelᴺ α → ⊥
        no ()

guardˢ : ∀ α → Found α → Gd zero raw1 (G.suc (coordᴺ α))
guardˢ α s = inj₂ (inj₂ (zero , inj₁ refl)) , found→lgl α s , raw0-Nested (G.suc (coordᴺ α))

copy→irr-search : LegalCopy → IrrSearch
copy→irr-search lcp α s =
  use (lcp (coordᴺ α) (guardˢ α s)) (λ L lg eq → legal-irr→found α L eq lg)

slot-irr→irr-search : SlotIrr → IrrSearch
slot-irr→irr-search si = copy→irr-search (slot→copy si)

kid-irr→irr-search : KidIrr → IrrSearch
kid-irr→irr-search ki = copy→irr-search (kid→copy ki)
```

## 5 `LegalCopy → IrrDecide`

坐标 `suc (coordᴰ γ)` (`YiLvNegCompare` §2)：第 0 步的路径是相等时 `γ` 全假，是真前驱时交出真值的下标。
相等只无关地知道，但 "`γ m` 为假" 逐点可判定。`IrrDecide` 不能由只读 `γ` 的可计算过程实现 (判断，见 `YiIrrNegWideDecide` 文首)。

```agda
pathᵈ₃ : ∀ (x : Bool) (a b : LF) → a ≡ suc (read0 onesᴰ) → b ≡ read0 (tickᴰ x) → CP a b → x ≡ true
pathᵈ₃ true a b ea eb p = refl
pathᵈ₃ false a b refl refl (suc ())

pathᵈ₂ : ∀ γ (a b : LF) → .(a ≡ suc (read0 onesᴰ)) → .(b ≡ read0 (betaᴰ γ)) → CP a b → Found γ
pathᵈ₂ γ a .a ea eb self = ⊥-elim-irr (no ea eb)
  where no : a ≡ suc (read0 onesᴰ) → a ≡ read0 (betaᴰ γ) → ⊥
        no refl ()
pathᵈ₂ γ a (suc b) ea eb (suc p) = ⊥-elim-irr (no eb)
  where no : suc b ≡ read0 (betaᴰ γ) → ⊥
        no ()
pathᵈ₂ γ a (lim f) ea eb (lim n p) =
  n , bool-irr (γ n) true (pathᵈ₃ (γ n) a (f n) ea (cong (λ x → bodyᴸ x n) eb) p)
pathᵈ₂ γ a (lc k c w b t g) ea eb (fst p) = ⊥-elim-irr (no eb)
  where no : lc k c w b t g ≡ read0 (betaᴰ γ) → ⊥
        no ()

flatᵈ : ∀ γ m (a : LF) → a ≡ suc (read0 onesᴰ) → a ≡ suc (read0 (betaᴰ γ)) → γ m ≡ false
flatᵈ γ m a ea eb =
  tick-flat (γ m) _ (sym (cong (λ x → bodyᴸ (predᴸ x) m) (trans (sym ea) eb)))

pathᵈ₁ : ∀ γ (a b : LF) → .(a ≡ suc (read0 onesᴰ)) → .(b ≡ suc (read0 (betaᴰ γ))) → CP a b →
  AllFalse γ ⊎ Found γ
pathᵈ₁ γ a .a ea eb self = inj₁ (λ m → bool-irr (γ m) false (flatᵈ γ m a ea eb))
pathᵈ₁ γ a (suc b) ea eb (suc p) = inj₂ (pathᵈ₂ γ a b ea (cong predᴸ eb) p)
pathᵈ₁ γ a (lim f) ea eb (lim n p) = ⊥-elim-irr (no eb)
  where no : lim f ≡ suc (read0 (betaᴰ γ)) → ⊥
        no ()
pathᵈ₁ γ a (lc k c w b t g) ea eb (fst p) = ⊥-elim-irr (no eb)
  where no : lc k c w b t g ≡ suc (read0 (betaᴰ γ)) → ⊥
        no ()

legal-irr→decide : ∀ γ (L : LF) → .(L ≡ read0 (coordᴰ γ)) → Legal L → AllFalse γ ⊎ Found γ
legal-irr→decide γ (lim f) eq (st , lg) =
  pathᵈ₁ γ (f 0) (f 1) (cong (λ x → bodyᴸ x 0) eq) (cong (λ x → bodyᴸ x 1) eq) (st 0)
legal-irr→decide γ zero eq lg = ⊥-elim-irr (no eq)
  where no : zero ≡ read0 (coordᴰ γ) → ⊥
        no ()
legal-irr→decide γ (suc x) eq lg = ⊥-elim-irr (no eq)
  where no : suc x ≡ read0 (coordᴰ γ) → ⊥
        no ()
legal-irr→decide γ (lc k c w b t g) eq lg = ⊥-elim-irr (no eq)
  where no : lc k c w b t g ≡ read0 (coordᴰ γ) → ⊥
        no ()

guardᵈ : ∀ γ → Mono γ → Evidence γ → Gd zero raw1 (G.suc (coordᴰ γ))
guardᵈ γ mono ev =
  inj₂ (proj₁ (coordᴰ-guard γ mono ev)) , proj₁ (proj₂ (coordᴰ-guard γ mono ev)) ,
  raw0-Nested (G.suc (coordᴰ γ))

copy→irr-decide : LegalCopy → IrrDecide
copy→irr-decide lcp γ mono ev =
  use (lcp (coordᴰ γ) (guardᵈ γ mono ev)) (λ L lg eq → legal-irr→decide γ L eq lg)

slot-irr→irr-decide : SlotIrr → IrrDecide
slot-irr→irr-decide si = copy→irr-decide (slot→copy si)

kid-irr→irr-decide : KidIrr → IrrDecide
kid-irr→irr-decide ki = copy→irr-decide (kid→copy ki)
```

## 6 两者都不可反驳；守卫相关的坐标上都成立

`GdData`：守卫从无关变回相关。它给出两条接口陈述 (取 `slot-rel`, `kid-rel`)；判定守卫的神谕 (排中律的实例) 给出它。
`α = always` 时探针坐标的守卫有闭的相关证明，槽位直接写出：定理 §4 的前提在闭实例上可满足。

```agda
GdData : Set
GdData = ∀ η → .(Gd zero raw1 η) → Gd zero raw1 η

GdDec : Set
GdDec = ∀ η → Gd zero raw1 η ⊎ (Gd zero raw1 η → ⊥)

dec→data : GdDec → GdData
dec→data dec η e with dec η
... | inj₁ e′ = e′
... | inj₂ no = ⊥-elim-irr (no e)

data→slot-irr : GdData → SlotIrr
data→slot-irr d η e r = slot-rel η (d η e) r

data→kid-irr : GdData → KidIrr
data→kid-irr d = (λ η e T → kid-rel η (d η e) T) , (λ η e T nb → nb , refl)

closed-slot : Slot (G.suc (coordᴺ always)) (inj₁ tt)
closed-slot = slot-rel (G.suc (coordᴺ always)) (guardˢ always always-found) (inj₁ tt)
```

## 7 位置的守卫若也无关：同一支里的比较推出同样的原则

把位置与孩子的守卫改成无关 (块的一种变体) 之后，§2 的两条陈述平凡成立；但同一支里两个位置的三路只能无关地读那一支的合法性。
这条陈述在当前的块上就能写出，它推出 `IrrSearch` 与 `IrrDecide` (证明同 `YiLvNegCompare.compare-read→irr-search`，前提多了 `1 ⊲ η`)。
守卫相关时它成立 (`YiRawNegOmega.compare-same-branch`)。

```agda
BranchCompareIrr : Set
BranchCompareIrr = ∀ (η : R) → .(Gd zero raw1 η) → (r r′ : Pre (read0 η)) →
  Tri (lev (read0 η) r) (lev (read0 η) r′)

branch-compare→irr-search : BranchCompareIrr → IrrSearch
branch-compare→irr-search cmp α s with cmp (coordᴺ α) (witness-guard α s) (hi α) (lo α)
... | below (m , r) e = seen-found α m (pre-flag (seen α m) _ r)
... | above () e
... | same ()

branch-compare→irr-decide : BranchCompareIrr → IrrDecide
branch-compare→irr-decide cmp γ mono ev
  with cmp (coordᴰ γ) (coordᴰ-guard γ mono ev) (1 , inj₁ tt) (0 , inj₁ tt)
... | below (m , r) e = inj₂ (m , tick-hit (γ m) _ r e)
... | above (n , inj₁ _) ()
... | above (n , inj₂ ()) e
... | same e = inj₁ (λ m → tick-flat (γ m) _ (cong (λ x → bodyᴸ x m) e))
```
