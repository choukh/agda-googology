# 跨段 (一): 码的上移

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (编译过, 无条件).** $M\subset M'$ 是字面的初始段: `_⊂_` 是一条从 $M'$ 走到 $M$ 的路径 (`es`: 剥一个后继; `el`: 进第 0 块), 这样复合不需要码的结合律 (`ᶜ+` 的结合律在 `cl` 上要函数外延). `⊂+ M N : M ⊂ M ᶜ+ N`. `up e : Pos (cs M) → Pos (cs M′)`.
>
> - `up-mono`, `up-refl`: 序在两边字面相同.
> - `up-inj`, `up-tri`: 单射; 三歧结果的形状不变 (规范形不变: 位置的表示唯一, 相等就是 $\equiv$).
> - `up-down`: 像是下闭的, 新高度只会加在上面.
> - `up-rk`: 秩字面不变.
> - `up-fst`: 最低点映到最低点.
> - `⊂-trans`, `up-trans`: 路径复合, 上移复合.
> - `align`, `rowq`: 第 0 行的写法对齐: 闭包的前驱是前驱的像, 链是链的像. 对 `V.viewC` 的上下文归纳.
>
> 只有第 0 行的写法是实质内容, 其余都是路径的直接结果. 这里不读记号.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.CrossMUp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level using (Ordᴵ)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_ᶜ+_)
import OCF.Align.CrossMSimEq as CE
import OCF.Align.LadderOrdTree
```

## §1 上移

```agda
infix 4 _⊂_
data _⊂_ : Code → Code → Set where
  ⊂r : ∀ {M} → M ⊂ M
  es : ∀ {M M′} → M ⊂ M′ → M ⊂ cs M′
  el : ∀ {M g} → M ⊂ g 0 → M ⊂ cl g

⊂-trans : ∀ {A B D} → A ⊂ B → B ⊂ D → A ⊂ D
⊂-trans a ⊂r = a
⊂-trans a (es b) = es (⊂-trans a b)
⊂-trans a (el b) = el (⊂-trans a b)

⊂+ : ∀ M N → M ⊂ M ᶜ+ N
⊂+ M cz = ⊂r
⊂+ M (cs N) = es (⊂+ M N)
⊂+ M (cl g) = el (⊂+ M (g 0))

up : ∀ {M M′} → M ⊂ M′ → Pos (cs M) → Pos (cs M′)
up ⊂r p = p
up (es e) p = low (up e p)
up (el e) p = low (blk 0 (up e p))

up-trans : ∀ {A B D} (a : A ⊂ B) (b : B ⊂ D) (p : Pos (cs A)) → up (⊂-trans a b) p ≡ up b (up a p)
up-trans a ⊂r p = refl
up-trans a (es b) p = cong low (up-trans a b p)
up-trans a (el b) p = cong (λ z → low (blk 0 z)) (up-trans a b p)

up-mono : ∀ {M M′} (e : M ⊂ M′) {p q : Pos (cs M)} → p <ᴾ q → up e p <ᴾ up e q
up-mono ⊂r x = x
up-mono (es e) x = up-mono e x
up-mono (el e) x = up-mono e x

up-refl : ∀ {M M′} (e : M ⊂ M′) {p q : Pos (cs M)} → up e p <ᴾ up e q → p <ᴾ q
up-refl ⊂r x = x
up-refl (es e) x = up-refl e x
up-refl (el e) x = up-refl e x

irrᴾ : ∀ {c} {p : Pos (cs c)} → p <ᴾ p → ⊥
irrᴾ {c} {p} x = HtB.irr (HB c) {p} x

no-self : ∀ {c} {a b : Pos (cs c)} → a ≡ b → a <ᴾ b → ⊥
no-self {c} {a} refl x = irrᴾ {c} {a} x

up-inj : ∀ {M M′} (e : M ⊂ M′) {p q : Pos (cs M)} → up e p ≡ up e q → p ≡ q
up-inj e {p} {q} d with <ᴾ-tri p q
... | tlt x = ⊥-elim (no-self d (up-mono e {p} {q} x))
... | teq x = x
... | tgt x = ⊥-elim (no-self (sym d) (up-mono e {q} {p} x))

-- 三歧结果的形状
data Sh3 : Set where
  slt seq sgt : Sh3

sh3 : ∀ {H : Set} {_<_ : H → H → Set} {a b} → Tri _<_ a b → Sh3
sh3 (tlt _) = slt
sh3 (teq _) = seq
sh3 (tgt _) = sgt

up-tri : ∀ {M M′} (e : M ⊂ M′) (p q : Pos (cs M)) → sh3 (<ᴾ-tri p q) ≡ sh3 (<ᴾ-tri (up e p) (up e q))
up-tri e p q with <ᴾ-tri p q | <ᴾ-tri (up e p) (up e q)
... | tlt x | tlt y = refl
... | teq x | teq y = refl
... | tgt x | tgt y = refl
... | tlt x | teq y = ⊥-elim (no-self y (up-mono e {p} {q} x))
... | tlt x | tgt y = ⊥-elim (irrᴾ {p = up e p} (<ᴾ-trans (up e p) (up e q) (up e p) (up-mono e {p} {q} x) y))
... | teq refl | tlt y = ⊥-elim (irrᴾ {p = up e p} y)
... | teq refl | tgt y = ⊥-elim (irrᴾ {p = up e p} y)
... | tgt x | tlt y = ⊥-elim (irrᴾ {p = up e q} (<ᴾ-trans (up e q) (up e p) (up e q) (up-mono e {q} {p} x) y))
... | tgt x | teq y = ⊥-elim (no-self (sym y) (up-mono e {q} {p} x))

-- 像是下闭的
up-down : ∀ {M M′} (e : M ⊂ M′) {y : Pos (cs M′)} {q : Pos (cs M)} → y <ᴾ up e q → Σ (Pos (cs M)) λ y₀ → (y ≡ up e y₀) × (y₀ <ᴾ q)
up-down ⊂r {y} x = y , refl , x
up-down (es e) {low y} x with up-down e {y} x
... | y₀ , d , l = y₀ , cong low d , l
up-down (el e) {low (blk zero y)} x with up-down e {y} x
... | y₀ , d , l = y₀ , cong (λ z → low (blk 0 z)) d , l

-- 秩字面不变
up-rk : ∀ {M M′} (e : M ⊂ M′) b (p : Pos (cs M)) → rkP b (up e p) ≡ rkP b p
up-rk ⊂r b p = refl
up-rk (es e) b p = up-rk e b p
up-rk (el e) b p = up-rk e b p

-- 最低点
up-fst : ∀ {M M′} (e : M ⊂ M′) → up e (fstC M) ≡ fstC M′
up-fst ⊂r = refl
up-fst (es e) = cong low (up-fst e)
up-fst (el e) = cong (λ z → low (blk 0 z)) (up-fst e)
```

## §2 第 0 行的写法对齐

一般形式: 两个世界 $A$, $B$, 保序映射 $u$. 关系 `Rel` 说两个上下文的 $\iota$ 差一个 $u$, 这里 **函数相等是字面写出来的**, 不用函数外延: 进一层上下文时只用 `cong`. `Aln v v′` 说右边的写法是左边的像; `base` 不要求内容, 由 §4 单独处理.

```agda
module Align (M M′ : Code) (u : Pos (cs M) → Pos (cs M′)) where
  module A = V M
  module B = V M′

  StR : A.St → B.St → Set
  StR A.sf A.sf = ⊤
  StR A.sf (B.sp _) = ⊥
  StR (A.sp _) B.sf = ⊥
  StR (A.sp n) (B.sp n′) = n′ ≡ u n

  record Rel {c} (C : A.Cxt c) (C′ : B.Cxt c) : Set where
    constructor rel
    field
      ιe  : B.Cxt.ι C′ ≡ (λ x → u (A.Cxt.ι C x))
      ste : StR (A.Cxt.stv C) (B.Cxt.stv C′)
  open Rel

  Aln : ∀ {x x′} → View _<ᴾ_ A.h₀ᴾ x → View _<ᴾ_ B.h₀ᴾ x′ → Set
  Aln base _ = ⊤
  Aln {x′ = x′} (clos {n = n} q) v′ = Σ (u n <ᴾ x′) λ r → v′ ≡ clos {n = u n} r
  Aln {x′ = x′} (chain F qs) v′ = Σ (∀ i → u (F i) <ᴾ x′) λ r → v′ ≡ chain (λ i → u (F i)) r

  closE : ∀ {x′ n′ n″} (e : n′ ≡ n″) (q : n′ <ᴾ x′) → Σ (n″ <ᴾ x′) λ r → clos {_<_ = _<ᴾ_} {h₀ = B.h₀ᴾ} {n = n′} q ≡ clos {n = n″} r
  closE refl q = q , refl

  chainE : ∀ {x′} {F′ F″ : ℕ → B.H} (e : F′ ≡ F″) (qs : ∀ i → F′ i <ᴾ x′) → Σ (∀ i → F″ i <ᴾ x′) λ r → chain {_<_ = _<ᴾ_} {h₀ = B.h₀ᴾ} F′ qs ≡ chain F″ r
  chainE refl qs = qs , refl

  base-sf : ∀ {x} (e : x ≡ A.h₀ᴾ) {x′} (v′ : View _<ᴾ_ B.h₀ᴾ x′) → Aln (proj₁ (subst A.W (sym e) (base , tt))) v′
  base-sf refl v′ = tt

  Rel-Cl : ∀ {c} {C : A.Cxt (cs c)} {C′ : B.Cxt (cs c)} → Rel C C′ → Rel (A.Cl C) (B.Cl C′)
  Rel-Cl (rel e s) = rel (cong (λ f p → f (low p)) e) s

  Rel-Cb0 : ∀ {g} {C : A.Cxt (cl g)} {C′ : B.Cxt (cl g)} → Rel C C′ → Rel (A.Cb0 C) (B.Cb0 C′)
  Rel-Cb0 (rel e s) = rel (cong (λ f p → f (blk 0 p)) e) s

  Rel-CbS : ∀ {g} j {C : A.Cxt (cl g)} {C′ : B.Cxt (cl g)} → Rel C C′ → Rel (A.CbS j C) (B.CbS j C′)
  Rel-CbS j (rel e s) = rel (cong (λ f p → f (blk (suc j) p)) e) (cong (λ f → f (blk j end)) e)

  aln : ∀ {c} (C : A.Cxt c) (C′ : B.Cxt c) → Rel C C′ → (p : Pos c) → Aln (proj₁ (A.viewC C p)) (proj₁ (B.viewC C′ p))
  aln {cs cz} (A.mkC ι ιm A.sf ok0 dec) C′ R end = base-sf (ok0 end tt) (proj₁ (B.viewC C′ end))
  aln {cs cz} (A.mkC ι ιm (A.sp n) ok0 dec) (B.mkC ι′ ιm′ (B.sp n′) ok0′ dec′) (rel e s) end = closE s (ok0′ end)
  aln {cs cz} C C′ R (low ())
  aln {cs (cs c)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln {cs (cs c)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln {cs (cs c)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (low p) = aln {cs c} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {cs (cs c)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (low p) = aln {cs c} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {cs (cl g)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln {cs (cl g)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln {cs (cl g)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (low p) = aln {cl g} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {cs (cl g)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (low p) = aln {cl g} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {cl g} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (blk zero p) = aln {cs (g 0)} (A.Cb0 C) (B.Cb0 C′) (Rel-Cb0 R) p
  aln {cl g} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (blk zero p) = aln {cs (g 0)} (A.Cb0 C) (B.Cb0 C′) (Rel-Cb0 R) p
  aln {cl g} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (blk (suc j) p) = aln {cs (g (suc j))} (A.CbS j C) (B.CbS j C′) (Rel-CbS j R) p
  aln {cl g} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (blk (suc j) p) = aln {cs (g (suc j))} (A.CbS j C) (B.CbS j C′) (Rel-CbS j R) p
```

## §3 从最外层走到 $M$ 这一块

$M'$ 的最外层上下文沿 `up` 的路径走进去, 就是 $M$ 这一段的上下文. 每一步的 $\iota$ 字面地差一个 `low` 或 `blk 0`. `alnU` 对 $N$ 归纳, 右边的上下文逐层变窄, 左边不动.

```agda
module AlignU (M M′ : Code) (u : Pos (cs M) → Pos (cs M′)) where
  open Align M M′ u

  record RelU {N₁ : Code} (e₁ : M ⊂ N₁) (C : A.Cxt (cs M)) (C′ : B.Cxt (cs N₁)) : Set where
    constructor relU
    field
      ιeU : (λ x → B.Cxt.ι C′ (up e₁ x)) ≡ (λ x → u (A.Cxt.ι C x))
      steU : StR (A.Cxt.stv C) (B.Cxt.stv C′)

  alnU : ∀ {N₁} (e₁ : M ⊂ N₁) (C : A.Cxt (cs M)) (C′ : B.Cxt (cs N₁)) → RelU e₁ C C′ → (p : Pos (cs M)) → Aln (proj₁ (A.viewC C p)) (proj₁ (B.viewC C′ (up e₁ p)))
  alnU ⊂r C C′ (relU d s) p = aln C C′ (rel d s) p
  alnU (es e₁) C C′@(B.mkC _ _ B.sf _ _) (relU d s) p = alnU e₁ C (B.Cl C′) (relU d s) p
  alnU (es e₁) C C′@(B.mkC _ _ (B.sp _) _ _) (relU d s) p = alnU e₁ C (B.Cl C′) (relU d s) p
  alnU (el e₁) C C′@(B.mkC _ _ B.sf _ _) (relU d s) p = alnU e₁ C (B.Cb0 (B.Cl C′)) (relU d s) p
  alnU (el e₁) C C′@(B.mkC _ _ (B.sp _) _ _) (relU d s) p = alnU e₁ C (B.Cb0 (B.Cl C′)) (relU d s) p
```

## §4 结论: `RowEq`

```agda
module UpWorld {M M′ : Code} (e : M ⊂ M′) where
  u : Pos (cs M) → Pos (cs M′)
  u = up e

  𝔸 𝔹 : HtB
  𝔸 = HB M
  𝔹 = HB M′

  ε : ∀ {p q : Pos (cs M)} → p <ᴾ q → u p <ᴾ u q
  ε = up-mono e

  open Align M M′ u
  open AlignU M M′ u
  module I = OCF.Align.LadderOrdTree 𝔹

  align : ∀ (p : Pos (cs M)) → Aln (proj₁ (A.vw p)) (proj₁ (B.vw (u p)))
  align = alnU e A.C₀ B.C₀ (relU refl tt)

  row-base : ∀ x → x ≡ I.h₀ → (v : View I._<ᴸ_ I.h₀ x) → I.rowV x (I.ΩI x) v ≡ I.rowB {x}
  row-base _ d base = refl
  row-base x d (clos {n = n} q) = ⊥-elim (I.no< {n} (subst (n I.<ᴸ_) d q))
  row-base x d (chain F qs) = ⊥-elim (I.no< {F 0} (subst (F 0 I.<ᴸ_) d (qs 0)))

  to-row : ∀ m (v : View _<ᴾ_ A.h₀ᴾ m) → Aln v (proj₁ (B.vw (u m))) → CE.RowEq 𝔸 𝔹 u ε m v
  to-row _ base a = row-base (u A.h₀ᴾ) (up-fst e) (I.view (u A.h₀ᴾ))
  to-row m (clos {n = n} q) (r , d) = trans d (cong (clos {n = u n}) (<ᴾ-prop {p = u n} {q = u m} r (ε q)))
  to-row m (chain F qs) (r , d) = r , d

  rowq : ∀ m → CE.RowEq 𝔸 𝔹 u ε m (HtB.view 𝔸 m)
  rowq m = to-row m (proj₁ (A.vw m)) (align m)
```
