# 跨段, 下一步 (四): 码逐点相同, 树同值

> 入口 [CrossNext](CrossNext.lagda.md). **判决: HOLDS (编译过, 无条件).** `A ≋ B`: 两个码逐点相同. 没有函数外延时 `cl f ≡ cl g` 证不出来, 而 $\lceil\eta\rceil$ 与 $\lceil$ `η` 转成树再读回 $\rceil$ 就只差这个. `≋-T`: `A ≋ B` 时两个世界顶上的第 0 行 $\cong$.
>
> 做法与 [CrossMUp](CrossMUp.lagda.md) 相同: 对上下文归纳说第 0 行的写法对齐, 再喂给 [CrossMSim](CrossMSim.lagda.md). `map≋ d end = end` 是定义等式, 所以链行的函数相等只要 `cong`, 不要外延.
>
> 还有 `cz+≋ d : cz ᶜ+ d ≋ d`, `≋-refl`, `≋-sym`.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.CrossNextEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_ᶜ+_)
open import OCF.Align.CrossMUp using (module Align)
import OCF.Align.CrossMSimEq as CE
import OCF.Align.LadderOrdTree

infix 4 _≋_
data _≋_ : Code → Code → Set where
  cz≋ : cz ≋ cz
  cs≋ : ∀ {a b} → a ≋ b → cs a ≋ cs b
  cl≋ : ∀ {f g} → (∀ n → f n ≋ g n) → cl f ≋ cl g

≋-refl : ∀ c → c ≋ c
≋-refl cz = cz≋
≋-refl (cs c) = cs≋ (≋-refl c)
≋-refl (cl g) = cl≋ (λ n → ≋-refl (g n))

≋-sym : ∀ {a b} → a ≋ b → b ≋ a
≋-sym cz≋ = cz≋
≋-sym (cs≋ d) = cs≋ (≋-sym d)
≋-sym (cl≋ h) = cl≋ (λ n → ≋-sym (h n))

cz+≋ : ∀ d → cz ᶜ+ d ≋ d
cz+≋ cz = cz≋
cz+≋ (cs d) = cs≋ (cz+≋ d)
cz+≋ (cl g) = cl≋ go
  where
  go : ∀ n → _ ≋ g n
  go zero = cz+≋ (g 0)
  go (suc n) = ≋-refl (g (suc n))

map≋ : ∀ {a b} → a ≋ b → Pos a → Pos b
map≋ (cs≋ d) end = end
map≋ (cs≋ d) (low p) = low (map≋ d p)
map≋ (cl≋ h) (blk j p) = blk j (map≋ (cs≋ (h j)) p)

mono≋ : ∀ {a b} (d : a ≋ b) (p q : Pos a) → p <ᴾ q → map≋ d p <ᴾ map≋ d q
monoB : ∀ {f g} (h : ∀ n → f n ≋ g n) j k (p : Pos (cs (f j))) (q : Pos (cs (f k))) → ltB f j k p q → ltB g j k (map≋ (cs≋ (h j)) p) (map≋ (cs≋ (h k)) q)
mono≋ (cs≋ d) (low p) end x = tt
mono≋ (cs≋ d) (low p) (low q) x = mono≋ d p q x
mono≋ (cl≋ h) (blk j p) (blk k q) x = monoB h j k p q x
monoB h zero zero p q x = mono≋ (cs≋ (h 0)) p q x
monoB h zero (suc k) p q x = tt
monoB {f} {g} h (suc j) (suc k) p q x = monoB {λ i → f (suc i)} {λ i → g (suc i)} (λ i → h (suc i)) j k p q x

fst≋ : ∀ {a b} (d : a ≋ b) → map≋ (cs≋ d) (fstC a) ≡ fstC b
fst≋ cz≋ = refl
fst≋ (cs≋ d) = cong low (fst≋ d)
fst≋ (cl≋ h) = cong (λ z → low (blk 0 z)) (fst≋ (h 0))
```

## §1 第 0 行的写法对齐

```agda
module World {M M′ : Code} (d₀ : M ≋ M′) where
  u : Pos (cs M) → Pos (cs M′)
  u = map≋ (cs≋ d₀)

  ε : ∀ {p q : Pos (cs M)} → p <ᴾ q → u p <ᴾ u q
  ε {p} {q} = mono≋ (cs≋ d₀) p q

  open Align M M′ u

  record Rel₂ {c c′} (d : c ≋ c′) (C : A.Cxt c) (C′ : B.Cxt c′) : Set where
    constructor rel₂
    field
      ιe  : (λ x → B.Cxt.ι C′ (map≋ d x)) ≡ (λ x → u (A.Cxt.ι C x))
      ste : StR (A.Cxt.stv C) (B.Cxt.stv C′)
  open Rel₂

  aln₂ : ∀ {c c′} (d : c ≋ c′) (C : A.Cxt c) (C′ : B.Cxt c′) → Rel₂ d C C′ → (p : Pos c) → Aln (proj₁ (A.viewC C p)) (proj₁ (B.viewC C′ (map≋ d p)))
  aln₂ (cs≋ cz≋) (A.mkC ι ιm A.sf ok0 dec) C′ R end = base-sf (ok0 end tt) (proj₁ (B.viewC C′ end))
  aln₂ (cs≋ cz≋) (A.mkC ι ιm (A.sp n) ok0 dec) (B.mkC ι′ ιm′ (B.sp n′) ok0′ dec′) (rel₂ e s) end = closE s (ok0′ end)
  aln₂ (cs≋ cz≋) C C′ R (low ())
  aln₂ (cs≋ (cs≋ d)) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln₂ (cs≋ (cs≋ d)) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln₂ (cs≋ (cs≋ d)) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) (rel₂ e s) (low p) = aln₂ (cs≋ d) (A.Cl C) (B.Cl C′) (rel₂ (cong (λ f p′ → f (low p′)) e) s) p
  aln₂ (cs≋ (cs≋ d)) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) (rel₂ e s) (low p) = aln₂ (cs≋ d) (A.Cl C) (B.Cl C′) (rel₂ (cong (λ f p′ → f (low p′)) e) s) p
  aln₂ (cs≋ (cl≋ h)) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln₂ (cs≋ (cl≋ h)) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln₂ (cs≋ (cl≋ h)) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) (rel₂ e s) (low p) = aln₂ (cl≋ h) (A.Cl C) (B.Cl C′) (rel₂ (cong (λ f p′ → f (low p′)) e) s) p
  aln₂ (cs≋ (cl≋ h)) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) (rel₂ e s) (low p) = aln₂ (cl≋ h) (A.Cl C) (B.Cl C′) (rel₂ (cong (λ f p′ → f (low p′)) e) s) p
  aln₂ (cl≋ h) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) (rel₂ e s) (blk zero p) = aln₂ (cs≋ (h 0)) (A.Cb0 C) (B.Cb0 C′) (rel₂ (cong (λ f p′ → f (blk 0 p′)) e) s) p
  aln₂ (cl≋ h) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) (rel₂ e s) (blk zero p) = aln₂ (cs≋ (h 0)) (A.Cb0 C) (B.Cb0 C′) (rel₂ (cong (λ f p′ → f (blk 0 p′)) e) s) p
  aln₂ (cl≋ h) C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) (rel₂ e s) (blk (suc j) p) = aln₂ (cs≋ (h (suc j))) (A.CbS j C) (B.CbS j C′) (rel₂ (cong (λ f p′ → f (blk (suc j) p′)) e) (cong (λ f → f (blk j end)) e)) p
  aln₂ (cl≋ h) C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) (rel₂ e s) (blk (suc j) p) = aln₂ (cs≋ (h (suc j))) (A.CbS j C) (B.CbS j C′) (rel₂ (cong (λ f p′ → f (blk (suc j) p′)) e) (cong (λ f → f (blk j end)) e)) p

  𝔸 𝔹 : HtB
  𝔸 = HB M
  𝔹 = HB M′

  module I = OCF.Align.LadderOrdTree 𝔹

  align : ∀ (p : Pos (cs M)) → Aln (proj₁ (A.vw p)) (proj₁ (B.vw (u p)))
  align = aln₂ (cs≋ d₀) A.C₀ B.C₀ (rel₂ refl tt)

  row-base : ∀ x → x ≡ I.h₀ → (v : View I._<ᴸ_ I.h₀ x) → I.rowV x (I.ΩI x) v ≡ I.rowB {x}
  row-base _ e base = refl
  row-base x e (clos {n = n} q) = ⊥-elim (I.no< {n} (subst (n I.<ᴸ_) e q))
  row-base x e (chain F qs) = ⊥-elim (I.no< {F 0} (subst (F 0 I.<ᴸ_) e (qs 0)))

  to-row : ∀ m (v : View _<ᴾ_ A.h₀ᴾ m) → Aln v (proj₁ (B.vw (u m))) → CE.RowEq 𝔸 𝔹 u (λ {n} {m′} → ε {n} {m′}) m v
  to-row _ base a = row-base (u A.h₀ᴾ) (fst≋ d₀) (I.view (u A.h₀ᴾ))
  to-row m (clos {n = n} q) (r , e) = trans e (cong (clos {n = u n}) (<ᴾ-prop {p = u n} {q = u m} r (ε {n} {m} q)))
  to-row m (chain F qs) (r , e) = r , e

  rowq : ∀ m → CE.RowEq 𝔸 𝔹 u (λ {n} {m′} → ε {n} {m′}) m (HtB.view 𝔸 m)
  rowq m = to-row m (proj₁ (A.vw m)) (align m)
```
