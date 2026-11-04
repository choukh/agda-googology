# 严格列 (七): 块形的上移

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** `s ⊂ s′`: 块形 $s$ 是 $s'$ 的字面初始段. §2 由 [CrossMUp](CrossMUp.lagda.md) §2, §3 机械改名 (`Code` → `Sh`). 比原文件多的是: 世界是 `HL h`, `HL h′`, 其余相同. `⊂⊕`: $a$ 的块形是 $a\oplus b$ 的初始段, 对一切带证书的 $a,b$. **这不是累加的定义: $\oplus$ 是通常的序数加法, 证书只说 $a$ 字面在里面.**
>
> - `up-simᴸ`: `Tᴸ h p α ≈ᴿ Tᴸ h′ (up e p) α′`.
> - `up≅ᴸ`, `up≺ᴸ`, `step≺ᴸ`: 计值 $\cong$; 跨段严格增长, 比较在 $h'$ 这个字面公共上界里做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeUp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level hiding (up; sim)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅; _≈ᴿ_)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdBase
open import OCF.Align.TLCodeShape
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeArith using (_⊕_; L⊕)
open import OCF.Align.TLCodeCert using (Ptᴸ; Tᴸ; Gᴸ; growᴸ; ev₀)
import OCF.Align.CrossMSimEq as CE
import OCF.Align.CrossMSim
import OCF.Align.LadderOrdTree
```

## §1 上移

```agda
infix 4 _⊂_
data _⊂_ : Sh → Sh → Set where
  ⊂r : ∀ {M} → M ⊂ M
  es : ∀ {M M′} → M ⊂ M′ → M ⊂ ss M′
  el : ∀ {M g} → M ⊂ g 0 → M ⊂ sl g

up : ∀ {M M′} → M ⊂ M′ → Pos (ss M) → Pos (ss M′)
up ⊂r p = p
up (es e) p = low (up e p)
up (el e) p = low (blk 0 (up e p))

up-mono : ∀ {M M′} (e : M ⊂ M′) {p q : Pos (ss M)} → p <ᴾ q → up e p <ᴾ up e q
up-mono ⊂r x = x
up-mono (es e) x = up-mono e x
up-mono (el e) x = up-mono e x

up-fst : ∀ {M M′} (e : M ⊂ M′) → up e (fstS M) ≡ fstS M′
up-fst ⊂r = refl
up-fst (es e) = cong low (up-fst e)
up-fst (el e) = cong (λ z → low (blk 0 z)) (up-fst e)

⊂⊕ : ∀ {a b} (ha : Lit a) (hb : Lit b) → shape ha ⊂ shape (L⊕ ha hb)
⊂⊕ ha lz = ⊂r
⊂⊕ ha (ls hb) = es (⊂⊕ ha hb)
⊂⊕ ha (ll hf hr) = el (⊂⊕ ha (hf 0))
```

## §2 第 0 行的写法对齐

一般形式: 两个世界 $A$, $B$, 保序映射 $u$. 关系 `Rel` 说两个上下文的 $\iota$ 差一个 $u$, 这里 **函数相等是字面写出来的**, 不用函数外延: 进一层上下文时只用 `cong`. `Aln v v′` 说右边的写法是左边的像; `base` 不要求内容, 由 §4 单独处理.

```agda
module Align (M M′ : Sh) (u : Pos (ss M) → Pos (ss M′)) where
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

  Rel-Cl : ∀ {c} {C : A.Cxt (ss c)} {C′ : B.Cxt (ss c)} → Rel C C′ → Rel (A.Cl C) (B.Cl C′)
  Rel-Cl (rel e s) = rel (cong (λ f p → f (low p)) e) s

  Rel-Cb0 : ∀ {g} {C : A.Cxt (sl g)} {C′ : B.Cxt (sl g)} → Rel C C′ → Rel (A.Cb0 C) (B.Cb0 C′)
  Rel-Cb0 (rel e s) = rel (cong (λ f p → f (blk 0 p)) e) s

  Rel-CbS : ∀ {g} j {C : A.Cxt (sl g)} {C′ : B.Cxt (sl g)} → Rel C C′ → Rel (A.CbS j C) (B.CbS j C′)
  Rel-CbS j (rel e s) = rel (cong (λ f p → f (blk (suc j) p)) e) (cong (λ f → f (blk j end)) e)

  aln : ∀ {c} (C : A.Cxt c) (C′ : B.Cxt c) → Rel C C′ → (p : Pos c) → Aln (proj₁ (A.viewC C p)) (proj₁ (B.viewC C′ p))
  aln {ss sz} (A.mkC ι ιm A.sf ok0 dec) C′ R end = base-sf (ok0 end tt) (proj₁ (B.viewC C′ end))
  aln {ss sz} (A.mkC ι ιm (A.sp n) ok0 dec) (B.mkC ι′ ιm′ (B.sp n′) ok0′ dec′) (rel e s) end = closE s (ok0′ end)
  aln {ss sz} C C′ R (low ())
  aln {ss (ss c)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln {ss (ss c)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = closE (cong (λ f → f (low end)) (ιe R)) (ιm′ (low end) end tt)
  aln {ss (ss c)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (low p) = aln {ss c} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {ss (ss c)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (low p) = aln {ss c} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {ss (sl g)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ ιm′ B.sf _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln {ss (sl g)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ ιm′ (B.sp _) _ _) R end = chainE (cong (λ f i → f (low (blk i end))) (ιe R)) (λ i → ιm′ (low (blk i end)) end tt)
  aln {ss (sl g)} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (low p) = aln {sl g} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {ss (sl g)} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (low p) = aln {sl g} (A.Cl C) (B.Cl C′) (Rel-Cl R) p
  aln {sl g} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (blk zero p) = aln {ss (g 0)} (A.Cb0 C) (B.Cb0 C′) (Rel-Cb0 R) p
  aln {sl g} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (blk zero p) = aln {ss (g 0)} (A.Cb0 C) (B.Cb0 C′) (Rel-Cb0 R) p
  aln {sl g} C@(A.mkC _ _ A.sf _ _) C′@(B.mkC _ _ B.sf _ _) R (blk (suc j) p) = aln {ss (g (suc j))} (A.CbS j C) (B.CbS j C′) (Rel-CbS j R) p
  aln {sl g} C@(A.mkC _ _ (A.sp _) _ _) C′@(B.mkC _ _ (B.sp _) _ _) R (blk (suc j) p) = aln {ss (g (suc j))} (A.CbS j C) (B.CbS j C′) (Rel-CbS j R) p
```

## §3 从最外层走到这一块

$M'$ 的最外层上下文沿 `up` 的路径走进去, 就是 $M$ 这一段的上下文. 每一步的 $\iota$ 字面地差一个 `low` 或 `blk 0`. `alnU` 对 $N$ 归纳, 右边的上下文逐层变窄, 左边不动.

```agda
module AlignU (M M′ : Sh) (u : Pos (ss M) → Pos (ss M′)) where
  open Align M M′ u

  record RelU {N₁ : Sh} (e₁ : M ⊂ N₁) (C : A.Cxt (ss M)) (C′ : B.Cxt (ss N₁)) : Set where
    constructor relU
    field
      ιeU : (λ x → B.Cxt.ι C′ (up e₁ x)) ≡ (λ x → u (A.Cxt.ι C x))
      steU : StR (A.Cxt.stv C) (B.Cxt.stv C′)

  alnU : ∀ {N₁} (e₁ : M ⊂ N₁) (C : A.Cxt (ss M)) (C′ : B.Cxt (ss N₁)) → RelU e₁ C C′ → (p : Pos (ss M)) → Aln (proj₁ (A.viewC C p)) (proj₁ (B.viewC C′ (up e₁ p)))
  alnU ⊂r C C′ (relU d s) p = aln C C′ (rel d s) p
  alnU (es e₁) C C′@(B.mkC _ _ B.sf _ _) (relU d s) p = alnU e₁ C (B.Cl C′) (relU d s) p
  alnU (es e₁) C C′@(B.mkC _ _ (B.sp _) _ _) (relU d s) p = alnU e₁ C (B.Cl C′) (relU d s) p
  alnU (el e₁) C C′@(B.mkC _ _ B.sf _ _) (relU d s) p = alnU e₁ C (B.Cb0 (B.Cl C′)) (relU d s) p
  alnU (el e₁) C C′@(B.mkC _ _ (B.sp _) _ _) (relU d s) p = alnU e₁ C (B.Cb0 (B.Cl C′)) (relU d s) p
```

## §4 结论

```agda
module UpWorld {t t′} (h : Lit t) (h′ : Lit t′) (e : shape h ⊂ shape h′) where
  M = shape h
  M′ = shape h′

  u : Pos (ss M) → Pos (ss M′)
  u = up e

  𝔸 𝔹 : HtB
  𝔸 = HL h
  𝔹 = HL h′

  ε : ∀ {p q : Pos (ss M)} → p <ᴾ q → u p <ᴾ u q
  ε = up-mono e

  open Align M M′ u
  open AlignU M M′ u
  module I = OCF.Align.LadderOrdTree 𝔹

  align : ∀ (p : Pos (ss M)) → Aln (proj₁ (A.vw p)) (proj₁ (B.vw (u p)))
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

  open OCF.Align.CrossMSim 𝔸 𝔹 u ε <ᴾ-tri-self rowq public using (bridge)

up-simᴸ : ∀ {t t′} (h : Lit t) (h′ : Lit t′) (e : shape h ⊂ shape h′) (p : Ptᴸ h) (α α′ : Ordᴵ) → α ≅ᴵ α′ → Tᴸ h p α ≈ᴿ Tᴸ h′ (up e p) α′
up-simᴸ h h′ e = UpWorld.bridge h h′ e

up≅ᴸ : ∀ {t t′} (h : Lit t) (h′ : Lit t′) (e : shape h ⊂ shape h′) (p : Ptᴸ h) (α : Ordᴵ) → forceᴺ _ (Gᴸ h p α) ≅ forceᴺ _ (Gᴸ h′ (up e p) α)
up≅ᴸ h h′ e p α = forceᴺ-≅ (toZ-≅ (up-simᴸ h h′ e p α α (≅ᴵ-refl α) ev₀ zero ev₀ zero z≅)) _ _

≺-≅ˡ′ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₃} {a : Ordᶜ ℓ₂} → c′ ≅ c → c ≺ a → c′ ≺ a
≺-≅ˡ′ e (≺z e₀) = ≺z (≅-trans e e₀)
≺-≅ˡ′ e (≺s h) = ≺s (≺-≅ˡ′ e h)
≺-≅ˡ′ e (≺l n h) = ≺l n (≺-≅ˡ′ e h)
≺-≅ˡ′ e (≺i x ex h) = ≺i x ex (≺-≅ˡ′ e h)
≺-≅ˡ′ e (≺u h) = ≺u (≺-≅ˡ′ e h)

-- 跨段的严格增长: 比较在字面公共上界里做
up≺ᴸ : ∀ {t t′} (h : Lit t) (h′ : Lit t′) (e : shape h ⊂ shape h′) (p : Ptᴸ h) (m : Ptᴸ h′) → up e p <ᴾ m → forceᴺ _ (Gᴸ h p zero) ≺ forceᴺ _ (Gᴸ h′ m zero)
up≺ᴸ h h′ e p m r = ≺-≅ˡ′ (up≅ᴸ h h′ e p zero) (growᴸ h′ {up e p} {m} r)

-- a 与 a ⊕ suc b
step≺ᴸ : ∀ {a b} (ha : Lit a) (hb : Lit b) → forceᴺ _ (Gᴸ ha end zero) ≺ forceᴺ _ (Gᴸ (L⊕ ha (ls hb)) end zero)
step≺ᴸ ha hb = up≺ᴸ ha (L⊕ ha (ls hb)) (⊂⊕ ha (ls hb)) end end tt
```
