# 严格列 (五): 与码世界的桥

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** 这是验收工具, 导入 `LadderOrdPos`. `s ~ c`: 块形 $s$ 与码 $c$ 逐点同形 (只比形状, 不比值; 要逐点是因为 `cl g` 的 $g$ 之间没有函数外延). 给 $s\sim c$ 就有保序映射 `pm`, 第 0 行逐字对齐 (`rowq`), 于是 [CrossMSim](CrossMSim.lagda.md) 的 `bridge` 无条件成立:
>
> - `Br.sim`: `Tᴸ h p α ≈ᴿ Tᵖ M (pm p) α′`, $\alpha\cong\alpha'$.
> - `Br.val≅`, `Br.fgh`, `Br.lvl≅`, `Br.val≈`: 计值 $\cong$, FGH 逐点相等, 层号 $\cong$, 序数值互相 `≼`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeBridge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level hiding (up; sim)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅; _≈ᴿ_)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-≅; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdBase
import OCF.Align.TLCodeShape as A
import OCF.Align.LadderOrdPos as B
open import OCF.Align.TLCodeShape using (Sh; sz; ss; sl)
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl; HB)
open import OCF.Align.TLCodeLit using (Lit; shape; HL)
open import OCF.Align.TLCodeCert using (Tᴸ; Gᴸ; ev₀; Ptᴸ)
open import OCF.Align.LadderOrdCert using (Tᵖ; Gᵖ)
open import OCF.Align.ValueJudgeBase using (_≈ᵛ_) renaming (≅→≼ to ≅→≼ᵛ)
import OCF.Align.CrossMSimEq as CE
import OCF.Align.CrossMSim
import OCF.Align.LadderOrdTree
```

## §1 同形

```agda
infix 4 _~_
data _~_ : Sh → Code → Set where
  ~z : sz ~ cz
  ~s : ∀ {s c} → s ~ c → ss s ~ cs c
  ~l : ∀ {g h} → (∀ i → g i ~ h i) → sl g ~ cl h

pm : ∀ {s c} → s ~ c → A.Pos s → B.Pos c
pm (~s r) A.end = B.end
pm (~s r) (A.low p) = B.low (pm r p)
pm (~l R) (A.blk j p) = B.blk j (pm (~s (R j)) p)

pm-mono : ∀ {s c} (r : s ~ c) (p q : A.Pos s) → p A.<ᴾ q → pm r p B.<ᴾ pm r q
ltB-pm : ∀ (g : ℕ → Sh) (h : ℕ → Code) (R : ∀ i → g i ~ h i) j k (p : A.Pos (ss (g j))) (q : A.Pos (ss (g k))) →
         A.ltB g j k p q → B.ltB h j k (pm (~s (R j)) p) (pm (~s (R k)) q)
pm-mono (~s r) (A.low p) A.end x = tt
pm-mono (~s r) (A.low p) (A.low q) x = pm-mono r p q x
pm-mono (~l {g} {h} R) (A.blk j p) (A.blk k q) x = ltB-pm g h R j k p q x
ltB-pm g h R zero zero p q x = pm-mono (~s (R 0)) p q x
ltB-pm g h R zero (suc k) p q x = tt
ltB-pm g h R (suc j) (suc k) p q x = ltB-pm (λ i → g (suc i)) (λ i → h (suc i)) (λ i → R (suc i)) j k p q x

pm-fst : ∀ {s c} (r : s ~ c) → pm (~s r) (A.fstS s) ≡ B.fstC c
pm-fst ~z = refl
pm-fst (~s r) = cong B.low (pm-fst r)
pm-fst (~l R) = cong (λ z → B.low (B.blk 0 z)) (pm-fst (R 0))
```

## §2 第 0 行对齐

与 [CrossMUp](CrossMUp.lagda.md) §2 同样的做法: 函数相等字面写出, 进一层上下文只用 `cong`.

```agda
module Align {s₀ : Sh} {c₀ : Code} (r₀ : s₀ ~ c₀) where
  module AV = A.V s₀
  module BV = B.V c₀

  u : A.Pos (ss s₀) → B.Pos (cs c₀)
  u = pm (~s r₀)

  StR : AV.St → BV.St → Set
  StR AV.sf BV.sf = ⊤
  StR AV.sf (BV.sp _) = ⊥
  StR (AV.sp _) BV.sf = ⊥
  StR (AV.sp n) (BV.sp n′) = n′ ≡ u n

  record Rel {x y} (r : x ~ y) (C : AV.Cxt x) (C′ : BV.Cxt y) : Set where
    constructor rel
    field
      ιe  : (λ p → BV.Cxt.ι C′ (pm r p)) ≡ (λ p → u (AV.Cxt.ι C p))
      ste : StR (AV.Cxt.stv C) (BV.Cxt.stv C′)
  open Rel

  Aln : ∀ {x x′} → View A._<ᴾ_ AV.h₀ᴾ x → View B._<ᴾ_ BV.h₀ᴾ x′ → Set
  Aln base _ = ⊤
  Aln {x′ = x′} (clos {n = n} q) v′ = Σ (u n B.<ᴾ x′) λ r → v′ ≡ clos {n = u n} r
  Aln {x′ = x′} (chain F qs) v′ = Σ (∀ i → u (F i) B.<ᴾ x′) λ r → v′ ≡ chain (λ i → u (F i)) r

  closE : ∀ {x′ n′ n″} (e : n′ ≡ n″) (q : n′ B.<ᴾ x′) → Σ (n″ B.<ᴾ x′) λ r → clos {_<_ = B._<ᴾ_} {h₀ = BV.h₀ᴾ} {n = n′} q ≡ clos {n = n″} r
  closE refl q = q , refl

  chainE : ∀ {x′} {F′ F″ : ℕ → BV.H} (e : F′ ≡ F″) (qs : ∀ i → F′ i B.<ᴾ x′) → Σ (∀ i → F″ i B.<ᴾ x′) λ r → chain {_<_ = B._<ᴾ_} {h₀ = BV.h₀ᴾ} F′ qs ≡ chain F″ r
  chainE refl qs = qs , refl

  base-sf : ∀ {x} (e : x ≡ AV.h₀ᴾ) {x′} (v′ : View B._<ᴾ_ BV.h₀ᴾ x′) → Aln (proj₁ (subst AV.W (sym e) (base , tt))) v′
  base-sf refl v′ = tt

  Rel-Cl : ∀ {x y} {r : x ~ y} {C : AV.Cxt (ss x)} {C′ : BV.Cxt (cs y)} → Rel (~s r) C C′ → Rel r (AV.Cl C) (BV.Cl C′)
  Rel-Cl (rel e t) = rel (cong (λ f p → f (A.low p)) e) t

  Rel-Cb0 : ∀ {g h} {R : ∀ i → g i ~ h i} {C : AV.Cxt (sl g)} {C′ : BV.Cxt (cl h)} → Rel (~l R) C C′ → Rel (~s (R 0)) (AV.Cb0 C) (BV.Cb0 C′)
  Rel-Cb0 (rel e t) = rel (cong (λ f p → f (A.blk 0 p)) e) t

  Rel-CbS : ∀ {g h} {R : ∀ i → g i ~ h i} j {C : AV.Cxt (sl g)} {C′ : BV.Cxt (cl h)} → Rel (~l R) C C′ → Rel (~s (R (suc j))) (AV.CbS j C) (BV.CbS j C′)
  Rel-CbS j (rel e t) = rel (cong (λ f p → f (A.blk (suc j) p)) e) (cong (λ f → f (A.blk j A.end)) e)

  aln : ∀ {x y} (r : x ~ y) (C : AV.Cxt x) (C′ : BV.Cxt y) → Rel r C C′ → (p : A.Pos x) → Aln (proj₁ (AV.viewC C p)) (proj₁ (BV.viewC C′ (pm r p)))
  aln (~s ~z) (AV.mkC ι ιm AV.sf ok0 dec) C′ R A.end = base-sf (ok0 A.end tt) (proj₁ (BV.viewC C′ B.end))
  aln (~s ~z) (AV.mkC ι ιm (AV.sp n) ok0 dec) (BV.mkC ι′ ιm′ (BV.sp n′) ok0′ dec′) (rel e t) A.end = closE t (ok0′ B.end)
  aln (~s ~z) C C′ R (A.low ())
  aln (~s (~s r)) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ ιm′ BV.sf _ _) R A.end = closE (cong (λ f → f (A.low A.end)) (ιe R)) (ιm′ (B.low B.end) B.end tt)
  aln (~s (~s r)) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ ιm′ (BV.sp _) _ _) R A.end = closE (cong (λ f → f (A.low A.end)) (ιe R)) (ιm′ (B.low B.end) B.end tt)
  aln (~s (~s r)) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ _ BV.sf _ _) R (A.low p) = aln (~s r) (AV.Cl C) (BV.Cl C′) (Rel-Cl R) p
  aln (~s (~s r)) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ _ (BV.sp _) _ _) R (A.low p) = aln (~s r) (AV.Cl C) (BV.Cl C′) (Rel-Cl R) p
  aln (~s (~l Q)) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ ιm′ BV.sf _ _) R A.end = chainE (cong (λ f i → f (A.low (A.blk i A.end))) (ιe R)) (λ i → ιm′ (B.low (B.blk i B.end)) B.end tt)
  aln (~s (~l Q)) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ ιm′ (BV.sp _) _ _) R A.end = chainE (cong (λ f i → f (A.low (A.blk i A.end))) (ιe R)) (λ i → ιm′ (B.low (B.blk i B.end)) B.end tt)
  aln (~s (~l Q)) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ _ BV.sf _ _) R (A.low p) = aln (~l Q) (AV.Cl C) (BV.Cl C′) (Rel-Cl R) p
  aln (~s (~l Q)) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ _ (BV.sp _) _ _) R (A.low p) = aln (~l Q) (AV.Cl C) (BV.Cl C′) (Rel-Cl R) p
  aln (~l Q) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ _ BV.sf _ _) R (A.blk zero p) = aln (~s (Q 0)) (AV.Cb0 C) (BV.Cb0 C′) (Rel-Cb0 R) p
  aln (~l Q) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ _ (BV.sp _) _ _) R (A.blk zero p) = aln (~s (Q 0)) (AV.Cb0 C) (BV.Cb0 C′) (Rel-Cb0 R) p
  aln (~l Q) C@(AV.mkC _ _ AV.sf _ _) C′@(BV.mkC _ _ BV.sf _ _) R (A.blk (suc j) p) = aln (~s (Q (suc j))) (AV.CbS j C) (BV.CbS j C′) (Rel-CbS j R) p
  aln (~l Q) C@(AV.mkC _ _ (AV.sp _) _ _) C′@(BV.mkC _ _ (BV.sp _) _ _) R (A.blk (suc j) p) = aln (~s (Q (suc j))) (AV.CbS j C) (BV.CbS j C′) (Rel-CbS j R) p

  align : ∀ (p : A.Pos (ss s₀)) → Aln (proj₁ (AV.vw p)) (proj₁ (BV.vw (u p)))
  align = aln (~s r₀) AV.C₀ BV.C₀ (rel refl tt)
```

## §3 结论

```agda
module Br {t} (h : Lit t) {M : Code} (r : shape h ~ M) where
  open Align r public using (u; align; Aln)
  module AV′ = A.V (shape h)
  module BV′ = B.V M

  𝔸 𝔹 : HtB
  𝔸 = HL h
  𝔹 = HB M

  ε : ∀ {p q : Ptᴸ h} → p A.<ᴾ q → u p B.<ᴾ u q
  ε {p} {q} = pm-mono (~s r) p q

  module I = OCF.Align.LadderOrdTree 𝔹

  row-base : ∀ x → x ≡ I.h₀ → (v : View I._<ᴸ_ I.h₀ x) → I.rowV x (I.ΩI x) v ≡ I.rowB {x}
  row-base _ d base = refl
  row-base x d (clos {n = n} q) = ⊥-elim (I.no< {n} (subst (n I.<ᴸ_) d q))
  row-base x d (chain F qs) = ⊥-elim (I.no< {F 0} (subst (F 0 I.<ᴸ_) d (qs 0)))

  to-row : ∀ m (v : View A._<ᴾ_ AV′.h₀ᴾ m) → Aln v (proj₁ (BV′.vw (u m))) → CE.RowEq 𝔸 𝔹 u (λ {n} {m} → ε {n} {m}) m v
  to-row _ base a = row-base (u AV′.h₀ᴾ) (pm-fst r) (I.view (u AV′.h₀ᴾ))
  to-row m (clos {n = n} q) (x , d) = trans d (cong (clos {n = u n}) (B.<ᴾ-prop {p = u n} {q = u m} x (ε {n} {m} q)))
  to-row m (chain F qs) (x , d) = x , d

  rowq : ∀ m → CE.RowEq 𝔸 𝔹 u (λ {n} {m} → ε {n} {m}) m (HtB.view 𝔸 m)
  rowq m = to-row m (proj₁ (AV′.vw m)) (align m)

  open OCF.Align.CrossMSim 𝔸 𝔹 u (λ {n} {m} → ε {n} {m}) B.<ᴾ-tri-self rowq using (bridge)

  sim : (p : Ptᴸ h) (α α′ : Ordᴵ) → α ≅ᴵ α′ → Tᴸ h p α ≈ᴿ Tᵖ M (u p) α′
  sim = bridge

  val≅ : (p : Ptᴸ h) (α : Ordᴵ) → forceᴺ _ (Gᴸ h p α) ≅ forceᴺ _ (Gᵖ M (u p) α)
  val≅ p α = forceᴺ-≅ (toZ-≅ (sim p α α (≅ᴵ-refl α) ev₀ zero ev₀ zero z≅)) _ _

  fgh : (p : Ptᴸ h) (α : Ordᴵ) (n : ℕ) → FGH (forceᴺ _ (Gᴸ h p α)) n ≡ FGH (forceᴺ _ (Gᵖ M (u p) α)) n
  fgh p α = FGH-≅ (val≅ p α)

  lvl≅ : (p : Ptᴸ h) (α : Ordᴵ) → lvG (Gᴸ h p α) ≅ᴵ lvG (Gᵖ M (u p) α)
  lvl≅ p α = toLevel-≅ (forceᴺ-HS _ _) (forceᴺ-HS _ _) (val≅ p α)

  val≈ : (p : Ptᴸ h) (α : Ordᴵ) → forceᴺ _ (Gᴸ h p α) ≈ᵛ forceᴺ _ (Gᵖ M (u p) α)
  val≈ p α = ≅→≼ᵛ (val≅ p α) , ≅→≼ᵛ (≅-sym (val≅ p α))
```
