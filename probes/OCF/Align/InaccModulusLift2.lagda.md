# 层号判决的范数模: 由单调与有界共尾性提升 (验收)

> **验收节.** 与 [InaccModulusLift](InaccModulusLift.lagda.md) 的 `Lift` 相同的结论, 前提换成标准形理论里实际有的两条: `mono` (`t[n] < t[n+1]`) 与 `cofb` (`s < t ⟹ s < t[n]`, 其中 `n ≤ 1 + sz s`). 从 `sz-step` 得 **`sz≤wk`: 项的大小不超过其树的 1-走步长度**, 所以树读出的 `wk` 是 `cofb` 的模. 结论在 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusLift2 where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-trans; ≤⇒≤′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst; subst₂)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase
open import OCF.Align.InaccStrikeCommute
open import OCF.Align.InaccModulusBase
open import OCF.Align.InaccModulusLift using (below-suc; lt-nz; cof0; cmp-eq; gt→lt)
open import OCF.Align.InaccModulusSize using (sz-step; sz-pred)
open import OCF.Align.Standard using (sz)
import OCF.Align.EBO as E
open E using (T; c0; c1; cω; cΩ; cof; pred; pred-suc; fsn; fsT; cmpᵀ; lt; eq; gt)

module Lift₂ (fe : Funext) {Q N : T → Set} (cl : ClQ Q N)
             (agr : ∀ u v → N u → N v → GV (cmpᵀ u v) (Dᵐ (Tr.L Dᵐ u) (Tr.L Dᵐ v)))
             (P : T → Set)
             (p⊂q : ∀ {t} → P t → Q t)
             (p-fs : ∀ {t} → P t → cof t ≡ cω → ∀ n → P (fsn t n))
             (p-pr : ∀ {t} → P t → cof t ≡ c1 → P (pred t))
             (p-nc : ∀ {t ν} → P t → cof t ≡ cΩ ν → ⊥)
             (mono : ∀ {t} → P t → cof t ≡ cω → ∀ n → cmpᵀ (fsn t n) (fsn t (suc n)) ≡ lt)
             (cofb : ∀ {s t} → P s → P t → cof t ≡ cω → cmpᵀ s t ≡ lt →
                     Σ ℕ λ n → (n ≤ suc (sz s)) × (cmpᵀ s (fsn t n) ≡ lt))
             where
  open Step Dᵐ
  open Main fe Dᵐ Q N cl agr

  Nd₂ : ∀ x s t → x ≡ S t → P s → P t → cmpᵀ s t ≡ lt → Nd (L s) (toLvS x)
  Nd₂ zero s t e ps p l with cof t in ce | stepT t (p⊂q p)
  ... | c0   | _ = ⊥-elim (lt-nz s t (cof0 t ce) l)
  ... | c1   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  Nd₂ (suc a) s t e ps p l with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | c1   | c with below-suc s (pred t) (subst (λ z → cmpᵀ s z ≡ lt) (sym (pred-suc t ce)) l)
  ...   | inj₁ q with Nd₂ a s (pred t) (suc-inj (trans e c)) ps (p-pr p ce) q
  ...     | r , h = inj₂ r , h
  Nd₂ (suc a) s t e ps p l | c1 | c | inj₂ q =
    inj₁ tt , trans (cong toLvS (suc-inj (trans e c))) (cong L (sym (cmp-eq s (pred t) q)))
  Nd₂ (lim f) s t e ps p l with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | c1   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | cω   | c with cofb ps p ce l
  ...   | n , _ , q with Nd₂ (f n) s (fsn t n) (cong-app (lim-inj (trans e c)) n) ps (p-fs p ce n) q
  ...     | r , h = (n , r) , h
  Nd₂ (limᵢ ℓ f) s t e ps p l with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | c1   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)

  Nd-Lt : ∀ {s t} → P s → P t → cmpᵀ s t ≡ lt → Nd (L s) (L t)
  Nd-Lt {s} {t} ps p l = Nd₂ (S t) s t refl ps p l
```

**范数从树读出.** `sz≤wk` 对树递归, 每步只用 `sz-step` (极限) 或 `sz-pred` (后继). 不用标准形, 不用单调.

```agda
  sz≤wk′ : ∀ x t → x ≡ S t → P t → sz t ≤ wk (toLvS x)
  sz≤wk′ zero t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | _ = subst (λ z → sz z ≤ 0) (sym (cof0 t ce)) z≤n
  ... | c1   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  sz≤wk′ (suc a) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | c1   | c = subst (_≤ suc (wk (toLvS a))) (sym (sz-pred t ce))
                         (s≤s (sz≤wk′ a (pred t) (suc-inj (trans e c)) (p-pr p ce)))
  sz≤wk′ (lim f) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | c1   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | cω   | c = ≤-trans (sz-step t ce)
                     (s≤s (sz≤wk′ (f 1) (fsn t 1) (cong-app (lim-inj (trans e c)) 1) (p-fs p ce 1)))
  sz≤wk′ (limᵢ ℓ f) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | c with () ← trans e c
  ... | c1   | c with () ← trans e c
  ... | cω   | c with () ← trans e c
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)

  sz≤wk : ∀ {t} → P t → sz t ≤ wk (L t)
  sz≤wk {t} p = sz≤wk′ (S t) t refl p
```

**族.** `F` 是 `L` 在 `P` 上的像. 这一步把记号的事实变成 `Fam` 的五条; 判决本身不知道 `F`.

```agda
  F : Lv → Set
  F ℓ = Σ T λ s → P s × (ℓ ≡ L s)

  stepAt : ∀ t → Q t → ∀ {c} → cof t ≡ c → StepF t c (fsn t) (fsT t)
  stepAt t q refl = stepT t q

  inv-suc : ∀ {a s} → P s → suc a ≡ L s → (cof s ≡ c1) × (a ≡ L (pred s))
  inv-suc {a} {s} p e with cof s in ce | stepT s (p⊂q p)
  ... | c0   | c with () ← trans e (cong toLvS c)
  ... | cω   | c with () ← trans e (cong toLvS c)
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | c1   | c with trans e (cong toLvS c)
  ...   | refl = refl , refl

  inv-lim : ∀ {h s} → P s → lim h ≡ L s → (cof s ≡ cω) × (∀ n → h n ≡ L (fsn s n))
  inv-lim {h} {s} p e with cof s in ce | stepT s (p⊂q p)
  ... | c0   | c with () ← trans e (cong toLvS c)
  ... | c1   | c with () ← trans e (cong toLvS c)
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)
  ... | cω   | c with trans e (cong toLvS c)
  ...   | refl = refl , (λ _ → refl)

  inv-no : ∀ {k g s} → P s → limᴼ k g ≡ L s → ⊥
  inv-no {s = s} p e with cof s in ce | stepT s (p⊂q p)
  ... | c0   | c with () ← trans e (cong toLvS c)
  ... | c1   | c with () ← trans e (cong toLvS c)
  ... | cω   | c with () ← trans e (cong toLvS c)
  ... | cΩ ν | _ = ⊥-elim (p-nc p ce)

  f-suc : ∀ {a} → F (suc a) → F a
  f-suc (s , p , e) with inv-suc p e
  ... | ce , q = pred s , p-pr p ce , q

  f-lim : ∀ {h} → F (lim h) → ∀ n → F (h n)
  f-lim (s , p , e) n with inv-lim p e
  ... | ce , q = fsn s n , p-fs p ce n , q n

  f-step : ∀ {h} → F (lim h) → ∀ n → Nd (h n) (h (suc n))
  f-step (s , p , e) n with inv-lim p e
  ... | ce , q = subst₂ Nd (sym (q n)) (sym (q (suc n)))
                   (Nd-Lt (p-fs p ce n) (p-fs p ce (suc n)) (mono p ce n))

  irrF : ∀ x → F x → Nd x x → ⊥
  irrF zero fx (() , _)
  irrF (suc a) fx n = irrF a (f-suc fx) (Nd-suc n)
  irrF (lim h) fx ((m , s) , e) with f-step fx m
  ... | r , e′ = irrF (h m) (f-lim fx m) (Nd-trans (s , e) ((suc m , r) , e′))
  irrF (limᴼ _ _) (s , p , e) _ = inv-no p e

  chain : ∀ {h j m n} → F (lim h) → m ≤′ n → Nd j (h m) → Nd j (h n)
  chain fh ≤′-refl     q = q
  chain fh (≤′-step p) q = Nd-trans (f-step fh _) (chain fh p q)

  f-mod : ∀ {j h} → F j → F (lim h) → Nd j (lim h) → Nd j (h (suc (wk j)))
  f-mod {h = h} (s′ , ps , refl) fh@(s , p , e) n with inv-lim p e | cmpᵀ s′ s in c
  ... | ce , q | lt with cofb ps p ce c
  ...   | k , k≤ , r = chain fh (≤⇒≤′ (≤-trans k≤ (s≤s (sz≤wk ps))))
                         (subst (Nd (L s′)) (sym (q k)) (Nd-Lt ps (p-fs p ce k) r))
  f-mod {h = h} (s′ , ps , refl) fh@(s , p , e) n | ce , q | eq with cmp-eq s′ s c
  ...   | refl = ⊥-elim (irrF (lim h) fh (subst (λ z → Nd z (lim h)) (sym e) n))
  f-mod {h = h} (s′ , ps , refl) fh@(s , p , e) n | ce , q | gt =
    ⊥-elim (irrF (L s′) (s′ , ps , refl) (Nd-trans (Nd-Lt p ps (gt→lt c)) (subst (Nd (L s′)) e n)))

  famF : Fam F
  famF = record
    { f-suc = f-suc ; f-lim = f-lim ; f-no = λ { (s , p , e) → inv-no p e }
    ; f-step = f-step ; f-mod = f-mod }

  open OnFam famF
  open CastR fe

  fF : ∀ {t} → P t → F (L t)
  fF {t} p = t , p , refl

  gv-lt : ∀ {j i} {V : Verdict j i} → PenOK V → GV lt V
  gv-lt record { rr = r ; bb = b ; vq = refl ; lb = l ; sb = q } = l , q

  agr′ : ∀ u v → P u → P v → GV (cmpᵀ u v) (Dᵐ (L u) (L v))
  agr′ u v pu pv with cmpᵀ u v in ce
  ... | lt = gv-lt (Dᵐ-lt (fF pu) (fF pv) (Nd-Lt pu pv ce))
  ... | gt = subst (GV gt) (sym (Dᵐ-gt (fF pu) (fF pv) (Nd-Lt pv pu (gt→lt ce)))) tt
  ... | eq with cmp-eq u v ce
  ...   | refl = subst (GV eq) (sym (Dᵐ-eq (L u) (fF pu))) tt
```
