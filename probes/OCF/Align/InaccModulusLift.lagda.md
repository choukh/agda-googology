# 层号判决的范数模: 比较的语法事实与 `bach ⟹ Reg` (验收)

> **验收节.** §1 是 [InaccModulusLift2](InaccModulusLift2.lagda.md) 用到的比较事实. §2–§3 陈述一条**未证明的项上性质**与它的推论: `bach` (`t[n]` 在 `t[n+1]` 的 1-走步上) ⟹ `L t` 落在纯树谓词 `Reg` 里 (`Reg-Lt`). `bach` 不是主定理的前提 (主定理走 `Lift₂`); 它的意义是: 若它成立, 规整类就有不提项的刻画. 只有采样, 见 [InaccModulus](InaccModulus.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulusLift where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst; subst₂)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeBase
open import OCF.Align.InaccStrikeCommute
open import OCF.Align.InaccModulusBase
import OCF.Align.EBO as E
open E using (T; PT; Cof; c0; c1; cω; cΩ; cof; pred; pred-suc; fsn; fsT; sucT; cmpᵀ; cmpᴾ; Cmp; lt; eq; gt; 𝟏) renaming (ψ to ψᵗ)
```

## §1 比较的语法事实

```agda
flipC : Cmp → Cmp
flipC lt = gt
flipC eq = eq
flipC gt = lt

cmp-flip  : ∀ a b → cmpᵀ b a ≡ flipC (cmpᵀ a b)
cmpᴾ-flip : ∀ x y → cmpᴾ y x ≡ flipC (cmpᴾ x y)
cmp-flip [] [] = refl
cmp-flip [] (y ∷ ys) = refl
cmp-flip (x ∷ xs) [] = refl
cmp-flip (x ∷ xs) (y ∷ ys) with cmpᴾ x y | cmpᴾ y x | cmpᴾ-flip x y
... | lt | gt | refl = refl
... | gt | lt | refl = refl
... | eq | eq | refl = cmp-flip xs ys
cmpᴾ-flip (ψᵗ u a) (ψᵗ v b) with cmpᵀ u v | cmpᵀ v u | cmp-flip u v
... | lt | gt | refl = refl
... | gt | lt | refl = refl
... | eq | eq | refl = cmp-flip a b

cmp-eq  : ∀ a b → cmpᵀ a b ≡ eq → a ≡ b
cmpᴾ-eq : ∀ x y → cmpᴾ x y ≡ eq → x ≡ y
cmp-eq [] [] e = refl
cmp-eq (x ∷ xs) (y ∷ ys) e with cmpᴾ x y in q
... | eq = cong₂ _∷_ (cmpᴾ-eq x y q) (cmp-eq xs ys e)
cmpᴾ-eq (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in q
... | eq = cong₂ ψᵗ (cmp-eq u v q) (cmp-eq a b e)

gt→lt : ∀ {a b} → cmpᵀ a b ≡ gt → cmpᵀ b a ≡ lt
gt→lt {a} {b} e = trans (cmp-flip a b) (cong flipC e)

lt→gt : ∀ {a b} → cmpᵀ a b ≡ lt → cmpᵀ b a ≡ gt
lt→gt {a} {b} e = trans (cmp-flip a b) (cong flipC e)

-- s < a+1 ⟹ s ≤ a
below-suc : ∀ s a → cmpᵀ s (sucT a) ≡ lt → (cmpᵀ s a ≡ lt) ⊎ (cmpᵀ s a ≡ eq)
below-suc s a e with cmpᵀ s a in q
... | lt = inj₁ refl
... | eq = inj₂ refl
... | gt = ⊥-elim (bad (cmpᵀ a s) (cmpᵀ (sucT a) s) (gt→lt q) (lt→gt e) (sc a s))
  where
    bad : ∀ p r → p ≡ lt → r ≡ gt → SC p r → ⊥
    bad .lt .gt refl refl ()

lt-nz : ∀ s t → t ≡ [] → cmpᵀ s t ≡ lt → ⊥
lt-nz [] _ refl ()
lt-nz (x ∷ xs) _ refl ()

cof0 : ∀ t → cof t ≡ c0 → t ≡ []
cof0 [] e = refl
cof0 (x ∷ xs) e = ⊥-elim (cof-nz x xs e)
```

## §2 项的 1-走步

```agda
data WT (a : T) : T → Set where
  wt0 : ∀ {b} → cof b ≡ c1 → pred b ≡ a → WT a b
  wts : ∀ {b} → cof b ≡ c1 → WT a (pred b) → WT a b
  wl0 : ∀ {b} → cof b ≡ cω → fsn b 1 ≡ a → WT a b
  wls : ∀ {b} → cof b ≡ cω → WT a (fsn b 1) → WT a b
```

## §3 `bach` 推出 `Reg`

```agda
module Lift (fe : Funext) {Q N : T → Set} (cl : ClQ Q N)
            (agr : ∀ u v → N u → N v → GV (cmpᵀ u v) (Dᵐ (Tr.L Dᵐ u) (Tr.L Dᵐ v)))
            (P : T → Set)
            (p⊂q : ∀ {t} → P t → Q t)
            (p-fs : ∀ {t} → P t → cof t ≡ cω → ∀ n → P (fsn t n))
            (p-pr : ∀ {t} → P t → cof t ≡ c1 → P (pred t))
            (p-nc : ∀ {t ν} → P t → cof t ≡ cΩ ν → ⊥)
            (bach : ∀ {t} → P t → cof t ≡ cω → ∀ n → WT (fsn t n) (fsn t (suc n)))
            where
  open Step Dᵐ
  open Main fe Dᵐ Q N cl agr

  stepAt : ∀ t → Q t → ∀ {c} → cof t ≡ c → StepF t c (fsn t) (fsT t)
  stepAt t q refl = stepT t q

  L-suc : ∀ {t} → P t → cof t ≡ c1 → L t ≡ suc (L (pred t))
  L-suc {t} p e = cong toLvS (stepAt t (p⊂q p) e)

  L-lim : ∀ {t} → P t → cof t ≡ cω → L t ≡ lim (λ n → L (fsn t n))
  L-lim {t} p e = cong toLvS (stepAt t (p⊂q p) e)

  toW : ∀ {a b} → P b → WT a b → W (L a) (L b)
  toW {a} {b} p (wt0 e refl) = subst (W (L (pred b))) (sym (L-suc p e)) ws0
  toW {a} {b} p (wts e w)    = subst (W (L a)) (sym (L-suc p e)) (ws (toW (p-pr p e) w))
  toW {a} {b} p (wl0 e refl) = subst (W (L (fsn b 1))) (sym (L-lim p e)) (wl0 refl)
  toW {a} {b} p (wls e w)    = subst (W (L a)) (sym (L-lim p e)) (wl (toW (p-fs p e 1) w))

  Reg-L : ∀ x t → x ≡ S t → P t → Reg (toLvS x)
  Reg-L zero t e p = tt
  Reg-L (suc a) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | s with () ← trans e s
  ... | c1   | s = Reg-L a (pred t) (suc-inj (trans e s)) (p-pr p ce)
  ... | cω   | s with () ← trans e s
  ... | cΩ ν | s = ⊥-elim (p-nc p ce)
  Reg-L (lim f) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | s with () ← trans e s
  ... | c1   | s with () ← trans e s
  ... | cω   | s = (λ n → subst₂ W (sym (fq n)) (sym (fq (suc n))) (toW (p-fs p ce (suc n)) (bach p ce n))) ,
                   (λ n → Reg-L (f n) (fsn t n) (cong-app (lim-inj (trans e s)) n) (p-fs p ce n))
    where
      fq : ∀ n → toLvS (f n) ≡ L (fsn t n)
      fq n = cong toLvS (cong-app (lim-inj (trans e s)) n)
  ... | cΩ ν | s = ⊥-elim (p-nc p ce)
  Reg-L (limᵢ ℓ f) t e p with cof t in ce | stepT t (p⊂q p)
  ... | c0   | s with () ← trans e s
  ... | c1   | s with () ← trans e s
  ... | cω   | s with () ← trans e s
  ... | cΩ ν | s = ⊥-elim (p-nc p ce)

  Reg-Lt : ∀ {t} → P t → Reg (L t)
  Reg-Lt {t} p = Reg-L (S t) t refl p
```
