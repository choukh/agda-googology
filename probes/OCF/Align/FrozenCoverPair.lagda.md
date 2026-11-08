# 双 Ω 反例经显式种子变换后的实际值覆盖

直接比较共享模型中的 pair 与 D pair，所有回灌项同时归纳。
D pair 在这里仅为验收对象；不声称其合法，更不把它当现有 Tω 的分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenCoverPair where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenSupportExt using (Ext; ext-add; up-ext; up-same; generated-ext)
open import OCF.Align.FrozenOutputIf using (changing; frozen; update; initial; plus)
import OCF.Align.FrozenOutputIf as If
open import OCF.Align.FrozenCoverIf using (D)
import OCF.Align.FrozenCoverIf as Cover
import OCF.Align.FrozenCoverSeedMono as SM
open import OCF.Align.FrozenAbsorbNegUpper using (P; run-prefix)
import OCF.Align.FrozenOutputModel as M
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Original

I : HB (step S⊥)
I = top (hs hz)
pair : HB (step S⊥)
pair = I ⊞ I

same-D : ∀ {a b} → Same a b → Same (D a) (D b)
same-D zz = zz
same-D (ss p) = ss (same-D p)
same-D (ll p) = ll (λ n → same-D (p n))
same-D (oo {κ = inj₁ ()} p)
same-D (oo {κ = inj₂ tt} p) = oo (λ c → same-add (same-refl (up c)) (same-D (p c)))

ext-D : ∀ c → Ext c → Ext (D c)
ext-D hz e = tt
ext-D (hs c) e = ext-D c e
ext-D (hl f) e = λ n → ext-D (f n) (e n)
ext-D (hΩ (inj₁ ()) g) e
ext-D (hΩ (inj₂ tt) g) (r , e) =
  (λ p → same-add (up-same p) (same-D (r p))) ,
  (λ c → ext-add (up c) (D (g c)) (up-ext c) (ext-D (g c) (e c)))

zero-add : ∀ {U} (c : HB U) → Same (hz ⊞ c) c
zero-add hz = zz
zero-add (hs c) = ss (zero-add c)
zero-add (hl f) = ll (λ n → zero-add (f n))
zero-add (hΩ κ g) = oo (λ c → zero-add (g c))

module Pair (A : Cd) where
  open If.Model A
  module S = SM.SeedMono A

  module Old = F.Col _⊞_ _⊞_ hz hz (update changing)
    (λ w e → run changing w (I ⊞ up e))
    (λ w e → run changing w (I ⊞ up e))
  module New = F.Col _⊞_ _⊞_ hz hz (update frozen)
    (λ w e → run frozen w (up e ⊞ D (I ⊞ up e)))
    (λ w e → run frozen w (up e ⊞ D (I ⊞ up e)))

  old-world : ∀ n → Old.cw n ≡ Old.ce n
  old-world zero = refl
  old-world (suc n) = refl
  new-world : ∀ n → New.cw n ≡ hz
  new-world zero = refl
  new-world (suc n) = refl

  tail-normal : ∀ x c → Same (run frozen hz (up x ⊞ D (I ⊞ up c))) (P (S.C x) c)
  tail-normal x hz = same-refl _
  tail-normal x (hs c) = ll (same-mul (tail-normal x c))
  tail-normal x (hl f) = ll (λ n → tail-normal x (f n))

  old-output : ∀ n → Same (Old.oo n) (S.old-step (Old.ce n))
  old-output n rewrite old-world n = run-prefix A changing (Old.ce n) I (Old.ce n)
  new-output : ∀ n → Same (New.oo n) (S.new-step (New.ce n))
  new-output n rewrite new-world n = tail-normal (New.ce n) (New.ce n)

  coordinates : ∀ n → Old.ce n ≤ᵛ New.ce n
  outputs : ∀ n → Old.oo n ≤ᵛ New.oo n
  coordinates zero = z≤
  coordinates (suc n) = add-mono (coordinates n) (outputs n)
  outputs n = ≤-trans (same-value (old-output n))
    (≤-trans (S.step-cover (coordinates n)) (same-value (same-sym (new-output n))))
  sums : ∀ n → Old.oO n ≤ᵛ New.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))

  pair-cover : run changing hz pair ≤ᵛ run frozen hz (D pair)
  pair-cover = l≤ (λ n → ≤l n (sums n))

  -- 接回冻结接口 Covers 的字面零前缀，不偷用函数外延消去它。
  interface-pair-cover : Cover.Candidate.Covers A hz pair
  interface-pair-cover = ≤-trans pair-cover
    (same-value (M.Congruence.run-same A frozen (D pair)
      (ext-D pair (generated-ext (plus initial initial)))
      (same-sym (zero-add (D pair))) (same-refl hz)))

module Actual = Pair Original.TΩ1
```

`Actual.interface-pair-cover` 修复了之前真实 Generated 反例对象的值覆盖：
原 pair 不被同点冻结 pair 覆盖，但被显式变换后的冻结 D pair 覆盖。
本篇不证明 D 保持合法性，也不证明 D pair 被实际冻结 ce 族覆盖；
因此没有据此获得合法新闭项或完整第二分量下界。
