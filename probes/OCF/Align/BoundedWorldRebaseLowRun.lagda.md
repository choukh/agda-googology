# 原双槽全部低输出的共尾覆盖

按输入的有向关系推导递归。底Ω逐项比较动态底槽；中Ω使用原中槽
轨道的一步延迟与补偿和预算，不把terminal当作加法同态。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseLowRun where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; trans; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; mul-≤)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (value-zero; right-rel; prefix-rel)
open import OCF.Align.BoundedWorldSeedIf
import OCF.Align.BoundedWorldSeedClosure as S
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; low; mid)
open import OCF.Lean.RebaseMiddleIf using (eval)
open import OCF.Lean.RebaseMiddleRun using (native-seed; read-positive; one-seed; chain-seed)
open import OCF.Align.BoundedWorldRebaseIf using (enc)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
open import OCF.Align.BoundedWorldRebaseLowIf
import OCF.Lean.Fold1Fold as F
import OCF.Lean.RebaseMiddleOrbit as Orbit
import OCF.Lean.RebaseOutputChain as Chain
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedCompletionTerminalValueIf as VI
import OCF.Align.BoundedCompletionTerminalValueRun as TV
import OCF.Align.BoundedCompletionOutputRepeat as Repeat
import OCF.Align.BoundedCompletionOutputPadding as P

lower : ∀ {a b u v x y} → Seed0 u → Seed0 v → Seed1 a → Seed1 b →
  Value (hs hz) a b → Value hz u v → x ≤ᵛ y →
  low x u a ≤ᵛ T.fold y (eval v b)
lower su sv sa sb vz uv xy = terminal-positive _ _
lower {b = hs b} {v = v} {y = y} su sv sa sb (vs p) uv xy = ≤-trans
  (l≤ (λ n → ≤l n (mul-≤ (lower su sv (proj₂ sa) (proj₂ sb) p uv xy) n)))
  (R.lower y)
  where
  module R = Repeat.Repeat (eval v b)
    (value-zero (S.self0 (native-seed v b sv (proj₂ sb))))
    (value-zero (read-positive (enc v b)))
lower su sv sa sb (vr p) uv xy = ≤l 0 (lower su sv sa (proj₂ sb) p uv xy)
lower su sv sa sb (vl p) uv xy = l≤ (λ n → lower su sv (proj₂ sa n) sb (p n) uv xy)
lower su sv sa sb (vli n p) uv xy = ≤l n (lower su sv sa (proj₂ sb n) p uv xy)
lower su sv sa sb (vo {κ = inj₁ (inj₁ ())} p) uv xy
lower {u = u} {v} {x} {y} su sv sa sb (vo {κ = inj₁ (inj₂ _)} {f} {g} p) uv xy =
  l≤ (λ n → ≤l n (sums n))
  where
  module L = F.Col _⊞_ _⊞_ x x (λ _ e → e)
    (λ z e → low z u (f e)) (λ z e → low z u (f e))
  module R = T.Orbit y (λ e → eval v (g e))
  current : ∀ n → L.cw n ≡ L.ce n
  current zero = refl
  current (suc n) = refl
  coordinates : ∀ n → L.ce n ≤ᵛ R.C.ce n
  outputs : ∀ n → L.oo n ≤ᵛ R.C.oo n
  coordinates zero = xy
  coordinates (suc n) = add-mono (coordinates n) (outputs n)
  outputs n rewrite current n | R.current n = lower su sv
    (proj₂ (proj₂ sa) (L.ce n)) (proj₂ (proj₂ sb) (R.C.ce n))
    (p _ _ (coordinates n)) uv (coordinates n)
  sums : ∀ n → L.oO n ≤ᵛ R.C.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
lower {u = u} {v} {x} {y} su sv sa sb (vo {κ = inj₂ _} {f} {g} p) uv xy =
  l≤ (λ n → ≤l (Chain.budget n) (≤-trans (sums n)
    (TV.eval (value-zero (O.Cover.padded-partial n)) (≤-refl y))))
  where
  module O = Orbit.Compare u v su sv f g
    (proj₂ (proj₂ sa)) (proj₂ (proj₂ sb)) (proj₁ (proj₂ sb)) p uv
  module L = F.Col _⊞_ _⊞_ u u (λ _ e → e)
    (λ b e → mid b (f e)) (λ b e → low x b (f e))
  samples = O.Cover.samples
  selves : ∀ n → VI.VRel (samples n) (samples n)
  selves n = value-zero (O.Cover.output-selves (suc n))
  ce-equal : ∀ n → L.ce n ≡ O.Original.ce n
  cw-equal : ∀ n → L.cw n ≡ O.Original.cw n
  ce-equal zero = refl
  ce-equal (suc n) = cong₂ (λ e w → e ⊞ mid w (f e)) (ce-equal n) (cw-equal n)
  cw-equal zero = refl
  cw-equal (suc n) = ce-equal (suc n)
  outputs : ∀ n → L.oo n ≤ᵛ T.fold y (samples n)
  outputs n = subst (λ z → z ≤ᵛ T.fold y (samples n))
    (sym (cong₂ (λ w e → low x w (f e)) (trans (cw-equal n) (O.current n)) (ce-equal n)))
    (lower
    (O.old-coordinates n) (S.add0 sv (chain-seed O.H O.keeps (suc n)))
    (proj₂ (proj₂ sa) (O.Original.ce n) (O.old-coordinates n))
    (proj₂ (proj₂ sb) (v ⊞ chain O.H (suc n)) (S.add0 sv (chain-seed O.H O.keeps (suc n))))
    (p _ _ (right-rel v (O.coordinates n))) (right-rel v (O.coordinates n)) xy)
  sums : ∀ n → L.oO n ≤ᵛ T.fold y (P.pad samples n)
  sums zero = outputs zero
  sums (suc n) = ≤-trans (add-mono (sums n) (outputs (suc n)))
    (P.padded-add (P.pad-self samples selves n) (selves (suc n)) (≤-refl y) (≤-refl y))
lower su sv sa sb (vor {κ = inj₁ (inj₁ ())} p) uv xy
lower {y = y} su sv sa sb (vor {κ = inj₁ (inj₂ _)} p) uv xy =
  ≤l 0 (lower su sv sa (proj₂ (proj₂ sb) y) (p y) uv xy)
lower {v = v} su sv sa sb (vor {κ = inj₂ _} p) uv xy = ≤l 0
  (lower su cap sa (proj₂ (proj₂ sb) (v ⊞ hs hz) cap)
    (p (v ⊞ hs hz)) (prefix-rel uv (hs hz)) xy)
  where cap = S.add0 sv one-seed

instance-lower : LowerComparison
instance-lower = record { lower = lower }
```

结论比较原low与实际Native运行后末段折叠。它尚不表示后者被旧C
覆盖；新的合法闭项及其整族输出需要另外连接。
