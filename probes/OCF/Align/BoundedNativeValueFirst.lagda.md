# 原可数输出的首个非平凡外层采样

这里只验收原始 raw 树值；尚未证明该闭项合法。先核对实际外轨道：
根分支在0处为1，但末段折叠把1变为ω，所以首个反馈坐标不是1。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeValueFirst where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1If using (Sm; sz; ss; sl; Sm-mul; Sm-⊞; module Det)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; mul-≤)
open import OCF.Align.FrozenAbsorbNegUpper using (P; mono; infl)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path; Adm₀; sh₀; adm-sh; nxt₀; lg-nx; nx-up)
import OCF.Align.BoundedNativeFoldRun as R
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Old
open import OCF.Lean.TowerCollapseIf using (module Ops)

one : Cd
one = hs hz
ω : Cd
ω = hl (mul one)
module Outer = T.Orbit hz T.native-branch

first-coordinate : Outer.C.ce 1 ≡ hz ⊞ ω
first-coordinate = refl

-- 原实际外层第1输出是一个ℕ极限；其首项为原θ1的折叠。
feedback : Cd
feedback = Outer.C.ce 1
ad : Adm₀ hz (sh₀ hz feedback)
ad = adm-sh {B = hz} feedback tt
B : Cd
B = nxt₀ hz (sh₀ hz feedback) ad
lB : LgB B
lB = lg-nx ad tt
pt : hz ⊲ B
pt = ⊲ᴮ-tr hself (nx-up ad)
component : HB (Native hz)
component = R.fold B lB hz pt
  (N.θ one) (N.θ-path one B (hsuc (hlim 0 hself)))

private
  branch : HB (Native hz) → Cd → HB (Native hz)
  branch (hΩ (inj₂ _) g) = g
  branch _ = λ _ → hz
G : Cd → HB (Native hz)
G = branch component
component-shape : component ≡ hΩ (inj₂ tt) G
component-shape = refl

first-lower : T.fold feedback component ≤ᵛ Outer.C.oo 1
first-lower = ≤l 0 (≤-refl _)
```

以下证明该真实分量的所有原始 d 分支，不把 d 换成常数样本。

```agda
sm-refl : ∀ (c : Cd) → Sm c c
sm-refl hz = sz
sm-refl (hs c) = ss (sm-refl c)
sm-refl (hl f) = sl (λ n → sm-refl (f n))
sm-value : ∀ {a b : Cd} → Sm a b → a ≤ᵛ b
sm-value sz = z≤
sm-value (ss p) = s≤s (sm-value p)
sm-value (sl p) = l≤ (λ n → ≤l n (sm-value (p n)))
sm-sym : ∀ {S R} {a : HB S} {b : HB R} → Sm a b → Sm b a
sm-sym sz = sz
sm-sym (ss p) = ss (sm-sym p)
sm-sym (sl p) = sl (λ n → sm-sym (p n))

partial-pure : ∀ {S R} {a : HB S} {b : HB R} → Sm a b → ∀ n →
  Sm (Ops.partial S (λ _ → a) n) (mul b n)
partial-pure p zero = p
partial-pure p (suc n) = Sm-⊞ (partial-pure p n) p

fold-pure : ∀ B lB t pt {h : HB Source} {c : Cd} → Sm h c → (p : Path B h) →
  Sm (R.fold B lB t pt h p) (P one c)
fold-pure B lB t pt sz p = ss sz
fold-pure B lB t pt (ss s) p = sl (partial-pure (fold-pure B lB t pt s p))
fold-pure B lB t pt (sl s) p = sl (λ n → fold-pure B lB t pt (s n) (p n))

source-pure : ∀ (d : Cd) → Sm {Source} {S⊥} (hz ⊞ ι (inj₂ hz) (up d)) d
source-pure hz = sz
source-pure (hs d) = ss (source-pure d)
source-pure (hl f) = sl (λ n → source-pure (f n))

G-pure : ∀ d → Sm (G d) (P one d)
G-pure d = fold-pure B lB hz pt (source-pure d) _

terminal-pure : ∀ b {h : HB (Native hz)} {c : Cd} → Sm h c →
  Sm (T.fold b h) (P one c)
terminal-pure b = Det.Sm-F (T.fold b) refl (λ _ → refl) (λ _ → refl)
  (P one) refl (λ _ → refl) (λ _ → refl)

up-pure : ∀ d → Sm (up {S⊥} d) d
up-pure hz = sz
up-pure (hs d) = ss (up-pure d)
up-pure (hl f) = sl (λ n → up-pure (f n))

branch-lower : ∀ b b′ {x y} → x ≤ᵛ y → T.fold b (up x) ≤ᵛ T.fold b′ (G y)
branch-lower b b′ {x} {y} xy = ≤-trans (sm-value (terminal-pure b (up-pure x)))
  (≤-trans (mono (≤-refl one) (≤-trans xy (infl one (≤-refl one) y)))
    (sm-value (sm-sym (terminal-pure b′ (G-pure y)))))

module OldOrbit = T.Orbit hz (up {S⊥})
module NewOrbit = T.Orbit feedback G

coordinates : ∀ n → OldOrbit.C.ce n ≤ᵛ NewOrbit.C.ce n
outputs : ∀ n → OldOrbit.C.oo n ≤ᵛ NewOrbit.C.oo n
coordinates zero = z≤
coordinates (suc n) = add-mono (coordinates n) (outputs n)
outputs n = branch-lower _ _ (coordinates n)
sums : ∀ n → OldOrbit.C.oO n ≤ᵛ NewOrbit.C.oO n
sums zero = outputs zero
sums (suc n) = add-mono (sums n) (outputs (suc n))

old-below-component : Old.TΩ1 ≤ᵛ T.fold feedback component
old-below-component = l≤ (λ n → ≤l n (sums n))

right≤ : ∀ (a b : Cd) → b ≤ᵛ a ⊞ b
right≤ a hz = z≤
right≤ a (hs b) = s≤s (right≤ a b)
right≤ a (hl f) = l≤ (λ n → ≤l n (right≤ a (f n)))

old-below-output : Old.TΩ1 ≤ᵛ N.countable-output
old-below-output = ≤-trans old-below-component
  (≤-trans first-lower (≤l 1 (right≤ (Outer.C.oo 0) (Outer.C.oo 1))))
```

old-below-output 是原 countable-output 的实际值下界。证明比较旧地板
与真实采样分量的所有内层坐标和部分和，再嵌入原外层第1项。它不使用
任意 Ω 输入的值单调，也未改闭项。旧 TΩ1 本身的记号读法未在这里验收，
所以本篇不把下界擅自命名为 ε₀；当前候选合法性也仍需另证。
