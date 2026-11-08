# 同形旧层的树形反射与有界相等

验收专用。第一条只把已给索引同形反射为Same，不判定索引。
第二条推出字面树相等时必须携同一合法W及两条位置证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueIndexShape where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-sym)
import OCF.Lean.GeneralOmegaCountableRegularCompareIf as S
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (H; sim-measure; sim-to-position; position-strict)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape)
import OCF.Align.Level as L

index-shape : ∀ a b la lb → height a la L.≅ᴵ height b lb → Same a b
index-shape hz hz la lb L.z≅ = zz
index-shape hz (hs b) la lb ()
index-shape hz (hl g) la lb ()
index-shape (hs a) hz la lb ()
index-shape (hs a) (hs b) la lb (L.s≅ p) = ss (index-shape a b la lb p)
index-shape (hs a) (hl g) la lb ()
index-shape (hl f) hz la lb ()
index-shape (hl f) (hs b) la lb ()
index-shape (hl f) (hl g) la lb (L.l≅ p) = ll
  (λ n → index-shape (f n) (g n) (proj₂ la n) (proj₂ lb n) (p n))
index-shape (hΩ () f) b la lb p
index-shape a (hΩ () g) la lb p

shape-sim : ∀ {a b : Cd} → Same a b → S.Sim hz a b
shape-sim zz = S.sz
shape-sim (ss p) = S.ss (shape-sim p)
shape-sim (ll p) = S.sl (λ n → shape-sim (p n))
shape-sim (oo {κ = ()} p)

bounded-shape-equal : ∀ {W a b : Cd} → LgB W → a ⊲ W → b ⊲ W → Same a b → a ≡ b
bounded-shape-equal {a = a} lw pa pb p with position-strict (sim-to-position lw pa pb (shape-sim p))
... | inj₁ e = e
... | inj₂ strict = ⊥-elim (¬s≤ᵛ (H a)
  (≤-trans strict (sim-measure (shape-sim (same-sym p)))))

bounded-index-equal : ∀ {W a b : Cd} (lw : LgB W) (pa : a ⊲ W) (pb : b ⊲ W)
  (la : LgB a) (lb : LgB b) → height a la L.≅ᴵ height b lb → a ≡ b
bounded-index-equal {a = a} {b = b} lw pa pb la lb e =
  bounded-shape-equal lw pa pb (index-shape a b la lb e)

one-instance : _≡_ {A = Cd} (hs hz) (hs hz)
one-instance = bounded-index-equal tt hself hself tt tt (L.s≅ L.z≅)
omega-instance : omega ≡ omega
omega-instance = bounded-index-equal omega-legal hself hself omega-legal omega-legal
  (height-shape (same-refl omega) omega-legal omega-legal)
```

严格方向由形状测量H排除；未要求输入Reg，也未要求任意Cd自反值
关系反演。两项实例分别填合法非零及非有限公共界。没有证明路径
证据相等，没有函数外延，也没有裸Cd上的判等或全局UIP。
