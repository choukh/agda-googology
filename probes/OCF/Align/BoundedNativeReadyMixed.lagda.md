# 原θ混合树的相干世界证书

原θ内部仅有分量标签，所有分量世界可直接同时取seed c v，无须判等
不可数分量。枝仍返回整个Source。指标根另由末段Ready准则处理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadyMixed where
open import Data.Nat using (suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls; FXL)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; cxI)
import OCF.Lean.LHRecLeg as Leg
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeZeroWorld using (seed; seed-legal)
open import OCF.Align.BoundedNativeReadyGood using (Good; Coord; floor-good)
import OCF.Align.BoundedNativeFloor as N

shared : Wd (Native hz) → Wd Source
shared v (inj₁ _) = v
shared v (inj₂ c) = seed c v
shared-legal : ∀ {v} → LgW (Native hz) v → LgW Source (shared v)
shared-legal lv (inj₁ _) = lv
shared-legal lv (inj₂ c) = seed-legal c lv

Mixed : Cd → HB Source → Set
Mixed B hz = ⊤
Mixed B (hs a) = Mixed B a
Mixed B (hl f) =
  (∀ {v} → LgW (Native hz) v → ∀ n → f n ⊲[ shared v ] f (suc n)) ×
  (∀ n → Mixed B (f n))
Mixed B (hΩ (inj₁ _ , κ) g) = ⊥
Mixed B (hΩ (inj₂ c , κ) g) =
  (c ⊲ B) ×
  (∀ {v e d} → LgW (Native hz) v → Bd (Native c) κ e (seed c v) →
    Bd (Native c) κ d (seed c v) → Pr (Native c) κ (seed c v) e d →
    g e ⊲[ shared v ] g d) ×
  (∀ e → Coord c κ e → Mixed B (g e))

add-mixed : ∀ B a b → Mixed B a → Mixed B b → Mixed B (a ⊞ b)
add-mixed B a hz la lb = la
add-mixed B a (hs b) la lb = add-mixed B a b la lb
add-mixed B a (hl f) la (st , l) =
  (λ lv n → ⊞-⊲ a (st lv n)) , (λ n → add-mixed B a (f n) la (l n))
add-mixed B a (hΩ (inj₁ _ , κ) g) la ()
add-mixed B a (hΩ (inj₂ c , κ) g) la (pc , mo , l) =
  pc , (λ lv e d p → ⊞-⊲ a (mo lv e d p)) , (λ e le → add-mixed B a (g e) la (l e le))

put : ∀ c → HB (Native c) → HB Source
put c = ι {I = ⊤ ⊎ Cd} {F = FXL lz (λ d → ls lz ⊕L upL lz d)} (inj₂ c)

put-position : ∀ c {a b : HB (Native c)} {v : Wd (Native hz)} → a ⊲[ seed c v ] b →
  put c a ⊲[ shared v ] put c b
put-position c hself = hself
put-position c (hsuc p) = hsuc (put-position c p)
put-position c (hlim n p) = hlim n (put-position c p)
put-position c (hLim b p) = hLim b (put-position c p)

put-mixed : ∀ {B} c → c ⊲ B → ∀ a → Good c a → Mixed B (put c a)
put-mixed c pc hz l = tt
put-mixed c pc (hs a) l = put-mixed c pc a l
put-mixed c pc (hl f) (st , l) =
  (λ lv n → put-position c (st lv n)) , (λ n → put-mixed c pc (f n) (l n))
put-mixed c pc (hΩ κ g) (mo , l) =
  pc , (λ lv e d p → put-position c (mo lv e d p)) ,
  (λ e le → put-mixed c pc (g e) (l e le))

theta-mixed : ∀ a B → a ⊲ B → LgB a → Mixed B (N.θ a)
theta-mixed hz B p l = tt
theta-mixed (hs a) B p l = add-mixed B _ _
  (theta-mixed a B (⊲ᴮ-tr (hsuc hself) p) l)
  (put-mixed a (⊲ᴮ-tr (hsuc hself) p) (flL (ls lz ⊕L upL lz a)) (floor-good a))
theta-mixed (hl f) B p (st , l) =
  (λ lv n → Leg.New.θ-⊲ (cxI lz (λ c → ls lz ⊕L upL lz c)) _ (st n)) ,
  (λ n → theta-mixed (f n) B (⊲ᴮ-tr (hlim n hself) p) (l n))
```

theta-mixed直接给原NativeFloor.θ的证书：没有复制树、fold或路径函数。
实际根分支使用的sh结果有原LgB，故该实例可接固定共同界内的Good
保持归纳；该归纳本身不由本篇宣称完成。
