# 原cl的实际秩与坐标读回

验收专用。每个nw保留其原pi路径、原to和由该路径诱导的合法证。
秩相等与坐标cast显式记录，不把两次合法证明生成的层默认判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedClass where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; rank-legal)
open import OCF.Align.GeneralOmegaCountableTypedIf

cast : ∀ {i j} → i ≡ j → L.Ordᶜ i → L.Ordᶜ j
cast = subst L.Ordᶜ

data ClassLink (B : Cd) (lB : LgB B) (κ : K (F B)) : C.Cl {S⊥} B κ → Set where
  linked : ∀ {i : Cd} {pi : hs i ⊲ B} {encode : HB (F i) → E (F B) κ}
    (rank-equal : rank B lB κ ≡ height i (lgB⊲ pi tt lB)) →
    (∀ {x e} → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
      Coord B lB κ (cast (sym rank-equal) x) (encode e)) →
    ClassLink B lB κ (C.nw i pi encode)

class-link : ∀ B lB κ → ClassLink B lB κ (C.cl B κ)
class-link hz lB ()
class-link (hs B) lB (inj₁ κ) with C.cl B κ | class-link B lB κ
... | C.nw i pi encode | linked eq feed = linked eq feed
class-link (hs B) lB (inj₂ _) = linked refl (λ r → r)
class-link (hl f) lB (n , κ) with C.cl (f n) κ | class-link (f n) (proj₂ lB n) κ
... | C.nw i pi encode | linked eq feed = linked eq feed
class-link (hΩ () f) lB κ

-- 仅沿显式合法证等式运输；并非任意LgB证明无关。
change-legal : ∀ i {li li′ : LgB i} (eq : li ≡ li′) {x e} →
  Read i li (canonical i li) x e →
  Read i li′ (canonical i li′) (cast (cong (height i) eq) x) e
change-legal i refl r = r

RuntimeFeed : ∀ {B lB κ v} → ClassLink B lB κ v → Set
RuntimeFeed {B} {lB} {κ} {C.nw i pi encode} (linked eq feed) =
  ∀ {x e} → Read i (lgB⊲ (⊲ᴮ-tr (hsuc hself) pi) tt lB)
    (canonical i (lgB⊲ (⊲ᴮ-tr (hsuc hself) pi) tt lB)) x e →
  Coord B lB κ
    (cast (sym eq) (cast (cong (height i) (rank-legal pi lB)) x)) (encode e)
runtime-feed : ∀ {B lB κ v} (p : ClassLink B lB κ v) → RuntimeFeed p
runtime-feed {B} {lB} {κ} {C.nw i pi encode} (linked eq feed) r =
  feed (change-legal i (rank-legal pi lB) r)
actual-runtime-feed : ∀ B lB κ → RuntimeFeed (class-link B lB κ)
actual-runtime-feed B lB κ = runtime-feed (class-link B lB κ)
```

class-link对全部普通Cd原kind成立，runtime-feed进一步使用原above
回灌实际采用的rank路径。它未证明typed三分派与native cmp一致；
旧via e若只给≅ᴵ，仍须相应低层运输，不能拿本篇字面eq替代。
