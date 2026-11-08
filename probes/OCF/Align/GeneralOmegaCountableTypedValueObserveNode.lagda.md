# 原分类器三个内部节点分支的封闭

只消费原cl及cmpB实际结果；旧比较的代表元保留到keep助手，same
与above的整个真实反馈交给已证耦合。最终Nodes由原分类实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveNode where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe; point-node)
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (measure-position)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.Fold1If using (s≤s; ≤l)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass
open import OCF.Align.GeneralOmegaCountableTypedDispatch
open import OCF.Align.GeneralOmegaCountableTypedKeepNode using (keep-read)
open import OCF.Align.GeneralOmegaCountableTypedCollapse using (same-at-rank; above-at-rank)
open import OCF.Align.GeneralOmegaCountableTypedValueObserveRecursor
open import OCF.Align.GeneralOmegaCountableTypedValueObserveRootNode using (node-root)
import OCF.Align.Level as L

source-lower : ∀ {B lB κ i pi encode} → ClassLink B lB κ (C.nw i pi encode) →
  ∀ {t} lt → hs i ⊲ t → rank B lB κ L.≺ᴵ height t lt
source-lower (linked eq feed) lt p = subst (λ j → j L.≺ᴵ height _ lt)
  (sym eq) (keep-order _ lt p)

module Pick (B : Cd) (lB : LgB B) {ℓ} (σ : L.Simᴵ ℓ (height B lB))
  (κ : K (F B)) (q : rank B lB κ L.<ᴵ ℓ)
  (f : L.U _ (L.<→◃ q) → L.Ordᶜ ℓ) (g : E (F B) κ → HB (F B))
  (sa : L.limᵢ q f L.≅ L.limᵢ q f)
  (sub : ∀ x e → Coord B lB κ x e → Read B lB σ (f (L.into (L.<→◃ q) x)) (g e))
  (ih : ∀ x e → Coord B lB κ x e → Result B lB σ (f (L.into (L.<→◃ q) x)) (g e)) where
  kept : ∀ t (ht : hs t ⊲ B) {i pi encode} (cl : ClassLink B lB κ (C.nw i pi encode))
    (p : hs i ⊲ t) →
    Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
      (L.ψ (index-bound lB ht) σ (L.limᵢ q f))
      (hΩ (C.along p) (λ e → point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) (g (encode (C.frA p e)))))
  kept t ht cl p with L.<ᴵ-dec (σ q) (index-bound lB ht) |
    lower-consistent (source-lower cl (lgB⊲ ht tt lB) p) (L.<ᴵ-dec (σ q) (index-bound lB ht))
  ... | inj₁ (L.via e r) | lower .(L.via e r) = keep-read B lB t ht σ κ q {f = f} {g = g} cl p sa
    (λ x e c → Result.internal (ih x e c) t ht) e r

  pick-read : ∀ t (ht : hs t ⊲ B) {i pi encode} (cl : ClassLink B lB κ (C.nw i pi encode))
    (choice : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
    Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
      (L.ψ (index-bound lB ht) σ (L.limᵢ q f))
      (point-node (⊲ᴮ-tr (hsuc hself) ht) (C.pick S⊥ encode pi choice)
        (λ r pr e → point-observe B lB r pr (g e)))
  pick-read t ht cl (inj₂ p) = kept t ht cl p
  pick-read .(hs _) ht cl (inj₁ hself) = kept _ ht cl hself
  pick-read t ht (linked {i = .t} {pi} {encode} eq feed) (inj₁ (hsuc hself)) =
    same-at-rank B lB t pi ht _ eq σ q f g encode
      (λ x e c → sub _ _ (feed c)) (λ x e c → ih _ _ (feed c))
  pick-read t ht (linked {i} {pi} {encode} eq feed) (inj₁ (hsuc (hsuc p))) =
    above-at-rank B lB t ht i pi (hsuc p) (s≤s (position-value (measure-position p))) _ eq σ q f g encode
      (λ x e c → sub _ _ (feed c)) (λ x e c → ih _ _ (feed c))
  pick-read t ht (linked {i} {pi} {encode} eq feed) (inj₁ (hsuc (hlim n p))) =
    above-at-rank B lB t ht i pi (hlim n p) (s≤s (≤l n (position-value (measure-position p)))) _ eq σ q f g encode
      (λ x e c → sub _ _ (feed c)) (λ x e c → ih _ _ (feed c))
  pick-read t ht cl (inj₁ (hsuc (hLim {κ = ()} e p)))

  link-read : ∀ t (ht : hs t ⊲ B) {v} → ClassLink B lB κ v →
    Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
      (L.ψ (index-bound lB ht) σ (L.limᵢ q f))
      (point-node (⊲ᴮ-tr (hsuc hself) ht) (C.dcl (⊲ᴮ-tr (hsuc hself) ht) lB v)
        (λ r pr e → point-observe B lB r pr (g e)))
  link-read t ht cl@(linked {pi = pi} eq feed) = pick-read t ht cl
    (cmpB pi (⊲ᴮ-tr (hsuc hself) ht) tt lB)

instance-nodes : Nodes
Result.internal (Nodes.node instance-nodes B lB σ κ q {f} {g} align sa sub ih) t ht =
  Pick.link-read B lB σ κ q f g sa sub ih t ht (class-link B lB κ)
Result.root (Nodes.node instance-nodes B lB σ κ q {f} {g} align sa sub ih) pt =
  node-root B lB σ κ q {f = f} {g = g} sub ih pt
```
