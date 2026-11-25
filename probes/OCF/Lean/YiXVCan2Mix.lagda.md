# YiXV YiXVCan2Mix
> 验收文件。编译定理：固定低层尾部的加法保持二层好树与带证据比较。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Mix where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVRef2 as F

σ₀ = A.σ₀
σ₁ = A.σ₁

good₀ : ∀ {X} → Gd X → (y : R.T₀) → Gd (L.add X σ₀ y)
good₀ g L.zero = g
good₀ g (L.suc y) = gs (good₀ g y)
good₀ g (L.lim f) = gl (λ n → good₀ g (f n))
good₀ g (L.limᵢ () f)
good₀ g (L.up () y)

right₀ : ∀ {X X′} → Le X X′ → (y : R.T₀) → Le X (L.add X′ σ₀ y)
right₀ p L.zero = p
right₀ p (L.suc y) = pack (left p) (gs (good₀ (right p) y)) (ws (right₀ p y))
right₀ p (L.lim f) = pack (left p) (gl (λ n → good₀ (right p) (f n))) (lr 0 (right₀ p (f 0)))
right₀ p (L.limᵢ () f)
right₀ p (L.up () y)

ground : ∀ {X X′} {x y : R.T₀} → Le X X′ → x ≼ y → Le (L.add X σ₀ x) (L.add X′ σ₀ y)
ground p z≼ = right₀ p _
ground p (s≼s q) = s≤ (ground p q)
ground p (≼l {a = x} {f = f} n q) =
  pack (good₀ (left p) x) (gl (λ m → good₀ (right p) (f m))) (lr n (ground p q))
ground p (l≼ {f = f} {b = y} h) =
  pack (gl (λ n → good₀ (left p) (f n))) (good₀ (right p) y) (ll (λ n → ground p (h n)))
ground p (≼i {p = ()} x ex q)
ground p (i≼ {p = ()} h)
ground p (≼u {r = ()} q)
ground p (u≼ {r = ()} q)

mutual
  flatE : ∀ {X X′ Y} {y : R.T₀} → Le X X′ →
    Gd (L.add X σ₁ Y) → Gd (L.add X′ σ₀ y) → R.Flat Y → Y ≼ y →
    Le (L.add X σ₁ Y) (L.add X′ σ₀ y)
  flatE p ga gb fy z≼ = right₀ p _
  flatE p (gs ga) (gs gb) (R.fs fy) (s≼s q) = s≤ (flatE p ga gb fy q)
  flatE p ga (gl gb) fy (≼l n q) = pack ga (gl gb) (lr n (flatE p ga (gb n) fy q))
  flatE p (gl ga) gb (R.fl fy) (l≼ h) = pack (gl ga) gb (ll (λ n → flatE p (ga n) gb (fy n) (h n)))
  flatE p ga gb fy (≼i {p = ()} x ex q)
  flatE p ga gb () (i≼ h)
  flatE p ga gb fy (≼u {r = ()} q)
  flatE p ga gb R.fu (u≼ q) = ground p q

  tailE : ∀ {X X′ Y Y′} → Le X X′ → Gd (L.add X σ₁ Y) → Gd (L.add X′ σ₁ Y′) →
    Y R.≤ₚ Y′ → Le (L.add X σ₁ Y) (L.add X′ σ₁ Y′)
  tailE p ga gb R.zz = p
  tailE p (gs ga) (gs gb) (R.ss q) = s≤ (tailE p ga gb q)
  tailE p ga (gs gb) (R.ws q) = pack ga (gs gb) (ws (tailE p ga gb q))
  tailE p ga (gl gb) (R.≤l n q) = pack ga (gl gb) (lr n (tailE p ga (gb n) q))
  tailE p (gl ga) gb (R.l≤ h) = pack (gl ga) gb (ll (λ n → tailE p (ga n) gb (h n)))
  tailE p (gn₀ la ga) (gn₀ lb gb) (R.ii h) = pack (gn₀ la ga) (gn₀ lb gb)
    (nn₀ (λ x y o q → tailE p (ga x o) (gb y (OCF.Align.Value.≼-trans o q)) (h x y o q)))
  tailE p ga (gn₀ lb gb) (R.i1 q) = pack ga (gn₀ lb gb)
    (aa₀ (tailE p ga (gb R.𝟙 (OCF.Align.Value.≼-refl _)) q))
  tailE p ga gb (R.fu fy q) = flatE p ga gb fy q

positive₀ : ∀ {X} {y : R.T₀} → Gd (L.add X σ₀ y) → O.𝟙₁ ≼ y → Le one (L.add X σ₀ y)
positive₀ (gs g) (s≼s p) = s≤ (z≤ g)
positive₀ (gl g) (≼l n p) = pack (gs gz) (gl g) (lr n (positive₀ (g n) p))
positive₀ g (≼i {p = ()} x ex p)
positive₀ g (≼u {r = ()} p)

positiveE : ∀ {X Y} → Gd (L.add X σ₁ Y) → O.𝟙₁ R.≤ₚ Y → Le one (L.add X σ₁ Y)
positiveE (gs g) (R.ss p) = s≤ (z≤ g)
positiveE (gs g) (R.ws p) = pack (gs gz) (gs g) (ws (positiveE g p))
positiveE (gl g) (R.≤l n p) = pack (gs gz) (gl g) (lr n (positiveE (g n) p))
positiveE (gn₀ law g) (R.i1 p) = pack (gs gz) (gn₀ law g)
  (aa₀ (positiveE (g R.𝟙 (OCF.Align.Value.≼-refl _)) p))
positiveE g (R.fu (R.fs R.fz) p) = positive₀ g p

good₁ : ∀ {X Y} → Gd X → O.Gd Y → Gd (L.add X σ₁ Y)
good₁ g O.gz = g
good₁ g (O.gs h) = gs (good₁ g h)
good₁ g (O.gl h) = gl (λ n → good₁ g (h n))
good₁ g (O.gi {f = f} law gb) = gn₀ (sc₀
  (λ x y o q → tailE (refl g) (good₁ g (gb x o)) (good₁ g (gb y (OCF.Align.Value.≼-trans o q))) (O.SC.mo law x y o q))
  (λ x o → tailE (refl g) (gs (good₁ g (gb x o))) (good₁ g (gb (L.suc x) (s≼s z≼))) (O.SC.db law x o))
  (positiveE (good₁ g (gb R.𝟙 (OCF.Align.Value.≼-refl _))) (O.SC.po law)))
  (λ x o → good₁ g (gb x o))
good₁ g O.gu = good₀ g _

tail : ∀ {X X′ Y Y′} → Le X X′ → O.Gd Y → O.Gd Y′ → Y R.≤ₚ Y′ →
  Le (L.add X σ₁ Y) (L.add X′ σ₁ Y′)
tail p ga gb q = tailE p (good₁ (left p) ga) (good₁ (right p) gb) q

sample : Gd (L.add F.Ω₂ σ₁ O.Ω₁)
sample = good₁ Gd-Ω₂ O.Gd-Ω
```
