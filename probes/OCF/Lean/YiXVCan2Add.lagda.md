# YiXV YiXVCan2Add
> 验收文件。编译定理：同层加法保持二层好树与带证据比较。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Add where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼-trans; s≼s; z≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCanTau as T

mutual
  good : ∀ {X Y} → Gd X → Gd Y → Gd (X L.+ Y)
  good gx gz = gx
  good gx (gs gy) = gs (good gx gy)
  good gx (gl gy) = gl (λ n → good gx (gy n))
  good gx (gn₀ (sc₀ mo db po) gb) = gn₀ (sc₀
    (λ x y o q → plusE (refl gx) (good gx (gb x o)) (good gx (gb y (≼-trans o q))) (mo x y o q))
    (λ x o → plusE (refl gx) (gs (good gx (gb x o))) (good gx (gb (L.suc x) (s≼s z≼))) (db x o))
    (plusE (z≤ gx) (gs gz) (good gx (gb R.𝟙 (≼-refl _))) (po)))
    (λ x o → good gx (gb x o))
  good gx (gn₁ (sc₁ mo db po) gb) = gn₁ (sc₁
    (λ x y hx hy o q → plusE (refl gx) (good gx (gb x hx o)) (good gx (gb y hy (R.trans o q))) (mo x y hx hy o q))
    (λ x hx o → plusE (refl gx) (gs (good gx (gb x hx o))) (good gx (gb (L.suc x) (O.gs hx) (R.ws o))) (db x hx o))
    (plusE (z≤ gx) (gs gz) (good gx (gb O.Ω₁ O.Gd-Ω O.Ω≤Ω)) (po)))
    (λ x hx o → good gx (gb x hx o))
  good gx (gu gy) = M.good₁ gx gy

  rightE : ∀ {X X′ Y} → Le X X′ → Gd Y → Gd (X′ L.+ Y) → Le X (X′ L.+ Y)
  rightE p gz g = p
  rightE p (gs gy) (gs g) = pack (left p) (gs g) (ws (rightE p gy g))
  rightE p (gl gy) (gl g) = pack (left p) (gl g) (lr 0 (rightE p (gy 0) (g 0)))
  rightE p (gn₀ law gy) (gn₀ law′ g) = pack (left p) (gn₀ law′ g)
    (aa₀ (rightE p (gy R.𝟙 (≼-refl _)) (g R.𝟙 (≼-refl _))))
  rightE p (gn₁ law gy) (gn₁ law′ g) = pack (left p) (gn₁ law′ g)
    (aa₁ (λ z hz → rightE p (gy z (T.start-good hz) (T.start-floor hz)) (g z (T.start-good hz) (T.start-floor hz))))
  rightE p (gu O.gz) g = p
  rightE p (gu (O.gs gy)) (gs g) = pack (left p) (gs g) (ws (rightE p (gu gy) g))
  rightE p (gu (O.gl gy)) (gl g) = pack (left p) (gl g) (lr 0 (rightE p (gu (gy 0)) (g 0)))
  rightE p (gu (O.gi law gy)) (gn₀ law′ g) = pack (left p) (gn₀ law′ g)
    (aa₀ (rightE p (gu (gy R.𝟙 (≼-refl _))) (g R.𝟙 (≼-refl _))))
  rightE p (gu O.gu) g = M.right₀ p _

  prefixE : ∀ {X X′ Y} → Le X X′ → Gd Y → Gd (X L.+ Y) → Gd (X′ L.+ Y) → Le (X L.+ Y) (X′ L.+ Y)
  prefixE p gz ga gb = p
  prefixE p (gs gy) (gs ga) (gs gb) = s≤ (prefixE p gy ga gb)
  prefixE p (gl gy) (gl ga) (gl gb) = pack (gl ga) (gl gb) (ll (λ n → pack (ga n) (gl gb) (lr n (prefixE p (gy n) (ga n) (gb n)))))
  prefixE p (gn₀ law gy) (gn₀ la ga) (gn₀ lb gb) = pack (gn₀ la ga) (gn₀ lb gb)
    (nn₀ (λ x y o q → plusE p (ga x o) (gb y (≼-trans o q)) (SC₀.mo₀ law x y o q)))
  prefixE p (gn₁ law gy) (gn₁ la ga) (gn₁ lb gb) = pack (gn₁ la ga) (gn₁ lb gb)
    (nn₁ (λ x y hx hy o q → plusE p (ga x hx o) (gb y hy (R.trans o q)) (SC₁.mo₁ law x y hx hy o q)))
  prefixE p (gu gy) ga gb = M.tailE p ga gb (O.reflₚ gy)

  plusE : ∀ {X X′ Y Y′} → Le X X′ → Gd (X L.+ Y) → Gd (X′ L.+ Y′) → Le Y Y′ → Le (X L.+ Y) (X′ L.+ Y′)
  plusE p ga gb (pack gy gy′ rr) = prefixE p gy ga gb
  plusE p ga gb (pack gy gy′ zz) = rightE p gy′ gb
  plusE p (gs ga) (gs gb) (pack gy gy′ (ss q)) = s≤ (plusE p ga gb q)
  plusE p ga (gs gb) (pack gy gy′ (ws q)) = pack ga (gs gb) (ws (plusE p ga gb q))
  plusE p (gl ga) gb (pack gy gy′ (ll h)) = pack (gl ga) gb (ll (λ n → plusE p (ga n) gb (h n)))
  plusE p ga (gl gb) (pack gy gy′ (lr n q)) = pack ga (gl gb) (lr n (plusE p ga (gb n) q))
  plusE p (gn₀ la ga) (gn₀ lb gb) (pack gy gy′ (nn₀ h)) = pack (gn₀ la ga) (gn₀ lb gb)
    (nn₀ (λ x y o q → plusE p (ga x o) (gb y (≼-trans o q)) (h x y o q)))
  plusE p (gn₁ la ga) (gn₁ lb gb) (pack gy gy′ (nn₁ h)) = pack (gn₁ la ga) (gn₁ lb gb)
    (nn₁ (λ x y hx hy o q → plusE p (ga x hx o) (gb y hy (R.trans o q)) (h x y hx hy o q)))
  plusE p ga (gn₀ lb gb) (pack gy gy′ (aa₀ q)) = pack ga (gn₀ lb gb) (aa₀ (plusE p ga (gb R.𝟙 (≼-refl _)) q))
  plusE p ga (gn₁ lb gb) (pack gy gy′ (aa₁ h)) = pack ga (gn₁ lb gb)
    (aa₁ (λ z hz → plusE p ga (gb z (T.start-good hz) (T.start-floor hz)) (h z hz)))
  plusE p ga gb (pack gy gy′ (uu q)) = M.tailE p ga gb q
  plusE p (gs ga) (gs gb) (pack gy gy′ (uS g)) = s≤ (M.tailE p ga gb (O.reflₚ g))
  plusE p (gs ga) (gs gb) (pack gy gy′ (uS⁻ g)) = s≤ (M.tailE p ga gb (O.reflₚ g))
  plusE p ga gb (pack gy gy′ uZ) = p
  plusE p ga gb (pack gy gy′ uZ⁻) = p
  plusE p (gl ga) (gl gb) (pack gy gy′ (uL g)) = pack (gl ga) (gl gb)
    (ll (λ n → pack (ga n) (gl gb) (lr n (M.tailE p (ga n) (gb n) (O.reflₚ (g n))))))
  plusE p (gl ga) (gl gb) (pack gy gy′ (uL⁻ g)) = pack (gl ga) (gl gb)
    (ll (λ n → pack (ga n) (gl gb) (lr n (M.tailE p (ga n) (gb n) (O.reflₚ (g n))))))
  plusE p (gn₀ la ga) (gn₀ lb gb) (pack gy gy′ (uN (O.gi law g))) = pack (gn₀ la ga) (gn₀ lb gb)
    (nn₀ (λ x y o q → M.tailE p (ga x o) (gb y (≼-trans o q)) (O.SC.mo law x y o q)))
  plusE p (gn₀ la ga) (gn₀ lb gb) (pack gy gy′ (uN⁻ (O.gi law g))) = pack (gn₀ la ga) (gn₀ lb gb)
    (nn₀ (λ x y o q → M.tailE p (ga x o) (gb y (≼-trans o q)) (O.SC.mo law x y o q)))
  plusE p ga gb (pack gy gy′ (tr (pack gq gmid q) r)) = trans
    (plusE p ga (good (right p) gmid) (pack gq gmid q))
    (plusE (refl (right p)) (good (right p) gmid) gb r)

plus : ∀ {X X′ Y Y′} → Le X X′ → Le Y Y′ → Le (X L.+ Y) (X′ L.+ Y′)
plus p q = plusE p (good (left p) (left q)) (good (right p) (right q)) q

sample : Gd (F.Ω₂ L.+ F.Ω₂)
sample = good Gd-Ω₂ Gd-Ω₂
sample-le : Le (F.Ω₂ L.+ F.Ω₂) (F.Ω₂ L.+ F.Ω₂)
sample-le = plus Ω₂-refl Ω₂-refl
```
