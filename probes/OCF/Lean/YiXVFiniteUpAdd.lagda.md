# YiXVFiniteUpAdd
> 验收文件。档位：编译定理。up 与任意有限层加法的比较，规范闭实例已填。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteUpAdd where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteUp as Up

module Ground (n : ℕ) (X : I.T n) (gx : A.Gd n X) (σ : L.Simᴵ L.zero (L.natᴵ n)) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  l r : I.T zero → I.T (suc n)
  l Y = L.up L.zero (L.add X σ Y)
  r Y = L.add (L.up L.zero X) (λ q → L.suc (σ q)) Y
  gl : ∀ Y → D.Gd (l Y)
  gl Y = D.gu (Add.good n 0 {X = X} gx σ Y tt)
  gr : ∀ Y → D.Gd (r Y)
  gr Y = Add.good (suc n) 0 {X = L.up L.zero X} (D.gu gx) (λ q → L.suc (σ q)) Y tt
  result : ∀ Y → D.Le (l Y) (r Y)
  result L.zero = D.refl (D.gu gx)
  result (L.suc Y) = D.trans
    (D.pack (gl (L.suc Y)) (D.gs (gl Y)) (D.uS⁻ (Add.good n 0 {X = X} gx σ Y tt))) (D.s≤ (result Y))
  result (L.lim a) = D.trans
    (D.pack (gl (L.lim a)) (D.gl (λ k → gl (a k))) (D.uL (λ k → Add.good n 0 {X = X} gx σ (a k) tt)))
    (D.pack (D.gl (λ k → gl (a k))) (gr (L.lim a))
      (D.ll (λ k → D.pack (gl (a k)) (gr (L.lim a)) (D.lr k (result (a k))))))
  result (L.limᵢ () a)
  result (L.up () Y)

module Stage (n k : ℕ)
  (low : ∀ X (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ (suc n))) Y → A.Gd (suc n) X → A.Gd k Y →
    A.Le (suc (suc n)) (L.up L.zero (L.add X σ Y)) (L.add (L.up L.zero X) (λ q → L.suc (σ q)) Y)) where
  module S = A.Layer k (A.GoFam k) (A.LeFam k)
  module D = A.Layer (suc n) (A.GoFam (suc n)) (A.LeFam (suc n))
  module At (X : I.T (suc n)) (σ : L.Simᴵ (L.natᴵ (suc k)) (L.natᴵ (suc n))) (gx : A.Gd (suc n) X) where
    l r : I.T (suc k) → I.T (suc (suc n))
    l Y = L.up L.zero (L.add X σ Y)
    r Y = L.add (L.up L.zero X) (λ q → L.suc (σ q)) Y
    gl : ∀ Y → S.Gd Y → D.Gd (l Y)
    gl Y gy = D.gu (Add.good (suc n) (suc k) {X = X} gx σ Y gy)
    gr : ∀ Y → S.Gd Y → D.Gd (r Y)
    gr Y gy = Add.good (suc (suc n)) (suc k) {X = L.up L.zero X} (D.gu gx) (λ q → L.suc (σ q)) Y gy
    result : ∀ {Y} → S.Gd Y → D.Le (l Y) (r Y)
    result S.gz = D.refl (D.gu gx)
    result (S.gs {X = Y} gy) = D.trans
      (D.pack (gl (L.suc Y) (S.gs gy)) (D.gs (gl Y gy)) (D.uS⁻ (Add.good (suc n) (suc k) {X = X} gx σ Y gy)))
      (D.s≤ (result gy))
    result (S.gl {a} ga) = D.trans
      (D.pack (gl (L.lim a) (S.gl ga)) (D.gl (λ k → gl (a k) (ga k)))
        (D.uL (λ b → Add.good (suc n) (suc k) {X = X} gx σ (a b) (ga b))))
      (D.pack (D.gl (λ k → gl (a k) (ga k))) (gr (L.lim a) (S.gl ga))
        (D.ll (λ k → D.pack (gl (a k) (ga k)) (gr (L.lim a) (S.gl ga)) (D.lr k (result (ga k))))))
    result gY@(S.gn {q = q} {f = f} law gb) = D.trans
      (D.pack (gl _ gY) normal (D.uN lower))
      (D.pack normal (gr _ gY) (D.nn (λ u v gu gv o t → D.trans
        (result (gb (In.Change.pull c u) (In.Change.good c u gu) (In.Change.floor c u o)))
        (Add.mono (suc (suc n)) (suc k) {X = L.up L.zero X} {X′ = L.up L.zero X} (D.refl (D.gu gx))
          (λ r → L.suc (σ r)) _ _ (S.SC.mo law (In.Change.pull c u) (In.Change.pull c v)
            (In.Change.good c u gu) (In.Change.good c v gv) (In.Change.floor c u o) (In.Change.rel c u v t))))))
      where
      c = In.change k (suc n) q (L.suc (σ q))
      lower = Add.good (suc n) (suc k) {X = X} gx σ (L.limᵢ q f) gY
      normal = Up.Raise.normal n lower
    result (S.gu {X = Y} gy) = low X (λ q → σ (L.suc q)) Y gx gy

up-add : ∀ n k X (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ n)) Y → A.Gd n X → A.Gd k Y →
  A.Le (suc n) (L.up L.zero (L.add X σ Y)) (L.add (L.up L.zero X) (λ q → L.suc (σ q)) Y)
up-add n zero X σ Y gx gy = Ground.result n X gx σ Y
up-add zero (suc k) X σ Y gx gy with σ (L.zero {a = L.natᴵ k})
... | ()
up-add (suc n) (suc k) X σ Y gx gy = Stage.At.result n k (up-add (suc n) k) X σ gx gy

model : A.Le 2 (L.up L.zero (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1)))
  (L.add (L.up L.zero (L.Ω (L.natᴵ 1))) (λ q → L.suc q) (L.Ω (L.natᴵ 1)))
model = up-add 1 1 (L.Ω (L.natᴵ 1)) (λ q → q) (L.Ω (L.natᴵ 1)) (B.actual 1) (B.actual 1)
```
