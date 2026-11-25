# YiXVFiniteGroundCompose
> 验收文件。档位：编译定理。有限层参照侧的加法复合与前缀下界工具。尚无所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteGroundCompose where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add

compose : ∀ t k (X : I.T t) (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) (Y : I.T k)
  (τ : L.Simᴵ L.zero (L.natᴵ k)) (Z : I.T zero) → A.Gd t X → A.Gd k Y →
  A.Le t (L.add (L.add X σ Y) (λ q → σ (τ q)) Z) (L.add X σ (L.add Y τ Z))
compose t k X σ Y τ L.zero gx gy = B.rfl t F.zero {X = L.add X σ Y} (Add.good t k {X = X} gx σ Y gy)
compose t k X σ Y τ (L.suc Z) gx gy = B.s≤ t F.zero
  {X = L.add (L.add X σ Y) (λ q → σ (τ q)) Z} {Y = L.add X σ (L.add Y τ Z)} (compose t k X σ Y τ Z gx gy)
compose t k X σ Y τ (L.lim a) gx gy = B.ll t F.zero {a = left} {Y = L.lim right} gl (B.gl t F.zero {a = right} gr)
  (λ j → B.lr t F.zero {X = left j} {a = right} (gl j) gr j (compose t k X σ Y τ (a j) gx gy))
  where
  left right : ℕ → I.T t
  left j = L.add (L.add X σ Y) (λ q → σ (τ q)) (a j)
  right j = L.add X σ (L.add Y τ (a j))
  gl : ∀ j → A.Gd t (left j)
  gl j = Add.good t 0 {X = L.add X σ Y} (Add.good t k {X = X} gx σ Y gy) (λ q → σ (τ q)) (a j) tt
  gr : ∀ j → A.Gd t (right j)
  gr j = Add.good t k {X = X} gx σ (L.add Y τ (a j)) (Add.good k 0 {X = Y} gy τ (a j) tt)
compose t k X σ Y τ (L.limᵢ () a) gx gy
compose t k X σ Y τ (L.up () Z) gx gy
```
