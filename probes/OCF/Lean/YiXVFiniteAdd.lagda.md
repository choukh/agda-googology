# YiXVFiniteAdd
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteAdd where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteGroundAdd as G
import OCF.Lean.YiXVFiniteAddStage as S

mutual
  good : ∀ t k {X} → A.Gd t X → (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) →
    (y : I.T k) → A.Gd k y → A.Gd t (L.add X σ y)
  good t zero {X} gx σ y gy = G.good t {X = X} gx σ y
  good zero (suc k) gx σ y gy with σ L.zero
  ... | ()
  good (suc n) (suc m) gx σ y gy = M.good gx σ gy
    where module M = S.Stage n m (good (suc n) m) (mono (suc n) m)

  mono : ∀ t k {X X′} → A.Le t X X′ → (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) →
    (y y′ : I.T k) → A.Le k y y′ → A.Le t (L.add X σ y) (L.add X′ σ y′)
  mono t zero {X} {X′} p σ y y′ q = G.mono t {X = X} {X′ = X′} {σ = σ} {τ = σ} {x = y} {y = y′} p q
  mono zero (suc k) p σ y y′ q with σ L.zero
  ... | ()
  mono (suc n) (suc m) p σ y y′ q = M.mono p σ q
    where module M = S.Stage n m (good (suc n) m) (mono (suc n) m)

plus-good : ∀ n {X Y} → A.Gd n X → A.Gd n Y → A.Gd n (X L.+ Y)
plus-good n {X} {Y} gx gy = good n n {X = X} gx (λ q → q) Y gy
plus : ∀ n {X X′ Y Y′} → A.Le n X X′ → A.Le n Y Y′ → A.Le n (X L.+ Y) (X′ L.+ Y′)
plus n {X} {X′} {Y} {Y′} p q = mono n n {X = X} {X′ = X′} p (λ r → r) Y Y′ q

model₃ : A.Gd 3 (L.Ω (L.natᴵ 3) L.+ L.Ω (L.natᴵ 3))
model₃ = plus-good 3 A.actual₃ A.actual₃
```
