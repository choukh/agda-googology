# YiXVReadGround
> 验收文件。档位：编译定理。实际零源层的完整 Out，底部与槽位复用原第零层折叠上界。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadGround where
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; ≼-refl)
open import OCF.Lean.YiCeilRead using (fold₀≼; folds₀≼)
open import OCF.Lean.YiXVAffine using (pw-add)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVCountableZeroRead as Z
import OCF.Lean.YiXVZeroRead as Zero
import OCF.Lean.YiXVReadEnv as Env
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadOutInput as O
module Ground (root : S.Tr S.zero) (within : S.zero P.≤ᵀ root) (B : Fold.Base S.zero)
  (Z₀ : L.Ordᶜ (T.lvl root)) (w : W.World root S.zero within B Z₀) where
  β = Fold.bs B S.zero Path.self
  nβ = Fold.ns B S.zero Path.self
  bs : Read.read β ≼ L.ψ⁰ Z₀
  bs = ≼-trans (W.World.slots w S.zero within Path.self)
    (≅→≼ (Zero.same (W.pc within) (λ q → L.suc q) Z₀))
  Both : S.Tr S.zero → L.Ordᶜ L.zero → Set
  Both a X =
    (Read.read (Fold.ψ⊥ S.zero tt tt B a) ≼ L.ψ⁰ (O.cap within Z₀ X)) ×
    (Read.read (Fold.ψs S.zero tt tt B S.zero Path.self β nβ a) ≼ L.ψ⁰ (O.cap within Z₀ X))
  both : ∀ {a X} → U.UR S.zero a X → Both a X
  both {a} {X} h =
    ≼-trans (fold₀≼ B (W.World.bot w) a) (≼-trans (pw-add (O.σ within) Z₀ (Read.read a)) tail) ,
    ≼-trans (folds₀≼ B β nβ bs a) (≼-trans (pw-add (O.σ within) Z₀ (Read.read a)) tail)
    where
    tail = Z.mono {κ = T.lvl root} {a = L.suc (T.lvl root)}
      (read-strong root) (read-strong root) (Env.zero-bound root) (λ q → L.suc q)
      (Add.mono {σ = O.σ within} (W.World.good w) (G.native h))
  upper : ∀ {a X} → U.UR S.zero a X → O.Out root S.zero within B Z₀ a X
  O.Out.good (upper {X = X} h) = Add.good (W.World.good w) (G.good X)
  O.Out.bot (upper h) = proj₁ (both h)
  O.Out.slots (upper {X = X} h) S.zero p Path.self = ≼-trans (proj₂ (both h))
    (≅→≼ (L.≅-sym (Zero.same (W.pc p) (λ q → L.suc q) (O.cap within Z₀ X))))
  O.Out.slots (upper h) (S.suc y) p ()
  O.Out.slots (upper h) (S.lim f a) p ()
  O.Out.slots (upper h) (S.Ω () g) p v
  O.Out.slots (upper h) (S.up x () y e) p v

model : O.Out (S.suc S.zero) S.zero (P.below P.root) (Fold.B₀ S.zero)
  (W.seed (S.suc S.zero)) (S.suc S.zero) (L.suc L.zero)
model = Ground.upper (S.suc S.zero) (P.below P.root) (Fold.B₀ S.zero) (W.seed (S.suc S.zero))
  (Start.initial-any (S.suc S.zero) S.zero (P.below P.root)) (≼-refl _)
```
