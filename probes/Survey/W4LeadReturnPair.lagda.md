# 在下一次真实运算的同一输入状态内取得 P 的两个投影

第四层。任取此前的有限轮数，下一次内反馈执行前，所有零槽支配 ψ₀(P)，指定正槽同时承载 ψ₁(P)。该运算的零层返回沿实际地址进入同一塔。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadReturnPair where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import W4Block
open import W4Ops
open import W4Fold
open import WVOne using (read; 𝟏)
open import WVTwo using (◃→≼; g₂; p₂)
open import WKGen using (Ω₁t; node-ge)
open import YiLAB7Orbit using (lvl1; lvl2; ok₂)
open import WKShape using (lvl3)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl)
import B11OuterCore as C
import B12Terminal as T
import B12ActualSlots as Cv
import B13Orbit as Orb
import B13SeedOuter
import B24AFirst
import B13OrbitFeed as O
import B15OrbitModel as M
import B18OrbitWorld as W
import B21RowDynamics as I
import B23ABlocks as Bl
import B24NStore as Store
import B24NProduct as Prod
import B24ROrbit as D
import Survey.W4LeadReturnState as Prev

module At (r : T.Run lvl3) (cv : Cv.Covered r) (n : ℕ) where
  private module A = Prev.At r cv
  open B13SeedOuter.At r using (w2; c⁺)
  open B24AFirst.At r cv using (Q₁; Q₂)
  private module B = A.Call n (B13SeedOuter.At.w2 r) (A.values (ℕ.suc n)) (A.base (ℕ.suc n))
  private
    module G = B.G
    op₁ = op (E ok₂ O.D₁ (G.seq 1) G.K) (Einf ok₂ O.D₁ (G.seq 1) G.K)
  -- 这是本层后继分支取第 1 项时，第二次求值收到的环境。
  state = stepS op₁ G.S
  picked = M.pull state
  scalar : ∀ t → D.D ≼ read (proj₁ (picked zero t))
  scalar t = ≼-trans (A.floor n t) (◃→≼ (inf op₁ G.S zero (σ O.m₁ t) (G.S zero (σ O.m₁ t))))
  upper : I.Index (picked lvl1 C.slot) Store.Sem.target
  upper = W.rise Prod.world B.tree (picked lvl1 C.slot) below Store.Sem.target B.selected
    where
    d : lvl1 ⊢ Ω₁t ◃ G.seq 1
    d = ◃t B.cov (Einf ok₂ tdNil (g₂ zero) Q₁ B.state lvl1 C.slot G.c₀)
    below = Emono ok₂ O.D₁ G.K G.S lvl1 G.high G.c₀ {x = Ω₁t} {y = G.seq 1} d
  result = read (proj₁ (itV op₁ 2 G.S zero G.own (A.values (ℕ.suc n))))
  child : result ≼ read (proj₁ (G.out₂ (G.seq 1)))
  child = ◃→≼ (◃l 1)
  step : read (proj₁ (G.out₂ (G.seq 1))) ≼ read (proj₁ (run (Orb.block (Ωt lvl2) Q₁) B.state zero w2 (A.values (ℕ.suc n))))
  step = node-ge (kp lvl2 ok₂ p₂ w2) G.out₂ G.step₂ 1
  public-value : result ≼ read (T.value r)
  public-value = ≼-trans child (≼-trans step (≼-trans (to-full (Bl.Site.cp r cv)) (A.into (ℕ.suc n))))
    where
    b = A.values (ℕ.suc n)
    f = λ z → read (proj₁ (E ok₂ tdNil z Q₁ B.state zero w2 b))
    to-full : Cv._⊴_ (proj₁ (Ωt lvl2)) (proj₁ c⁺) → f (proj₁ (Ωt lvl2)) ≼ f (proj₁ c⁺)
    to-full (inj₁ eq) = subst (λ z → f (proj₁ (Ωt lvl2)) ≼ f z) eq (≼-refl _)
    to-full (inj₂ d) = ◃→≼ (Emono ok₂ tdNil Q₁ B.state zero w2 b d)
```
