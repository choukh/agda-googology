# 旧 Ω₃ 的整个正回灌只需一个二层算子

第四层。标准底旧 Ω₃ 的正轨道有统一上界。由 X₀=Ω₂、Xₙ₊₁=ψ₂(Xₙ+1) 生成 Xₙ，可逐项界住原来的正树。标准种子的自身折叠在任一已解释的输入上只需施一次 ψ₂；这也给出第二个真实实参内完整 Ω₂ 自折叠的零层观察上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchSelf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼l; l≼; +-mono; ≅→≼)
import OCF.Lean.YiLegOps as Op
import OCF.Lean.YiXVCan2Zero as Z
import B12BtboCut as Ref
import B12Omega3Ref as Third
open import Data.Product using (_,_)
import OCF.Lean.YiLegBlock as Tree
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLSRead as V
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCanTau as Tau
import OCF.Lean.YiXVCanTauPair as Pair
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCan2Plus as Plus
import OCF.Lean.YiXVCan2Rel as Rel
import OCF.Lean.YiXVCan2Lift as Lift
import OCF.Lean.YiXVCan2Gamma as G
import OCF.Lean.YiXVCan2Domain as D
import OCF.Lean.YiXVLocal as I
import Survey.W4FirstBranchNativeThree as Old

module Self (B : Fold.Base (Tree.suc Tree.zero)) (E : Fold.Base Old.two)
  (a : Tree.Tr Old.two) (nz : Old.two Tree.⊢ Tree.zero ◃ a)
  (seed : Rel.Rel.U B a (P.Ψ F.Ω₂)) where
  module U = Rel.Rel B
  χ = Fold.ψs Old.two tt tt E Old.two Path.self a nz
  nonzero = Fold.nzs Old.two tt tt E Old.two Path.self a nz

  bound : ∀ {x X} → C.Gd X → U.U x X → U.U (χ x) (P.Ψ X)
  bound gx U.uz = seed
  bound (C.gs gx) (U.us {x = x} h) = Plus.Closure.next B (nonzero x) (P.good gx) (bound gx h)
  bound gx (U.uw h p) = U.uw (bound (C.left p) h) (P.mono p)
  bound gx (U.ul h) = U.ul (λ n → bound gx (h n))
  bound (C.gn₀ _ g) (U.un₀ h) = U.un₀ (λ a y p →
    let y′ = L.tr⁻ L.z≅ y
        p′ = ≼-trans p (proj₂ (O.tr⁻≈ y))
    in bound (g y′ (O.s→1 p′)) (h a y′ p′))
  bound (C.gn₁ _ g) (U.un₁ h) = U.un₁ (λ a X Y gx gy o ha ca p →
    bound (g (Tau.τ Y) (Tau.good gy) (Tau.floor o))
      (h a X (Tau.τ Y) gx (Tau.good gy) (Tau.floor o) ha ca (R.trans p (proj₁ (Pair.pair gy)))))
  bound gx (U.uu {x = x} gy h point-good hz cz) = Lift.Lift.upc B (nonzero x) gy (bound gy h) point-good hz cz

module Actual = Self I.D1 Old.E Old.Rows.β Old.Rows.nβ D.ΩψU

X : ℕ → F.T₂
X zero = F.Ω₂
X (suc n) = P.Ψ (L.suc (X n))
good : ∀ n → C.Gd (X n)
good zero = C.Gd-Ω₂
good (suc n) = P.good (C.gs (good n))

orbit : ∀ n → D.U.U (Old.Rows.c n) (X n)
orbit zero = D.U.uz
orbit (suc n) = Actual.bound (C.gs (good n)) (D.U.us (orbit n))

self-upper : V.read (Fold.ψ⊥ Old.two tt tt Old.E Old.positive-self) ≼ L.ψ⁰ (P.Ψ Old.double)
self-upper = Old.Out.Out.bot≤ (Old.Interpretation.upper (P.good Old.good-double) (Actual.bound Old.good-double D.ΩU))

rows : ∀ n → V.read (Old.Rows.rows n) ≼ L.ψ⁰ (L.suc (X n))
rows n = Old.Out.Out.bot≤ (Old.Interpretation.upper (C.gs (good n)) (D.U.us (orbit n)))

tower-index : ℕ → ℕ
tower-index zero = 0
tower-index (suc n) = suc (suc (tower-index n))

bounded : ∀ n → C.Le (X n) (G.Γ (tower-index n))
bounded zero = C.Ω₂-refl
bounded (suc n) = P.mono (C.trans (C.s≤ (bounded n)) (G.inv (tower-index n)))

from-tower : ∀ n → C.Le (G.Γ n) (X n)
from-tower zero = C.Ω₂-refl
from-tower (suc n) = P.mono (C.pack (G.good n) (C.gs (good n)) (C.ws (from-tower n)))

value = λ n → L.ψ⁰ (X n)
cofinal : Ref.finite 3 ≈ᵛ L.lim value
cofinal = l≼ (λ n → ≼l {f = value} n (Z.mono₀ (from-tower n))) ,
  l≼ (λ n → ≼l {f = Old.Rows.Gr} (tower-index n) (Z.mono₀ (bounded n)))

row-bound : ∀ n → V.read (Old.Rows.rows n) ≼ Old.Rows.Gr (suc (tower-index n))
row-bound n = ≼-trans {b = L.ψ⁰ (L.suc (X n))} (rows n)
  (Z.mono₀ (C.trans (C.s≤ (bounded n)) (G.inv (tower-index n))))

prefix-bound : ∀ n → V.read (Op.cum Old.Rows.rows n) ≼ Old.Rows.Gr (suc (suc (tower-index n)))
prefix-bound zero = ≼-trans {b = Old.Rows.Gr 1} (row-bound 0) (Old.Rows.le 1)
prefix-bound (suc n) = ≼-trans {b = V.read (Op.cum Old.Rows.rows n) L.+ V.read (Old.Rows.rows (suc n))}
  (≅→≼ (V.read-+ (Op.cum Old.Rows.rows n) (Old.Rows.rows (suc n))))
  (≼-trans {b = Old.Rows.Gr i L.+ Old.Rows.Gr i}
    (+-mono (≼-trans (prefix-bound n) (Old.Rows.le (suc (suc (tower-index n))))) (row-bound (suc n)))
    (Old.Rows.dbl i))
  where i = suc (tower-index (suc n))

-- 第一次回灌可用正有限倍数之极限校准，再在同一条律中投入整棵树。
first : D.U.U (Old.Rows.c 1) (Third.finitePower 1)
first = D.U.uw (Plus.Closure.next I.D1 Old.Rows.nβ Old.good-double D.ΩU) Old.to-first-power

second : D.U.U (Old.Rows.c 2) (P.Ψ (L.suc (Third.finitePower 1)))
second = Actual.bound (C.gs (Old.good-power 1)) (D.U.us first)
```
