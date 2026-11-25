# YiLam 接口: 观察取部分和的 `Uni` 姊妹记录

非验收文件. 接口 (记录与谓词), 没有定理. `Uniᴾ` 与 [YiUniIf](YiUniIf.lagda.md) 的 `Uni` 除下面两处外逐字相同: `top-rowᶜ` 的第三个参数是链点观察的部分和 `psum m (…)`, 不是序列本身; 没有律 `top-up`.
`Domᴾ` 是同样的读回域. 原接口不改. 实例在 [YiLamNInst](YiLamNInst.lagda.md) (`YiLamFold`), 两份记录的关系在 [YiLamNRel](YiLamNRel.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
  using (lev; Way; keep; fold; Ext; Br; plus-lgl; succ; psum; self; Ψn; ΨN; ΩT)
open import OCF.Lean.YiUniIf using (Full)

record Uniᴾ : Set₁ where
  field
    Bd  : LF → Set
    bS  : ∀ {k} → Bd (suc k) → Bd k
    bL  : ∀ {f} → Bd (lim f) → ∀ n → Bd (f n)
    bC  : ∀ {k g} → Bd (lc k g) → ∀ η → Lgl k η → Bd (g η)
    Ψ   : ∀ m {k} → Bd k → Ext m k → Raw k → Raw m
    cmp : ∀ {k} → Bd k → (q r : Pre k) → Way (lev k q) (lev k r)
    ωw  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Way m k
    Kb  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Raw k → Raw m
    stp : ∀ {k g} (V : Bd (lc k g)) η → Lgl k η → Ext k (g η)
    obd : ∀ m {k g} (V : Bd (lc k g)) → Ext m (lc k g) → ∀ η → Lgl k η → Ext m (g η)
    cpt : ∀ {k g} → Bd (lc k g) → ℕ → Raw k
    cpt-lgl : ∀ {k g} (V : Bd (lc k g)) n → Lgl k (cpt V n)

    zero-row : ∀ m {k} (V : Bd k) x → Ψ m V x G.zero ≡ G.top
    suc-row  : ∀ m {k} (V : Bd k) x a → Ψ m V x (G.suc a) ≡ succ m (Ψ m V x a)
    lim-row  : ∀ m {k} (V : Bd k) x f → Ψ m V x (G.lim f) ≡ G.lim (λ n → Ψ m V x (f n))
    node-row : ∀ m {k} (V : Bd k) x r g → Ψ m V x (G.lc r g) ≡
      ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
    em-rowˢ : ∀ m {k} (V : Bd (suc k)) x a → Ψ m V x (G.em tt a) ≡ Ψ m (bS V) (λ r → x (inj₂ r)) a
    em-rowˡ : ∀ m {f} (V : Bd (lim f)) x n a → Ψ m V x (G.em n a) ≡ Ψ m (bL V n) (λ r → x (n , r)) a
    em-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x η l a →
      Ψ m V x (G.em (η , l) a) ≡ Ψ m (bC V η l) (λ r → x (η , l , r)) a
    top-row⁰ : ∀ m (V : Bd zero) x → Ψ m V x G.top ≡ succ m G.top
    top-rowˢ : ∀ m {k} (V : Bd (suc k)) x → Ψ m V x G.top ≡
      Ψn m k (x (inj₁ tt)) (λ η → Ψ m (bS V) (λ r → x (inj₂ r)) η) (λ η → Ψ k (bS V) (self k) η)
    top-rowˡ : ∀ m {f} (V : Bd (lim f)) x → Ψ m V x G.top ≡
      G.lim (psum m (λ n → Ψ m (bL V n) (λ r → x (n , r)) G.top))
    top-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x → Ψ m V x G.top ≡
      ΩT m k (ωw m V x) (Kb m V x)
        (psum m (λ n → Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top))
    cpt-zero : ∀ {k g} (V : Bd (lc k g)) → cpt V 0 ≡ G.top
    cpt-suc  : ∀ {k g} (V : Bd (lc k g)) n → cpt V (suc n) ≡
      plus k (cpt V n) (Ψ k (bC V (cpt V n) (cpt-lgl V n)) (stp V (cpt V n) (cpt-lgl V n)) G.top)

    Ψ-lgl : ∀ m {k} (V : Bd k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
    Ψ-cp  : ∀ m {k} (V : Bd k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
    Kb-br : ∀ m {k g} (V : Bd (lc k g)) x → Br (layer k) m (Kb m V x)

record Domᴾ (U : Uniᴾ) : Set where
  open Uniᴾ U
  field
    bd-tw : ∀ n → Bd (tw n)
    bd-Λ  : Bd Λ
```

能力 (候选的额外性质, 不在记录里), 照 `YiUniIf` §3.

```agda
CmpFullᴾ : (U : Uniᴾ) → ∀ {k} → Uniᴾ.Bd U k → Set
CmpFullᴾ U {k} V = ∀ q → Full (lev k q) k (Uniᴾ.cmp U V q)

StpFullᴾ : (U : Uniᴾ) → ∀ {k g} → Uniᴾ.Bd U (lc k g) → ∀ η → Lgl k η → Set
StpFullᴾ U {k} {g} V η l = Full k (g η) (Uniᴾ.stp U V η l)
```
