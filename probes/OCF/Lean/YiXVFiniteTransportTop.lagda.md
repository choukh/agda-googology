# YiXVFiniteTransportTop
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteTransportTop where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst₂; sym; cong)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteTransportShape as S
import OCF.Lean.YiXVFiniteTransportInputs as Q
import OCF.Lean.YiXVFiniteTransportNorm as N

module Top (n : ℕ) (old : Q.Ops n) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module P = Q.Inputs n old
  mutual
    good : ∀ d {X} → D.Gd X → D.Gd (S.τ d (suc n) X)
    good d D.gz rewrite S.z d (suc n) = D.gz
    good d (D.gs {X} gx) rewrite S.s d (suc n) X = D.gs (good d gx)
    good d (D.gl {a = a} ga) rewrite S.l d (suc n) a = D.gl (λ k → good d (ga k))
    good d (D.gn {q = q} {f = a} (D.sc mo db po) ga) rewrite S.node d (suc n) q a = D.gn (D.sc
      (λ u v gu gv o p → mono d (mo (S.pull d q u) (S.pull d q v) (P.good-pull d q u gu) (P.good-pull d q v gv)
        (P.floor-pull d q u o) (P.rel-pull d q u v p)))
      (λ u gu o → subst₂ D.Le (S.s d (suc n) (a (S.pull d q u))) (cong (λ v → S.τ d (suc n) (a v)) (sym (S.pull-next d q u)))
        (mono d (db (S.pull d q u) (P.good-pull d q u gu) (P.floor-pull d q u o))))
      (D.trans (subst₂ D.Le (S.o d (suc n)) refl (mono d po))
        (mono d (mo (C.start q) (S.pull d q (C.start q)) (In.At.good-start n q)
          (P.good-pull d q (C.start q) (In.At.good-start n q)) (In.At.floor-start n q) (P.start-rel d q)))))
      (λ u gu o → good d (ga (S.pull d q u) (P.good-pull d q u gu) (P.floor-pull d q u o)))
    good d (D.gu {X} gx) rewrite S.u d n X = D.gu (Q.Ops.good old d F.zero X gx)

    mono : ∀ d {X Y} → D.Le X Y → D.Le (S.τ d (suc n) X) (S.τ d (suc n) Y)
    mono d (D.pack gx gy p) = D.pack (good d gx) (good d gy) (step d gx gy p)

    step : ∀ d {X Y} → D.Gd X → D.Gd Y → D.Step X Y → D.Step (S.τ d (suc n) X) (S.τ d (suc n) Y)
    step d gx gy D.rr = D.rr
    step d gx gy D.zz rewrite S.z d (suc n) = D.zz
    step d (D.gs {X} gx) (D.gs {X = Y} gy) (D.ss p) rewrite S.s d (suc n) X | S.s d (suc n) Y = D.ss (mono d p)
    step d gx (D.gs {X = Y} gy) (D.ws p) rewrite S.s d (suc n) Y = D.ws (mono d p)
    step d (D.gl {a = a} ga) gy (D.ll h) rewrite S.l d (suc n) a = D.ll (λ k → mono d (h k))
    step d gx (D.gl {a = a} ga) (D.lr k p) rewrite S.l d (suc n) a = D.lr k (mono d p)
    step d (D.gn {q = q} {f = a} la ga) (D.gn {f = b} lb gb) (D.nn h) rewrite S.node d (suc n) q a | S.node d (suc n) q b =
      D.nn (λ u v gu gv o p → mono d (h (S.pull d q u) (S.pull d q v) (P.good-pull d q u gu) (P.good-pull d q v gv)
        (P.floor-pull d q u o) (P.rel-pull d q u v p)))
    step d gx (D.gn {q = q} {f = a} (D.sc mo db po) ga) (D.aa p) rewrite S.node d (suc n) q a = D.aa
      (D.trans (mono d p) (mono d (mo (C.start q) (S.pull d q (C.start q)) (In.At.good-start n q)
        (P.good-pull d q (C.start q) (In.At.good-start n q)) (In.At.floor-start n q) (P.start-rel d q))))
    step d (D.gu {X} gx) (D.gu {X = Y} gy) (D.uu p) rewrite S.u d n X | S.u d n Y = D.uu (Q.Ops.mono old d F.zero X Y p)
    step d gx gy (D.uS {X} gp) = N.At.uS n d {X = X} (Q.Ops.good old d F.zero X gp)
    step d gx gy (D.uS⁻ {X} gp) = N.At.uS⁻ n d {X = X} (Q.Ops.good old d F.zero X gp)
    step d gx gy D.uZ = N.At.uZ n d
    step d gx gy D.uZ⁻ = N.At.uZ⁻ n d
    step d gx gy (D.uL {a = a} gp) = N.At.uL n d {a = a} (λ k → Q.Ops.good old d F.zero (a k) (gp k))
    step d gx gy (D.uL⁻ {a = a} gp) = N.At.uL⁻ n d {a = a} (λ k → Q.Ops.good old d F.zero (a k) (gp k))
    step d gx gy (D.uN {q = q} {a = a} gp) = N.At.uN n d {q = q} {a = a} (Q.Ops.good old d F.zero (L.limᵢ q a) gp)
    step d gx gy (D.uN⁻ {q = q} {a = a} gp) = N.At.uN⁻ n d {q = q} {a = a} (Q.Ops.good old d F.zero (L.limᵢ q a) gp)
    step d gx gy (D.tr p q) = D.tr (mono d p) (mono d q)

  mutual
    pair : ∀ d {X} → D.Gd X → D.Le X (S.τ d (suc n) X) × D.Le (S.τ d (suc n) X) X
    pair d gx = D.pack gx (good d gx) (forth d gx) , D.pack (good d gx) gx (back d gx)
    forth : ∀ d {X} → D.Gd X → D.Step X (S.τ d (suc n) X)
    forth d D.gz rewrite S.z d (suc n) = D.rr
    forth d (D.gs {X} gx) rewrite S.s d (suc n) X = D.ss (proj₁ (pair d gx))
    forth d (D.gl {a = a} ga) rewrite S.l d (suc n) a = D.ll (λ k → D.pack (ga k) (D.gl (λ j → good d (ga j))) (D.lr k (proj₁ (pair d (ga k)))))
    forth d (D.gn {q = q} {f = a} (D.sc mo db po) ga) rewrite S.node d (suc n) q a = D.nn (λ u v gu gv o p → D.trans
      (mo u (S.pull d q v) gu (P.good-pull d q v gv) o (P.u≤pull-v d q u v gv p))
      (proj₁ (pair d (ga (S.pull d q v) (P.good-pull d q v gv) (P.floor-pull d q v (P.floor-right q u v o p))))))
    forth d (D.gu {X} gx) rewrite S.u d n X = D.uu (proj₁ (Q.Ops.pair old d F.zero X gx))
    back : ∀ d {X} → D.Gd X → D.Step (S.τ d (suc n) X) X
    back d D.gz rewrite S.z d (suc n) = D.rr
    back d (D.gs {X} gx) rewrite S.s d (suc n) X = D.ss (proj₂ (pair d gx))
    back d (D.gl {a = a} ga) rewrite S.l d (suc n) a = D.ll (λ k → D.pack (good d (ga k)) (D.gl ga) (D.lr k (proj₂ (pair d (ga k)))))
    back d (D.gn {q = q} {f = a} (D.sc mo db po) ga) rewrite S.node d (suc n) q a = D.nn (λ u v gu gv o p → D.trans
      (proj₂ (pair d (ga (S.pull d q u) (P.good-pull d q u gu) (P.floor-pull d q u o))))
      (mo (S.pull d q u) v (P.good-pull d q u gu) gv (P.floor-pull d q u o) (P.pull-u≤v d q u v gu p)))
    back d (D.gu {X} gx) rewrite S.u d n X = D.uu (proj₂ (Q.Ops.pair old d F.zero X gx))

extend : ∀ n → Q.Ops n → Q.Ops (suc n)
Q.Ops.good (extend n old) d F.zero X gx = Top.good n old d gx
Q.Ops.good (extend n old) d (F.suc i) X gx = Q.Ops.good old d i X gx
Q.Ops.mono (extend n old) d F.zero X Y p = Top.mono n old d p
Q.Ops.mono (extend n old) d (F.suc i) X Y p = Q.Ops.mono old d i X Y p
Q.Ops.pair (extend n old) d F.zero X gx = Top.pair n old d gx
Q.Ops.pair (extend n old) d (F.suc i) X gx = Q.Ops.pair old d i X gx
ops₁ : Q.Ops 1
ops₁ = extend 0 Q.ops₀
ops₂ : Q.Ops 2
ops₂ = extend 1 ops₁
actual₂ : A.Gd 2 (S.τ S.bwd 2 (L.Ω (L.natᴵ 2)))
actual₂ = Q.Ops.good ops₂ S.bwd F.zero (L.Ω (L.natᴵ 2)) A.actual₂
```
