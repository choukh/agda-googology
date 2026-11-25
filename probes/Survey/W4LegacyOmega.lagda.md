# 旧链第二点在 W4 的实际 ω 层调用中的比较

> 第四层验收。旧链第二点的各前缀夹在相邻的有限 Ω 层之间；第三个前缀恰为 ψ₀(Ω₃)。目标运行始终沿用 W4 实际传入的底与槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LegacyOmega where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≅→≼; ≼l; l≼; ≼-refl; ≼-trans; ≼lim⁻; ≼-suc; ≺→s≼; s≼s)
open import OCF.Align.BTBOFullV3 using (Fstep)
import OCF.Lean.YiLegBlock as O
import OCF.Lean.YiLegOps as Op
import OCF.Lean.YiLegFold as OF
import OCF.Lean.YiLSFold as Sim
import OCF.Lean.YiLSRel as Rel
import OCF.Lean.YiLSRead as V
import OCF.Lean.YiXVStart as S
import OCF.Lean.YiXVSourceCast as Cast
import OCF.Lean.YiXVSourceIndex as Ix
import OCF.Lean.YiXVSourcePrefixes as Upper
import OCF.Lean.YiXVTwo as Two
import OCF.Lean.YiXVCan2Ceiling as Three
import B25DOld as Old
import B12BtboCut as C
import W4Block as W
import WKTower as WT
import WVOne as One
open One using (T₀; read)
import B12Terminal as T
import B12TerminalSrc as TS
import B12TerminalTail as Tail
import OCF.Lean.YiCeilRead as Ceiling

p : ℕ → T₀
p n = V.read (S.pre n)

prefix : ℕ → O.Tr (O.lim S.fg)
prefix zero = O.zero
prefix (suc n) = Op.cumΩ S.fg n

base : OF.Base (O.lim S.fg)
base = OF.B₀ (O.lim S.fg)
base-at : ∀ n → OF.Base (S.fg n)
base-at = λ n → OF.dL S.fg S.e1 S.r1 base n (prefix n)
call : ∀ n → O.Tr O.zero
call = λ n → OF.ψ⊥ (S.fg n) (S.e1 n) (proj₁ S.r1 n) (base-at n) (Op.Ωt (S.fg n))
unfold : ∀ n → call n ≡ S.pre n
unfold zero = refl
unfold (suc n) = refl

nl : ∀ n → Sim.NL (Ix.nat n)
nl zero = Sim.n0
nl (suc n) = Sim.n+ (nl n)
corr : ∀ n → Rel.Corr (L.natᴵ n) (Ix.nat n)
corr zero = Rel.cz
corr (suc n) = Rel.cs (corr n)

lower : ∀ n → C.finite (suc n) ≼ p n
lower n = subst (λ x → C.finite (suc n) ≼ V.read x) (unfold n)
  (Sim.lower {ℓ = S.fg n} {i = L.natᴵ (suc n)} (subst Sim.NL (sym (Cast.fg n)) (nl (suc n))) (S.e1 n) (proj₁ S.r1 n) (base-at n)
    (Sim.ok-dL S.fg S.e1 S.r1 base (Sim.ok-B₀ (O.lim S.fg)) n (prefix n))
    (subst (Rel.Corr (L.natᴵ (suc n))) (sym (Cast.fg n)) (corr (suc n))))

upper : ∀ n → p n ≼ C.finite (suc (suc n))
upper = Upper.allpre

third : C.finite 3 ≈ᵛ p 2
third = lower 2 , Three.pre2-upper

join : Old.point 2 ≈ᵛ L.lim p
join = ≼-trans {a = Old.point 2} {b = C.omega-cut} {c = L.lim p} (proj₂ Old.point₂) (l≼ levels) ,
  (≼-trans {a = L.lim p} {b = C.omega-cut} {c = Old.point 2}
    (l≼ λ n → ≼l {f = C.finite} (suc (suc n)) (upper n)) (proj₁ Old.point₂))
  where
  levels : ∀ n → C.finite n ≼ L.lim p
  levels zero = ≼l {f = p} 0 (≼-trans {b = C.finite 1}
    (OCF.Align.Value.⊑→≼ (C.finite 0) (L.Ψ⁰0 (L.natᴵ 1))) (lower 0))
  levels (suc n) = ≼l {f = p} n (lower n)

margin : ∀ n → L.suc (p n) ≼ Old.point 2
margin n = ≼-trans {b = L.suc (C.finite (suc (suc n)))} (s≼s (upper n))
  (≼-trans {b = C.finite (suc (suc (suc n)))} (≺→s≼ {c = C.finite (suc (suc n))} {b = C.finite (suc (suc (suc n)))} (Fstep (L.natᴵ (suc (suc n)))))
    (≼-trans {b = C.omega-cut} (≼l (suc (suc (suc n))) (≼-refl _)) (proj₁ Old.point₂)))

module At (r : T.Run WT.Lω) where
  part : ∀ n → T.Run (WT.gL n)
  part = T.limRun WT.gL r
  term : ℕ → T₀
  term n = read (T.value (part n))

  first : p 0 ≼ term 0
  first = ≼-trans {b = C.finite 1} S.pre0-upper
    (One.eps₀ (T.Run.ok c) (T.Run.bs c) (T.Run.β c) (T.Run.oneβ c) (T.Run.oneB c (W.inc tt W.self)))
    where c = part 0

  second : p 1 ≼ term 1
  second = ≼-trans {b = C.finite 2} Two.pre1-upper (T.anchor₂ (part 1))

  third-first-row : V.read (Three.Actual.rows 0) ≼ term 2
  third-first-row = ≼-trans {b = Ceiling.ωx (term 1)} (Ceiling.next≼ (S.pre 1) (OF.n⊥ Three.Actual.E) {Y = term 1} second)
    (≼-trans {b = Tail.mulω (term 1)}
      (l≼ (λ n → ≼l n (One.iterS (≼-refl (term 1)) n))) (Tail.raise WT.gL r 1 {a = term 1} (≼-refl (term 1))))

live-first-row : V.read (Three.Actual.rows 0) ≼ read (T.value (T.finiteRun 2))
live-first-row = At.third-first-row TS.middle
```
