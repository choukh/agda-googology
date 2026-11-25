# YiXVSourceAffineNode
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineNode where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst; subst₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
open import OCF.Align.Value using (s≼s; ≼-refl; ≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourcePathInputs as In
import OCF.Lean.YiXVSourceAffineRef as Ref
import OCF.Lean.YiXVSourceAffineGround as Ground

module Node {n k} (H : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ (suc n) L.<ᴵ ambient)
  (ρ : L.Simᴵ (L.natᴵ H) ambient) (ε : L.Simᴵ (L.natᴵ (suc n)) (L.natᴵ H))
  (p : P.Path (suc n) (suc k)) (i : F.Fin (suc k))
  (x : J.Tr (suc n)) (nx : J.nat (suc n) S.⊢ S.zero ◃ x) (X : I.T H)
  (g : S.Br (J.nat (suc k)) (J.slot k i) → J.Tr (suc k))
  (f : L.U (L.natᴵ (I.rank k i)) (L.<→◃ (J.q k i)) → I.T (suc k)) where
  module D = U.Layer n (U.UR n)
  module G = In.Guards p i
  module NR = Ref.Node H pc ρ ε p i X f
  open NR
  g′ : S.Br (J.nat (suc n)) (J.slot n idx) → J.Tr (suc n)
  g′ z = O.Up (J.nat (suc k)) (P.src p) x nx (g (O.mvBr (P.src p) (J.slot k i)
    (subst (S.Br (J.nat (suc n))) (sym (P.slot p i)) z)))
  source-shape : O.Up (J.nat (suc k)) (P.src p) x nx (S.Ω (J.slot k i) g) ≡ S.Ω (J.slot n idx) g′
  source-shape = In.source-node (suc n) (P.slot p i) _
  module Run
    (IH : ∀ a V Y → A.Gd m V → A.Gd m Y → A.Le m (L.Ω (L.natᴵ m)) Y →
      U.UR k i a V → A.Le m (L.suc V) Y →
      U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx (g (J.inB k i a)))
        (L.ψ pc ρ (L.add X σ (f (L.into (L.<→◃ q) Y))))) where
    row : ∀ a V Y → A.Gd (I.rank n idx) V → A.Gd (I.rank n idx) Y →
      A.Le (I.rank n idx) (L.Ω (L.natᴵ (I.rank n idx))) Y → U.UR n idx a V →
      A.Le (I.rank n idx) (L.suc V) Y → D.U (g′ (J.inB n idx a)) (F′ (L.into (L.<→◃ qt) Y))
    row a V Y gv gy o ha t = subst₂ (U.U (suc n))
      (sym (cong (λ z → O.Up (J.nat (suc k)) (P.src p) x nx (g z)) (P.br p i a)))
      (sym (cong (λ z → L.ψ pc ρ (L.add X σ (f z))) (input Y)))
      (IH (P.pullS p i a) (P.pullR p i V) (T.τ T.bwd m (P.pullR p i Y))
        (G.good V gv) (G.τ-good Y gy) (G.τ-floor Y o) (G.rel a V ha) (G.τ-margin V Y gy t))
    result : U.U (suc n) (O.Up (J.nat (suc k)) (P.src p) x nx (S.Ω (J.slot k i) g))
      (L.ψ pc ρ (L.add X σ (L.limᵢ q f)))
    result = subst₂ (U.U (suc n)) (sym source-shape) (sym ref-shape) (D.un idx row)

module Model where
  p : P.Path 2 1
  p = P.down P.top
  Ω₁ = L.Ω (L.natᴵ 1)
  Ω₃ = L.Ω (L.natᴵ 3)
  x = O.Ωt (J.nat 2)
  nx = O.Ωt-nz (J.nat 2)
  ε : L.Simᴵ (L.natᴵ 2) (L.natᴵ 3)
  ε q = L.suc q
  σ₁ : L.Simᴵ (L.natᴵ 1) (L.natᴵ 3)
  σ₁ q = L.suc (L.suc q)
  σ₀ : L.Simᴵ L.zero (L.natᴵ 1)
  σ₀ q = L.suc q
  σg : L.Simᴵ L.zero (L.natᴵ 3)
  σg q = L.suc (L.suc (L.suc q))
  g : J.Tr 0 → J.Tr 1
  g a = S.up S.zero tt (S.suc a) (O.z◃s a)
  f : I.T 0 → I.T 1
  f Y = L.add Ω₁ σ₀ Y
  module N = Node 3 L.zero (λ q → q) ε p F.zero x nx Ω₃ g f
  module C = Ground.Frame 1 3 L.zero (λ q → q)
  hx : U.U 2 x (C.φ Ω₃)
  hx = UB.weakU 2 (UB.ΩU 2) (Omega.two 2 3 L.zero (λ q → q))
  IH : ∀ a V Y → A.Gd 0 V → A.Gd 0 Y → A.Le 0 (L.suc L.zero) Y →
    U.UR 0 F.zero a V → A.Le 0 (L.suc V) Y → U.U 2 (O.Up (J.nat 1) (P.src p) x nx (g a)) (C.φ (L.add Ω₃ σ₁ (f Y)))
  IH a V Y gv gy o ha t = UB.weakU 2
    (C.bound (O.down (P.src p) tt) nx A.actual₃ hx σg (≼-trans (s≼s ha) t))
    (C.mono (B.trans 3 F.zero {X = L.add Ω₃ σg Y}
      {Y = L.add (L.add Ω₃ σ₁ Ω₁) σg Y} {Z = L.add Ω₃ σ₁ (f Y)}
      (Add.mono 3 0 {X = Ω₃} {X′ = L.add Ω₃ σ₁ Ω₁}
        (Right.right 3 1 (B.rfl 3 F.zero {X = Ω₃} A.actual₃) σ₁ Ω₁ A.actual₁) σg Y Y (≼-refl Y))
      (Compose.compose 3 1 0 Ω₃ σ₁ Ω₁ σ₀ Y A.actual₃ A.actual₁ tt)))
  actual : U.U 2 (O.Up (J.nat 1) (P.src p) x nx (O.Ωt (J.nat 1)))
    (C.φ (L.add Ω₃ σ₁ (Ω₁ L.+ Ω₁)))
  actual = N.Run.result IH
```
