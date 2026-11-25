# YiXVSourceEmbed
> 验收文件。档位：编译定理。有限层源嵌入的模拟证书、有限 Ω 倍数界及 Γ 链界。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceEmbed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (γ; Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVFiniteUpAdd as Up

Ω : ∀ n → I.T n
Ω n = L.Ω (L.natᴵ n)
up-Ω : ∀ n → A.Le (suc n) (L.up L.zero (Ω n)) (Ω (suc n))
up-Ω n = D.pack (D.gu (B.actual n)) (B.actual (suc n)) (D.aa (D.refl (D.gu (B.actual n))))
  where module D = A.Layer n (A.GoFam n) (A.LeFam n)
M : ∀ n → ℕ → I.T n
M n zero = L.zero
M n (suc k) = Ω n L.+ M n k
mg : ∀ n k → A.Gd n (M n k)
mg n zero = B.gz n F.zero
mg n (suc k) = Add.plus-good n {X = Ω n} {Y = M n k} (B.actual n) (mg n k)
up-M : ∀ n k → A.Le (suc n) (L.up L.zero (M n k)) (M (suc n) k)
up-M n zero = D.pack (D.gu (B.gz n F.zero)) D.gz D.uZ
  where module D = A.Layer n (A.GoFam n) (A.LeFam n)
up-M n (suc k) = D.trans (Up.up-add n n (Ω n) (λ q → q) (M n k) (B.actual n) (mg n k))
  (Add.plus (suc n) {X = L.up L.zero (Ω n)} {X′ = Ω (suc n)} {Y = L.up L.zero (M n k)} {Y′ = M (suc n) k}
    (up-Ω n) (up-M n k))
  where module D = A.Layer n (A.GoFam n) (A.LeFam n)

E : ∀ {n m} → Sbᶠ n m → I.T m → I.T n
E s0 X = X
E {n = suc n} (ss s) X = L.add (Ω (suc n)) (λ q → L.suc q) (E s X)
eg : ∀ {n m} (s : Sbᶠ n m) X → A.Gd m X → A.Gd n (E s X)
eg s0 X gx = gx
eg {n = suc n} (ss s) X gx = Add.good (suc n) n {X = Ω (suc n)} (B.actual (suc n)) (λ q → L.suc q) (E s X) (eg s X gx)
embed : ∀ {n m} (s : Sbᶠ n m) {x X} (nx : J.nat m S.⊢ S.zero ◃ x) → A.Gd m X → U.U m x X →
  U.U n (Path.emb (J.nat n) (Default.ev n) (Slots.pth s) x nx) (E s X)
embed s0 nx gx h = h
embed {n = suc n} (ss s) nx gx h = U.Layer.uu (B.actual (suc n)) U.Layer.uz (eg s _ gx) (embed s nx gx h)

weight : ∀ {n m} → Sbᶠ n m → ℕ
weight s0 = 2
weight (ss s) = suc (weight s)
cap : ∀ {n m} → Sbᶠ n m → I.T n
cap {m = m} s = E s (Ω m L.+ Ω m)
cap-good : ∀ {n m} (s : Sbᶠ n m) → A.Gd n (cap s)
cap-good {m = m} s = eg s _ (Add.plus-good m {X = Ω m} {Y = Ω m} (B.actual m) (B.actual m))
cap-bound : ∀ {n m} (s : Sbᶠ n m) → A.Le n (cap s) (M n (weight s))
cap-bound {n} s0 = B.rfl n F.zero {X = Ω n L.+ Ω n} (cap-good s0)
cap-bound {n = suc n} {m} (ss s) = D.trans (Add.mono (suc n) n {X = Ω (suc n)} {X′ = Ω (suc n)}
  (B.rfl (suc n) F.zero {X = Ω (suc n)} (B.actual (suc n))) (λ q → L.suc q) (cap s) (M n (weight s)) (cap-bound s))
  (Add.plus (suc n) {X = Ω (suc n)} {X′ = Ω (suc n)} {Y = L.up L.zero (M n (weight s))} {Y′ = M (suc n) (weight s)}
    (D.refl (B.actual (suc n))) (up-M n (weight s)))
  where module D = A.Layer n (A.GoFam n) (A.LeFam n)

idx : ℕ → ℕ
idx zero = zero
idx (suc k) = suc (suc (idx k))
module Bound (n : ℕ) where
  module G = Gamma.At n
  base : ∀ k → A.Le n (Ω n) (γ n k)
  base zero = B.rfl n F.zero {X = Ω n} (B.actual n)
  base (suc k) = B.trans n F.zero {X = Ω n} {Y = γ n k} {Z = γ n (suc k)} (base k) (G.next k)
  double : ∀ {X} k → A.Le n X (γ n k) → A.Le n (X L.+ X) (γ n (suc (suc k)))
  double {X} k t = B.trans n F.zero {X = X L.+ X} {Y = γ n k L.+ Ψ n (γ n k)} {Z = γ n (suc (suc k))}
    (Add.plus n {X = X} {X′ = γ n k} {Y = X} {Y′ = Ψ n (γ n k)} t
      (B.trans n F.zero {X = X} {Y = γ n k} {Z = γ n (suc k)} t (G.next k)))
    (G.step k (B.rfl n F.zero {X = γ n k} (G.good k)))
  mult : ∀ k → A.Le n (M n k) (γ n (idx k))
  mult zero = B.z≤ n F.zero {Y = Ω n} (B.actual n)
  mult (suc k) = B.trans n F.zero {X = M n (suc k)} {Y = γ n (idx k) L.+ γ n (idx k)} {Z = γ n (idx (suc k))}
    (Add.plus n {X = Ω n} {X′ = γ n (idx k)} {Y = M n k} {Y′ = γ n (idx k)} (base (idx k)) (mult k))
    (double (idx k) (B.rfl n F.zero {X = γ n (idx k)} (G.good (idx k))))
  result : ∀ {m} (s : Sbᶠ n m) → A.Le n (cap s) (γ n (idx (weight s)))
  result s = B.trans n F.zero {X = cap s} {Y = M n (weight s)} {Z = γ n (idx (weight s))} (cap-bound s) (mult (weight s))

actual : U.U 3 (Path.emb (J.nat 3) (Default.ev 3) (Slots.pth (ss (ss s0))) (O.Ωt (J.nat 1)) (O.Ωt-nz (J.nat 1))) (cap (ss (ss s0)))
actual = embed (ss (ss s0)) (O.Ωt-nz (J.nat 1)) (Add.plus-good 1 {X = Ω 1} {Y = Ω 1} (B.actual 1) (B.actual 1)) (UB.ΩU 1)
```
