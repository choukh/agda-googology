# YiXVSourceSlots
> 验收文件。编译定理：保留分派交目标 Fin、rank 与全输入 cv 等式；未交世界或 Goal。
> 复用 YiASIface.Sbᶠ；feed 与 kcase 按 YiASProofLow.gen/kcase 在 J.nat 坐标上加强改写。两份 fin 在抽象 n 下不定义性相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceSlots where
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiASProofLow using (sb≤)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSelfInput as Model

pth : ∀ {n j} → Sbᶠ n j → J.nat j P.≤ J.nat n
pth s0 = P.self
pth (ss s) = P.ins (pth s)
slot-path : ∀ n i → Sbᶠ (suc n) (I.rank n i)
slot-path n F.zero = ss s0
slot-path zero (F.suc ())
slot-path (suc n) (F.suc i) = ss (slot-path n i)
feed : ∀ n i (Φ : ∀ k → k P.≤ J.nat (suc n) → S.Tr k) →
  S.fromBr (J.nat (suc n)) (J.slot n i)
    (Φ (S.at (J.nat (suc n)) (J.slot n i)) (P.posW (J.nat (suc n)) (J.slot n i))) ≡
      J.inB n i (Φ (J.nat (I.rank n i)) (pth (slot-path n i)))
feed n F.zero Φ = refl
feed zero (F.suc ()) Φ
feed (suc n) (F.suc i) Φ = feed n i (λ k w → Φ k (P.ins w))

kcase₀ : ∀ {n} (s : Sbᶠ (suc n) zero) (i : F.Fin (suc n)) (ε : P.Ev (J.nat (suc n))) (ρ : P.Rt (J.nat (suc n)))
  {X : Set} (Q : X → Set) {K : (q : S.Pos S.zero) → (S.Br S.zero q → S.Br (J.nat (suc n)) (J.slot n i)) → X} {d : X} →
  Q d → Q (Fold.kp (J.nat (suc n)) ε ρ (J.slot n i) (pth s) K d)
kcase₀ (ss s) F.zero ε ρ Q hd = hd
kcase₀ {n = suc n} (ss s) (F.suc i) ε ρ Q hd = kcase₀ s i ε ρ Q hd

kcase₊ : ∀ {n j} (s : Sbᶠ (suc n) (suc j)) (i : F.Fin (suc n)) (ε : P.Ev (J.nat (suc n))) (ρ : P.Rt (J.nat (suc n)))
  {X : Set} (Q : X → Set)
  {K : (q : S.Pos (J.nat (suc j))) → (S.Br (J.nat (suc j)) q → S.Br (J.nat (suc n)) (J.slot n i)) → X} {d : X} →
  (suc j ≤ I.rank n i → Q d) →
  (∀ (k : F.Fin (suc j)) (cv : S.Br (J.nat (suc j)) (J.slot j k) → S.Br (J.nat (suc n)) (J.slot n i))
    (e : I.rank j k ≡ I.rank n i) →
    (∀ a → cv (J.inB j k a) ≡ J.inB n i (Relation.Binary.PropositionalEquality.subst J.Tr e a)) → Q (K (J.slot j k) cv)) →
  Q (Fold.kp (J.nat (suc n)) ε ρ (J.slot n i) (pth s) K d)
kcase₊ s0 i ε ρ Q dr kc = kc i (λ z → z) refl (λ a → refl)
kcase₊ (ss s) F.zero ε ρ Q dr kc = dr (sb≤ s)
kcase₊ {n = suc n} (ss s) (F.suc i) ε ρ Q dr kc = kcase₊ s i ε ρ Q dr kc

actual-keep : Fold.kp (J.nat 3) (Model.ev 3) (Model.rt 3) (J.slot 2 (F.suc (F.suc F.zero)))
  (pth (ss s0)) (λ q cv → 1) 0 ≡ 1
actual-keep = kcase₊ (ss s0) (F.suc (F.suc F.zero)) (Model.ev 3) (Model.rt 3) (λ x → x ≡ 1)
  (λ ()) (λ k cv e h → refl)
```
