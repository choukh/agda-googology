# 任意塔高的实际反馈更新可连续套用

第四层，无条件。每降两层可任选这个运行的更新次数和反馈位置，把当时的整组独立重置值带到较低塔的每个零槽。在最内第二塔，实际返回容纳从所得预算起连续取下一个 h 不动点的全部有限次迭代。外部塔号和询问均可变。[单位返回入口](W4ReturnCarryUnit.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4TowerLaw where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; l≼; ≼l; z≼; +-mono; ≼-+ʳ)
import W4Block as W
import W4Path as P
import W4Fold as F
open import WVOne using (T₀; read)
import B12Terminal as T
import B12ActualSlots as Cv
import B18Product as M
import B20Room as R
import B27Joint as J
import Survey.W4ReturnCarry as C
import Survey.W4ReturnCarryUnit as Unit
import Survey.W4RoomDerivative as D

expand : T₀ → T₀
expand x = x M.· L.ωᶜ

module Sum (m : ℕ) (b : F.Base (W.tw (suc m))) (x : T₀) where
  module A = C.At.Orbit m b x
  prefix : ∀ n → x M.· L.natᶜ n ≼ A.total n
  prefix zero = z≼
  prefix (suc n) = +-mono {a = x M.· L.natᶜ n} {a′ = A.total n} {b = x} {b′ = x L.+ A.unit (suc n)}
    (prefix n) (≼-+ʳ x (A.unit (suc n)))
  all : expand x ≼ A.budget
  all = l≼ λ n → ≼l {f = A.total} n (prefix n)

number : ℕ → ℕ
number zero = 1
number (suc d) = suc (suc (number d))
level = λ d → suc (number d)

record Funded (n : ℕ) : Set where
  field
    run : T.Run (W.tw n)
    standard : T.Run.ok run ≡ P.Ok-tw n
    covered : Cv.Covered run
    amount : T₀
    high : R.Room run amount
  value = read (T.value run)
open Funded

module Lower (m : ℕ) (a : Funded (suc (suc m))) where
  module A = C.At.Actual m (run a) (standard a) (covered a) (amount a) (high a)
  module U = A.Use
  choice : ℕ → ℕ → Funded m
  run (choice n u) = U.Selected.target n u
  standard (choice n u) = U.Selected.standard n u
  covered (choice n u) = U.Selected.covered n u
  amount (choice n u) = U.reserve n
  high (choice n u) = U.Selected.common n u
  into : ∀ n u → value (choice n u) ≼ value a
  into = A.into

  paid : ∀ n → W.iter expand (amount a) (suc n) ≼ U.reserve n
  paid zero = Sum.all m U.initialB (amount a)
  paid (suc n) = ≼-trans {b = expand (U.reserve n)} (M.mono (paid n) (≼-refl L.ωᶜ))
    (Sum.all m (U.M.S n) (U.reserve n))

Choices : ℕ → Set
Choices zero = Data.Unit.Base.⊤ where import Data.Unit.Base
Choices (suc d) = (ℕ × ℕ) × Choices d

last : ∀ d → Funded (level d) → Choices d → Funded 2
last zero a e = a
last (suc d) a ((n , u) , e) = last d (Lower.choice (level d) a n u) e

within : ∀ d a e → value (last d a e) ≼ value a
within zero a e = ≼-refl (value a)
within (suc d) a ((n , u) , e) = ≼-trans (within d (Lower.choice (level d) a n u) e) (Lower.into (level d) a n u)

-- 只取序数乘法可读出的共同部分；last 的实际预算还保留了逐项重置值。
size : ∀ d → Choices d → T₀ → T₀
size zero e x = x
size (suc d) ((n , u) , e) x = size d e (W.iter expand x (suc n))

mono : ∀ n {x y} → x ≼ y → W.iter expand x n ≼ W.iter expand y n
mono zero q = q
mono (suc n) q = M.mono (mono n q) (≼-refl L.ωᶜ)

budget : ∀ d a e {x} → x ≼ amount a → size d e x ≼ amount (last d a e)
budget zero a e q = q
budget (suc d) a ((n , u) , e) {x} q = budget d (Lower.choice (level d) a n u) e
  (≼-trans {b = W.iter expand (amount a) (suc n)} (mono (suc n) q) (Lower.paid (level d) a n))

output : ∀ d a e {x} → x ≼ amount (last d a e) → D.block x ≼ value a
output d a e {x} q = ≼-trans (D.Second.block-in (run t) (standard t) (covered t) x
  (λ w → ≼-trans q (high t w))) (within d a e)
  where t = last d a e

module Actual (d extra j : ℕ) where
  module Q = Unit.Host (number d) extra j
  start : Funded (level d)
  run start = Q.r
  standard start = Q.okay
  covered start = Q.cv
  amount start = Q.x
  high start = Q.high
  exact : ∀ e → D.block (amount (last d start e)) ≼ J.f Q.k j
  exact e = ≼-trans (output d start e (≼-refl _)) Q.into
  ordinal : ∀ e → D.block (size d e Q.x) ≼ J.f Q.k j
  ordinal e = ≼-trans (output d start e (budget d start e (≼-refl Q.x))) Q.into
```
