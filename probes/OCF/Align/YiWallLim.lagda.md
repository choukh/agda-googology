# YiWall：极限行所需的外延实例及其边界

这是障碍审计，不改冻结接口。先只取 `FoldRows0` 的极限行和有界位置律。
所得函数等式限于**同一合法 LF 列的两套证书，经同一个算子求值所得的列**。
它没有量化任意两列 Raw 函数，也没有从逐点相等推出任意函数相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiWallLim where

open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Empty
import Data.Sum.Base
import Data.Unit.Base
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2bBase as B
import OCF.Align.YiK2cIrr as I
open F using (module G)

-- 只投影旧接口的两个字段，不改其定义域、公共界或目标关系。
record LimPosition : Set where
  field
    eval : B.Source0 → A.R
    lim-row : ∀ f r st l q →
      eval (I.pack (F.lim f) r (st , l) q) ≡
      G.lim (λ n → eval (I.pack (f n) (r n) (l n) (q n)))
    position : ∀ a b →
      C.Common (C.term (B.original a)) (C.term (B.original b)) →
      V.CP (C.term (B.original a)) (C.term (B.original b)) →
      C.RawStep F.zero (eval a) (eval b)

from-fold : B.FoldRows0 → LimPosition
from-fold d = record
  { eval = B.FoldRows0.ψ d
  ; lim-row = B.FoldRows0.lim-row d
  ; position = B.FoldRows0.bounded-position d
  }

module Required (d : LimPosition) where
  open LimPosition d

  pointwise : ∀ x r r′ l l′ q q′ →
    eval (I.pack x r l q) ≡ eval (I.pack x r′ l′ q′)
  pointwise x r r′ l l′ q q′ = B.raw-antisym
    (C.RawStep.path (position (I.pack x r l q) (I.pack x r′ l′ q′)
      (C.common x l V.self V.self) V.self))
    (C.RawStep.path (position (I.pack x r′ l′ q′) (I.pack x r l q)
      (C.common x l V.self V.self) V.self))

  sequence : ∀ (f : ℕ → F.LF)
    (r r′ : ∀ n → C.Carry (f n))
    (st st′ : ∀ n → V.CP (f n) (f (suc n)))
    (l l′ : ∀ n → V.Legal (f n)) (q q′ : ∀ n → B.Only0 (f n)) →
    (λ n → eval (I.pack (f n) (r n) (l n) (q n))) ≡
    (λ n → eval (I.pack (f n) (r′ n) (l′ n) (q′ n)))
  sequence f r r′ st st′ l l′ q q′ = I.lim-equality-reflects
    (trans (sym (lim-row f r st l q))
      (trans (pointwise (F.lim f) r r′ (st , l) (st′ , l′) q q′)
        (lim-row f r′ st′ l′ q′)))
```

公共界逐次就是该合法源树本身。`sequence` 是所要求的窄外延实例，
而且可以取每一位置的实际 Source 都不相等的族，不是先偷用 Source 相等。

```agda
actual-sequences : (d : LimPosition) (α β : ℕ → ℕ) →
  (λ n → LimPosition.eval d (I.actual (α n))) ≡
  (λ n → LimPosition.eval d (I.actual (β n)))
actual-sequences d α β = Required.sequence d (λ n → I.child)
  (λ n → I.child-carry) (λ n → I.child-carry)
  (λ n → V.self) (λ n → V.self)
  (λ n → I.child-legal (α n)) (λ n → I.child-legal (β n))
  (λ n → I.child-only) (λ n → I.child-only)

actual-inputs-differ : ∀ (n : ℕ) → I.actual zero ≡ I.actual (suc zero) →
  Data.Empty.⊥
actual-inputs-differ n = I.actual-sources-differ
```

## 两字段前提的可满足性：一个有意遗漏 gt 的对照

下面只用于证明前提非空：沿第一支裁去 lc，零、后继、极限仍结构递归。
它不是 ψ 候选，不交 gt 行，不修补实现。其换证书函数相等为 `refl`。
所以把上面的窄结论直接称为“完整函数外延公理不可缺少”没有依据。

```agda
cut : F.LF → A.R
cut F.zero = A.one
cut (F.suc x) = A.successor (cut x)
cut (F.lim f) = G.lim (λ n → cut (f n))
cut (F.lc k c t g) = cut t

cut-cp : ∀ {x y} → V.CP x y → F.Cp F.zero (cut x) (cut y)
cut-cp V.self = Data.Sum.Base.inj₁ refl
cut-cp (V.suc p) = Data.Sum.Base.inj₂ (1 , cut-cp p)
cut-cp (V.lim n p) = Data.Sum.Base.inj₂ (n , cut-cp p)
cut-cp (V.fst p) = cut-cp p

cut-positive : ∀ x → F.Dn F.zero G.zero (cut x)
cut-positive F.zero = Data.Sum.Base.inj₁ refl
cut-positive (F.suc x) = zero , Data.Sum.Base.inj₁ refl
cut-positive (F.lim f) = zero , Data.Sum.Base.inj₂ (cut-positive (f zero))
cut-positive (F.lc k c t g) = cut-positive t

cut-legal : ∀ x → V.Legal x → F.Lgl F.zero (cut x)
cut-legal F.zero l = Data.Unit.Base.tt
cut-legal (F.suc x) l =
  A.copies-step (cut x) (Data.Sum.Base.inj₂ (cut-positive x)) ,
  A.copies-legal (cut x) (cut-legal x l)
cut-legal (F.lim f) (st , l) =
  (λ n → cut-cp (st n)) , (λ n → cut-legal (f n) (l n))
cut-legal (F.lc k c t g) (lk , first , mono , irr , lt , lg) = cut-legal t lt

cut-instance : LimPosition
cut-instance = record
  { eval = λ s → cut (C.term (B.original s))
  ; lim-row = λ f r st l q → refl
  ; position = λ a b common p → record
      { path = cut-cp p
      ; target-legal = cut-legal (C.term (B.original b)) (C.lawful (B.original b))
      }
  }

cut-sequence-refl : ∀ (f : ℕ → F.LF)
  (r r′ : ∀ n → C.Carry (f n)) (l l′ : ∀ n → V.Legal (f n))
  (q q′ : ∀ n → B.Only0 (f n)) →
  (λ n → LimPosition.eval cut-instance (I.pack (f n) (r n) (l n) (q n))) ≡
  (λ n → LimPosition.eval cut-instance (I.pack (f n) (r′ n) (l′ n) (q′ n)))
cut-sequence-refl f r r′ l l′ q q′ = refl
```

**范围／判断。** 未推出对任意 `ℕ → Raw zero` 的函数外延，也未证明
这种推广不可能。当前证明的两边必须来自同一 f；任意逐点相等的两列
LF 不能直接作为同一 f，字面 CP 也不会把逐点等式自动提升为极限树相等。
完整 `FoldRows0` 未给实例；不拿这个未实填记录作可满足性说明。
`cut-instance` 只实填本篇确实用到的两字段，证书非空由 I 的闭实例实填。
