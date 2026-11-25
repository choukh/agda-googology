# YiXVSourceIndex
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceIndex where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as P
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I

nat : ℕ → S.L
nat = O.iter S.suc S.zero
Tr : ℕ → Set
Tr n = S.Tr (nat n)
slot : ∀ n (i : F.Fin (suc n)) → S.Pos (nat (suc n))
slot n F.zero = inj₁ tt
slot zero (F.suc ())
slot (suc n) (F.suc i) = inj₂ (slot n i)
q : ∀ n i → L.natᴵ (I.rank n i) L.<ᴵ L.natᴵ (suc n)
q n F.zero = L.zero
q zero (F.suc ())
q (suc n) (F.suc i) = L.suc (q n i)
inB : ∀ n i → Tr (I.rank n i) → S.Br (nat (suc n)) (slot n i)
inB n F.zero x = x
inB zero (F.suc ()) x
inB (suc n) (F.suc i) x = inB n i x
outB : ∀ n i → S.Br (nat (suc n)) (slot n i) → Tr (I.rank n i)
outB n F.zero x = x
outB zero (F.suc ()) x
outB (suc n) (F.suc i) x = outB n i x
out-in : ∀ n i x → outB n i (inB n i x) ≡ x
out-in n F.zero x = refl
out-in zero (F.suc ()) x
out-in (suc n) (F.suc i) x = out-in n i x
in-out : ∀ n i x → inB n i (outB n i x) ≡ x
in-out n F.zero x = refl
in-out zero (F.suc ()) x
in-out (suc n) (F.suc i) x = in-out n i x
first : ∀ n i → inB n i S.zero ≡ S.br0 (nat (suc n)) (slot n i)
first n F.zero = refl
first zero (F.suc ())
first (suc n) (F.suc i) = first n i
at : ∀ n i → S.at (nat (suc n)) (slot n i) ≡ nat (I.rank n i)
at n F.zero = refl
at zero (F.suc ())
at (suc n) (F.suc i) = at n i
```
