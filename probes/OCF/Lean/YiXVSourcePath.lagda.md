# YiXVSourcePath
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourcePath where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVSourceIndex as J

data Path (n : ℕ) : ℕ → Set where
  top : Path n n
  down : ∀ {k} → Path n (suc k) → Path n k
src : ∀ {n k} → Path n k → O.Dn (J.nat n) (J.nat k)
src top = O.stop
src (down p) = O.down (src p) tt
σ : ∀ {n k} → Path n k → L.Simᴵ (L.natᴵ k) (L.natᴵ n)
σ top q = q
σ (down p) q = σ p (L.suc q)
inc : ∀ {n k} → Path (suc n) (suc k) → F.Fin (suc k) → F.Fin (suc n)
inc top i = i
inc (down p) i = inc p (F.suc i)
level : ∀ {n k} (p : Path (suc n) (suc k)) i → I.rank n (inc p i) ≡ I.rank k i
level top i = refl
level (down p) i = level p (F.suc i)
slot : ∀ {n k} (p : Path (suc n) (suc k)) i → O.mv (src p) (J.slot k i) ≡ J.slot n (inc p i)
slot top i = refl
slot (down p) i = slot p (F.suc i)
pullS : ∀ {n k} (p : Path (suc n) (suc k)) i → J.Tr (I.rank n (inc p i)) → J.Tr (I.rank k i)
pullS p i a = subst J.Tr (level p i) a
pullR : ∀ {n k} (p : Path (suc n) (suc k)) i → I.T (I.rank n (inc p i)) → I.T (I.rank k i)
pullR p i X = subst I.T (level p i) X
br : ∀ {n k} (p : Path (suc n) (suc k)) i a →
  O.mvBr (src p) (J.slot k i) (subst (S.Br (J.nat (suc n))) (Relation.Binary.PropositionalEquality.sym (slot p i)) (J.inB n (inc p i) a)) ≡
    J.inB k i (pullS p i a)
br top i a = refl
br (down p) i a = br p (F.suc i) a

cast-q : ∀ {a b n} (e : a ≡ b) → L.natᴵ a L.<ᴵ L.natᴵ n → L.natᴵ b L.<ᴵ L.natᴵ n
cast-q refl q = q
bound : ∀ {n k} (p : Path (suc n) (suc k)) i → cast-q (level p i) (J.q n (inc p i)) ≡ σ p (J.q k i)
bound top i = refl
bound (down p) i = bound p (F.suc i)
```
