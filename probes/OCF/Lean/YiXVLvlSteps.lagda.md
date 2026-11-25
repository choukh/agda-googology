# YiXVLvlSteps
> 验收文件。档位：编译定理。原 HSr 步进的字面代表性质；每个原 lvl 都满足 Strong。
> 按 YiLSRead.St≺/st-dn/lt≺ 与 Level.sim/<ᴵ-dec 的现有计算证明；未交可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVLvlSteps where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVLiteralSim as M

preserve : ∀ {x y} (d : S.zero S.⊢ x ◃ y) {a : L.Ordᶜ L.zero} (h : L.HS a) (p : a L.≺ Read.read x) →
  M.Literal (L.toLevel-≺ h (Read.HSr x) p) → M.Literal (L.toLevel-≺ h (Read.HSr y) (Read.◃⊑ d p))
preserve S.◃s h p hp = M.succ _ hp
preserve (S.◃l n) h p hp = M.limit n _ hp
preserve (S.◃w {p = ()}) h p hp
preserve (S.◃u x () y e) h p hp
preserve (S.◃c x () e) h p hp
preserve (S.◃t d e) h p hp = preserve e h (Read.◃⊑ d p) (preserve d h p hp)
source : ∀ {x y} (d : S.zero S.⊢ x ◃ y) → M.LitSim (L.toLevel-⊑ (Read.HSr x) (Read.HSr y) (Read.◃⊑ d))
source {x = S.zero} d ()
source {x = S.suc x} {y} d q = M.successor
  (L.toLevel-≺ (Read.HSr x) (Read.HSr y) (Read.◃⊑ d (L.≺z (L.≅-refl⁰ (Read.read x)))))
  (preserve d (Read.HSr x) (L.≺z (L.≅-refl⁰ (Read.read x))) refl) q
source {x = S.lim f a} d (L.lim n q) = source (S.◃t (S.◃l n) d) q
source {x = S.Ω () g} d q
source {x = S.up x () y e} d q

Strong : L.Ordᴵ → Set
Strong L.zero = ⊤
Strong (L.suc a) = Strong a
Strong (L.lim f s) = ((n : ℕ) → Strong (f n)) × ((n : ℕ) → M.LitSim (s n))
read-strong : ∀ x → Strong (T.lvl x)
read-strong S.zero = tt
read-strong (S.suc x) = read-strong x
read-strong (S.lim f a) = (λ n → read-strong (f n)) , (λ n → source (a n))
read-strong (S.Ω () g)
read-strong (S.up x () y e)
```
