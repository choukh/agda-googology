# 原全混合序列的最初两个部分和合法

直接引用原 M，作为更高层反馈输出动作的合法前缀。这里只补实际
递归基，不以最初两项替代全部部分和的合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedMixedFirstLegal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (P; T)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Lean.BoundedContextClosed as C

fold : HB M.S → HB (T hz)
fold = M.Fold.fold hz (z⊲ᴮ C.B)

base : HB (T hz) → HB (T hz)
base c = fold (M.put 0 c)
base-position : ∀ {a b W} → a ⊲[ W ] b → base a ⊲[ W ] base b
base-position hself = hself
base-position (hsuc p) = ⊲ᴮ-tr (base-position p) (hlim 0 hself)
base-position (hlim n p) = hlim n (base-position p)
base-position (hLim b p) = hLim b (base-position p)

base-legal : ∀ c → LgB c → LgB (base c)
base-legal hz l = tt
base-legal (hs c) l = LegalSum.sum-legal (T hz) _ (λ n → base-legal c l)
base-legal (hl f) (st , l) = (λ n → base-position (st n)) , (λ n → base-legal (f n) (l n))
base-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → base-position (mo lw b b′ p)) ,
  (λ lw b → base-legal (g _) (l lw b))

module Action (A : HB M.S) where
  run : HB (T hz) → HB (T hz)
  run c = fold (A ⊞ M.put 0 c)
  position : ∀ {a b W} → a ⊲[ W ] b → run a ⊲[ W ] run b
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim 0 hself)
  position (hlim n p) = hlim n (position p)
  position (hLim b p) = hLim b (position p)
  legal : LgB (fold A) → ∀ c → LgB c → LgB (run c)
  legal la hz l = la
  legal la (hs c) l = LegalSum.sum-legal (T hz) _ (λ n → legal la c l)
  legal la (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal la (f n) (l n))
  legal la (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → legal la (g _) (l lw b))

legal-at-zero : LgB (fold (M.sums 0))
legal-at-zero = base-legal (flL P) (Lg-flL P)

next : HB (T hz) → HB (T hz)
next c = fold (M.floor 0 ⊞ M.put 1 (up c))
next-position : ∀ {a b W} → a ⊲[ W ] b → next a ⊲[ W ] next b
next-position hself = hself
next-position (hsuc p) = ⊲ᴮ-tr (next-position p) (hlim 0 hself)
next-position (hlim n p) = hlim n (next-position p)
next-position (hLim b p) = hLim b (next-position p)

next-legal : ∀ c → LgB c → LgB (next c)
next-legal hz l = legal-at-zero
next-legal (hs c) l = LegalSum.sum-legal (T hz) _ (λ n → next-legal c l)
next-legal (hl f) (st , l) = (λ n → next-position (st n)) , (λ n → next-legal (f n) (l n))
next-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → next-position (mo lw b b′ p)) ,
  (λ lw b → next-legal (g _) (l lw b))

chain-legal : ∀ n → LgB (chain next n)
chain-legal zero = tt
chain-legal (suc n) = Lg-⊞ _ _ (chain-legal n) (next-legal _ (chain-legal n))

legal-at-one : LgB (fold (M.sums 1))
legal-at-one = LegalSum.sum-legal (T hz) (λ n → next (chain next n))
  (λ n → next-legal _ (chain-legal n))
```

没有借结构双模拟传递 LgB；每条结论直接针对原 fold。Action 的前缀
条件已有 M.floor 0 与 M.sums 1 两个非零实例，供更高输出动作复用。
