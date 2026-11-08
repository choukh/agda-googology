# 原始全混合第二层的最高反馈坐标动作

直接使用原 M.put 和 M.Fold。最高坐标的目标是第 1 层，其旧种类全
保留；这里对任意前缀、任意第 1 层坐标证明实际动作的全部世界单调。
这是统一有限层归纳的第二层实例，不替代全 n 输出合法性义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedMixedSecondCoordinate where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T; P)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
import OCF.Lean.BoundedContextClosed as C
import OCF.Align.BoundedFoldValueMixed as M

pt : hs hz ⊲[ C.w ] C.B
pt = hLim (hlim 2 hself) (hsuc hself)

module Action (A : HB M.S) where
  prefix : HB (T (hs hz))
  prefix = M.Fold.fold (hs hz) pt A

  run : HB (T (hs hz)) → HB (T (hs hz))
  run c = M.Fold.fold (hs hz) pt (A ⊞ M.put 2 (up c))

  position : ∀ {a b W} → a ⊲[ W ] b → run a ⊲[ W ] run b
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim zero hself)
  position (hlim n p) = hlim n (position p)
  position (hLim {κ = inj₁ κ} b p) = hLim b (position p)
  position (hLim {κ = inj₂ _} b p) = hLim b (position p)

  legal : LgB prefix → ∀ c → LgB c → LgB (run c)
  legal la hz l = la
  legal la (hs c) l = LegalSum.sum-legal (T (hs hz)) _ (λ n → legal la c l)
  legal la (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal la (f n) (l n))
  legal la (hΩ (inj₁ κ) g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → legal la (g _) (l lw b))
  legal la (hΩ (inj₂ _) g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → legal la (g _) (l lw b))

  legal-chain : LgB prefix → ∀ n → LgB (chain run n)
  legal-chain la zero = tt
  legal-chain la (suc n) = Lg-⊞ _ _ (legal-chain la n)
    (legal la _ (legal-chain la n))

module Initial = Action hz
initial-chain : ∀ n → LgB (chain Initial.run n)
initial-chain = Initial.legal-chain tt

-- 第零分量的实际保留像，为非零前缀提供合法证据。
base : HB (T hz) → HB (T (hs hz))
base c = M.Fold.fold (hs hz) pt (M.put 0 c)
base-position : ∀ {a b W} → a ⊲[ Data.Product.proj₁ W ] b → base a ⊲[ W ] base b
base-position hself = hself
base-position (hsuc p) = ⊲ᴮ-tr (base-position p) (hlim zero hself)
base-position (hlim n p) = hlim n (base-position p)
base-position (hLim b p) = hLim b (base-position p)
base-legal : ∀ c → LgB c → LgB (base c)
base-legal hz l = tt
base-legal (hs c) l = LegalSum.sum-legal (T (hs hz)) _ (λ n → base-legal c l)
base-legal (hl f) (st , l) = (λ n → base-position (st n)) , (λ n → base-legal (f n) (l n))
base-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → base-position (mo (Data.Product.proj₁ lw) b b′ p)) ,
  (λ lw b → base-legal (g _) (l (Data.Product.proj₁ lw) b))

branch : HB (T hz) → HB (T (hs hz))
branch c = M.Fold.fold (hs hz) pt (M.floor 0 ⊞ M.put 1 (up c))
branch-position : ∀ {a b W} → a ⊲[ Data.Product.proj₁ W ] b → branch a ⊲[ W ] branch b
branch-position hself = hself
branch-position (hsuc p) = ⊲ᴮ-tr (branch-position p) (hlim zero hself)
branch-position (hlim n p) = hlim n (branch-position p)
branch-position (hLim b p) = hLim b (branch-position p)
branch-legal : ∀ c → LgB c → LgB (branch c)
branch-legal hz l = base-legal (flL P) (Lg-flL P)
branch-legal (hs c) l = LegalSum.sum-legal (T (hs hz)) _ (λ n → branch-legal c l)
branch-legal (hl f) (st , l) = (λ n → branch-position (st n)) , (λ n → branch-legal (f n) (l n))
branch-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → branch-position (mo (Data.Product.proj₁ lw) b b′ p)) ,
  (λ lw b → branch-legal (g _) (l (Data.Product.proj₁ lw) b))

prefix-legal : LgB (M.Fold.fold (hs hz) pt (M.sums 1))
prefix-legal =
  (λ lw b b′ p → branch-position p) ,
  (λ lw b → branch-legal _ (lgB⊲ b (Data.Product.proj₁ lw) (Data.Product.proj₂ lw)))

module Actual = Action (M.sums 1)
actual-coordinate-legal : ∀ n → LgB (chain Actual.run n)
actual-coordinate-legal = Actual.legal-chain prefix-legal
```

坐标类型包含前缀的全部 Ω 与第 1 层新增 Ω。proof 使用源第 2 分量
导出的实际路径 pt，未替换为另一个目标路径。前缀合法前提有 A=0
的实例；实际 A=M.sums 1 的前缀也已给出合法证据，故其整条实际最高
坐标反馈链合法。折到第 0 层的输出动作并非这里的 run，且全自然数
归纳尚未完成。未改动运行器、源输入或种类支持。
