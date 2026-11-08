# 原运行器的第二层输出动作保合法

Reg只用于固定seed1下的位置证明；LgB单独用于真实合法回灌分支。
两者不相互替代，不要求非法world上的一般Ω单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedTargetRegAction where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (P)
open import OCF.Lean.BoundedTargetRegIf
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
import OCF.Lean.BoundedContextClosed as C
import OCF.Align.BoundedFoldValueMixed as M

module Action (A : HB M.S) where
  prefix : HB Base
  prefix = M.Fold.fold hz (z⊲ᴮ C.B) A
  run : HB Layer → HB Base
  run c = M.Fold.fold hz (z⊲ᴮ C.B) (A ⊞ M.put 2 (up c))

  position : ∀ {a b W} → Reg b → a ⊲[ (W , one) ] b → run a ⊲[ W ] run b
  position r hself = hself
  position r (hsuc p) = ⊲ᴮ-tr (position r p) (hlim zero hself)
  position r (hlim n p) = hlim n (position (r n) p)
  position r (hLim {κ = inj₁ κ} b p) = hLim b (position (r _) p)
  position (mo , r) (hLim {κ = inj₂ _} b p) =
    ⊲ᴮ-tr (position (r _) p)
      (⊲ᴮ-tr (position (r one) (mo b hself b)) (hlim zero hself))

  legal : LgB prefix → ∀ c → Reg c → LgB c → LgB (run c)
  legal la hz r l = la
  legal la (hs c) r l = LegalSum.sum-legal Base _ (λ n → legal la c r l)
  legal la (hl f) r (st , l) =
    (λ n → position (r (suc n)) (st n)) , (λ n → legal la (f n) (r n) (l n))
  legal la (hΩ (inj₁ κ) g) r (mo , l) =
    (λ lw b b′ p → position (r _) (mo (lw , tt) b b′ p)) ,
    (λ {w = W} lw b → legal la (g _) (r _) (l {w = (W , one)} (lw , tt) b))
  legal la (hΩ (inj₂ _) g) (mono , r) (mo , l) =
    LegalSum.sum-legal Base (λ n → feedback (chain feedback n)) legal-output
    where
    feedback : HB Base → HB Base
    feedback d = run (g d)
    feedback-legal : ∀ d → LgB d → LgB (feedback d)
    feedback-legal d ld = legal la (g d) (r d) (l (lw₀L P , ld) hself)
    legal-chain : ∀ n → LgB (chain feedback n)
    legal-chain zero = tt
    legal-chain (suc n) = Lg-⊞ (chain feedback n) (feedback (chain feedback n))
      (legal-chain n) (feedback-legal (chain feedback n) (legal-chain n))
    legal-output : ∀ n → LgB (feedback (chain feedback n))
    legal-output n = feedback-legal (chain feedback n) (legal-chain n)
```

此定理对任意实际源前缀A成立，前提只要求原运行器已将A折成合法树。
co分支的合法世界为 `(w₀L P,d)`，d就是当前真实反馈坐标；不是零替代。
