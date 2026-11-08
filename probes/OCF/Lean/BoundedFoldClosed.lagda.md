# 真正含旧 Ω 的非恒定回灌闭项

本例仅用后继新种类，但其反馈坐标在第一步就保留前缀地板的 Ω。
一般高层折叠合法性仍未证明；本例直接对实际分支和轨道证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf
open import OCF.Lean.BoundedFoldRun
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)

module F = Run hz tt (hs hz) tt
S = Safe hz (hs hz)

j : HB (T hz) → HB S
j hz = hz
j (hs c) = hs (j c)
j (hl f) = hl (λ n → j (f n))
j (hΩ κ g) = hΩ (inj₁ κ , tt) (λ c → j (g c))

j-position : ∀ {a b W} → a ⊲[ proj₁ W ] b → j a ⊲[ W ] j b
j-position hself = hself
j-position (hsuc p) = hsuc (j-position p)
j-position (hlim n p) = hlim n (j-position p)
j-position (hLim e p) = hLim e (j-position p)

j-legal : ∀ c → LgB c → LgB (j c)
j-legal hz l = l
j-legal (hs c) l = j-legal c l
j-legal (hl f) (st , l) = (λ n → j-position (st n)) , (λ n → j-legal (f n) (l n))
j-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → j-position (mo (proj₁ lw) b b′ p)) ,
  (λ lw b → j-legal (g _) (l (proj₁ lw) b))

act : HB (T hz) → HB (T hz)
act c = F.fold hz (hsuc hself) (j c)

act-position : ∀ {a b W} → a ⊲[ W ] b → act a ⊲[ W ] act b
act-position hself = hself
act-position (hsuc p) = ⊲ᴮ-tr (act-position p) (hlim 0 hself)
act-position (hlim n p) = hlim n (act-position p)
act-position (hLim e p) = hLim e (act-position p)

act-legal : ∀ c → LgB c → LgB (act c)
act-legal hz l = tt
act-legal (hs c) l = LegalSum.sum-legal (T hz) _ (λ n → act-legal c l)
act-legal (hl f) (st , l) = (λ n → act-position (st n)) , (λ n → act-legal (f n) (l n))
act-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → act-position (mo lw b b′ p)) ,
  (λ lw b → act-legal (g _) (l lw b))

a : HB (T hz)
a = flL P
legal-a : LgB a
legal-a = Lg-flL P

branch : HB (T hz) → HB S
branch c = j (a ⊞ c)
input : HB S
input = hΩ (inj₂ tt , tt) branch
legal-input : LgB input
legal-input =
  (λ lw b b′ p → j-position (⊞-⊲ a p)) ,
  (λ lw b → j-legal (a ⊞ _) (Lg-⊞ a _ legal-a (lgB⊲ b (proj₁ lw) (proj₂ lw))))

next : HB (T hz) → HB (T hz)
next c = act (a ⊞ c)
next-legal : ∀ c → LgB c → LgB (next c)
next-legal c l = act-legal (a ⊞ c) (Lg-⊞ a c legal-a l)

orbit-legal : ∀ n → LgB (chain next n)
orbit-legal zero = tt
orbit-legal (suc n) = Lg-⊞ (chain next n) (next (chain next n))
  (orbit-legal n) (next-legal (chain next n) (orbit-legal n))

output : HB (T hz)
output = F.fold hz (hsuc hself) input
legal-output : LgB output
legal-output = LegalSum.sum-legal (T hz) (λ n → next (chain next n))
  (λ n → next-legal (chain next n) (orbit-legal n))
```

输出停在 P，尚未折到 k 或可数层。此输入未使用 B 的 Ω 子分量，
所以不解决固定 Pos 中全部地板的可构造性；需要随分支扩世界的证书。
与先前纯轨道的区别是固定前缀 a 真正在每次原始坐标回灌中保留。
值验收另由独立文件给出，不能从含 Ω 类型名直接推强度。
