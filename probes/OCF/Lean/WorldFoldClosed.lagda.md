# 折叠闭项与第一条值定理

常值一分支的节点折成 ω（序数值验收，非 ψ₀Λ）。另交一个读取整个坐标
的非恒定节点，但其完整值未证。此处值关系沿用已有普通布劳威尔序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldFoldClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; LgB)
open import OCF.Lean.NegFab6Idx using (W; wz; ws; wl; wn)
open import OCF.Lean.WorldFoldIf
open import OCF.Lean.WorldFoldRun
open import OCF.Lean.NegFab6Sim using (_≼_; z≼; s≼s; l≼; ≼l; ≼s; ≼-refl)

nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ω : Cd
ω = hl nat

one-node : W hz
one-node = wn (λ e p → ws wz)

T : Cd
T = run one-node

legal-T : LgB T
legal-T = run-legal one-node

ones : ∀ n → partial (λ _ → hs hz) n ≡ nat (suc n)
ones zero = refl
ones (suc n) = cong hs (ones n)

T≤ω : T ≼ ω
T≤ω = l≼ (λ n → subst (λ x → x ≼ ω) (Relation.Binary.PropositionalEquality.sym (ones n)) (≼l (suc n) (≼-refl _)))

ω≤T : ω ≼ T
ω≤T = l≼ (λ n → ≼l n (subst (λ x → nat n ≼ x) (Relation.Binary.PropositionalEquality.sym (ones n)) (≼s (≼-refl _))))

embed : ∀ {B} → Cd → W B
embed hz = wz
embed (hs a) = ws (embed a)
embed (hl f) = wl (λ n → embed (f n))

coordinate-node : W hz
coordinate-node = wn (λ e p → ws (embed e))

U : Cd
U = run coordinate-node

legal-U : LgB U
legal-U = run-legal coordinate-node

-- 有限测试：分支确实读取坐标，不是常值分支。
branch0 : run (ws (embed {hs hz} hz)) ≡ hs hz
branch0 = refl
branch1 : run (ws (embed {hs (hs hz)} (hs hz))) ≡ hs (hs hz)
branch1 = refl
```

下一硬义务：当前 `W` 只有可数坐标的一种节点，不能把它重新命名为 Λ
来跨过多种类折叠。没有高层坐标类型或内部 View 的合法性，不应开始
塔的强度声明。`CountableFold` 是可运行解释器，其后继规则为恒等，
不是 ψ 的闭包规则。它只证明世界类型索引没有阻止这类回灌递归。
