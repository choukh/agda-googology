# 一致折叠的有限测试

非验收文件. **有限测试, 不是证明**: 闭实例上的归约 (`refl`, `tt`). 塔的根有见证 (`wit2` 到 `wit6`), 目标是层号自己时 `top` 保留成结点 (`keep2`, `keep3`, `keepΩ2`), 下一站丢掉的那一对现在保留 (`kept`), 极限根层没有见证且派发一律折叠 (`noWitω`, `dfinω`). 设计在 [YiLamFold](YiLamFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamTest where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  ( plus-lgl; plus-weak; add-cp; dnLc; lev; Way; keep; fold; Ext; Shift; R; ⌜_⌝
  ; iter; nodeAt; chain; Ψn; ΨN; succ; psum; self; succ-lgl; psum-lgl; ΨN-dn; ΨN-lgl
  ; Ψn-lgl; Br; acc-ind; ΩT; ΩT-lgl )
import OCF.Lean.YiNextTower as T
open import OCF.Lean.YiLamFold

------------------------------------------------------------------------
-- 有限测试 (闭实例, 归约): 塔的根都有见证; tw 2 的见证就是 p₀; 自身折叠在 top 上保留根.

IsAt : ∀ {k g} → Wit k g → Set
IsAt none = ⊥
IsAt (at _ _) = ⊤

witOf : ∀ {k g} → Lw (lc k g) → Wit k g
witOf (wΩ V w) = w

wit2 : witOf (Lw-tw 2) ≡ at (inj₁ tt) refl
wit2 = refl

wit3 : IsAt (witOf (Lw-tw 3))
wit3 = tt

wit4 : IsAt (witOf (Lw-tw 4))
wit4 = tt

wit6 : IsAt (witOf (Lw-tw 6))
wit6 = tt

IsNode : ∀ {k} → Raw k → Set
IsNode (G.lc _ _) = ⊤
IsNode _ = ⊥

-- Ω-keep 的推广: 目标是层号自己时 top 保留成根层上的结点 (tw 2, tw 3).
keep2 : IsNode (Ψ (tw 2) (Lw-tw 2) (self (tw 2)) G.top)
keep2 = tt

keep3 : IsNode (Ψ (tw 3) (Lw-tw 3) (self (tw 3)) G.top)
keep3 = tt

-- 正的根层: Ω₂ = upT 2 = lc 1 (up 1); 见证是 top 支里层号 1 的位置; 自身折叠保留根.
Ω2 : LF
Ω2 = upT (suc (suc zero))

LΩ2 : Lw Ω2
LΩ2 = Lw-Ω̂ (suc (suc zero)) tt (ws (ws w0))

witΩ2 : IsAt (witOf LΩ2)
witΩ2 = tt

keepΩ2 : IsNode (Ψ Ω2 LΩ2 (self Ω2) G.top)
keepΩ2 = tt

-- 根层是极限层号时没有见证 (自表示缺).
Lω : LF
Lω = ⌜ G.lim (λ n → iter G.suc G.zero n) ⌝

noWitω : witU Lω ≡ none
noWitω = refl

-- 链里正的目标层 (D 的缺口): Ω₂ 的 top 的链在第 1 层, 第 0 点 top 读回 upT 1 = tw 2, 下一点要把 tw 2 的 top 折到第 1 层.
-- 一律折叠的派发让根 (层号 0) 折叠; 而第 1 层有槽位 (inj₁) 可以保留.
lostD : rootW (suc zero) zero ⌜_⌝ (witOf (Lw-tw 2)) (λ _ → fold) ≡ fold
lostD = refl

couldD : Way (suc zero) zero
couldD = keep (inj₁ tt) refl

IsLim : ∀ {k} → Raw k → Set
IsLim (G.lim _) = ⊤
IsLim _ = ⊥

F1-fold : IsLim (Ψ (suc zero) (Lw-tw 2) (λ _ → fold) G.top)
F1-fold = tt

Dtest : Ext (suc zero) (tw 2)
Dtest (G.top , _ , inj₁ _) = keep (inj₁ tt) refl
Dtest _ = fold

F1-keep : IsNode (Ψ (suc zero) (Lw-tw 2) Dtest G.top)
F1-keep = tt

-- dfin 在这一对上给保留, 而且链点 1 用的就是它.
F1-auto : IsNode (Ψ (suc zero) (Lw-tw 2) (dfin (suc zero) (tw 2)) G.top)
F1-auto = tt

pt1 : Pk.co (ptsΩ (suc zero) (up (suc zero)) (λ η l → lgl→Lw (suc zero) tt (ws w0) η l) 1)
    ≡ plus (suc zero) G.top (Ψ (suc zero) (Lw-Ω̂ (suc zero) tt (ws w0)) (dfin (suc zero) (tw 2)) G.top)
pt1 = refl

-- YiNextAccTest 的那一对 (lost/could): 有限目标层上字面判定就保留, 不用比较两支的坐标.
s₂ s₂′ : Pre (tw 2)
s₂ = G.suc G.top , tt , inj₁ tt
s₂′ = G.suc G.top , tt , inj₂ (inj₁ tt)

kept : cmpw (Lw-tw 2) s₂ s₂′ ≡ keep (inj₁ tt) refl
kept = refl

-- 极限的根层上 dfin 一律折叠 (这里没有字面的判定).
dfinω : ∀ K r → dfin Lω K r ≡ fold
dfinω K r = refl
```
