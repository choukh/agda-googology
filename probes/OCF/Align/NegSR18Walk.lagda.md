# 第十八轮的否定 (工具): 回灌一格走过的路的长度给出值的下界

> 不读记号, 不依赖任何接口. 入口 [NegSR18](NegSR18.lagda.md).
>
> **(定理) `walkLow`**: `nκ` 回灌的一格 (`HtFeedFold.Walk`) 沿世界的路径 $a\lhd b$ 逐位置运行分支. 分支的每个值都是 `n1`, 动作在第 $0$ 层目标上的输出至少把底加一 (`asuc β ≤ sum β (…)`) 时, 这一格在第 $0$ 层目标上的和至少是 $b$ (底 $\beta\ge a$). 证明对 $b$ 结构递归 (与 `Walk` 自己的递归相同): 后继位置加一, 极限位置的尾段逐段接上 (`limAux`). 不用 `Funext`.
>
> **用处.** `nκ` 在第 $0$ 层目标上回灌, 第 $0$ 格的世界是 "运行世界 + 状态的第 $0$ 层累计" (`κc` 的字面). 所以 `walkLow` 把 "累计" 变成 "值的下界": 累计越大, 输出越大. 后面几篇用它说明: 动作不读累计时, 节点的分支含 `nκ`, 分支动作 `Ai` 仍读累计 (`NegSR18Ai`, `NegSR18Z`).
>
> `hAct`: 闭项的动作 `Act` (输出 `Step`) 满足 `walkLow` 的动作前提. 常数动作 `C1` (`NegSR17Rk`) 也满足 (`≤-refl`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18Walk where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; D; D₀; n1; AccY; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (module At)
```

## 1 极限位置: 尾段逐段接上

```agda
up : ∀ (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) k j → f k ⊲ f (j + k)
up f stp k zero = C.self
up f stp k (suc j) = ⊲-tr (up f stp k j) (stp (j + k))

limAux : ∀ {V} (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) n (s₀ : A) (e : ℕ → D₀ V) → f n ≤ s₀ →
         (∀ m β′ → f (m + n) ≤ β′ → f (suc (m + n)) ≤ sum β′ (e m)) → alim f ≤ alim (pt s₀ e)
limAux f stp n s₀ e h0 hS = l≤ (λ k → ≤l k (≤-trans (⊲→≤ (subst (λ j → f k ⊲ f j) (+-comm n k) (up f stp k n))) (g k)))
  where
  g : ∀ m → f (m + n) ≤ pt s₀ e m
  g zero = h0
  g (suc m) = hS m (pt s₀ e m) (g m)
```

## 2 `walkLow`

```agda
module WL (Λ : H) (lΛ : LgH Λ) where
  open At Λ lΛ using (τ₀; St; d; yc; Walk; Ig; LW; Act)

  -- 分支的每个值都是 n1
  κ1 : ∀ {ly W₀ c} → W₀ ⊲ c → Lg c → D ly c
  κ1 _ _ = n1

  walkLow : ∀ {ly W₀ V₁} (ac : AccY ly) b {a} (p : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b) (bV : b ⊲ V₁) (lV : Lg V₁) (ll : LW ly V₁)
              (A₀ : Ig ly V₁) (co : D ly V₁) (Y : St V₁) →
            (∀ w (Y′ : St V₁) β → asuc β ≤ sum β (yc (A₀ C.self lV w Y′) (τ₀ lV))) →
            ∀ β → a ≤ β → b ≤ sum β (yc (Walk ac κ1 b p ap lb bV lV ll A₀ co Y) (τ₀ lV))
  walkLow ac b C.self ap lb bV lV ll A₀ co Y hA β h = h
  walkLow ac (asuc c) (C.suc p) ap lb bV lV ll A₀ co Y hA β h =
    ≤-trans (s≤ (walkLow ac c p ap lb (⊲-tr (C.suc C.self) bV) lV ll A₀ co Y hA β h)) (hA _ _ _)
  walkLow ac (alim f) (C.lim n p) ap (stp , wl) bV lV ll A₀ co Y hA β h =
    limAux f stp n _ _ (walkLow ac (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll A₀ co Y hA β h)
      (λ m β′ h′ → walkLow ac (f (suc (m + n))) (stp (m + n)) _ (wl (suc (m + n))) _ lV ll A₀ _ _ hA β′ h′)

  -- 闭项的动作 Act 满足动作前提
  hAct : ∀ {ly W} (lW : Lg W) (w : D ly W) (Y : St W) β → asuc β ≤ sum β (yc (Act {ly} {W} C.self lW w Y) (τ₀ lW))
  hAct lW w Y β = ≤l 1 (⊲→≤ (sum-fst (asuc β) (yc (d Y) (τ₀ lW))))
```
