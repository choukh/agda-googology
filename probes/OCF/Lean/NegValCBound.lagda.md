# NegValC (二): 对接口 `ValC⊥` 的边界定理

> 不含记号. 入口 [NegValC](NegValC.lagda.md). 对构造一路 ValC 的接口 [ValCIf](ValCIf.lagda.md) (定稿 2026-11-06 01:41, 本路不改它) 的记录 `ValC⊥` 说话: 对**一切**满足律的实例. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延. 导入 [NegValCInst](NegValCInst.lagda.md) (Fab5 关系的移植, 用于 `fab5-port-excluded`).
>
> 1. **`pull` (定理, 对一切实例).** 值关系被锚拉住: 第 $m$ 层上 `Le m x y` 且 $x, y$ 值合法, 则 $x, y$ 以界 $0$ 折到第 $0$ 层后在标准前序 (`TLRuleSpec._≤_`) 下 $\le$. 由 `Φ-mono` (目标 $0$) 与 `sound₀`. 所以接口**不是盲的**: `Le m` 包含于 "折到第 0 层后的值序" 的拉回.
> 2. **`Mo-one` (定理).** 每个合法层号上 $1$ 值合法 (由 `Mo-Φ` 与 `Mo-top`, `Mo-hz`: $1$ 是第 $m+1$ 层的 $0$ 以地板为界折到第 $m$ 层的输出). **`no-triv` (定理).** 每个合法层号上 `¬ Le m 1 0`. 推论: 处处为 `⊤` 的关系不是实例.
> 3. **`rep-not-mono` (定理, 对一切实例, 一切合法层号, 一切值合法的 $x$).** 若 $\lim(x,x,x,\dots)$ 也值合法, 则 `¬ Le m (lim (x, x, …)) x`. 原因是累加: 折到第 0 层, 左边是 $\lim(\Phi x,\ \Phi x\boxplus\Phi x,\ \dots)$, 由 `one≤Φ` 它 $\ge \Phi x+1$. **`l≤-excl` (推论).** 若 `Le m` 对 "ℕ-极限在左边" 封闭 (Fab5 的规则 `l≤`), 则对一切值合法的 $x$, $\lim(x,x,\dots)$ 不值合法. **`fab5-port-excluded` (推论).** 不存在实例, 它的 `Le m` 包含 Fab5 关系 (搬到 CRw, 任一坐标关系 `cr`, 任一世界) 且 `Mo m` 包含 Fab5 的 `Mo`: Fab5 的原样移植不是实例.
>
> **前提实例.** 本篇的定理对一切 `V : ValC⊥` 成立; 实例由构造一路给出 (本篇写成时还没有). 在没有实例时 1, 2 与 3 的前两条空真, `fab5-port-excluded` 仍是有内容的否定 (它说的是 "不存在"). 其余前提: 合法层号 (`LgB m`) 例如 $m = 1, 2$, `lim(1,2,3,…)`; 值合法的 $x$: $0$ (`Mo-hz`), $1$ (`Mo-one`), 地板 `top b⊥ m` (`Mo-top`); `l≤` 封闭: Fab5 的关系有构造子 `l≤`; `cr`: `NegValCInst.cr⊥`, `cr⁺ cr⊥`.
>
> **只否定什么.** 只否定: 平凡关系是实例 (`no-triv`); 含 `l≤` 的关系与含相邻项相同的 ℕ-极限的值合法同时成立 (`l≤-excl`, `fab5-port-excluded`). **不否定**: 接口可满足 (构造一路去证); 收窄的值合法 (只收值严格的 ℕ-极限) 与含 `l≤` 的关系同时成立; 路线引理 `route` 本身 (本篇没有找到它在强制值合法的输入上的反例, 也没有证它).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.NegValCBound (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCIf I
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as TL
import OCF.Lean.NegValCInst as NI
```

## §1 第 0 层的两条小引理 (`TLRuleSpec` 上)

```agda
toA-≤⊞ : ∀ a b → toA a TL.≤ toA (a ⊞ b)
toA-≤⊞ a hz = TL.≤-refl _
toA-≤⊞ a (hs b) = TL.≤-suc (toA-≤⊞ a b)
toA-≤⊞ a (hl f) = TL.≤l 0 (toA-≤⊞ a (f 0))
toA-≤⊞ a (hΩ () _)

-- 右边至少是 1, 和就至少多一个后继
one-step : ∀ a b → asuc azero TL.≤ toA b → asuc (toA a) TL.≤ toA (a ⊞ b)
one-step a hz ()
one-step a (hs b) p = TL.s≤ (toA-≤⊞ a b)
one-step a (hl f) p with TL.≤lim⁻ p
... | n , q = TL.≤l n (one-step a (f n) q)
one-step a (hΩ () _) p
```

## §2 对一切实例

`F₀ m lm x`: 第 $m$ 层以界 $0$ 折到第 $0$ 层 (第 0 层的地板就是 $0$, 所以 "界在地板之上" 是自反).

```agda
module _ (V : ValC⊥) where
  open ValC⊥ V

  F₀ : ∀ m → LgB m → L m → Cd
  F₀ m lm x = F m lm hz (z⊲ᴮ m) hz x

  pull : ∀ m lm {x y} → Mo m x → Mo m y → Le m x y → toA (F₀ m lm x) TL.≤ toA (F₀ m lm y)
  pull m lm mx my p = sound₀ (Φ-mono m lm hz (z⊲ᴮ m) (Mo-hz hz) (Mo-hz hz) (le-refl hz hz) (le-refl hz hz) mx my p)

  Mo-one : ∀ m → LgB m → Mo m (hs hz)
  Mo-one m lm = Mo-Φ (hs m) lm m (hsuc hself) (Mo-top m lm) (le-refl m (top b⊥ m)) hz (Mo-hz (hs m))

  no-triv : ∀ m lm → ¬ Le m (hs hz) hz
  no-triv m lm p = TL.irr (asuc azero) (TL.≤-trans (TL.≤l 1 (TL.≤-refl _)) (pull m lm (Mo-one m lm) (Mo-hz m) p))

  rep-not-mono : ∀ m lm x → Mo m x → Mo m (hl (λ _ → x)) → ¬ Le m (hl (λ _ → x)) x
  rep-not-mono m lm x mx mL p =
    TL.irr (toA (F₀ m lm x))
      (TL.≤-trans (TL.≤l 1 (one-step (F₀ m lm x) (F₀ m lm x) (sound₀ (one≤Φ m lm hz (z⊲ᴮ m) hz x))))
                  (pull m lm mL mx p))

  -- 特例 x = 1: lim(1,1,…) 与 1
  no-l11 : ∀ m lm → Mo m (hl (λ _ → hs hz)) → ¬ Le m (hl (λ _ → hs hz)) (hs hz)
  no-l11 m lm mL = rep-not-mono m lm (hs hz) (Mo-one m lm) mL

  LClosed : Cd → Set
  LClosed m = ∀ {f : ℕ → L m} {y} → (∀ n → Le m (f n) y) → Le m (hl f) y

  l≤-excl : ∀ m lm → LClosed m → ∀ x → Mo m x → ¬ Mo m (hl (λ _ → x))
  l≤-excl m lm lc x mx mL = rep-not-mono m lm x mx mL (lc (λ n → le-refl m x))
```

**Fab5 的原样移植不是实例.** 对任一层号 $m$, 第 $m$ 层上任一坐标关系 `cr` 与世界 $w$: 若 `Le m` 包含 Fab5 的关系, `Mo m` 包含 Fab5 的 `Mo`, 则矛盾 ($\lim(1,1,\dots)$ 在 Fab5 的 `Mo` 下值合法, 在 Fab5 的关系下 $\le 1$).

```agda
  fab5-port-excluded : ∀ m lm (cr : NI.CR (Lev b⊥ m)) w →
    (∀ {x y} → NI.Rel._≤[_]_ cr x w y → Le m x y) →
    (∀ {x} → NI.Rel.Mo cr w x → Mo m x) → ⊥
  fab5-port-excluded m lm cr w emb mo =
    no-l11 m lm (mo (λ n → tt)) (emb (NI.l11≤one cr))
```

## 结论 (按档)

- **[定理, 对一切 `I`, 一切 `V : ValC⊥`]** `pull`, `Mo-one`, `no-triv`, `rep-not-mono`, `no-l11`, `l≤-excl`, `fab5-port-excluded`.
- **[定理]** `toA-≤⊞`, `one-step` (第 0 层).
- **[判断]** 构造一路的关系要么不含无限制的 `l≤`, 要么值合法排除相邻项相同的 ℕ-极限 (或两者都收窄到值严格的 ℕ-极限). 哪一种能让 `route` 成立, 本篇不判定.
