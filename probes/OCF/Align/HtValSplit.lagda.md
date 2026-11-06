# `T-Ω` 的值 (一): 闭项拆成回灌的格

> 不含记号, 不是验收文件. 入口 [HtVal](HtVal.lagda.md). 对高度 $\Omega$ (`Ωᴴ = hΩ emb`) 的折叠 (`HtFeedClosed.At Ωᴴ`) 与**任意动作** `Ac` (`Ig` 的元素) 写一次:
>
> - **`Ψ≡`** (`refl`): 闭项的第 0 层输出字面是 "动作在第一个 `n1` 上的第 0 层输出" 接 "回灌的 ℕ-和": $\Psi=1\mathbin{⨾}(s_0\mathbin{⨾}\mathrm{nl}\,(n\mapsto\mathrm{drp}\,\Delta_n))$, $\Delta_n$ 是第 $n$ 格 `κΔ` 在目标第 0 层的输出. 所以**目标第 0 层的输出只经过一个 `nκ`**: 输入 $\Omega_\Omega$ 最外的那个, 由 `RKy hz` 回灌; `RKk`, `Kp`, `Kb` (`nκ` 在非零目标上的输出) 不出现在第 0 层的输出里. 回灌的格里, `Walk` 只跑节点 $N_c$ = `ni (sL c …) (λ _ _ _ → n1)` (层 `emb c`), 它们的分支没有 `nκ`.
> - 格的层: `v n` (第 $n$ 格的世界), `a n` (第 $n$ 格从哪一层走起). `a 0 = 0`, `a (suc n) = v n` (`a-suc`, `refl`), `v (suc n) = sum (v n) (Δ n)` (`v-suc`, `refl`): 第 $n$ 格走层 $[v_{n-1}, v_n)$, 与 `SumOne` 的 `κc` 同一个骨架.
> - **`T≤lim`, `lim≤T`**: 闭项与 $\lim_n v_n$ 在树侧值序 `TLRuleSpec._≤_` 下互相 $\le$ (`drp` 只换世界, `sum-drp≤`, `≤sum-drp`).
> - `v-step`: $v_n\lhd v_{n+1}$ (字面第一位置).
>
> 实例 (`HtValAct`): 主线动作 `At.Act` 给 `T-Ω`; 换成照 `SumOne` 写 $\Omega_t$ 的动作给参照项 `T-Ω′`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValSplit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (module At; one)
```

## §1 `drp` 不改值

```agda
sum-drp≤ : ∀ {W W′} {b b′ : A} (x : D₀ W) → b ≤ b′ → sum b (drp {W} {W′} x) ≤ sum b′ x
pt-drp≤  : ∀ {W W′} {b b′ : A} (d : ℕ → D₀ W) → b ≤ b′ → ∀ n → pt b (λ m → drp {W} {W′} (d m)) n ≤ pt b′ d n
sum-drp≤ n0 e = e
sum-drp≤ n1 e = s≤ e
sum-drp≤ {W′ = W′} (x ⨾ y) e = sum-drp≤ {W′ = W′} y (sum-drp≤ {W′ = W′} x e)
sum-drp≤ (nl d) e = l≤ (λ n → ≤l n (pt-drp≤ d e n))
sum-drp≤ (ni () u) e
sum-drp≤ (nκ () u) e
sum-drp≤ (nw p x) e = sum-drp≤ x e
pt-drp≤ d e zero = e
pt-drp≤ {W′ = W′} d e (suc n) = sum-drp≤ {W′ = W′} (d n) (pt-drp≤ d e n)

≤sum-drp : ∀ {W W′} {b b′ : A} (x : D₀ W) → b ≤ b′ → sum b x ≤ sum b′ (drp {W} {W′} x)
≤pt-drp  : ∀ {W W′} {b b′ : A} (d : ℕ → D₀ W) → b ≤ b′ → ∀ n → pt b d n ≤ pt b′ (λ m → drp {W} {W′} (d m)) n
≤sum-drp n0 e = e
≤sum-drp n1 e = s≤ e
≤sum-drp {W′ = W′} (x ⨾ y) e = ≤sum-drp {W′ = W′} y (≤sum-drp {W′ = W′} x e)
≤sum-drp (nl d) e = l≤ (λ n → ≤l n (≤pt-drp d e n))
≤sum-drp (ni () u) e
≤sum-drp (nκ () u) e
≤sum-drp (nw p x) e = ≤sum-drp x e
≤pt-drp d e zero = e
≤pt-drp {W′ = W′} d e (suc n) = ≤sum-drp {W′ = W′} (d n) (≤pt-drp d e n)
```

## §2 高度 $\Omega$ 上的闭项, 对任意动作

`ΔΩ`, `ΨΩ`, `Tψ` 与 `HtFeedClosed.At` 字面相同, 只是动作 `Ac` 是参数 (`At` 里写死成 `Act`, 即 `Step`). `u′` 是 $\Omega_\Omega$ 的回灌分支: 层 $c$ 上的节点 $N_c$.

```agda
module P = At Ωᴴ Lg-Ωᴴ

u′ : ∀ {c} → azero ⊲ c → Lg c → D Ωᴴ c
u′ {c} _ _ = ni (sL {c = c} C.self hself) (λ _ _ _ → n1)

module Split (Ac : ∀ {ly W} → P.Ig ly W) where

  ΔΩ : P.Df one
  ΔΩ = P.Run accᴸ (Ωd Ωᴴ {azero}) (z⊲ one) tt hself Ac n0 P.Y₀

  ΨΩ : D₀ one
  ΨΩ = n1 ⨾ P.yc ΔΩ (P.τ₀ tt)

  Tψ : A
  Tψ = sum azero ΨΩ

  -- 第一个 n1 之后的状态与坐标
  Y₁ : P.St one
  Y₁ = P.Y₀ P.⊕⟨ tt ⟩ Ac {Ωᴴ} {one} C.self tt n0 P.Y₀

  w₁ : D Ωᴴ one
  w₁ = n0 ⨾ nw (z⊲ one) n1

  -- 第一个 n1 在目标第 0 层的输出
  s₀ : D₀ one
  s₀ = P.yc (Ac {Ωᴴ} {one} C.self tt n0 P.Y₀) (P.τ₀ tt)

  -- 回灌的第 n 格
  cell : ℕ → P.Cl one azero Ωᴴ
  cell n = P.κc accᴸ u′ (z⊲ one) tt hself Ac w₁ Y₁ n

  v a : ℕ → A
  v n = P.v (cell n)
  a n = P.a (cell n)

  lv : ∀ n → Lg (v n)
  lv n = P.lv (cell n)

  Δ : ∀ n → D₀ (v n)
  Δ n = P.yc (P.κΔ accᴸ u′ hself Ac (cell n)) (P.τ₀ (lv n))
```

**拆开.** 下面三条都是 `refl`: 目标第 0 层的输出不经过 `RKk`.

```agda
  Ψ≡ : ΨΩ ≡ n1 ⨾ (s₀ ⨾ nl (λ n → drp {v n} {one} (Δ n)))
  Ψ≡ = refl

  v-zero : v 0 ≡ sum one (n0 ⨾ s₀)
  v-zero = refl

  a-zero : a 0 ≡ azero
  a-zero = refl

  v-suc : ∀ n → v (suc n) ≡ sum (v n) (Δ n)
  v-suc n = refl

  a-suc : ∀ n → a (suc n) ≡ v n
  a-suc n = refl

  v-step : ∀ n → v n ⊲ v (suc n)
  v-step n = sum-fst (v n) (Δ n)
```

**闭项是格的极限.** `Tψ` 字面是 $\lim_n p_n$, $p_0=v_0$, $p_{n+1}=p_n+\mathrm{drp}\,\Delta_n$; 与 $v_n$ 只差 `drp`.

```agda
  T≡ : Tψ ≡ alim (pt (v 0) (λ n → drp {v n} {one} (Δ n)))
  T≡ = refl

  pt≤v : ∀ n → pt (v 0) (λ m → drp {v m} {one} (Δ m)) n ≤ v n
  pt≤v zero = ≤-refl (v 0)
  pt≤v (suc n) = sum-drp≤ {W′ = one} (Δ n) (pt≤v n)

  v≤pt : ∀ n → v n ≤ pt (v 0) (λ m → drp {v m} {one} (Δ m)) n
  v≤pt zero = ≤-refl (v 0)
  v≤pt (suc n) = ≤sum-drp {v n} {one} (Δ n) (v≤pt n)

  T≤lim : Tψ ≤ alim v
  T≤lim = l≤ (λ n → ≤l n (pt≤v n))

  lim≤T : alim v ≤ Tψ
  lim≤T = l≤ (λ n → ≤l n (v≤pt n))
```

## §3 主线实例: `T-Ω`

`HtFeedClosed.T-Ω` 就是动作取 `At.Act` 时的 `Tψ` (`refl`).

```agda
open import OCF.Align.HtFeedClosed using (T-Ω)

module M = Split P.Act

T-Ω≡ : T-Ω ≡ M.Tψ
T-Ω≡ = refl

-- 主线动作在第一个 n1 上: ω·(Ω₀ ⨾ 0), Ω₀ = 1
s₀≡ : M.s₀ ≡ nl (λ _ → n1 ⨾ n0)
s₀≡ = refl
```
