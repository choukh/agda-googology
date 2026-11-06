# `T-Ω` 的值 (二): 换掉动作里的 $\Omega_t$

> 不含记号, 不是验收文件. 入口 [HtVal](HtVal.lagda.md).
>
> 高度树主线的折叠里, 可数层 $\Omega_t$ 的写法 (`HtFeedTree.Ωd`) 只在两处出现: 闭项的输入 $\Omega_\Lambda$, 与动作 `Step` 的 $S(\Omega_t\mathbin{⨾}d_t)$. 高度 $\Omega$ 的闭项的输入 $\Omega_\Omega$ 只有 `nκ` 与层 `emb c` 上的节点 $N_c$, 与 `SumOne` 的 `Ω̂₀` 同形; **所以 `T-Ω` 里可数层 $\Omega_t$ 的写法只经动作进来.**
>
> 这里写一个参照的动作 `Act′`: 同一个折叠, 同一个输入, 动作里的 $\Omega_t$ 照 `SumOneTree.Ωd` 写成 $1\mathbin{⨾}\mathrm{Dif}_t$ (`Ωd′`, 先走完更低各层的节点再放层 $t-1$ 的节点). 闭项 `T-Ω′` 是 `HtValSplit.Split Act′` 的 `Tψ`. **它只作验收的参照物, 不进主线, 不改 `HtFeedTree.Ωd`.**
>
> - `Ωd≡`: 主线的 $\Omega_{b+1}$ 是 `Ωd′` 删去中段 $\mathrm{Dif}_b$ (与开头的 `n0`), 字面 (`refl`). 所以主线的写法是参照写法的**删除**: 上界方向是 "删除不升高" 一类的单调, 下界方向要 "删掉的那段被吸收".
> - `HtValNeg.T-Ω≇T-Ω′` (定理): 换动作在结构上看得见 (沿 `EndLowTShape.path` 构造子不同). 所以两者的比较只能在值上.
> - 有限测试 (测试档, [HtValTest](HtValTest.lagda.md)): `T-Ω′` 与 `SumOne.T₀` 在 `T-Ω` 与 `T₀` 分开的那条路径上相同, 并且到更深处都相同.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValAct where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (ω⋅; one; ord; T-Ω)
open import OCF.Align.HtValSplit using (module P; module Split; module M)
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl)
```

## §1 照 `SumOne` 写的 $\Omega_t$

`Dif′ b p q l`: 从层 $a$ ($a\lhd b$) 走到层 $b$, 每个后继层 $c+1$ 放一个层 $c$ 的节点 $\sum_{z:c}1$, 极限层走 ℕ-和; 与 `SumOneTree.Dif` 逐句相同, 只是层是高度树. $\Omega$-极限的高度在高度 $\Omega$ 的折叠里不会作为 $\mathrm{Dif}$ 的层出现 (目标都是 `emb c` 或 $\Omega$ 本身), 那一句随便取 `n0`; `Ωd′` 在 $\Omega$-极限的高度上就是主线的 `Ωd`.

```agda
Dif′ : ∀ b {a L W} → a ⊲[ W ] b → b ⊲[ W ] L → LgH b → D L W
Dif′ b hself q l = n0
Dif′ (hs c) (hsuc p) q l = Dif′ c p (⊲ᴴ-tr (hsuc hself) q) l ⨾ ni (Sk (ss hself) q) (λ _ _ _ → n1)
Dif′ (hl f) (hlim n p) q (st , l) =
  Dif′ (f n) p (⊲ᴴ-tr (hlim n hself) q) (l n) ⨾
  nl (λ m → Dif′ (f (suc (m + n))) (⊲ᴴ0 (st (m + n))) (⊲ᴴ-tr (hlim (suc (m + n)) hself) q) (l (suc (m + n))))
Dif′ (hΩ g) (hLim e p) q l = n0

Ωd′ : ∀ t {W} → LgH t → D t W
Ωd′ hz l = n1 ⨾ n0
Ωd′ (hs b) l = n1 ⨾ Dif′ (hs b) (z⊲ᴴ (hs b)) hself l
Ωd′ (hl f) l = n1 ⨾ Dif′ (hl f) (z⊲ᴴ (hl f)) hself l
Ωd′ (hΩ g) l = Ωd (hΩ g)
```

**主线的写法是删除.** 层 $b+1$: 主线 $1\mathbin{⨾}N_b$, 参照 $1\mathbin{⨾}(\mathrm{Dif}_b\mathbin{⨾}N_b)$.

```agda
Ωd≡ : ∀ b {W} (l : LgH (hs b)) →
      (Ωd (hs b) {W} ≡ n1 ⨾ ni (ss hself) (λ _ _ _ → n1)) ×
      (Ωd′ (hs b) {W} l ≡ n1 ⨾ (Dif′ b (z⊲ᴴ b) (hsuc hself) l ⨾ ni (ss hself) (λ _ _ _ → n1)))
Ωd≡ b l = refl , refl
```

## §2 参照动作与参照闭项

```agda
Step′ : ∀ {W} → P.St W → P.Df W
Step′ Y = P.df (λ {t} T → ω⋅ (Ωd′ t (lgH⊲ (P.tm T) (P.lm T) Lg-Ωᴴ) ⨾ P.yc (P.d Y) T))

Act′ : ∀ {ly W} → P.Ig ly W
Act′ p lW′ _ Y = Step′ Y

module R = Split Act′

T-Ω′ : A
T-Ω′ = R.Tψ

-- 第一个 n1 上: ω·((1 ⨾ 0) ⨾ 0), 与 SumOne 的 cc 同形
s₀′≡ : R.s₀ ≡ nl (λ _ → (n1 ⨾ n0) ⨾ n0)
s₀′≡ = refl
```

## §3 换动作在结构上看得见

`HtValNeg.T-Ω≇T-Ω′` (定理): `T-Ω` 与 `T-Ω′` 不 $\cong$, 沿 `EndLowTShape.path` 构造子不同. 放在 [HtValNeg](HtValNeg.lagda.md), 这样本文件的导入闭包不含 `EndLowT*`.

## §4 第 0 格: 两边都是 $\omega$

两个动作在第一个 `n1` 上的第 0 层输出只差一个 `n0` (`HtValSplit.s₀≡`, `s₀′≡`), 所以第 0 格的层互相 $\le$. 第 1 格起就要走层 $\ge2$ 的节点, 两个动作在那里写法不同 (`Ωd≡`).

```agda
pt₀ : ∀ n → pt {one} (asuc azero) (λ _ → n1 ⨾ n0) n ≤ pt {one} (asuc azero) (λ _ → (n1 ⨾ n0) ⨾ n0) n
pt₀ zero = ≤-refl _
pt₀ (suc n) = s≤ (pt₀ n)

pt₀′ : ∀ n → pt {one} (asuc azero) (λ _ → (n1 ⨾ n0) ⨾ n0) n ≤ pt {one} (asuc azero) (λ _ → n1 ⨾ n0) n
pt₀′ zero = ≤-refl _
pt₀′ (suc n) = s≤ (pt₀′ n)

v0≤v0′ : M.v 0 ≤ R.v 0
v0≤v0′ = l≤ (λ n → ≤l n (pt₀ n))

v0′≤v0 : R.v 0 ≤ M.v 0
v0′≤v0 = l≤ (λ n → ≤l n (pt₀′ n))
```
