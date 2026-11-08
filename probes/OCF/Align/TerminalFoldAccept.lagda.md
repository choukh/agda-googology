# 终点折叠的完整 EBO 值验收接线

**第 4 层验收文件：导入记号，不进入成品及其证书。** 本篇直接使用
`EboLean3Tree` 的完整 Ω 塔参照，保构造子转成现有 `Cd`；没有新增
序数记号或值关系。所用 `Fold1If._≤ᵛ_` 在此全为可数树，没有 Ω 规则。
这是已有参照与已有值序的接线，不是新强度结果，也不证明任一现有候选
已满足全塔覆盖。错位取站是充分条件，不声称每种终点证明都必须这样做。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TerminalFoldAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)
import OCF.Lean.CRw as C
import OCF.Align.EboLean3Tree as E
import OCF.Align.EboLeanDef as N

read : E.Ord → Cd
read E.zero = hz
read (E.suc a) = hs (read a)
read (E.lim f) = hl (λ n → read (f n))

referenceBranch : ℕ → Cd
referenceBranch k = read (E.tree (E.hc-tower k))

reference : Cd
reference = read E.EBO-tree″

reference-shape : reference ≡ hl referenceBranch
reference-shape = refl

-- 无额外记录参数或未填字段：全部参照支的下界足够。
all-branches : ∀ {T : Cd} → (∀ k → referenceBranch k ≤ᵛ T) → reference ≤ᵛ T
all-branches cover = l≤ cover

sampled : ∀ {T : Cd} (stage : ℕ → Cd) →
  (∀ k → Σ ℕ (λ n → referenceBranch k ≤ᵛ stage n)) →
  (∀ n → stage n ≤ᵛ T) → reference ≤ᵛ T
sampled stage choose upper = all-branches (λ k → go (choose k))
  where
  go : ∀ {k} → Σ ℕ (λ n → referenceBranch k ≤ᵛ stage n) → referenceBranch k ≤ᵛ _
  go (n , lower) = ≤ᵛ-trans lower (upper n)

-- 实际非空实例：完整原参照自身，不借用任何候选覆盖假设。
branch-in-reference : ∀ k → referenceBranch k ≤ᵛ reference
branch-in-reference k = ≤l k (≤ᵛ-refl (referenceBranch k))

reference-self : reference ≤ᵛ reference
reference-self = all-branches branch-in-reference

reference-sampled : reference ≤ᵛ reference
reference-sampled = sampled referenceBranch
  (λ k → k , ≤ᵛ-refl (referenceBranch k)) branch-in-reference
```

## FGH 核对

两端使用各自原有的 FGH。这里证明构造子转换保 FGH，避免把终点参照
接错；该等式并不把今后的序数值下界升级为任意候选的 FGH 下界。

```agda
iter-agree : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) →
  ∀ x k → C.iter f x k ≡ N.iter g x k
iter-agree eq x zero = refl
iter-agree {f} eq x (suc k) = trans (cong f (iter-agree eq x k)) (eq _)

read-fgh : ∀ a n → C.FGH (read a) n ≡ E.FGH a n
read-fgh E.zero n = refl
read-fgh (E.suc a) n = iter-agree (read-fgh a) n n
read-fgh (E.lim f) n = read-fgh (f n) n

branch-fgh : ∀ k n → C.FGH (referenceBranch k) n ≡ N.fgh (N.EBOψ k) (E.hc-tower k) n
branch-fgh k n = trans (read-fgh (E.tree (E.hc-tower k)) n) (E.fgh-tree (E.hc-tower k) n)

reference-fgh : ∀ n → C.FGH reference n ≡ N.fgh (N.EBOψ n) (E.hc-tower n) n
reference-fgh n = trans (read-fgh E.EBO-tree″ n) (E.fgh-EBO″ n)
```

最终成品仍须独立给出 `T : Cd`、其合法证书和内部中间层 View。
本篇的 `all-branches` 或 `sampled` 只负责完整 EBO 值下界；不允许把
高层同值经任意 ψ 搬运，也不从 raw/legal 分支覆盖自动推出原折叠观察覆盖。
