# 直接视图证书的完整 EBO 闭项与双向值验收

运行入口直接用 `wf` 和标准形证书调用新 `direct`，不先生成旧 HC
中间树。原 `hc-tower` 只出现在比较定理中。所有内部 ω 状态由冻结的
新算法产生；此实验仍读记号，不是最终记号无关成品。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedViewDirectClosed where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase using (Cd)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.EboLeanDef using (EBOψ; ΩTower; _<ᵀ_; []<)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-ψ; Ctbl; c∷; c[])
open import OCF.Align.EboLean3Omega using (wf)
open import OCF.Align.DirectedViewDirectIf using (direct)
open import OCF.Align.DirectedViewDirectBuild using (sound)
import OCF.Align.EboLean3Tree as E
import OCF.Align.TerminalFoldAccept as R
import OCF.Lean.CRw as C

normal-tower : ∀ k → NF (EBOψ k)
normal-tower k = nf-ψ n[] (E.nf-ΩT k)
  (λ i → subst (_<ᵀ ΩTower k) (sym (E.G0 k i)) (positive k))
  where
  positive : ∀ k → [] <ᵀ ΩTower k
  positive zero = []<
  positive (suc k) = []<

countable-tower : ∀ k → Ctbl (EBOψ k)
countable-tower k = c∷ c[]

branch : ℕ → E.Ord
branch k = direct (normal-tower k) (countable-tower k) (wf (normal-tower k))

program : E.Ord
program = E.lim branch

closed : Cd
closed = R.read program

branch-sound : ∀ k → Same (R.read (branch k)) (R.referenceBranch k)
branch-sound k = sound (normal-tower k) (countable-tower k)
  (wf (normal-tower k)) (E.hc-tower k)

closed-sound : Same closed R.reference
closed-sound = ll branch-sound

full-EBO : (R.reference ≤ᵛ closed) × (closed ≤ᵛ R.reference)
full-EBO = same-value (same-sym closed-sound) , same-value closed-sound

iter-cong : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ x k → C.iter f x k ≡ C.iter g x k
iter-cong p x zero = refl
iter-cong {f} {g} p x (suc k) = trans (cong f (iter-cong p x k)) (p _)

fgh-same : ∀ {a b : Cd} → Same a b → ∀ n → C.FGH a n ≡ C.FGH b n
fgh-same zz n = refl
fgh-same (ss p) n = iter-cong (fgh-same p) n n
fgh-same (ll p) n = fgh-same (p n) n

fgh : ℕ → ℕ
fgh = C.FGH closed

fgh-reference : ∀ n → fgh n ≡ C.FGH R.reference n
fgh-reference = fgh-same closed-sound
```

`full-EBO` 是全部 Ω 塔、全部内部分支的双向值定理，不是有限检查。
这次改写保留基本列，因而还可证明 FGH 逐点相等；不将此作为后续
定向简化必须逐项相同的限制。尚未据此声称导入依赖或 1513 行成本下降。
