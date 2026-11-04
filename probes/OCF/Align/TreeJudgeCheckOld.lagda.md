# 树侧判据: `Z` 的旧副本上的测试

> **检验旧树的文件.** `UniformLvTree` 的 `T₀` 与 `ScafLadderQ` 的 `Tᵠ` 用的是 `Z` 的另外两份 (`OCF.Align.Prefix`, `ScafLadderZPrefix`), 这里各写一个 `rd`. 不干净 (经旧文件的导入链). 判据的定义不在这里. **全部是有限测试.** `T₀` 的拒绝定理是 `reject-uniformLv` ([TreeJudgeNeg](TreeJudgeNeg.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeCheckOld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (Ordᴵ; _⊑ᴵ_; ⊑ᴵ-refl; ⊑ᴵ-trans; Sim→⊑ᴵ)
import OCF.Align.Level as FL
import OCF.Align.Prefix as AP
import OCF.Align.ScafLadderZPrefix as QP
open import OCF.Align.UniformLvTree using (T₀)
open import OCF.Align.LvCertNeg using (c₀; cfD)
import OCF.Align.ScafLadderQ as Q
open import OCF.Align.TreeJudgeObs

toN : Ordᴵ → ℕ
toN FL.zero = 0
toN (FL.suc a) = suc (toN a)
toN (FL.lim f s) = toN (f 1)

iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = FL.suc (iterᴵ c k)

up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → FL.suc q))

rdA : AP.Z → Obs
rdA AP.Z.zero = o0
rdA (AP.Z.suc x) = os (rdA x)
rdA (AP.Z.lim f) = ol (λ n → rdA (f n))
rdA (AP.Z.ĉᴸ c t₀ g o₀ o) = oc (toN c) (rdA t₀) (rdA o₀) (λ k → rdA (o (iterᴵ c k) (up⊑ k)))

rdQ : QP.Z → Obs
rdQ QP.Z.zero = o0
rdQ (QP.Z.suc x) = os (rdQ x)
rdQ (QP.Z.lim f) = ol (λ n → rdQ (f n))
rdQ (QP.Z.ĉᴸ c t₀ g o₀ o) = oc (toN c) (rdQ t₀) (rdQ o₀) (λ k → rdQ (o (iterᴵ c k) (up⊑ k)))
```

## §1 拒绝: `UniformLvTree` 的 `T₀`

$\psi_0(\Omega_{\Omega\cdot2+1})$. 这棵树的违反正是 `noW` 的形状: 同一条路径, 一个走第一支 (500), 一个走分支 (100), 界 1 与 2. 这条测试独立于 `noCert₂`.

```agda
tu : AP.Z
tu = AP.toZ (T₀ c₀ cfD)

hf-u : run 9 7 2 (rdA tu) ≡ just (vio (1 ∷ 500 ∷ 1 ∷ 500 ∷ 0 ∷ 1 ∷ []) 1 (1 ∷ 100 ∷ 1 ∷ 500 ∷ 0 ∷ 1 ∷ []) 2)
hf-u = refl
```

## §2 接受: `ScafLadderQ` 的 `Tᵠ`

高度分块的塔. 这棵树的证书走标签路线 (`TΩ·-label`), 所以 "接受" 这一半不算记号无关. 这里只有同头同界的测试.

```agda
tq : (m : ℕ) (α : Ordᴵ) → QP.Z
tq m α = QP.toZ (Q.Tᵠ m α {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)

tqω : QP.Z
tqω = QP.toZ (Q.Tω {FL.zero} {FL.suc FL.zero} (tt , (λ q → q)) FL.zero)

hf-q1 : run 9 7 2 (rdQ (tq 0 FL.zero)) ≡ nothing
hf-q1 = refl
hf-q2 : run 9 7 2 (rdQ (tq 1 FL.zero)) ≡ nothing
hf-q2 = refl
hf-q21 : run 9 7 2 (rdQ (tq 1 (FL.suc FL.zero))) ≡ nothing
hf-q21 = refl
hf-qω : run 9 7 2 (rdQ tqω) ≡ nothing
hf-qω = refl
```

**没跑完的:** `tq 2 zero` ($\Omega\cdot3$) 即使 深 7 指纹 7 也超过 80 秒, 深 9 指纹 7 超过 170 秒, 深 9 指纹 9 的版本 (连同其他几棵) 跑了 36 分钟没结束, 我停了它. **无结果, 不是通过.** 间接: `qa-3` ([GuardTightAccept](GuardTightAccept.lagda.md)) 说这棵树与 `t3` 到深 9 界一致, `hf-t3` ([TreeJudgeCheck](TreeJudgeCheck.lagda.md)) 说 `t3` 不违反. 这里指纹用 7, 不是 9, 因为塔计值慢.
