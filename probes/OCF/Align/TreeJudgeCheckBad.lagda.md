# 树侧判据: 拒绝的测试 (错的树, 与读法的对照)

> **检验旧树的文件.** 不干净 (经 `GuardTightAccept`, `LvCertNeg`). 判据的定义不在这里. 结论写在 [TreeJudge](TreeJudge.lagda.md). **这里全部是有限测试 (`refl`): `just` 说取样里有一对指纹相同, 界不同.** 定理在 [TreeJudgeNeg](TreeJudgeNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeCheckBad where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightAccept using (xΩ₁; Cf-xΩ₁; Tc-x1; x2; Cf-x2; Tc-x2)
open import OCF.Align.GuardTightBase using (Tc-id)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (suc; s≈)
import OCF.Align.GuardTightTree as G
import OCF.Align.TreeJudgeNoTrim as N
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeCheck using (rd)

-- 恒等读法 (`Tc-id`) 与紧的读法同一个折叠
t2id t21id : Z
t2id = G.T₀ x2 Cf-x2 (Tc-id x2)
t21id = G.T₀ (suc x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2)) (Tc-id (suc x2))

-- 没有 `trim`
n11 n2 n21 : Z
n11 = N.T₀ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) Tc-x1
n2 = N.T₀ x2 Cf-x2 Tc-x2
n21 = N.T₀ (suc x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2)) Tc-x2
```

## §1 恒等读法: 被拒绝

$\Omega\cdot2$ 上已经违反: 路径 $[500,0]$ 界 1, 路径 $[500,1,101,0,1,1]$ 界 2. 指纹深度 9.

```agda
hf-t2id : run 9 9 2 (rd t2id) ≡ just (vio (500 ∷ 0 ∷ []) 1 (500 ∷ 1 ∷ 101 ∷ 0 ∷ 1 ∷ 1 ∷ []) 2)
hf-t2id = refl

hf-t21id : run 9 9 2 (rd t21id) ≡ just (vio (0 ∷ []) 1 (1 ∷ 101 ∷ 0 ∷ 0 ∷ 500 ∷ 1 ∷ 1 ∷ []) 2)
hf-t21id = refl
```

## §2 没有 `trim`: 被拒绝, 但不在 $\Omega+1$

**`trim` 的错误, 这个判据在 $\Omega\cdot2$ 看到 (`hf-n2`, `hf-n21`), 指纹深度 9 仍在.** $\Omega+1$ 上没有违反 (`hf-n11`). 一致性: [TreeJudgeBase](TreeJudgeBase.lagda.md) 的 `force-≃` 说只差界的两棵树值相同, 所以没有 `trim` 的害处不在值, 在窗口.

```agda
hf-n11 : run 9 7 2 (rd n11) ≡ nothing
hf-n11 = refl

hf-n2 : run 9 9 2 (rd n2) ≡ just (vio (101 ∷ 1 ∷ 0 ∷ []) 1 (101 ∷ 1 ∷ 1 ∷ 101 ∷ 0 ∷ 0 ∷ 0 ∷ []) 2)
hf-n2 = refl

hf-n21 : run 9 9 2 (rd n21) ≡ just (vio (0 ∷ 101 ∷ 1 ∷ 0 ∷ []) 1 (0 ∷ 101 ∷ 1 ∷ 1 ∷ 101 ∷ 0 ∷ 0 ∷ 0 ∷ []) 2)
hf-n21 = refl

-- Bachmann 的取样看不见它: 与带 `trim` 的树计数相同 (`reg-t21`). 所以这一条拒绝不了
reg-n21 : reg 6 20 3 2 [] (rd n21) ≡ okv 42 172
reg-n21 = refl
```
