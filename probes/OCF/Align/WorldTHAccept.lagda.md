# 高度进世界: 验收 (记号只在本文件)

> 入口 [WorldTH](WorldTH.lagda.md). **没有基本列验收, 没有前驱结构验收, 没有序数值验收**: 树与记号之间没有定理. 这里两件事: (1) 记号一侧的基本列 (定理, 只关于记号), 与 `WorldTHInst.Shape` 并排看; (2) 有限测试, 比较器 `same d w` / `fpO d w`: 深度 $d$, 宽度 $w$, 只读形状. 盲区: 只看前 $w$ 项, 只看前 $d$ 层, 形状相同不等于树相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EBO using (ψ; Ωt; Ωs; fsn; cof; cΩ; cω)
open import OCF.Align.CrossMAccept using (u; ψ₀; ψ₁; Ω₁; tψΩ; tψΩ1; fs-ψΩ1-0; fs-ψΩ1-1)
open import OCF.Align.CumUpAcceptF using (same)
open import OCF.Align.CumReadAccept using (fpO)
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadCF using (azero; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; g₀)
open import OCF.Align.CumUp using (TΩ)
open import OCF.Align.WorldTHW using (Tψ; ht; top)
open import OCF.Align.CrossMClosed using (T⊤)
open import OCF.Align.WorldTHInst using (T₀; T₁; at)
```

## §1 记号的基本列

$\psi_0(\Omega_{u+1})$ 的基本列是 $\psi_u$ 的折叠链, 与 `Shape.fs₀`, `fs₁`, `fs₂` 同形. $u$ 按约定写成 $\Omega^2$.

```agda
fs₂ : fsn tψΩ1 2 ≡ ψ₀ (ψ u (ψ u (Ωt u) ∷ []) ∷ [])
fs₂ = refl

-- 顶行: u 的共尾度是 Ω₁, 这是树上 top 的分支由 Gw 下标给出的依据 (判断)
cof-u : cof u ≡ cΩ []
cof-u = refl
```

## §2 有限测试

`same d w x y`: 深度 $d$, 宽度 $w$ 的形状相同.

**回归.** 高度为 1 的行对 `CumUp` 的 $\psi_0(\Omega_\Omega)$: 高度换成世界里的下标, 这一行形状没变.

```agda
R₁ : Ord₀
R₁ = Tψ (ht one) azero one g₀ (z⊲ one , C.self)

t-row1 : same 8 2 R₁ TΩ ≡ true
t-row1 = refl
```

**这一站的第 1 项.** 下面 `T₁[i]` 是树的第 $i$ 项, 只读形状. 第 0 项就是 `T₀`; 第 1 项的第 0 项的第 1 项又是 `T₀`, 这就是 "折叠 $\Omega_u$ 本身": 第 1 项的里层 $\psi_u(\Omega_u)$ 的第一支是 $\psi_u(1)=\Omega_u\cdot\omega$, 它的第 1 项是 $\Omega_u$. 记号一侧的 `fs-ψΩ1-1` 同形. 这是形状的对照, 严格增长的证据是定理 `T₀≺T₁`.

```agda
T₁[0] T₁[1] T₁[1][0] T₁[1][0][1] : Ord₀
T₁[0] = at T₁ 0
T₁[1] = at T₁ 1
T₁[1][0] = at T₁[1] 0
T₁[1][0][1] = at T₁[1][0] 1

t-0 : same 8 2 T₁[0] T₀ ≡ true
t-0 = refl

t-101 : same 8 2 T₁[1][0][1] T₀ ≡ true
t-101 = refl

-- 对照: 比较器分得开
t-1 : same 3 2 T₁[1] T₀ ≡ false
t-1 = refl

t-T : same 3 2 T₁ T₀ ≡ false
t-T = refl

t-10 : same 4 2 T₁[1][0] T₀ ≡ false
t-10 = refl
```

**对 `T⊤`.** 只记录形状在深度 3 就不同. 这不说明谁大: `T⊤` 不在这一族里, 两族之间没有定理.

```agda
t-⊤₂ : same 2 2 T₀ T⊤ ≡ true
t-⊤₂ = refl

t-⊤₃ : same 3 2 T₀ T⊤ ≡ false
t-⊤₃ = refl
```
