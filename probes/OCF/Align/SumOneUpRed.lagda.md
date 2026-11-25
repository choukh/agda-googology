# `SumOne.T₁` 的上界 (四): 对参照树, 与剩下的前提

> **验收文件. 判决: 上界未走通, 不是否定.** 参照 `Ref₁ = fr CtxMonoAccept.Ref` (标签 $\psi_0(\Omega_{\Omega+1})$). 定理: 站 `Sω`, `S¹` 在参照之下 (`Sω≼Ref`, `S¹≼Ref`). 条件定理: `fb-upper` (一格的步进 `CellStep` 推出 $\psi_0(\Omega_\Omega\cdot2)$ 这一站的上界), `upper` (逐段). 上界的必要条件: `upper→Open₂` (第一个未定的站 `S²`).
> 不否定 `T₁` 的读法, 也没有超值或掉值的见证. 入口 [SumOneUp](SumOneUp.lagda.md). `--safe --without-K --lossy-unification`, 无公设, 无洞, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUpRed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.NoCumsum using (BTBOᴵ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.Stage2 using (t2; sq; sqLab; walk; Lab-walk; Lab-uniq; χ; χ1-label; γ′ᴱ; diag2-fs)
open import OCF.Align.GoodL using (T2ᴸ; T2-label)
open import OCF.Align.CumUpAcceptSim using (fr)
import OCF.Align.CtxMonoAccept as CM
open import OCF.Align.TreeLevelsO8 using (reference-label-value; sq-below; Upper; prefix; upper-from-positive-prefixes)
open import Data.Sum using (inj₁)
open import OCF.Align.CumReadCF using (A; azero; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-trans)
open import OCF.Align.SumOneTree using (D; D̂; n0; n1; _⨾_; nw; ni; sum; drp)
open import OCF.Align.SumOneClosed using (T₀; T₁; v; one; St; Df; yc; _⊕_; _⨾ᴰ_; zeroD; Ig↾; accTop; Run; A₁; lv; wv; co; Sv)
open import OCF.Align.SumOneAccept using (T₀≇; sum≥)
open import OCF.Align.SumOneUpStation using (Sω)
open import OCF.Align.SumOneUpCell using (Cκ; fb₁; Fb₁; Fb₁≤T₁; Fb≅)
open import OCF.Align.SumOneUpChain using (Pa; stop; pL; pR; pI; cut; cut≤; π¹; S¹; S¹≈; S¹≤T₁; W¹; kW¹; Y¹; r₀)
```

## §1 参照树里的位置

参照树沿基本列 $[1][0][0][2]$ 走到 $\psi_0(\Omega_\Omega\cdot2)$ 的带标签的树 (`T2ᴸ`), 它的第 0 项是 $\psi_0(\Omega_\Omega+\Omega_1)$ (`χ 1`). 两处都由标签的唯一性认出, 记号侧只是计算.

```agda
Ref₁ : Ordᶜ zero
Ref₁ = fr CM.Ref

walk-below : ∀ (X : Ordᶜ zero) p → walk X p ≼ X
walk-below X [] = ≼-refl X
walk-below X (n ∷ p) = ≼-trans (walk-below (sq X n) p) (sq-below X n)

T2≼Ref : T2ᴸ ≼ Ref₁
T2≼Ref =
  ≼-trans (≅→≼ (Lab-uniq T2-label (Lab-walk (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) reference-label-value (refl , refl , refl , refl , tt))))
          (walk-below Ref₁ (1 ∷ 0 ∷ 0 ∷ 2 ∷ []))

χ1≅ : χ 1 ≅ sq T2ᴸ 0
χ1≅ = Lab-uniq χ1-label (subst (Lab (sq T2ᴸ 0)) (diag2-fs 0) (sqLab T2-label refl 0))

S¹≼T2₀ : trA S¹ ≼ sq T2ᴸ 0
S¹≼T2₀ = ≼-trans (proj₁ S¹≈) (≅→≼ χ1≅)

S¹≼Ref : trA S¹ ≼ Ref₁
S¹≼Ref = ≼-trans S¹≼T2₀ (≼-trans (sq-below T2ᴸ 0) T2≼Ref)

Sω≤S¹ : Sω ≤ S¹
Sω≤S¹ = sum≥ Sω (cut fb₁ π¹)

Sω≼Ref : trA Sω ≼ Ref₁
Sω≼Ref = ≼-trans (≤→≼ Sω≤S¹) S¹≼Ref
```

## §2 第一个带上下文的回灌: 一格的步进

`CellStep`: 格的世界对参照链 $\gamma'_{m+1}=\psi_0(\Omega_\Omega+\Omega_{\gamma'_m})$ (`sq T2ᴸ m` 的标签) 的一步. 它是一条跨折叠的单调陈述: 左边是 `SumOne` 的一格, 右边是带标签的树的下一项. 第 0 格的前提是定理 (`cell₀`); `CellStep` 本身没有证.

```agda
CellStep : Set
CellStep = ∀ k m → trA (v (Cκ k)) ≼ sq T2ᴸ m → trA (v (Cκ (suc k))) ≼ sq T2ᴸ (suc m)

cell₀ : trA (v (Cκ 0)) ≼ sq T2ᴸ 0
cell₀ = ≼-trans (≤→≼ Sω≤S¹) S¹≼T2₀

cells : CellStep → ∀ k → trA (v (Cκ k)) ≼ sq T2ᴸ k
cells P zero = cell₀
cells P (suc k) = P k k (cells P k)

fb-upper : CellStep → trA Fb₁ ≼ T2ᴸ
fb-upper P = ≼-trans (≅→≼ Fb≅) (l≼ (λ k → ≼-trans (cells P k) (sq-below T2ᴸ k)))

fb-ref : CellStep → trA Fb₁ ≼ Ref₁
fb-ref P = ≼-trans (fb-upper P) T2≼Ref
```

## §3 第一个未定的站

`S²`: 第 0 格里走完第 0 层与第 1 层的位置. 第 1 层的坐标是状态在第 1 层的差, 它含折叠产出的节点与 `nκ`, §2 之前的办法到这里为止. 上界成立的话它必须在参照之下 (`upper→Open₂`); 这一条没有证, 也没有反驳.

```agda
π² : Pa fb₁
π² = pI (pL (pL (pR (pI stop))))

S² : A
S² = sum Sω (cut fb₁ π²)

rgt : ∀ {W} → D azero W → D azero W
rgt (x ⨾ y) = y
rgt x = x

S¹≤S² : S¹ ≤ S²
S¹≤S² = sum≥ S¹ (rgt (cut fb₁ π²))

S²≤T₁ : S² ≤ T₁
S²≤T₁ = ≤-trans (cut≤ Sω fb₁ π²) Fb₁≤T₁

Open₂ : Set
Open₂ = trA S² ≼ Ref₁

upper→Open₂ : Upper → Open₂
upper→Open₂ u = ≼-trans (≤→≼ S²≤T₁) u

upper→fb : Upper → trA Fb₁ ≼ Ref₁
upper→fb u = ≼-trans (≤→≼ Fb₁≤T₁) u
```

`S²-shape`: 路径取出的第二段就是第 1 层节点的折叠输出 `R₁` (状态 `Y²` 是走完第 0 层之后的状态). 实参由检查器核对. 下一步要定的就是这一次 `Run`.

```agda
R₀ : Df W¹
R₀ = Run accTop (ni {k = azero} C.self (λ _ _ _ → n1)) kW¹ (lv (Cκ 0)) tt (Ig↾ (wv (Cκ 0)) A₁) (co (Cκ 0) ⨾ n0) Y¹

Y² : St W¹
Y² = (Sv (Cκ 0) ⊕ (zeroD ⨾ᴰ R₀)) ⊕ zeroD

q¹ : one ⊲ W¹
q¹ = C.lim 0 (C.lim 0 (C.lim 1 (C.suc C.self)))

co² : D̂ W¹
co² = (co (Cκ 0) ⨾ (n0 ⨾ nw kW¹ (ni {k = azero} C.self (λ _ _ _ → n1)))) ⨾ n0

R₁ : Df W¹
R₁ = Run accTop (ni {k = one} C.self (λ _ _ _ → n1)) q¹ (lv (Cκ 0)) tt (Ig↾ (wv (Cκ 0)) A₁) co² Y²

S²-shape : cut fb₁ π² ≡ (n0 ⨾ drp r₀) ⨾ (n0 ⨾ drp (yc R₁ (inj₁ kW¹) tt))
S²-shape = refl
```

## §4 整体

`StageUp` 与上界等价 (`TreeLevelsO8.upper-obligation`), 这里只是引用. `T₁≇`: 基本列验收对 `T₁` 不可能, 只能做序数值验收.

```agda
StageUp : Set
StageUp = ∀ n → trA (prefix (suc n)) ≼ Ref₁

upper : StageUp → Upper
upper = upper-from-positive-prefixes

R₀≅ : sq Ref₁ 0 ≅ BTBOᴵ
R₀≅ = Lab-uniq (sqLab reference-label-value refl 0) BTBO-label

lim≅→sq : ∀ {f : ℕ → Ordᶜ zero} {Y : Ordᶜ zero} → lim f ≅ Y → ∀ n → f n ≅ sq Y n
lim≅→sq (l≅ h) n = h n
lim≅→sq (upʳ {r = ()} e) n

T₁≇ : trA T₁ ≅ Ref₁ → ⊥
T₁≇ e = T₀≇ (≅-trans (lim≅→sq e 0) R₀≅)
```
