# LamIso (四): 形状定理 (第 4 层)

> 不含记号. 入口 [LamIso](LamIso.lagda.md). 只新增定理, 不改定义. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 1. **按自己的级 (§1, 对照否定一路 `NegLeanLvBlind.no-own-sim`).** 对一切 $n$: `LvSim SLs Λ′ (Lv (st n))` 有实例, 层号就是 `st n`, 嵌入是 `idE` (`own-x`, `own-em`, `refl`); 读回字面地沿 `π` 读 (`own-reads`, `refl`; 回应否定一路的盲定理 `ownConst`: 接口不逼, 实例是); 计划里头 $2+m$ 的回灌就是它 (`plan-own`).
> 2. **第 3 站的层, 显式 (§2).** `L 3` 的顶种类是第 3 站的 `(inj₁ tt , inj₂ tt)` (`L3-top`); 第 $c+1$ 支的结点种类是第 3 站分量 `inj₂ (c+1)` 的左分量的新种类, 坐标 `HB (Lv (g₂ c))` (`L3-node`, `L3-node-co`); 第 $0$ 支是 `L 2` (`L3-br0`). 全部 `refl`: 一般 $n$ 的定义里经 `tw-eq`, `eqH` 的 `subst` 在 $n=1$ 处化掉.
> 3. **头 3 的读回产出 `kTop3` (§3, 对照否定一路 `NegLeanLvS.no-top3-RLs`).** 在一个合法世界里 (`W3`: 第 3 站左分量的界是 $1$), 层 `L 3` 上过 "第 $1$ 支的结点的第 $0$ 支本身" 的一份数据, 读回 (`Rown 3`) 是 `kTop3` 的 $\Omega$-结点 (坐标 `HB (Lv (st 2))`, 级 `st 2`). 主候选 `TVs` 的头 3 读不出它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoShape where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt using (FS; SLs; νS) renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Emb; LvSim; HasK; here)
open import OCF.Lean.LeanLvEmb using (idE; botE)
open import OCF.Lean.LamIsoIf using (OwnRd)
open import OCF.Lean.LamIsoPsi SLs using (Ψ; X)
open import OCF.Lean.LamIsoL using (L; Sr; Λ′)
open import OCF.Lean.LamIsoTm
import OCF.Lean.LeanLvRdS as RdM
open RdM SLs using (readS)
open Tree SLs
```

## §1 按自己的级

```agda
own-x : ∀ n → LvSim.x (lvSimI n) ≡ stL n
own-x n = refl

own-em : ∀ n → LvSim.em (lvSimI n) ≡ idE
own-em n = refl

own-layer : ∀ n → LvRd.ℓ (OwnRd.R (own n)) ≡ L n
own-layer n = refl

own-reads : ∀ n {W} (lW : LgW L₀ W) (x : D (L n) W) → LvRd.δ (OwnRd.R (own n)) lW x ≡ readS (toS (OwnRd.π (own n))) idE lW hz x
own-reads n lW x = refl

plan-own : ∀ m → planI (νS (suc (suc m))) ≡ inj₁ (feedOwn (suc (suc m)))
plan-own m = refl
```

## §2 第 3 站的层, 显式

```agda
g₂ : HB S⊥ → LH
g₂ c = ofHB (hs hz ⊞ ι {LH} {FL} lz (up c))

L3-top : Σ (HB S⊥ → HB X) (λ B → L 3 ≡ hΩ (inj₁ (3 , inj₁ (inj₁ tt , inj₂ tt))) B)
L3-top = _ , refl

L3-br0 : Ψ 1 (L 2) (Sr 1) botE hz ≡ L 2
L3-br0 = refl

L3-node : ∀ c → Σ (_ → HB X) (λ h → Ψ 1 (L 2) (Sr 1) botE (hs c) ≡ hΩ (inj₁ (3 , inj₁ (inj₂ (hs c) , (inj₁ tt , inj₂ tt)))) h)
L3-node c = _ , refl

L3-node-co : ∀ c → E X (inj₁ (3 , inj₁ (inj₂ (hs c) , (inj₁ tt , inj₂ tt)))) ≡ HB (Lv (g₂ c))
L3-node-co c = refl
```

## §3 头 3 的读回产出 `kTop3`

```agda
kTop3 : K (Lv (stL 3))
kTop3 = inj₂ (hs hz) , (inj₂ (hs hz) , inj₂ tt)

kTop3-co : E (Lv (stL 3)) kTop3 ≡ HB (Lv (stL 2))
kTop3-co = refl

g₃ : HB S⊥ → LH
g₃ c = ofHB (Ω̂ (hs hz ⊞ ι {LH} {FL} lz (up c)))

w3 : Wd (Lv (stL 3))
w3 (inj₁ tt) = (λ ()) , hs hz
w3 (inj₂ c) = w₀ (Lv (g₃ c))

lw3 : LgW (Lv (stL 3)) w3
lw3 (inj₁ tt) = (λ ()) , tt
lw3 (inj₂ c) = lw₀ (Lv (g₃ c))

wS : Wd SLs
wS 0 = w₀ (FS 0)
wS 1 = w₀ (FS 1)
wS 2 = w₀ (FS 2)
wS 3 = w3 , hz
wS (suc (suc (suc (suc m)))) = w₀ (FS (4 Data.Nat.+ m))

lwS : LgW SLs wS
lwS 0 = lw₀ (FS 0)
lwS 1 = lw₀ (FS 1)
lwS 2 = lw₀ (FS 2)
lwS 3 = lw3 , tt
lwS (suc (suc (suc (suc m)))) = lw₀ (FS (4 Data.Nat.+ m))

W3 : Wd L₀
W3 = wS , hz

lW3 : LgW L₀ W3
lW3 = lwS , tt

-- 第 1 支的结点的第 0 支本身
r3 : StH W3 (L 2) (L 3)
r3 = sL {c = hs hz} hself (hLim {κ = κ1} {c = hz} (botBd X κ1 W3) hself)
  where
  κ1 : K X
  κ1 = inj₁ (3 , inj₁ (inj₂ (hs hz) , (inj₁ tt , inj₂ tt)))

x3 : D (L 3) W3
x3 = ni r3 (λ _ _ _ → n1)

rd-top3 : Σ _ (λ g → LvRd.δ (Rown 3) lW3 x3 ≡ hΩ kTop3 g)
rd-top3 = _ , refl

rd-top3-has : HasK kTop3 (LvRd.δ (Rown 3) lW3 x3)
rd-top3-has = here
```
