# 头按自己的级读回, 否定一路 (六): 对构造一路闭项 `TV` 的检查

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 只读导入构造一路的 [LeanLvTm](LeanLvTm.lagda.md), [LeanLvRd](LeanLvRd.lagda.md), [LeanLvEmb](LeanLvEmb.lagda.md) (22:18 版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **四个检查.**
>
> 1. **新的回灌行在闭项里出现 (定理 `exec-TV2`, `fbV-head2`).** 沿 `NegLeanFbInst.exec-TF2` 的同一条路径, `TV` 的第 0 层数据 `ΨV` 的子项字面地是 `RKa _ (fbV (νS 2)) …`, 而 `fbV (νS 2)` 是 `inj₁ (toFb (feedLv 0))` (级层 `Sg 1`, 读回 `readS σ₂ (emb2 0)`). 所以头 2 的按级读回出现在闭项的计算里.
> 2. **头 2, 3 的读回是不是 "自己的级" (定理).** `own-head2`: `lvSim 0` 的层号是 `st 2` (`refl`), 嵌入是 `emb2 0 = idE` (`refl`). `not-own-head`: 对一切 $m$, `lvSim (1+m)` 的层号不是 `st (3+m)` (由 `NegLeanLvBlind.no-own-sim`; 不只是这个实例: 一切 `LvSim SLs ΛF _` 都如此).
> 3. **头 3 的读回产出的种类 (定理 `no-top3-RLv`).** `RLv 1` 的读回的输出里没有 `kTop3` (坐标为 `HB (Lv (st 2))` 的种类) 的 $\Omega$-结点, 对一切世界与数据 (由 `NegLeanLvInst.no-top3`).
> 4. **$\Omega_{S_1}$ 的数据读成有限 (定理 `rd-Ωd`, `refl`).** 对一切 $m$, 世界, 起点 $b$: `readS σ₂ (emb2 m) lW b (Ωd (Sg 1)) ≡ hs (hs b)`. 原因是 `Ωd` 的 $\Omega$-行发出的结点恰好停在一支本身 (`NegLeanLvInst.rdΩ-top-lossy`), 闭包结点也有损. 对照 (定理 `rd-deep`, `refl`): 停在一支内部的后继处的结点读成 `Lv (st 2)` 的种类 `(inj₂ c , inj₂ tt)` 的 $\Omega$-结点, 所以读回不是处处平凡. **读法 [判断]:** 折叠的状态里第 `Sg 1` 层的数据有 `Stp` 发出的 `Ωd (Sg 1)` (`LeanTFold.Stp`), 那一部分对头 $2+m$ 的回灌只贡献有限的增量; 回灌是否升出 $\Omega$-结点, 取决于第 `Sg 1` 层上是否有停在一支内部的结点, 要对路径算.
>
> **只否定什么.** 都是对实例的形状定理; 不说 `TV` 的值, 不否定路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (bkS; toFb)
open import OCF.Lean.LeanLvIf renaming (inS to hinS; inL to hinL; inΩ to hinΩ; here to hhere)
open import OCF.Lean.LeanLvEmb using (emb2; idE)
open import OCF.Lean.LeanLvTm using (Sg; σ₂; RLv; lvSim; feedLv; fbV; ΨV)
import OCF.Lean.LeanLvRd as RdM
import OCF.Lean.LeanTFold as Fold
open import OCF.Lean.NegLeanFbInst using (Dir; dL; dR; dN; nav)
open import OCF.Lean.NegLeanLvBlind using (no-own-sim)
open import OCF.Lean.NegLeanLvEmb using (kTop3)
open import OCF.Lean.NegLeanLvInst using (module Img)
open Tree SLs
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fbV
open RdM SLs using (readS)
```

## §1 新的回灌行在闭项里出现

```agda
fbV-head2 : fbV (νS 2) ≡ inj₁ (toFb (feedLv 0))
fbV-head2 = refl

exec-TV2 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 3 ∷ dN 0 ∷ dL ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨV ≡ RKa _ (fbV (νS 2)) _ _ _ _ _ _ _ Tq
exec-TV2 Tq = refl
```

## §2 是不是自己的级

```agda
own-head2 : (LvSim.x (lvSim 0) ≡ stL 2) × (LvSim.em (lvSim 0) ≡ idE)
own-head2 = refl , refl

not-own-head : ∀ m → ¬ (LvSim.x (lvSim (suc m)) ≡ stL (suc (suc (suc m))))
not-own-head m = no-own-sim m (lvSim (suc m))
```

## §3 头 3 读不出 `kTop3`

```agda
open Img SLs using (no-top3-hz)

no-top3-RLv : ∀ {W} (lW : LgW L₀ W) (x : D (Sg 1) W) → ¬ HasK kTop3 (LvRd.δ (RLv 1) lW x)
no-top3-RLv lW x = no-top3-hz σ₂ lW x
```

## §4 $\Omega_{S_1}$ 的数据读成有限; 一支内部的结点读成 $\Omega$-结点

```agda
rd-Ωd : ∀ m {W} (lW : LgW L₀ W) b → readS σ₂ (emb2 m) lW b (Ωd (Sg 1)) ≡ hs (hs b)
rd-Ωd m lW b = refl
```

一支内部: 结点过 $S_1$ 在坐标 $c=c'+1$ 处的分支 $1+c$ 的直接前驱 (`hLim bd (hsuc hself)`), 读成 `j (emb2 m) (inj₂ c , inj₂ tt)` 的 $\Omega$-结点.

```agda
rd-deep : ∀ m {W} (lW : LgW L₀ W) b {c′ : HB S⊥} (bd : Bd L₀ (inj₁ (νS 0)) (hs c′) W)
  (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → _ → D (Sg 1) W′) →
  Σ (_ → HB (Lv (stL (suc (suc m))))) (λ g →
    readS σ₂ (emb2 m) lW b (ni (sL {κ = inj₁ (νS 0)} {c = hs c′} bd (hsuc hself)) u)
      ≡ hΩ (Emb.j (emb2 m) (inj₂ (hs c′) , inj₂ tt)) g)
rd-deep m lW b bd u = _ , refl
```

## §5 结论 (按档)

- **[定理, 闭项]** **`exec-TV2`**, `fbV-head2`: 头 2 的按级读回在 `TV` 的计算里出现.
- **[定理, 实例]** `own-head2` (头 2: 层号 `st 2`, 嵌入恒等); **`not-own-head`** (头 $3+m$: 层号不是 `st (3+m)`; 一切 `LvSim SLs ΛF _` 都如此). **`no-top3-RLv`**. **`rd-Ωd`** (`refl`): $\Omega_{S_1}$ 的数据读成 $b+2$. `rd-deep` (`refl`): 一支内部的后继处读成 $\Omega$-结点.
- **[判断]** 回灌是否让值变大: 由 `rd-Ωd`, 状态里 `Stp` 那一部分只贡献有限; 由 `NegLeanLvVal.absorb-D`, 若回灌的格只多出被有损格固定倍数界住的量, 值不变. 没有对 `TV` 的值的定理或测试.
