# LeanLv (五): 值 — 回灌格的世界 (定理) 与严格值定理的卡点 (未走通)

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md). 第 4 层 (只新增定理, 不改定义). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **任务 3** (作者选项说明 "做第一条值定理 (TF 严格高于全有损折叠)"). **结果: 严格的值定理未走通** (没有编译过的 `TVs > TL` 或 `TF > TL`, 也没有否定定理). 本篇只有**世界这一档**的定理: 回灌格把头 $2+m$ 的界从原顶升到 "原顶 $\boxplus$ 读回" (`top0`), 读回 $\Omega_{\mathrm{Sg}\,1}$ 的数据时这个增量是 `Lv (st 2)` 的后继种类的 $\Omega$-结点 (`rdΩd`, `top0-Ωd`); 而全有损的那一行不动世界 (判断: `RKa` 的 `inj₂` 行字面上用当前世界, 无需定理). 世界变大**不是**值变大: 见 §3.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (bkS; toFb)
open import OCF.Lean.LeanLvIf
open import OCF.Lean.LeanLvEmb
open import OCF.Lean.LeanLvTmS
import OCF.Lean.LeanLvRdS as RdM
import OCF.Lean.LeanTFold as Fold
open RdM SLs using (readS)
open Tree SLs hiding (inS)
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fbS
```

## §1 回灌格的世界

对一切折叠参数 (任一层, 世界, 分支, 状态), 头 $2+m$ 的回灌第 0 格的世界里, 头的顶坐标 = 原顶 $\boxplus\ \delta_0$, $\delta_0$ 是状态在级层 `Sg 1` 上的数据沿 `σ₂⁺` 的读回 (接口 `LeanFbIf.rz-top`).

```agda
hasK-⊞ : ∀ {S : KS} {κ : K S} (a : HB S) {b} → HasK κ b → HasK κ (a ⊞ b)
hasK-⊞ a here = here
hasK-⊞ a (inS h) = inS (hasK-⊞ a h)
hasK-⊞ a (inL n h) = inL n (hasK-⊞ a h)
hasK-⊞ a (inΩ c h) = inΩ c (hasK-⊞ a h)

module Cell {ly W₀ W} (m : ℕ) (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
            (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
  c : ℕ → ClA W ly
  c = κcF ac (toFb (feedLs m)) u q₀ lW lL A₀ w Y

  δ₀ : HB (Lv (stL (suc (suc m))))
  δ₀ = readS σ₂⁺ (emb2 m) lW hz (yc (d Y) (tg ≤rf (Sg⊲ 1) lW))

  top0 : top SLs (νS (suc (suc m))) (wA (c zero)) ≡ top SLs (νS (suc (suc m))) (proj₁ W) ⊞ δ₀
  top0 = rz-top (headUp (suc (suc m))) tt δ₀ (proj₁ W)
```

**读回 $\Omega_{\mathrm{Sg}\,1}$ (定理, `refl`).** $\Omega_{\mathrm{Sg}\,1}$ (`Ωd (Sg 1)`, 主结点过坐标 $\beta$ = 头 0 在当前世界的顶的那一支本身) 读成 `Lv (st 2)` 的后继种类 `(inj₂ (hs β) , inj₂ tt)` (坐标 `HB (Lv (g₂ β))`) 沿 `emb2 m` 的 $\Omega$-结点. (否定一路 `NegLeanLvS.rd-Ωd⁺` 是同一件事的等式形式; 沿 `Sim` 读的 `TV` 这里只读出有限值, 对照 `NegLeanLvTm.rd-Ωd`.)

```agda
βW : Wd L₀ → HB S⊥
βW W′ = top L₀ (inj₁ (νS 0)) W′

rdΩd : ∀ m {W′} (lW′ : LgW L₀ W′) →
       HasK (j (emb2 m) (inj₂ (hs (βW W′)) , inj₂ tt)) (readS σ₂⁺ (emb2 m) lW′ hz (Ωd (Sg 1)))
rdΩd m lW′ = here
```

**升界含这个种类 (定理).** 状态在 `Sg 1` 上的数据是 $\Omega_{\mathrm{Sg}\,1}$ 时, 第 0 格的世界里头 $2+m$ 的顶含后继种类的 $\Omega$-结点. 前提可满足: `Y-Ωd` (状态的累计输出在每个目标层 $t$ 上取 $\Omega_t$; `Stp` 发出的正是 $\Omega_t$ 的 $\omega$ 份, 这里不说折叠的路径上恰好是它).

```agda
module CellΩ {ly W₀ W} (m : ℕ) (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
             (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
             (hY : yc (d Y) (tg ≤rf (Sg⊲ 1) lW) ≡ Ωd (Sg 1)) where
  open Cell m ac u q₀ lW lL A₀ w Y

  top0-Ωd : HasK (j (emb2 m) (inj₂ (hs (βW W)) , inj₂ tt)) (top SLs (νS (suc (suc m))) (wA (c zero)))
  top0-Ωd = subst (HasK _) (sym top0)
              (hasK-⊞ (top SLs (νS (suc (suc m))) (proj₁ W))
                 (subst (λ x → HasK (j (emb2 m) (inj₂ (hs (βW W)) , inj₂ tt)) (readS σ₂⁺ (emb2 m) lW hz x)) (sym hY) (rdΩd m lW)))

-- 前提实例
Y-Ωd : ∀ {W} → St W
Y-Ωd = st (df (λ {t} _ → Ωd t)) n0 n0

hY-Ωd : ∀ {W} (lW : LgW L₀ W) → yc (d (Y-Ωd {W})) (tg ≤rf (Sg⊲ 1) lW) ≡ Ωd (Sg 1)
hY-Ωd lW = refl
```

## §2 有限测试 (引用)

[LeanLvTest](LeanLvTest.lagda.md) `sz-7V`: 有界展开 ($k=7$) 的结点数 `TVs` 与 `TL` 都是 7238 (有限测试, 不是证明): 回灌行离根 11 步 (`LeanLvShape.exec-TVs2`), 在这一深度上看不见.

## §3 严格值定理: 卡点 (未走通)

要证的是 `TL` $\prec$ `TVs` (或 `TL` $\prec$ `TF`), `TL` = 同一 `T`, `ΛF`, 底种类, 一切种类有损的折叠 (`LeanFbTest.TL`). 写下来的路线与卡在哪里:

1. **一条模拟关系穿过整个折叠 (`ValNewRun.Run-R` 式).** 左边 (`TL`) 与右边 (`TVs`) 在同一数据上跑. `RKa` 一行左边是 `ω⋅ (… 当前世界 W …)`, 右边是 `nl (λ n → … 世界 wA (c n) …)`, `wA (c n)` $\ge W$ (`top0`). 从这一行往下, 两边的 `Run` 在**不同的世界**里跑: 关系要带 $W\le W'$ 的证据 (右边更大). 卡点 (判断, 未写否定): (a) 结点 `RunNi` 的 "保留/上升" 由 `rkT` 在各自的世界里比较决定, 世界变大后右边可能出现左边没有的结点证据 (`keep` 对 `rise`), 两边输出的形状不同, `Mo` 的同形构造子接不上; (b) 闭包结点 `RKk` 的分支取 "一切更大的世界", 左右的世界不同, 要 "分支对世界单调" (这正是 `ValNew` 接手清单第 1 条与 `ValTK` 的第一个障碍, `GoodUp` 的位置). 本路没有写这条关系 (估计: `ValNewRel` + `ValNewRun` 的 377 行加世界参数, 判断).
2. **"每格严格 ⇒ 闭项严格" 不成立.** 否定一路 `NegLeanLvVal.absorb-D` (引用, 复核由主审做): 第 0 层 `sum b (nl d)` 与有损形状 `sum b (nl (λ _ → x))` 互相 $\le$, 只要每格的值夹在 `sum 0 x` 与它的常数倍之间. 所以即使 `RKa` 的回灌格逐格严格高于有损格, 也推不出闭项严格高; 严格的值定理要回灌格不被常数倍界住 (例如格里出现新种类的 $\Omega$-结点读出的 $\omega$-幂). 本篇的 `top0-Ωd` 只到世界: 升上来的界里有后继种类的 $\Omega$-结点; 这个界在第 0 层输出里是否留下大于常数倍的痕迹, 要走完 1.
3. **"回灌只让世界变大、可用单调关系穿过的位置" (作者提示) [判断].** 在 `TVs` 里找到的候选是头 $2+m$ 的回灌行本身 (`exec-TVs2` 的路径): 这一行的分支 (闭包结点 `nc (inj₁ (νS 2))` 的 $u$, 来自 $\Omega_{\mathrm{stage}}$) 只经 `sL top hself` 读世界的顶, 世界变大只让它走更高的一支. 要在这一处穿过, 需要 "`Run` 在 $(W, t)$ 与 $(W', t)$ 上, $W\le W'$, 第 0 层输出 `sum` 单调" 对这一支成立; 这一支的 `Run` 仍要过 `rkT` 与下层闭包, 所以仍落在卡点 1 的 (a)(b). 本路没有找到不经过它们的位置.

**粗界 (全部是判断).**

| 对象 | 界 | 依据 |
|---|---|---|
| `TVs` 下界 | 不低于 `TL` 的读法 | 回灌只让世界变大 (`top0`), 判断折叠对世界不减; 没有定理 (卡点 1) |
| `TVs` 与 `TF` | 读法同一档或更高 | 头 $n\ge2$ 的升界从 "一个级 0 种类" (`rdX-one-kind`) 变成 `Lv (st 2)` 的拷贝里的种类 (`rd-a`, `rd-b`, `top0-Ωd`); 头 0, 1 不变. 没有定理 |
| `TVs` 上界 | 低于 $\psi_0(\Lambda)$ 的参照 | 头 $n\ge3$ 只在 `emb2` 的像里长 (否定一路 `no-top3⁺`), 第 $n$ 站的头的坐标里高于 `st 2` 的种类不被回灌触到; 判断, 没有参照树 |

`LeanFb` 对 `TF` 的读法 (不超过 $\psi_0(\Omega_3)$ 量级, 判断) 本路没有重算.
