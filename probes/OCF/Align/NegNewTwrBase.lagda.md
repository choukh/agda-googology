# 新塔, 否定一路 (四): 站的求值与最终坍缩都在基世界里

> 不含记号. 入口 [NegNewTwr](NegNewTwr.lagda.md). 对着接口 [NewTwrIf](NewTwrIf.lagda.md) ("接口定稿 2026-11-05 17:39 (首次编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 主审转告的补充义务: "检查站的世界是否仍是基世界 (若是, 读回只见底支, 对照 `only-botLev`/`code-botK`)". 接口没有世界 (`RdK`, `CollK` 都不带世界); 世界在构造一路的实现里 (只读观察, 文件 17:43–17:48 版): 站的求值 `NewTwrEv.evN X` 在 `GenFoldK.W₀X X = (w₀ (genLev X) , hz)` 里, 最终坍缩 `NewTwrColl.At` 在 `W₁ = (w₀ G , hz)` 里, `G = GΛ = genSupℕ Kc genKc`. 这两个都是 `GenK` 实例给的**基世界**. 本篇:
>
> - **`only-botG` (定理).** 对一切层号 $x$, 在 `w₀ (genLev x)` 里任一种类的界之下只有最小坐标 `bot` (`NegLvKtCopy.only-botLev` 对 `GenK` 的基世界重写一遍: `genLev` 的基世界与码的基世界 `w0 (cdLev x)` 逐分量同形, 但作为函数不定义相等, 不用外延就分别证). `only-botKcG` (一切站), `only-botΛG` (`KΛc`).
> - **`stage-only-bot`, `final-only-bot` (定理).** 站的求值世界 `(w₀ (genLev X) , hz)` 与最终坍缩的世界 `(w₀ GΛ , hz)` 里, `step` 的**一切**种类 (旧种类与新种类) 的界之下只有 `bot`. 推论 `final-top-bot`: 最终坍缩起始世界里每个种类的顶坐标就是 `bot` (构造一路 `NewTwrK.base-bot` 是其中一族的 `refl`).
>
> **读法 (判断).** 折叠里能把世界升高的只有回灌 (`GenFoldRun` 文件头的表). 最终坍缩: 层里没有新种类结点 (`NegNewTwrShape.final-kinds`), 层号对角的结点在 `GΛ` 下全有损 (`final-lossy`, 起点无 $\Omega$-结点时), 所以没有回灌改变它们的界 (构造一路 `NewTwrObs.keepΛ` 说 A-回灌不动读回分量); 有损一支读 "当前世界的分支", 即底支. 站的求值: 新种类有回灌 (这是每站的内容, `NewTwrK.rd-head`), 旧种类 (第 $X$ 级本身的 $\Omega$-结构) 的闭包有损地读 (`NewTwrRd` 文件头 "旧种类的闭包结点有损地读 (当前世界的分支)"), 当前世界的旧分量是基世界, 只见底支. 两处都是 "读回只见底支" 的形状 (对照 `code-botK`); 把它写成对 `Run` 全程的不变式, 本篇没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwrBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.GenFoldIf using (w₀; tpK; top; topBd)
open import OCF.Align.GenFoldInst using (genLev; genKc)
open import OCF.Align.NegLvKtCopy using (botA; botH)
open import OCF.Align.NegNewTwrFeed using (genΛ)
open import OCF.Align.NewTwrIf using (NewTw)
```

## §1 `GenK` 的基世界里只有底坐标

```agda
only-botG : ∀ {S : KS} (x : HB S) (κ : K (Lev x)) (c : E (Lev x) κ) →
  Bd (Lev x) κ c (w₀ (genLev x)) → c ≡ bot (Lev x) κ
only-botG hz κ c e = botA e
only-botG (hs x) (inj₁ κ) c e = only-botG x κ c e
only-botG (hs x) (inj₂ tt) c e = botH e
only-botG (hl f) (n , κ) c e = only-botG (f n) κ c e
only-botG (hΩ κ₀ g) (i , κ) c e = only-botG (g i) κ c e

only-botKcG : ∀ s (κ : K (Kc s)) (c : E (Kc s) κ) → Bd (Kc s) κ c (w₀ (genKc s)) → c ≡ bot (Kc s) κ
only-botKcG zero κ c e = botA e
only-botKcG (suc s) (inj₁ tt , κ) c e = only-botKcG s κ c e
only-botKcG (suc s) (inj₂ c′ , κ) c e = only-botG c′ κ c e

only-botΛG : ∀ (κ : K KΛc) (c : E KΛc κ) → Bd KΛc κ c (w₀ genΛ) → c ≡ bot KΛc κ
only-botΛG (s , κ) c e = only-botKcG s κ c e
```

## §2 站的求值世界与最终坍缩的世界

```agda
-- 站的求值: GenFoldK.W₀X X = (w₀ (genLev X) , hz)
stage-only-bot : ∀ {S : KS} (X : HB S) (κ : K (step (Lev X))) (c : E (step (Lev X)) κ) →
  Bd (step (Lev X)) κ c (w₀ (genLev X) , hz) → c ≡ bot (step (Lev X)) κ
stage-only-bot X (inj₁ κ) c e = only-botG X κ c e
stage-only-bot X (inj₂ tt) c e = botH e

-- 最终坍缩: NewTwrColl.At.W₁ = (w₀ GΛ , hz)
final-only-bot : ∀ (κ : K (step KΛc)) (c : E (step KΛc) κ) →
  Bd (step KΛc) κ c (w₀ genΛ , hz) → c ≡ bot (step KΛc) κ
final-only-bot (inj₁ κ) c e = only-botΛG κ c e
final-only-bot (inj₂ tt) c e = botH e

-- 起始世界里每个种类的顶坐标就是 bot
final-top-bot : ∀ (κ : K KΛc) → top (tpK genΛ) κ (w₀ genΛ) ≡ bot KΛc κ
final-top-bot κ = only-botΛG κ _ (topBd (tpK genΛ) κ (w₀ genΛ))
```

## §3 结论 (按档)

- **[定理]** `only-botG`, `only-botKcG`, `only-botΛG`; **`stage-only-bot`**, **`final-only-bot`**, `final-top-bot`.
- **[只读观察]** 构造一路的站求值与最终坍缩取的正是这两个世界 (`GenFoldK.W₀X`, `NewTwrColl.At.W₁`); 本篇的定理不导入构造文件, 对着的是 `GenK` 实例的基世界本身.
- **[判断]** 见文件头 "读法". 只否定 "基世界里看得见非底坐标"; 不否定换成随站长高的世界 (`KcFoldIf.WTower` 那一类, `NegKcFoldTower.limW`) 后的折叠.
