# 第十七轮的否定 (二): 时间关系的封闭性; 换世界之后得不到时间条件 `DomL`

> 不读记号. 入口 [NegSR17](NegSR17.lagda.md). 对着接口 [StrRel17If](StrRel17If.lagda.md) (定稿 2026-11-05 12:12) §1–§2 写.
>
> 1. **(定理, 正面, 一切 $\Lambda$) `later⊕`, `laterᵈ⊕`, `laterᵈcv₀`, `laterᵈcv`, `laterᵈKb`**: 同一世界的 `Later` 对向右加一段 (`⊕`) 封闭; 跨世界的 `Laterᵈ` 对 `⊕` 封闭, `cv q Y` 对 $Y$ 字面地是 `Laterᵈ q`, 并且 `Laterᵈ` 沿路径复合经过 `cv` (`laterᵈcv`, 用 `⊲-tr` 的结合律, 命题等式, 不用 `Funext`). `Kb` 的状态形状 (两次换世界, 中间与之后各加一段) 由此是产生时状态的 `Laterᵈ` (`laterᵈKb`); `BNi` (`cv p Y ⊕ …`), `κc` 的格 (`cv … (Sv ⊕ κΔ)`), `Kp` (`cv wu Y`) 同理, 都是这几条的组合.
> 2. **(定理) `¬domCv`**: 一切 $\Lambda$: 产生时状态的第 $0$ 层累计不是字面的 `n0`, 则任何 `cv q Y′` 都不满足时间条件 `DomL` (累计分量 `RelX⁺ hz hz (z Y₀) n0` 推出 `z Y₀ ≡ n0`, `inv0`).
> 3. **(否定) `¬domFromLaterᵈ`**: "`J²⁺ Y₀ Y′` 且 `Laterᵈ q Y′ Y₂` ⇒ `DomL Y₀ Y₂`" 不成立. 实例: $\Lambda_2$, 闭项的状态 $Y_1=Y_0\oplus\mathrm{Step}\,Y_0$ (累计 `n0 ⨾ ω⋅(1 ⨾ 0)`), 换到世界 $1$. 也就是说, 接口所说 "由字面的时间关系推出 `DomL`" 只在不换世界时成立 (`Later` 加 `jPfx⁺`); 经过 `cv` 的再折叠, 时间条件要另给.
>
> **构造一路为什么需要这些.** `RkSoundT` 只对满足 `DomL` 的再折叠给结论. 折叠里 `rk⁺` 的输出 (`RKi` 在目标 $T$ 上的输出, 世界 $m\unrhd W$) 加进状态之后, 要在目标的世界里被再折叠: 节点上升时链的第 $0$ 段读 `yc (d Y) (tg self hk lW)`, 这一读数在 `cv q` 之后是旧状态在 `tg↑ q …` 上的读数 (`HtFeedFold.cv` 的字面), 而 `BNi`, `Kp`, `Kb`, `κc` 都先 `cv` 再运行. 所以构造一路要从折叠的字面关系 (这里证明了的是 `Laterᵈ`) 得到 `DomL`; 第 3 条说这一步在换世界之后不成立.
>
> **只否定什么.** 第 3 条只否定 "`Laterᵈ` 加 `J²⁺` 推出 `DomL`" 这一律 (累计分量). 本文不否定 `RkSoundT` (它由 [NegSR17RkT](NegSR17RkT.lagda.md) 另行否定, 机制同源: `cv` 清零累计), 也不否定把 `DomL` 换成只比差分量的条件 (例如 `J²⁺` 去掉累计) 之后的 `rk⁺` 可靠性: 那要看产生时的累计是否影响左边的值 (坐标层下有 $\Omega$-极限时的 `nκ`, 或读累计的动作); 本文没有比较值 (判断: 坐标层 $0$, 动作不读累计时累计不影响左边; 一般情形未知). 第 1 条是正面的. 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `¬domFromLaterᵈ` 的实例: `hY₁⁺ tt tt` (`J²⁺ Y₁ Y₁`), `laterᵈcv₀ q₁ Y₁` (`Laterᵈ`), 累计非 `n0` 由 `λ ()`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR17Time where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; LgH; hz; D₀; n0)
open import OCF.Align.StrRel13Val using (Λ₂)
open import OCF.Align.StrRel16Lem using (Lp; here; left)
import OCF.Align.StrRel16If as If³
import OCF.Align.StrRel17If as If⁴
```

## 1 `Later`, `Laterᵈ` 对 `⊕`, `cv` 的封闭性 (一切 $\Lambda$)

```agda
-- §A 时间关系的封闭性 (一切 Λ)
⊲-assoc : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (s : c ⊲ d) → ⊲-tr (⊲-tr p q) s ≡ ⊲-tr p (⊲-tr q s)
⊲-assoc p q C.self = refl
⊲-assoc p q (C.suc s) = cong C.suc (⊲-assoc p q s)
⊲-assoc p q (C.lim n s) = cong (C.lim n) (⊲-assoc p q s)

module Clo (Λ : H) (lΛ : LgH Λ) where
  open If³ Λ lΛ using (module P; RelX⁺; n0⁺; in⁺; J²⁺)
  open If⁴ Λ lΛ using (Later; Laterᵈ; DomL)
  open P using (Tg; tg; wm; tm; lm; tg↑; St; Df; yc; d; z; cv; _⊕⟨_⟩_)

  later⊕ : ∀ {W} {lW : Lg W} {Y₀ Y : St W} (Δ : Df W) → Later Y₀ Y → Later Y₀ (Y ⊕⟨ lW ⟩ Δ)
  later⊕ Δ (h , hz₀) = (λ T → left (h T)) , left hz₀

  laterᵈ⊕ : ∀ {W₀ W} {lW : Lg W} {q : W₀ ⊲ W} {Y₀ : St W₀} {Y : St W} (Δ : Df W) → Laterᵈ q Y₀ Y → Laterᵈ q Y₀ (Y ⊕⟨ lW ⟩ Δ)
  laterᵈ⊕ Δ h T = left (h T)

  laterᵈcv₀ : ∀ {W₀ W} (q : W₀ ⊲ W) (Y : St W₀) → Laterᵈ q Y (cv q Y)
  laterᵈcv₀ q Y T = here

  laterᵈcv : ∀ {W₀ W W₂} (q : W₀ ⊲ W) (q₂ : W ⊲ W₂) {Y₀ : St W₀} {Y : St W} → Laterᵈ q Y₀ Y → Laterᵈ (⊲-tr q q₂) Y₀ (cv q₂ Y)
  laterᵈcv q q₂ {Y₀} {Y} h {t} {m} T =
    subst (λ w → Lp (yc (d Y₀) (tg w (tm T) (lm T))) (yc (d Y) (tg↑ q₂ T))) (sym (⊲-assoc q q₂ (wm T))) (h (tg↑ q₂ T))
```

## 2 `Kb` 的状态形状

```agda
  -- Kb 的状态形状: 两次换世界, 中间与之后各加一段
  laterᵈKb : ∀ {W W⁺ c} {lW⁺ : Lg W⁺} {lc : Lg c} (wu : W ⊲ W⁺) (p : W⁺ ⊲ c) (Y : St W) (Δ₁ : Df W⁺) (Δ₂ : Df c) →
             Laterᵈ (⊲-tr wu p) Y ((cv p (cv wu Y ⊕⟨ lW⁺ ⟩ Δ₁)) ⊕⟨ lc ⟩ Δ₂)
  laterᵈKb {lW⁺ = lW⁺} {lc} wu p Y Δ₁ Δ₂ =
    laterᵈ⊕ {lW = lc} {q = ⊲-tr wu p} {Y₀ = Y} {Y = cv p (cv wu Y ⊕⟨ lW⁺ ⟩ Δ₁)} Δ₂
      (laterᵈcv wu p {Y₀ = Y} {Y = cv wu Y ⊕⟨ lW⁺ ⟩ Δ₁} (laterᵈ⊕ {lW = lW⁺} {q = wu} {Y₀ = Y} {Y = cv wu Y} Δ₁ (laterᵈcv₀ wu Y)))
```

## 3 换世界之后 `DomL` 不成立

```agda
  -- 第 0 层: x ≤ n0 ⇒ x 字面为 n0
  inv0 : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {x : D₀ W} → RelX⁺ hz hz lW lW′ x (n0 {W = W′}) → x ≡ n0
  inv0 n0⁺ = refl
  inv0 (in⁺ h If³.here) = inv0 h

  -- 换世界之后, 时间条件 DomL 只要产生时的累计非 n0 就不成立
  ¬domCv : ∀ {W₀ V W W₂} (lW₀ : Lg W₀) (Y₀ : St W₀) → ¬ (z Y₀ ≡ n0) → ∀ (q : W ⊲ W₂) (lV : Lg V) (lW₂ : Lg W₂) (Y : St V) (Y′ : St W) →
           ¬ DomL lW₀ Y₀ lV lW₂ Y (cv q Y′)
  ¬domCv lW₀ Y₀ nz q lV lW₂ Y Y′ ((_ , rz) , _) = nz (inv0 rz)
```

## 4 实例: 闭项的状态 $Y_1$ 换到世界 $1$

```agda
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open FinΛ⁺ Λ₂ tt tt using (Y₁; hY₁⁺)
module C₂ = Clo Λ₂ tt
open If³ Λ₂ tt using (module P; J²⁺)
open If⁴ Λ₂ tt using (Laterᵈ; DomL)

DomFromLaterᵈ : Set
DomFromLaterᵈ = ∀ {W₀ W W₂ V} (lW₀ : Lg W₀) (lW : Lg W) (lW₂ : Lg W₂) (lV : Lg V) (q : W ⊲ W₂)
                  (Y₀ : P.St W₀) (Y′ : P.St W) (Y₂ : P.St W₂) (Y : P.St V) →
                J²⁺ lW₀ lW Y₀ Y′ → Laterᵈ q Y′ Y₂ → DomL lW₀ Y₀ lV lW₂ Y Y₂

Ya : P.St azero
Ya = Y₁ {azero} tt

-- 换到下一个世界 1: 状态是 cv Ya, 差分量与 Ya 的读数字面相同 (Laterᵈ), 累计被清零
q₁ : azero ⊲ asuc azero
q₁ = C.suc C.self

¬domFromLaterᵈ : ¬ DomFromLaterᵈ
¬domFromLaterᵈ h =
  C₂.¬domCv {W₀ = azero} {V = azero} {W = azero} {W₂ = asuc azero} tt Ya (λ ()) q₁ tt tt Ya Ya
    (h {W₀ = azero} {W = azero} {W₂ = asuc azero} {V = azero} tt tt tt tt q₁ Ya Ya (P.cv q₁ Ya) Ya (hY₁⁺ tt tt) (C₂.laterᵈcv₀ q₁ Ya))
```
