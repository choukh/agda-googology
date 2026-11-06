# 共享槽, 否定一路 (三): 对构造一路实例的检查

> 不含记号. 入口 [NegSlot](NegSlot.lagda.md). 只读导入接口 [SlotIf](SlotIf.lagda.md) 与构造一路的 [SlotCp](SlotCp.lagda.md), [SlotTw](SlotTw.lagda.md) (都不改), 以及本路的 [NegSlotWall](NegSlotWall.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> 构造一路的实例 (`SlotCp.CpNew.famNew`, `SlotTw.famU s`): `Lev (hs a′ ⊞ b)` 里 `step` 的新种类沿 $b$ 的一切路径的拷贝, 共享槽是 `Lev (hs a′)` 的新种类, 世界带证据 `ShW`. 本篇回答简报的两个检查问题.
>
> 1. **是否真的升了坐标是高度的种类? 是, 但成员的坐标类型都是同一个 `HB (Lev a′)`.** `coord-same` (定理, `refl`): 成员 $p$ 的坐标经 `cE` 落在 `HB (Lev a′)`, 不随 $p$ 变; 读回无损 (`cE⁻-cE`, 接口律), `rs-top` 精确 (`SlotGen.rsW-top`). 所以不是 "有损地经共享槽": 读回不丢. 但这一族不是原卡点的形状 (坐标类型随下标变的 `κHc`); 后者没有 `Slot` (`NegSlotWall.no-slot-κHc`, 定理).
> 2. **代价: 拷贝在带证据的世界里不可区分 (盲).** **`sh-same`** (定理, 一切 `Slot`): `ShW` 世界上任意两个成员的顶经搬运相等. 实例: **`tw-same`** (`SlotTw` 的 $U$, 一切站 $s$, 一切路径 $p, p'$), **`κd-same`** (`NegStratTwDeep.κd c` 与 `κd c′`, 一切坐标 $c, c'$). 推论 **`tw-no-split`**: 带证据的世界类型里, 没有一个世界让两份拷贝的界经搬运不同. 于是 `NegStratTwDeep` 的 "升一份留别份" 在这个世界类型里连世界都写不出来 (不是撞分离子, 是被世界证据排除).
> 3. **边界: 相邻的 `step` 新种类不能并进同一个槽 (定理).** **`no-slot-step2`** (一切 `T′`): `step (step T′)` 的两个新种类 (外层坐标 `HB (step T′)`, 内层坐标 `HB T′`) 不能同是一个 `Slot` 的成员 (外层可达: 世界的第二分量就是它的顶). 实例 **`no-slot-steps`**: `Lev (a ⊞ hs (hs y))` (对一切 $a$, $y$; `SlotTw` 的判断里说 `famU` 不覆盖的 "$B_s$ 自己的 `step` 新种类" 就是这种位置). 所以 `famU` 的覆盖面不能经同一个槽扩到相邻两级的新种类上; 别的方式未否定.
>
> **只否定什么.** 只否定: 相邻两级的新种类同在一个 `Slot` (外层可达). **不否定**: 构造一路的 `famNew`, `famU` (同一坐标类型的拷贝; 本篇只给它们的代价 `sh-same`); 每级一个槽 (组之间如何升界是原问题, 判断); 不经 `Slot` 的升界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSlotInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; tpK; w₀)
open import OCF.Align.GenFoldInst using (genLev)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.StratTwTw using (U; GU)
import OCF.Align.NegStratTwDeep as ND
open import OCF.Align.SlotIf
open import OCF.Align.SlotCp using (Path; module Cp; module CpNew)
open import OCF.Align.SlotTw using (a′; BS; memU; slotU; pd; κd≡)
open import OCF.Align.NegSlotWall using (module SL)
```

## §1 盲: 带证据的世界里, 成员的顶经搬运相等 (一切 `Slot`)

```agda
module _ {T : KS} {tp : TopG T} {J : Set} {κJ : J → K T} {Q : KS} {tq : TopG Q} {κ₀ : K Q}
         (S : Slot T tp J κJ Q tq κ₀) where

  sh-same : ∀ j j′ w → ShW S w → cE S j′ (top tp (κJ j′) w) ≡ cE S j (top tp (κJ j) w)
  sh-same j j′ w (ω , al) =
    trans (top-cp S j′ w)
      (trans (cong (top tq κ₀) (trans (al-pr S j′ al) (sym (al-pr S j al)))) (sym (top-cp S j w)))

  no-split : ∀ j j′ → ¬ Σ (Wd T) (λ w → ShW S w × ¬ (cE S j′ (top tp (κJ j′) w) ≡ cE S j (top tp (κJ j) w)))
  no-split j j′ (w , ev , ne) = ne (sh-same j j′ w ev)
```

## §2 构造一路的实例

**坐标类型不随路径变.** `CpNew.SN a′ b` 的成员 $p$ 的搬运 `cE` 的值域是 `HB (Lev a′)` (类型由接口给定, 这里写出它; 与 $p$ 无关).

```agda
coord-same : ∀ {S : KS} (a₀ b : HB S) (p : Path b) →
  (E (Lev (hs a₀ ⊞ b)) (Cp.kupP (hs a₀) (inj₂ tt) b p) → HB (Lev a₀)) ≡
  (E (Lev (hs a₀ ⊞ b)) (Cp.kupP (hs a₀) (inj₂ tt) b p) → E (Lev (hs a₀)) (inj₂ tt))
coord-same a₀ b p = refl

cp-same : ∀ {S : KS} (a₀ b : HB S) (p p′ : Path b) w → ShW (CpNew.SN a₀ b) w →
  cE (CpNew.SN a₀ b) p′ (top (tpK (genLev (hs a₀ ⊞ b))) (Cp.kupP (hs a₀) (inj₂ tt) b p′) w) ≡
  cE (CpNew.SN a₀ b) p (top (tpK (genLev (hs a₀ ⊞ b))) (Cp.kupP (hs a₀) (inj₂ tt) b p) w)
cp-same a₀ b p p′ w ev = sh-same (CpNew.SN a₀ b) p p′ w ev
```

**`SlotTw` 的 $U$: 一切站, 一切路径.**

```agda
tw-same : ∀ s (p p′ : Path (BS s)) (w : Wd U) → ShW (slotU s) w →
  cE (slotU s) p′ (top (tpK GU) (memU s p′) w) ≡ cE (slotU s) p (top (tpK GU) (memU s p) w)
tw-same s p p′ w ev = sh-same (slotU s) p p′ w ev

tw-no-split : ∀ s (p p′ : Path (BS s)) →
  ¬ Σ (Wd U) (λ w → ShW (slotU s) w × ¬ (cE (slotU s) p′ (top (tpK GU) (memU s p′) w) ≡ cE (slotU s) p (top (tpK GU) (memU s p) w)))
tw-no-split s p p′ = no-split (slotU s) p p′

-- NegStratTwDeep.κd c 与 κd c′ (经 κd≡ 是成员 pd c, pd c′)
κd-same : ∀ c c′ (w : Wd U) → ShW (slotU 0) w →
  cE (slotU 0) (pd c′) (top (tpK GU) (memU 0 (pd c′)) w) ≡ cE (slotU 0) (pd c) (top (tpK GU) (memU 0 (pd c)) w)
κd-same c c′ w ev = tw-same 0 (pd c) (pd c′) w ev
```

## §3 边界: 相邻两级的 `step` 新种类

`step (step T′)`: 外层新种类 `inj₂ tt` (坐标 `HB (step T′)`), 内层新种类 `inj₁ (inj₂ tt)` (坐标 `HB T′`, 也是 `step T′` 的新种类的坐标). 外层可达: 世界的第二分量就是它的顶 (`topStepG`).

```agda
module _ {T′ : KS} (tp′ : TopG T′) where
  private
    T₂ : KS
    T₂ = step (step T′)

    tp₂ : TopG T₂
    tp₂ = topStepG (topStepG tp′)

  reach-out : ∀ (k : K T₂) → k ≡ inj₂ tt → Wd T₂ → ∀ (e : E T₂ k) → Σ (Wd T₂) (λ w → top tp₂ k w ≡ e)
  reach-out k refl w e = (proj₁ w , e) , refl

  Eκ₂ : ∀ {k k′ : K T₂} → k ≡ k′ → E T₂ k ≡ E T₂ k′
  Eκ₂ refl = refl

  no-slot-step2 : ∀ {J κJ Q tq κ₀} (S : Slot T₂ tp₂ J κJ Q tq κ₀) jL jH →
    κJ jL ≡ inj₁ (inj₂ tt) → κJ jH ≡ inj₂ tt → Wd T₂ → ⊥
  no-slot-step2 {κJ = κJ} S jL jH eL eH w =
    SL.no-slot-adj S jL jH {S′ = step T′} (inj₂ tt) (Eκ₂ eH) (sym (Eκ₂ eL)) (reach-out (κJ jH) eH w)

-- 实例: Lev (a ⊞ hs (hs y)) = step (step (Lev (a ⊞ y))) (定义相等), 顶坐标也是
no-slot-steps : ∀ {S : KS} (a y : HB S) {J κJ Q tq κ₀}
  (Sl : Slot (Lev (a ⊞ hs (hs y))) (tpK (genLev (a ⊞ hs (hs y)))) J κJ Q tq κ₀) jL jH →
  κJ jL ≡ inj₁ (inj₂ tt) → κJ jH ≡ inj₂ tt → ⊥
no-slot-steps a y Sl jL jH eL eH =
  no-slot-step2 (tpK (genLev (a ⊞ y))) Sl jL jH eL eH (w₀ (genLev (a ⊞ hs (hs y))))
```

**前提实例.** `no-slot-step2` 的每个前提单独可满足: 内层新种类自己成一个 `Slot` (`NegSlotWall.slot-one`), 外层亦然; 世界 `w₀ (genLev _)`. 两份同在一个槽里才矛盾.

```agda
inst-in : ∀ {S : KS} (a y : HB S) →
  Slot (Lev (a ⊞ hs (hs y))) (tpK (genLev (a ⊞ hs (hs y)))) ⊤ (λ _ → inj₁ (inj₂ tt))
       (Lev (a ⊞ hs (hs y))) (tpK (genLev (a ⊞ hs (hs y)))) (inj₁ (inj₂ tt))
inst-in a y = OCF.Align.NegSlotWall.slot-one _ _

inst-out : ∀ {S : KS} (a y : HB S) →
  Slot (Lev (a ⊞ hs (hs y))) (tpK (genLev (a ⊞ hs (hs y)))) ⊤ (λ _ → inj₂ tt)
       (Lev (a ⊞ hs (hs y))) (tpK (genLev (a ⊞ hs (hs y)))) (inj₂ tt)
inst-out a y = OCF.Align.NegSlotWall.slot-one _ _
```

## §4 结论 (按档)

- **[定理, 盲]** **`sh-same`**, `no-split` (一切 `Slot`); `cp-same` (`SlotCp`), **`tw-same`**, **`tw-no-split`** (`SlotTw`, 一切 $s$), **`κd-same`** (一切坐标 $c, c'$). `coord-same` (`refl`).
- **[定理, 否定]** **`no-slot-step2`** (一切 `T′`), **`no-slot-steps`** (一切 $a$, $y$).
- **[定理, 前提实例]** `reach-out`, `inst-in`, `inst-out`.
- **[判断]** 构造一路的 `famU` 确实给坐标是高度的种类 (拷贝) 精确的升界, 不经有损的槽; 代价是这些拷贝在世界类型里被认成同一个 (`tw-same`): 升一份等于升一切 (`SlotGen.rs-other`), 两份的界不能不同 (`tw-no-split`). 它推进的是 "同一种类的拷贝" 这一类, 不推进 "坐标类型随级变" 这一类 (`no-slot-κHc`, `no-slot-steps`).
