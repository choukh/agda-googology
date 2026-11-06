# 补四条正面判据, 否定一路 (二): 判据 (i) 顺序一致不定 "世界里有哪些界"

> 不含记号. 入口 [NegTL2](NegTL2.lagda.md). 对着接口 [TL2If](TL2If.lagda.md) §1 ("接口定稿 2026-11-05 21:12 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 候选取自 [NegTL2Pre](NegTL2Pre.lagda.md) (接口定稿前写的). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **判据 (i).** `OrdCrit R`: 级为 $y$ 的种类, 第一位置 `Pr` 与坐标 (沿 `coord` 读成第 $y$ 层高度) 在投影世界 `prj` 里的 `⊲` 互推. 构造一路已证 `Lev` 满足 (`TL2Ord.LevO`), `Fl` 不满足 (`TL2Ord.no-ord-Fl`).
>
> **结果.**
>
> 1. **`ordP` (定理, 对一切 `P`).** `NegTL2Pre.LevP P` (世界的高度分量只取自 `P`) 满足 `OrdCrit`. 所以 `LevP P` 对一切 `P` 同时满足 `LvCrit`, `LvUpper`, `OrdCrit`. 本篇也独立证了 `Lev` 满足 (`ordLev`, 与构造一路的 `LevO` 同一件事) 与重数为 2 的 `LevD` 满足 (`ordD`).
> 2. **`kmP`, `kmP⁻`, `kmP-lv`, `kmP⁻kmP` (定理).** `LevP P c` 与 `Lev c` 的种类逐个对应, 互逆, 保级; 第一位置在对应的种类上都是坐标的 `⊲`. 差别只在世界.
> 3. **`blind-i` (定理, 盲).** 层号 `hs hz` (第 1 层), 同一种类 (新种类): `Lev` 与 `LevP Pz` 都满足 `LvCrit` + `LvUpper` + `OrdCrit`, 两者都有合法的非常值 Ω-分支 (`up`, `upP`); 但 `Lev` 里 $1\lhd\mathrm{h\Omega}\,\mathrm{up}$ (合法世界), `LevP Pz` 里对一切世界 $1\not\lhd\mathrm{h\Omega}\,\mathrm{upP}$, 且 Ω-结点的一切第一位置都经过第 0 支 (`pz-coll`). `blind-iω` 对 `LevP Pn` 同样 (Ω-结点只经过有限坐标, `pn-coll`; $\mathrm{up}(\mathrm{hl}\,\mathrm{ev})$ 在 `Lev` 里是它的第一位置, 在 `LevP Pn` 里不是).
>
> **只否定什么.** 只否定推断 "加了 (i) 之后, 判据确定了第 $c$ 层的种类结构 (到 Ω-结点不塌缩为止)". (i) 确实排除了 `Fl` (构造一路的定理, 本篇不重复); 它没排除的是**世界里可用的界**: (i) 把 `Pr` 绑到 `⊲[ prj w ]`, 但不说哪些高度能当某个合法世界的界, 而 Ω-结点的第一位置只经过界之下的坐标. **不否定**: `Lev`, `OrdCrit` 本身, 构造一路的任何定理; 加一条 "每个合法高度都是某个合法世界的界" (`NegTL2Pre.Rich`) 之后的唯一性 (`LevD` 仍满足, 见入口; 本篇不再往下).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTL2Ord where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (evᴴ; Lg-ev)
open import OCF.Align.NegKindLvLev using (lvK)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR; LevC; LevU)
open import OCF.Align.TL2If
open import OCF.Align.NegTL2Pre
```

## §1 `LevP P` 满足 (i), 对一切 `P`

按层号的构造子: 底层的级不是层号 (`e` 不可能); 后继的新种类 `prj` 取世界第一分量, `Pr` 字面就是 `⊲`; 继承的种类与并的分量递归.

```agda
module OrdP (P : (T : KS) → HB T → Set) where
  prjP : ∀ {S : KS} (c : HB S) κ {y} → lvP P c κ ≡ inj₂ y → Wd (LevP P c) → Wd (LevP P y)
  prjP hz κ ()
  prjP (hs x) (inj₁ κ) e w = prjP x κ e (proj₁ w)
  prjP (hs x) (inj₂ _) refl w = proj₁ w
  prjP (hl f) (n , κ) e w = prjP (f n) κ e (w n)
  prjP (hΩ κ g) (c , κ′) e w = prjP (g c) κ′ e (w c)

  ordP→ : ∀ {S : KS} (c : HB S) κ {y} (e : lvP P c κ ≡ inj₂ y) {w a a′} →
          Pr (LevP P c) κ w a a′ → toH (RP P) c κ e a ⊲[ prjP c κ e w ] toH (RP P) c κ e a′
  ordP→ hz κ ()
  ordP→ (hs x) (inj₁ κ) e q = ordP→ x κ e q
  ordP→ (hs x) (inj₂ _) refl q = q
  ordP→ (hl f) (n , κ) e q = ordP→ (f n) κ e q
  ordP→ (hΩ κ g) (c , κ′) e q = ordP→ (g c) κ′ e q

  ordP← : ∀ {S : KS} (c : HB S) κ {y} (e : lvP P c κ ≡ inj₂ y) {w a a′} →
          toH (RP P) c κ e a ⊲[ prjP c κ e w ] toH (RP P) c κ e a′ → Pr (LevP P c) κ w a a′
  ordP← hz κ ()
  ordP← (hs x) (inj₁ κ) e q = ordP← x κ e q
  ordP← (hs x) (inj₂ _) refl q = q
  ordP← (hl f) (n , κ) e q = ordP← (f n) κ e q
  ordP← (hΩ κ g) (c , κ′) e q = ordP← (g c) κ′ e q

  ordP : ∀ {S : KS} → OrdCrit (RP P {S})
  ordP = record { prj = prjP ; ord→ = ordP→ ; ord← = ordP← }
open OrdP public
```

**`Lev` 与 `LevD` 同样** (与构造一路的 `TL2Ord.LevO` 同一件事; 这里独立写, 不依赖它的文件).

```agda
prjLev′ : ∀ {S : KS} (c : HB S) κ {y} → lvK c κ ≡ inj₂ y → Wd (Lev c) → Wd (Lev y)
prjLev′ hz κ ()
prjLev′ (hs x) (inj₁ κ) e w = prjLev′ x κ e (proj₁ w)
prjLev′ (hs x) (inj₂ _) refl w = proj₁ w
prjLev′ (hl f) (n , κ) e w = prjLev′ (f n) κ e (w n)
prjLev′ (hΩ κ g) (c , κ′) e w = prjLev′ (g c) κ′ e (w c)

ordLev→ : ∀ {S : KS} (c : HB S) κ {y} (e : lvK c κ ≡ inj₂ y) {w a a′} →
          Pr (Lev c) κ w a a′ → toH LevR c κ e a ⊲[ prjLev′ c κ e w ] toH LevR c κ e a′
ordLev→ hz κ ()
ordLev→ (hs x) (inj₁ κ) e q = ordLev→ x κ e q
ordLev→ (hs x) (inj₂ _) refl q = q
ordLev→ (hl f) (n , κ) e q = ordLev→ (f n) κ e q
ordLev→ (hΩ κ g) (c , κ′) e q = ordLev→ (g c) κ′ e q

ordLev← : ∀ {S : KS} (c : HB S) κ {y} (e : lvK c κ ≡ inj₂ y) {w a a′} →
          toH LevR c κ e a ⊲[ prjLev′ c κ e w ] toH LevR c κ e a′ → Pr (Lev c) κ w a a′
ordLev← hz κ ()
ordLev← (hs x) (inj₁ κ) e q = ordLev← x κ e q
ordLev← (hs x) (inj₂ _) refl q = q
ordLev← (hl f) (n , κ) e q = ordLev← (f n) κ e q
ordLev← (hΩ κ g) (c , κ′) e q = ordLev← (g c) κ′ e q

ordLev : ∀ {S : KS} → OrdCrit (LevR {S})
ordLev = record { prj = prjLev′ ; ord→ = ordLev→ ; ord← = ordLev← }

prjD : ∀ {S : KS} (c : HB S) κ {y} → lvD c κ ≡ inj₂ y → Wd (LevD c) → Wd (LevD y)
prjD hz κ ()
prjD (hs x) (inj₁ κ) e w = prjD x κ e (proj₁ w)
prjD (hs x) (inj₂ _) refl w = proj₁ w
prjD (hl f) (n , κ) e w = prjD (f n) κ e (w n)
prjD (hΩ κ g) (c , κ′) e w = prjD (g c) κ′ e (w c)

ordD→ : ∀ {S : KS} (c : HB S) κ {y} (e : lvD c κ ≡ inj₂ y) {w a a′} →
        Pr (LevD c) κ w a a′ → toH RD c κ e a ⊲[ prjD c κ e w ] toH RD c κ e a′
ordD→ hz κ ()
ordD→ (hs x) (inj₁ κ) e q = ordD→ x κ e q
ordD→ (hs x) (inj₂ _) refl q = q
ordD→ (hl f) (n , κ) e q = ordD→ (f n) κ e q
ordD→ (hΩ κ g) (c , κ′) e q = ordD→ (g c) κ′ e q

ordD← : ∀ {S : KS} (c : HB S) κ {y} (e : lvD c κ ≡ inj₂ y) {w a a′} →
        toH RD c κ e a ⊲[ prjD c κ e w ] toH RD c κ e a′ → Pr (LevD c) κ w a a′
ordD← hz κ ()
ordD← (hs x) (inj₁ κ) e q = ordD← x κ e q
ordD← (hs x) (inj₂ _) refl q = q
ordD← (hl f) (n , κ) e q = ordD← (f n) κ e q
ordD← (hΩ κ g) (c , κ′) e q = ordD← (g c) κ′ e q

ordD : ∀ {S : KS} → OrdCrit (RD {S})
ordD = record { prj = prjD ; ord→ = ordD→ ; ord← = ordD← }
```

## §2 `LevP P` 与 `Lev` 的种类逐个对应

```agda
module KmP (P : (T : KS) → HB T → Set) where
  kmP : ∀ {S : KS} (c : HB S) → K (Lev c) → K (LevP P c)
  kmP hz κ = κ
  kmP (hs x) (inj₁ κ) = inj₁ (kmP x κ)
  kmP (hs x) (inj₂ t) = inj₂ t
  kmP (hl f) (n , κ) = n , kmP (f n) κ
  kmP (hΩ κ g) (e , κ′) = e , kmP (g e) κ′

  kmP⁻ : ∀ {S : KS} (c : HB S) → K (LevP P c) → K (Lev c)
  kmP⁻ hz κ = κ
  kmP⁻ (hs x) (inj₁ κ) = inj₁ (kmP⁻ x κ)
  kmP⁻ (hs x) (inj₂ t) = inj₂ t
  kmP⁻ (hl f) (n , κ) = n , kmP⁻ (f n) κ
  kmP⁻ (hΩ κ g) (e , κ′) = e , kmP⁻ (g e) κ′

  kmP⁻kmP : ∀ {S : KS} (c : HB S) κ → kmP⁻ c (kmP c κ) ≡ κ
  kmP⁻kmP hz κ = refl
  kmP⁻kmP (hs x) (inj₁ κ) = cong inj₁ (kmP⁻kmP x κ)
  kmP⁻kmP (hs x) (inj₂ t) = refl
  kmP⁻kmP (hl f) (n , κ) = cong (n ,_) (kmP⁻kmP (f n) κ)
  kmP⁻kmP (hΩ κ g) (e , κ′) = cong (e ,_) (kmP⁻kmP (g e) κ′)

  kmPkmP⁻ : ∀ {S : KS} (c : HB S) κ → kmP c (kmP⁻ c κ) ≡ κ
  kmPkmP⁻ hz κ = refl
  kmPkmP⁻ (hs x) (inj₁ κ) = cong inj₁ (kmPkmP⁻ x κ)
  kmPkmP⁻ (hs x) (inj₂ t) = refl
  kmPkmP⁻ (hl f) (n , κ) = cong (n ,_) (kmPkmP⁻ (f n) κ)
  kmPkmP⁻ (hΩ κ g) (e , κ′) = cong (e ,_) (kmPkmP⁻ (g e) κ′)

  kmP-lv : ∀ {S : KS} (c : HB S) κ → lvP P c (kmP c κ) ≡ lvK c κ
  kmP-lv hz κ = refl
  kmP-lv (hs x) (inj₁ κ) = kmP-lv x κ
  kmP-lv (hs x) (inj₂ t) = refl
  kmP-lv (hl f) (n , κ) = kmP-lv (f n) κ
  kmP-lv (hΩ κ g) (e , κ′) = kmP-lv (g e) κ′
open KmP public
```

## §3 盲: `Lev` 与 `LevP Pz` (`LevP Pn`) 同时满足 (i) 与上一对的判据, Ω-结点的第一位置不同

```agda
-- 两个候选都过的判据
Crit3 : ∀ {S : KS} {B : Set} → LvRule S B → Set
Crit3 R = LvCrit R × LvUpper R × OrdCrit R

blind-i :
  (Crit3 (LevR {S₀}) × Crit3 (RP Pz {S₀})) ×
  -- 同一层号同一种类, 两边都有合法的非常值 Ω-分支
  (LgB {Lev {S₀} (hs hz)} (hΩ (inj₂ tt) (λ c → up c)) × ¬ (up {S₀} hz ≡ up (hs hz))) ×
  (LgB {LevP Pz {S₀} (hs hz)} (hΩ (inj₂ tt) (upP (Pz S₀))) × ¬ (upP (Pz S₀) hz ≡ upP (Pz S₀) (hs hz))) ×
  -- 第一位置: Lev 里 1 ◁ hΩ up (合法世界), LevP Pz 里对一切世界不是
  (Σ (Wd (Lev {S₀} (hs hz))) (λ w → LgW (Lev {S₀} (hs hz)) w × (hs hz ⊲[ w ] hΩ {Lev {S₀} (hs hz)} (inj₂ tt) (λ c → up c)))) ×
  (∀ (w : Wd (LevP Pz {S₀} (hs hz))) → ¬ (hs hz ⊲[ w ] hΩ (inj₂ tt) (upP (Pz S₀))))
blind-i =
  ((LevC , LevU , ordLev) , (CP Pz , UP Pz , ordP Pz)) ,
  (((λ lw e e′ q → up-⊲ q) , (λ c lc → Lg-up c lc)) , (λ ())) ,
  (Lg-upΩP (Pz S₀) , upP-nc (Pz S₀)) ,
  ((azero , hs hz) , proj₁ lev-reach , proj₂ lev-reach) ,
  pz-noreach

blind-iω :
  Crit3 (RP Pn {S₀}) ×
  (LgB {LevP Pn {S₀} (hs hz)} (hΩ (inj₂ tt) (upP (Pn S₀))) × ¬ (upP (Pn S₀) hz ≡ upP (Pn S₀) (hs hz))) ×
  (Σ (Wd (Lev {S₀} (hs hz))) (λ w → LgW (Lev {S₀} (hs hz)) w × (up (hl evᴴ) ⊲[ w ] hΩ {Lev {S₀} (hs hz)} (inj₂ tt) (λ c → up c)))) ×
  (∀ (w : Wd (LevP Pn {S₀} (hs hz))) → ¬ (upP (Pn S₀) (hl evᴴ) ⊲[ w ] hΩ (inj₂ tt) (upP (Pn S₀))))
blind-iω =
  (CP Pn , UP Pn , ordP Pn) ,
  (Lg-upΩP (Pn S₀) , upP-nc (Pn S₀)) ,
  ((azero , hl evᴴ) , proj₁ lev-reach-lim , proj₂ lev-reach-lim) ,
  pn-noreach

-- 重数为 2 的 LevD 也过
blind-D : Crit3 (RD {S₀})
blind-D = CD , UD , ordD
```

## §4 结论 (按档)

- **[定理, 前提实例]** `ordP` (对一切 `P`), `ordLev`, `ordD`: 三族候选满足 `OrdCrit`.
- **[定理, 对应]** `kmP`, `kmP⁻`, `kmP⁻kmP`, `kmPkmP⁻`, `kmP-lv`: 种类逐个对应, 保级.
- **[定理, 盲]** **`blind-i`** (`Lev` 与 `LevP Pz`), **`blind-iω`** (`LevP Pn`), `blind-D` (`LevD`).
- **[判断]** (1) (i) 绑定的是 `Pr` 与 `⊲` 的关系, 界 `Bd` 与世界的内容不在 (i) 里; `LevP P` 的 `Bd` 也是 "在世界高度分量之下" (`NegTL2Pre.P-bd`), 所以即便 (i) 再加一条 "`Bd` 就是 `⊲` 世界的某个分量" 也排除不了 `LevP Pz`. 要排除它需要 "界够多" (`Rich`, 或 (iii) 绑到候选自己的世界上, 见 [NegTL2Raise](NegTL2Raise.lagda.md) §3). (2) 穷尽是判断.
