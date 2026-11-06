# 树的语言, 第二对 (一): 判据 (i) 顺序一致

> 不含记号. 入口 [TL2](TL2.lagda.md), 接口 [TL2If](TL2If.lagda.md) ("接口定稿 2026-11-05 21:12 (首次编译通过)"). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **问题.** 上一对: 平的候选 `Fl` 满足 `LvCrit` + `LvUpper`, 级集合与 `Lev` 相同, 但一切合法 Ω-结点的分支是常函数 (`NegTreeLangFlat.fl-const`). 加 (i) `OrdCrit` (第一位置就是坐标高度在投影世界里的 `⊲`) 之后呢?
>
> **结果 (定理).**
>
> 1. **`LevO`, `LvO` (实例).** `Lev` 满足 `OrdCrit`, `LFReTy.Lv` 满足 `OrdCritL`; 投影 `prj` 就是沿种类的来路取世界的分量 (`step` 取第一分量, `sup` 取第 $i$ 分量), `ord→`, `ord←` 都是恒等.
> 2. **`no-ord-Fl`, `no-ord-FlL` (定理, 排除).** 平的候选不满足 (i): 第 1 层的新种类的第一位置恒真, 推出 `hs hz ⊲ hz`, 没有这样的项.
> 3. **`ord-dec` (形状定理).** 满足 (i) 的任一候选, 任一层, 级为 $y$ 的任一种类: 同一合法世界的界之下的两个坐标**相等可判定**. 证明: `cmpK` 给出一个方向的 `Pr`, (i) 把它变成坐标高度的 `⊲`, 再用 `StallDxBdec.toLt` (非自反的第一位置是严格子项). 这正是 (ii) 的升界在种类坐标上可实现所要的 (见 [TL2Raise](TL2Raise.lagda.md) 的 `Cross`): **(i) 推出 "界下的坐标可以做升界的键"**.
> 4. **`ord-antisym` (形状定理).** 满足 (i) 时, 一个种类的第一位置 (在任两个世界里) 反对称. `Fl` 的退化机制 (两个方向都是第一位置) 被这一条整个排除, 不只排除 `Fl`.
> 5. **`ord-mono` (形状定理, "Ω-分支对坐标单调").** 满足 (i) 时, 合法 Ω-结点的分支对坐标高度的 `⊲` (投影世界里) 单调.
>
> **只说明什么, 不说明什么.** (i) 排除的是 "第一位置不是坐标高度的序" 的候选. 它**不排除**世界里的界只取一部分高度的候选: 否定一路的 `NegTL2Pre.LevP` (step 的世界高度分量取自 $\Sigma$ (HB S) P) 对一切 $P$ 满足 Pr = ⊲, 但 $P = (\equiv \mathrm{hz})$ 时 Ω-结点在第一位置上塌成第 0 支 (否定一路的消息, 其定理以它的文件为准; 本篇未复核). 把这一类也排除要 "每个合法高度都是某个合法世界的界"; 本路在 [TL2Raise](TL2Raise.lagda.md) §5 证明它可以由 (iii)+(iv) 在 "界框架" 上推出 (`up→rich`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TL2Ord where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (toLt; lt→≢)
open import OCF.Align.NegKindLvLev using (lvK)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; lvl; E-lvl)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR; LvRL)
open import OCF.Align.NegTreeLangFlat using (RFl; RFlL; antisym)
open import OCF.Align.TL2If
```

## §1 `Lev` 与 `Lv` 满足 (i)

```agda
prjLev : ∀ {S : KS} (c : HB S) κ {y} → lvK c κ ≡ inj₂ y → Wd (Lev c) → Wd (Lev y)
prjLev hz κ ()
prjLev (hs x) (inj₁ κ) e w = prjLev x κ e (proj₁ w)
prjLev (hs x) (inj₂ _) refl w = proj₁ w
prjLev (hl f) (n , κ) e w = prjLev (f n) κ e (w n)
prjLev (hΩ κ g) (c , κ′) e w = prjLev (g c) κ′ e (w c)

ordLev→ : ∀ {S : KS} (c : HB S) κ {y} (e : lvK c κ ≡ inj₂ y) {w a a′} →
  Pr (Lev c) κ w a a′ → toH LevR c κ e a ⊲[ prjLev c κ e w ] toH LevR c κ e a′
ordLev→ hz κ ()
ordLev→ (hs x) (inj₁ κ) e p = ordLev→ x κ e p
ordLev→ (hs x) (inj₂ _) refl p = p
ordLev→ (hl f) (n , κ) e p = ordLev→ (f n) κ e p
ordLev→ (hΩ κ g) (c , κ′) e p = ordLev→ (g c) κ′ e p

ordLev← : ∀ {S : KS} (c : HB S) κ {y} (e : lvK c κ ≡ inj₂ y) {w a a′} →
  toH LevR c κ e a ⊲[ prjLev c κ e w ] toH LevR c κ e a′ → Pr (Lev c) κ w a a′
ordLev← hz κ ()
ordLev← (hs x) (inj₁ κ) e p = ordLev← x κ e p
ordLev← (hs x) (inj₂ _) refl p = p
ordLev← (hl f) (n , κ) e p = ordLev← (f n) κ e p
ordLev← (hΩ κ g) (c , κ′) e p = ordLev← (g c) κ′ e p

LevO : ∀ {S : KS} → OrdCrit (LevR {S})
LevO = record { prj = prjLev ; ord→ = ordLev→ ; ord← = ordLev← }

prjL : ∀ x κ → Wd (Lv x) → Wd (Lv (lvl x κ))
prjL lz ()
prjL (ls x) (inj₁ κ) w = prjL x κ (proj₁ w)
prjL (ls x) (inj₂ _) w = proj₁ w
prjL (ll f) (n , κ) w = prjL (f n) κ (w n)
prjL (lΩ k g) (inj₁ t , inj₁ κ) w = prjL k κ (proj₁ (w (inj₁ t)))
prjL (lΩ k g) (inj₁ t , inj₂ _) w = proj₁ (w (inj₁ t))
prjL (lΩ k g) (inj₂ c , κ) w = prjL (g c) κ (w (inj₂ c))

ordL→ : ∀ x κ {w a a′} → Pr (Lv x) κ w a a′ → toHL LvRL x κ a ⊲[ prjL x κ w ] toHL LvRL x κ a′
ordL→ lz ()
ordL→ (ls x) (inj₁ κ) p = ordL→ x κ p
ordL→ (ls x) (inj₂ _) p = p
ordL→ (ll f) (n , κ) p = ordL→ (f n) κ p
ordL→ (lΩ k g) (inj₁ t , inj₁ κ) p = ordL→ k κ p
ordL→ (lΩ k g) (inj₁ t , inj₂ _) p = p
ordL→ (lΩ k g) (inj₂ c , κ) p = ordL→ (g c) κ p

ordL← : ∀ x κ {w a a′} → toHL LvRL x κ a ⊲[ prjL x κ w ] toHL LvRL x κ a′ → Pr (Lv x) κ w a a′
ordL← lz ()
ordL← (ls x) (inj₁ κ) p = ordL← x κ p
ordL← (ls x) (inj₂ _) p = p
ordL← (ll f) (n , κ) p = ordL← (f n) κ p
ordL← (lΩ k g) (inj₁ t , inj₁ κ) p = ordL← k κ p
ordL← (lΩ k g) (inj₁ t , inj₂ _) p = p
ordL← (lΩ k g) (inj₂ c , κ) p = ordL← (g c) κ p

LvO : OrdCritL LvRL
LvO = record { prjᴸ = prjL ; ordᴸ→ = ordL→ ; ordᴸ← = ordL← }
```

## §2 平的候选不满足 (i)

第 1 层 (`hs hz`) 的新种类, 坐标是第 0 层的高度; 平的结构里第一位置恒真, (i) 就给出 `hs hz ⊲ hz`.

```agda
no-ord-Fl : ¬ OrdCrit (RFl {S₀})
no-ord-Fl O with ord→ O (hs hz) (inj₂ tt) refl {tt} {hs hz} {hz} tt
... | ()

no-ord-FlL : ¬ OrdCritL RFlL
no-ord-FlL O with ordᴸ→ O (ls lz) (inj₂ tt) {tt} {hs hz} {hz} tt
... | ()
```

## §3 满足 (i) 的候选: 界下坐标可判定, 第一位置反对称, 分支单调

```agda
subst-inj : ∀ {X Y : Set} (p : X ≡ Y) {a a′ : X} → subst (λ Z → Z) p a ≡ subst (λ Z → Z) p a′ → a ≡ a′
subst-inj refl q = q

module _ {S : KS} {B : Set} {R : LvRule S B} (O : OrdCrit R) where
  private
    T : HB S → KS
    T = L R

  ord-dec : ∀ c κ {y} (e : lv R c κ ≡ inj₂ y) {w a a′} →
    Bd (T c) κ a w → Bd (T c) κ a′ w → LgW (T c) w → (a ≡ a′) ⊎ ¬ (a ≡ a′)
  ord-dec c κ e {w} {a} {a′} ba ba′ lw with cmpK (T c) ba ba′ lw
  ... | inj₂ p with toLt (ord→ O c κ e p)
  ...   | inj₁ q = inj₁ (subst-inj (cdEq R c κ e) q)
  ...   | inj₂ s = inj₂ (λ q → lt→≢ s (cong (toH R c κ e) q))
  ord-dec c κ e {w} {a} {a′} ba ba′ lw | inj₁ p with toLt (ord→ O c κ e p)
  ...   | inj₁ q = inj₁ (sym (subst-inj (cdEq R c κ e) q))
  ...   | inj₂ s = inj₂ (λ q → lt→≢ s (cong (toH R c κ e) (sym q)))

  ord-antisym : ∀ c κ {y} (e : lv R c κ ≡ inj₂ y) {w w′ a a′} →
    Pr (T c) κ w a a′ → Pr (T c) κ w′ a′ a → a ≡ a′
  ord-antisym c κ e p q = subst-inj (cdEq R c κ e) (antisym (ord→ O c κ e p) (ord→ O c κ e q))

  ord-mono : ∀ c κ {y} (e : lv R c κ ≡ inj₂ y) (g : E (T c) κ → HB (T c)) → LgB {T c} (hΩ κ g) →
    ∀ {w a a′} → LgW (T c) w → Bd (T c) κ a w → Bd (T c) κ a′ w →
    toH R c κ e a ⊲[ prj O c κ e w ] toH R c κ e a′ → g a ⊲[ w ] g a′
  ord-mono c κ e g (mo , _) lw ba ba′ q = mo lw ba ba′ (ord← O c κ e q)
```

**`LH` 上同样** (界下坐标可判定).

```agda
module _ {R : LvRuleL} (O : OrdCritL R) where
  ord-decL : ∀ x κ {w a a′} → Bd (Lᴸ R x) κ a w → Bd (Lᴸ R x) κ a′ w → LgW (Lᴸ R x) w → (a ≡ a′) ⊎ ¬ (a ≡ a′)
  ord-decL x κ ba ba′ lw with cmpK (Lᴸ R x) ba ba′ lw
  ... | inj₂ p with toLt (ordᴸ→ O x κ p)
  ...   | inj₁ q = inj₁ (subst-inj (coordᴸ R x κ) q)
  ...   | inj₂ s = inj₂ (λ q → lt→≢ s (cong (toHL R x κ) q))
  ord-decL x κ ba ba′ lw | inj₁ p with toLt (ordᴸ→ O x κ p)
  ...   | inj₁ q = inj₁ (sym (subst-inj (coordᴸ R x κ) q))
  ...   | inj₂ s = inj₂ (λ q → lt→≢ s (cong (toHL R x κ) (sym q)))
```

**实例.** `Lev`, `Lv` 上这几条都有居留 (由 `LevO`, `LvO`); 前提 `Bd`, `LgW` 可满足: 例如 `Lev (hs hz)` 的新种类, 世界 `(azero , hs hz)` (合法), 坐标 `hz` 与 `hs hz` 都在界下.

```agda
ex-dec : (hz ≡ hs hz) ⊎ ¬ (hz ≡ hs hz)
ex-dec = ord-dec {S = S₀} LevO (hs hz) (inj₂ tt) refl {w = (azero , hs hz)} (hsuc hself) hself (tt , tt)
```

## §4 结论 (按档)

- **[定理, 实例]** `LevO`, `LvO`: 现有形状满足 (i).
- **[定理, 排除]** **`no-ord-Fl`**, **`no-ord-FlL`**: 平的候选被 (i) 排除.
- **[定理, 形状]** **`ord-dec`**, `ord-decL` (界下坐标相等可判定), **`ord-antisym`** (第一位置反对称), **`ord-mono`** (合法分支对坐标高度单调); `ex-dec` (前提可满足).
- **[判断]** (i) 是 "坐标是高度, 就用高度自己的序", 读自 `HtTowerTy.step` 的新种类那一行. 它不说世界里的界取哪些高度 (见文件头, 否定一路的 `LevP`).
