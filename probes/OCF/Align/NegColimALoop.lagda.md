# 只对可入层号给分量的否定 (一): 单个增量的更新与环的搬运

> 不含记号. 入口 [NegColimA](NegColimA.lagda.md). 对着接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延 `Funext` 只在 §5 作前提 (条件).
>
> 接口 §5 给两种更新: 族增量的 `RaiseA′` (增量是可入层号上的族 `IncA`, 族相干 `CohI`), 与单个增量的 `RaiseA1` (增量 $\delta :$ `HB (LevA w y₀)`, 律 `at1` 只在 $(y_0,p_0)$ 处, 相干 `coh1`). 本篇说清两者之间差的恰好是什么.
>
> 1. **`raise1→fix⊞`, `raise1→fix₀`** (定理, 对一切 `S`, $X$, $w$, 对**任一**满足 `at1` 与 `coh1` 的更新): 对每个可入层号 $y_0$ 上的环 $\ell : y_0 \equiv y_0$, 一切相干世界 $W$, 一切 $\delta$: `β y₀ p₀ ⊞ subst ℓ δ ≡ β y₀ p₀ ⊞ δ`; 取全 0 的世界得 `hz ⊞ subst ℓ δ ≡ hz ⊞ δ`. 证明: 对终点自由的 J 把 "$(y,p)$ 处的值 $= \beta\,y\,p \oplus$ `subst e δ`" 从 $e=$ `refl` (那里由 `coh1`, `at1` 给出) 推到一切 $e$, 包括环. 这把 `LocUipNegLoop.lemma1→fix₀` (只对特定的 `raise₀ᴮ`) 推广到一切满足律的更新, 并搬到 `ColimAIf` 的世界上.
> 2. **`famOf→fix`, `fix→famOf`** (定理): 把单个增量族化 (在 $(y_0,p_0)$ 处取 $\delta$, 族相干 `CohI`) **当且仅当** $y_0$ 上的环沿 `HB ∘ LevA w` 的搬运不动 $\delta$. 后一方向用 `bdec` (要 $X$, $w$ 合法).
> 3. **反方向的构造** (定理): `fix→raise1`: 一切可入层号上环的搬运平凡 (`LoopFixAt`) 且 $X$, $w$ 合法时, 有 `RaiseA1`. 所以 `RaiseA1` 夹在 `LoopFix₀` 与 `LoopFix` 之间, 与 `LocUipNegLoop.chain` 同形.
> 4. **前提可满足** (§5): 外层界有限 (`finH k`) 时 `RaiseA1` 无条件存在 (`raise1-fin`); 有 `UIP` 时对一切合法的 $X$, $w$ 存在 (`uip→raise1`); `S₀` 上有函数外延时存在 (`fe→raise1₀`, 条件: Funext, 经 `AdmWUip.fe→uip`). 接口的最小实例 $(x_0, w_\omega)$ 与第一个无限层号 `up ω₀`: `raise1→fixω` 的前提在 `HB S₁` 的 UIP 下可满足 (`uip→raise1`); "函数外延推出 `HB S₁` 的 UIP" 是判断 (仓库只对 `HB S₀` 证了).
>
> **为什么是构造一路需要的律.** `at1`, `coh1` 是接口 `RaiseA1` 的字段原文; `coh1` 是必需的, 因为认同 (`CrossA`) 以 `CohA` 为前提 (拷贝读同一个界要跨证据相干, 见 [NegColimACross](NegColimACross.lagda.md) 的 `cross-needs-coh`), 而回灌后的世界还要被认同. 若回灌只产出单个增量 (折叠在节点 $(y_0,p_0)$ 处算出一个高度), 构造一路要么用 `RaiseA1`, 要么先族化再用 `RaiseA′`; 两条路都要环的搬运平凡 (1, 2).
>
> **只否定什么.** 这里**没有禁忌**: 结论都被函数外延推出 (`HB S₀` 上: `fe→raise1₀`), 所以不能用来关闭路线. 编译的是强度: 单个增量的写法要 `LoopFix₀` (可入层号上), 族化要 `LoopFix`. **不否定**: 族增量的 `RaiseA′` (它的 `atA` 读 `δ y p`, 不搬运; 本篇不碰); 回灌直接产出相干的族 (例如对层号结构递归定义的截面, `LocUipNegSec.sec→coh` 的形状); 有限层号; 有 UIP 的模型.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegColimALoop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.StallDxBdec using (bdec)
open import OCF.Align.ColimWIf using (AdmL; DecAt; S₁; finH; x₀; ω₀)
open import OCF.Align.ColimWNeg using (wω; Lg-wω; Lg-ω₀; fin⊲; unhs; decAt-fin)
open import OCF.Align.AdmWCoh using (UIPᴴ)
open import OCF.Align.AdmWUip using (Funext; fe→uip)
open import OCF.Align.ColimAIf
```

## §1 任一满足 `at1`, `coh1` 的更新推出环的搬运在 `⊞` 之后平凡

```agda
module _ {S : KS} {X : HB S} {w : Wd S} where
  open Adm X w
  open RaiseA1

  HL : HB S → Set
  HL z = HB (LevA w z)

  W₀A : GWA X w
  W₀A = azero , λ y p → hz

  coh₀ : CohA W₀A
  coh₀ y p p′ = refl

  -- (y, p) 处的值, 沿 y₀ ≡ y 的一切证明 (对终点自由的 J)
  along1 : (R : RaiseA1) (W : GWA X w) → CohA W → ∀ {y₀} (p₀ : AdmL X w y₀) (δ : HL y₀) →
    ∀ y (e : y₀ ≡ y) (p : AdmL X w y) → proj₂ (raise1 R W y₀ p₀ δ) y p ≡ proj₂ W y p ⊞ subst HL e δ
  along1 R W cW {y₀} p₀ δ .y₀ refl p =
    trans (coh1 R W y₀ p₀ δ cW y₀ p p₀) (trans (at1 R W y₀ p₀ δ) (cong (λ t → t ⊞ δ) (cW y₀ p₀ p)))

  raise1→fix⊞ : RaiseA1 → ∀ W → CohA W → ∀ {y₀} (p₀ : AdmL X w y₀) (ℓ : y₀ ≡ y₀) (δ : HL y₀) →
    proj₂ W y₀ p₀ ⊞ subst HL ℓ δ ≡ proj₂ W y₀ p₀ ⊞ δ
  raise1→fix⊞ R W cW p₀ ℓ δ = trans (sym (along1 R W cW p₀ δ _ ℓ p₀)) (along1 R W cW p₀ δ _ refl p₀)

  -- 可入层号上的 LoopFix₀
  LoopFix₀At : HB S → Set
  LoopFix₀At y₀ = (ℓ : y₀ ≡ y₀) (δ : HL y₀) → hz ⊞ subst HL ℓ δ ≡ hz ⊞ δ

  raise1→fix₀ : RaiseA1 → ∀ {y₀} → AdmL X w y₀ → LoopFix₀At y₀
  raise1→fix₀ R p₀ ℓ δ = raise1→fix⊞ R W₀A coh₀ p₀ ℓ δ
```

## §2 族化单个增量 ⇔ 环的搬运平凡

```agda
  LoopFixAt : HB S → Set
  LoopFixAt y₀ = (ℓ : y₀ ≡ y₀) (δ : HL y₀) → subst HL ℓ δ ≡ δ

  record FamOf {y₀ : HB S} (p₀ : AdmL X w y₀) (δ : HL y₀) : Set where
    field
      fam     : IncA
      fam-at  : fam y₀ p₀ ≡ δ
      fam-coh : CohI fam
  open FamOf

  module _ {y₀ : HB S} {p₀ : AdmL X w y₀} {δ : HL y₀} (F : FamOf p₀ δ) where
    alongF : ∀ y (e : y₀ ≡ y) (p : AdmL X w y) → fam F y p ≡ subst HL e δ
    alongF .y₀ refl p = trans (fam-coh F y₀ p p₀) (fam-at F)

    famOf→fix : (ℓ : y₀ ≡ y₀) → subst HL ℓ δ ≡ δ
    famOf→fix ℓ = trans (sym (alongF y₀ ℓ p₀)) (alongF y₀ refl p₀)
```

反方向: 合法的 $X$, $w$ 之下, 两个可入层号的相等由 `bdec` 判定 (`dA`); 判为相等时沿相等证明搬运 (`incA`).

```agda
  hs-inj : ∀ {a b : HB S} → hs a ≡ hs b → a ≡ b
  hs-inj refl = refl

  module Legal (lw : LgW S w) (lX : LgB X) where
    dA : ∀ {y₀ y} → AdmL X w y → AdmL X w y₀ → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)
    dA p p₀ with bdec p₀ p lw lX
    ... | inj₁ e = inj₁ (hs-inj e)
    ... | inj₂ ne = inj₂ (λ e → ne (cong hs e))

    incA : ∀ {y₀ y} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → HL y₀ → HL y
    incA (inj₁ e) δ = subst HL e δ
    incA (inj₂ _) δ = hz

    -- 两条相等证明的搬运: 化成 y₀ 上的环
    fix-pair : ∀ {y₀ y} → LoopFixAt y₀ → (e e′ : y₀ ≡ y) (δ : HL y₀) → subst HL e δ ≡ subst HL e′ δ
    fix-pair F e refl δ = F e δ

    incA-irr : ∀ {y₀ y} → LoopFixAt y₀ → (d d′ : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) (δ : HL y₀) → incA d δ ≡ incA d′ δ
    incA-irr F (inj₁ e) (inj₁ e′) δ = fix-pair F e e′ δ
    incA-irr F (inj₁ e) (inj₂ ne) δ = ⊥-elim (ne e)
    incA-irr F (inj₂ ne) (inj₁ e) δ = ⊥-elim (ne e)
    incA-irr F (inj₂ _) (inj₂ _) δ = refl

    incA-diag : ∀ {y₀} → LoopFixAt y₀ → (d : (y₀ ≡ y₀) ⊎ ¬ (y₀ ≡ y₀)) (δ : HL y₀) → incA d δ ≡ δ
    incA-diag F (inj₁ ℓ) δ = F ℓ δ
    incA-diag F (inj₂ ne) δ = ⊥-elim (ne refl)

    fix→famOf : ∀ {y₀} (p₀ : AdmL X w y₀) (δ : HL y₀) → LoopFixAt y₀ → FamOf p₀ δ
    fix→famOf p₀ δ F = record
      { fam = λ y p → incA (dA p p₀) δ
      ; fam-at = incA-diag F (dA p₀ p₀) δ
      ; fam-coh = λ y p p′ → incA-irr F (dA p p₀) (dA p′ p₀) δ }
```

## §3 有了 `LoopFixAt`, 就有 `RaiseA1`

```agda
    fix→raise1 : (∀ y₀ → AdmL X w y₀ → LoopFixAt y₀) → RaiseA1
    fix→raise1 F = record
      { raise1 = λ W y₀ p₀ δ → proj₁ W , (λ y p → proj₂ W y p ⊞ incA (dA p p₀) δ)
      ; at1 = λ W y₀ p₀ δ → cong (λ t → proj₂ W y₀ p₀ ⊞ t) (incA-diag (F y₀ p₀) (dA p₀ p₀) δ)
      ; off1 = λ W y₀ p₀ δ y p ne → off-help (proj₂ W y p) (dA p p₀) {δ} ne
      ; coh1 = λ W y₀ p₀ δ cW y p p′ →
          cong₂ (λ s t → s ⊞ t) (cW y p p′) (incA-irr (F y₀ p₀) (dA p p₀) (dA p′ p₀) δ) }
      where
      off-help : ∀ {y₀ y} (s : HL y) (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) {δ : HL y₀} → ¬ (y₀ ≡ y) → s ⊞ incA d δ ≡ s
      off-help s (inj₁ e) ne = ⊥-elim (ne e)
      off-help s (inj₂ _) ne = refl

  -- UIP 推出 LoopFixAt
  UIPˢ : Set
  UIPˢ = ∀ {a b : HB S} (e e′ : a ≡ b) → e ≡ e′

  uip→fix : UIPˢ → ∀ y₀ → LoopFixAt y₀
  uip→fix u y₀ ℓ δ = cong (λ q → subst HL q δ) (u ℓ refl)

  uip→raise1 : UIPˢ → LgW S w → LgB X → RaiseA1
  uip→raise1 u lw lX = Legal.fix→raise1 lw lX (λ y₀ _ → uip→fix u y₀)
```

## §4 接口的最小实例: 第一个无限层号

外层界 $x_0 =$ `Ωtop S₀`, 外层世界 $w_\omega$, 层号 `up ω₀` 的证据 `pω` (接口 §6). 前提 `RaiseA1` 在 `HB S₁` 的 UIP 之下可满足 (`raise1ω-sat`).

```agda
raise1→fixω : Adm.RaiseA1 x₀ wω → LoopFix₀At {X = x₀} {w = wω} (up ω₀)
raise1→fixω R = raise1→fix₀ R pω

raise1ω-sat : UIPˢ {S = S₁} {X = x₀} {w = wω} → Adm.RaiseA1 x₀ wω
raise1ω-sat u = uip→raise1 u Lg-wω (Lg-Ωtop S₀)
```

## §5 前提可满足

**有限外层界, 无条件.** $X =$ `finH k` 时可入层号都是有限的, 每个都有判定证书 (`ColimWNeg.decAt-fin`); 更新用证书判定裸层号 $y$, 值与证据无关, 所以 `coh1` 一行.

```agda
module _ {S : KS} {w : Wd S} (k : ℕ) where
  open Adm {S} (finH k) w
  open RaiseA1

  HF : HB S → Set
  HF z = HB (LevA w z)

  finAdm : ∀ {y₀ : HB S} → AdmL (finH k) w y₀ → Σ ℕ (λ m → y₀ ≡ finH m)
  finAdm {y₀} p with fin⊲ k p
  ... | zero , ()
  ... | suc m , e = m , cong unhs e

  decA : ∀ {y₀} → AdmL (finH k) w y₀ → DecAt y₀
  decA p = subst DecAt (sym (proj₂ (finAdm p))) (decAt-fin (proj₁ (finAdm p)))

  incF : ∀ {y₀ y} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → HF y₀ → HF y
  incF (inj₁ e) δ = subst (HF) e δ
  incF (inj₂ _) δ = hz

  offF : ∀ {y₀ y} (s : HF y) (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) {δ : HF y₀} → ¬ (y₀ ≡ y) → s ⊞ incF d δ ≡ s
  offF s (inj₁ e) ne = ⊥-elim (ne e)
  offF s (inj₂ _) ne = refl

  raise1-fin : RaiseA1
  raise1-fin = record
    { raise1 = λ W y₀ p₀ δ → proj₁ W , (λ y p → proj₂ W y p ⊞ incF (proj₁ (decA p₀) y) δ)
    ; at1 = λ W y₀ p₀ δ → cong (λ d → proj₂ W y₀ p₀ ⊞ incF {y₀} {y₀} d δ) (proj₂ (decA p₀))
    ; off1 = λ W y₀ p₀ δ y p ne → offF (proj₂ W y p) (proj₁ (decA p₀) y) {δ} ne
    ; coh1 = λ W y₀ p₀ δ cW y p p′ → cong (λ (s : HF y) → s ⊞ incF (proj₁ (decA p₀) y) δ) (cW y p p′) }
```

**`S₀` 上, 条件: Funext.** 外层界 $X_0 = \omega + 2$ (`HB S₀`), 外层世界 $0$; 无限层号 $\omega$ 可入. 有函数外延就有 `HB S₀` 的 UIP (`AdmWUip.fe→uip`), 从而有 `RaiseA1`. 所以 §1 的前提在含无限可入层号的实例上 (在函数外延之下) 可满足, 结论在那里成立而不矛盾.

```agda
X₀ : HB S₀
X₀ = hs (hs ω₀)

lgX₀ : LgB X₀
lgX₀ = Lg-ω₀

pω₀ : AdmL X₀ azero ω₀
pω₀ = hsuc hself

fe→raise1₀ : Funext → Adm.RaiseA1 X₀ azero
fe→raise1₀ fe = uip→raise1 (fe→uip fe) tt lgX₀

-- 同一实例上 §1 的结论 (条件: Funext; 由前提可满足说明它不空)
fe→fix₀ω : Funext → LoopFix₀At {X = X₀} {w = azero} ω₀
fe→fix₀ω fe = raise1→fix₀ (fe→raise1₀ fe) pω₀
```
