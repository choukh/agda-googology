# 局部 UIP (一): 局部 Hedberg 归约到什么

> 不含记号. 入口 [LocUip](LocUip.lagda.md), 接口 [LocUipIf](LocUipIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 函数外延只在 §5 作前提 (条件).
>
> 主审的判断是: 由 `bdec` 的局部可判定相等做 "局部 Hedberg" (收缩函数 + J), 得到同一合法世界里可入坐标之间的 UIP. 这里先挑战它, 结果是四条等价 (都是定理):
>
> 1. **局部 Hedberg 只把问题换了个写法** (`diag→loc`, `loc→diag`): `LocUIP w` 当且仅当 `DiagCst w lo` (同一坐标的任意两个证据, 判定给出字面的 `inj₁ refl`). Hedberg 的 J 那一步把起点的证据换成了沿 $e$ 搬回去的证据 (`hed` 的陈述里 `subst (AdmE w) (sym e) py`), 所以要收缩函数在**起点的一切证据**上取同一个值; 这正是 `DiagCst`, 而 `DiagCst` 在 $q\ne p_0$ 处的内容又是一条局部 UIP. 卡点与主审预料的一致: 判定输出的相等证明依赖证据.
> 2. **"局部" 不比全局弱** (`loc→uipᴸ`, `uipᴸ→loc`): 对一切合法世界的 `LocUIP` 当且仅当 `UIPᴸ` (合法高度上的 K). 理由一行: 界 $b$ 自己是可入坐标 (证据 `hself`), 而世界 $(0, x)$ 对一切合法高度 $x$ 合法.
> 3. **"`toLt` 在环上给 `refl`" 就是 UIP** (`loop→uip`, `uip→loop`): `LoopRefl` 当且仅当 `UIPᴴ` (一切高度上的 UIP). 环 $x\lhd x$ 由相等 $e$ 搬 `hself` 得到 (`toLt` 把它送回 `inj₁ e`), 所以环上给 `refl` 就是每个 $e$ 是 `refl`.
> 4. **够用** (`loc→irr`, `irr→lemma1`): 对一切合法世界的 `LocUIP` 推出 `IncIrr`, `IncIrr` 推出 `Lemma1` (`raise₀ᴮ` 保 `Coh≡`).
>
> 所以第一条引理在要求的形式下等价于合法高度上的 K. 本篇**没有**无条件地证出它; 有函数外延时它成立 (`fe→uipᴸ`, 条件: Funext). 它在 `--safe --without-K` 里证不出, 是判断 (高度有函数分支, `hl f ≡ hl f` 与 `f ≡ f` 等价, 后者没有外延时不知道是命题); 否定一路 `LocUipNeg` 处理. 证据无关的写法见 [LocUipFam](LocUipFam.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipHed where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symˡ)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (toLt; _<ᴮ_; irr; wf)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (incD; dD; raise₀; raise₀ᴮ; UIPᴴ)
open import OCF.Align.AdmWUip using (Funext; fe→uip)
open import OCF.Align.LocUipIf
open Slot
open RaiseIf
```

## §1 局部 Hedberg

收缩函数 `colS`: 判定说 "相等" 就取判定给的证明, 说 "不等" 就由矛盾. 它对第二个参数是常值 (`colS-const`). `hed` 是 Hedberg 的 J 那一步; 注意起点的证据是 `subst (AdmE w) (sym e) py`, 不是固定的.

```agda
colS : ∀ {x y : HB S₀} → (x ≡ y) ⊎ ¬ (x ≡ y) → x ≡ y → x ≡ y
colS (inj₁ e′) _ = e′
colS (inj₂ ne) e = ⊥-elim (ne e)

colS-const : ∀ {x y : HB S₀} (d : (x ≡ y) ⊎ ¬ (x ≡ y)) (e e′ : x ≡ y) → colS d e ≡ colS d e′
colS-const (inj₁ _) _ _ = refl
colS-const (inj₂ ne) e _ = ⊥-elim (ne e)

module _ (w : Out) (lo : LgO w) where
  hed : ∀ {x} (px : AdmE w x) {y} (py : AdmE w y) (e : x ≡ y) →
        e ≡ trans (sym (colS (dD w lo (subst (AdmE w) (sym e) py) px) refl)) (colS (dD w lo py px) e)
  hed px py refl = sym (trans-symˡ (colS (dD w lo py px) refl))

  diag→loc : DiagCst w lo → LocUIP w
  diag→loc dc {x} {y} px py e e′ =
    trans (hed px py e)
      (trans (cong₂ (λ a b → trans (sym a) b) (trans (k e) (sym (k e′))) (colS-const (dD w lo py px) e e′))
             (sym (hed px py e′)))
    where
    k : (e : x ≡ y) → colS (dD w lo (subst (AdmE w) (sym e) py) px) refl ≡ refl
    k e = cong (λ d → colS d refl) (dc (subst (AdmE w) (sym e) py) px)

  loc→diag : LocUIP w → DiagCst w lo
  loc→diag u {c₀} q p₀ = h (dD w lo q p₀)
    where
    h : (d : (c₀ ≡ c₀) ⊎ ¬ (c₀ ≡ c₀)) → d ≡ inj₁ refl
    h (inj₁ e) = cong inj₁ (u p₀ q e refl)
    h (inj₂ ne) = ⊥-elim (ne refl)
```

## §2 局部不比合法高度上的 K 弱

```agda
uipᴸ→loc : UIPᴸ → ∀ w → LgO w → LocUIP w
uipᴸ→loc u w lo px py e refl = u (lgB⊲ px (proj₁ lo) (proj₂ lo)) e

loc→uipᴸ : (∀ w → LgO w → LocUIP w) → UIPᴸ
loc→uipᴸ u {x} lx e = u (azero , x) (tt , lx) hself hself e refl
```

## §3 环上给 `refl` 就是 UIP

环 `subst (λ y → x ⊲[ a ] y) e hself` 经 `toLt` 回到 `inj₁ e` (`toLt-tr`, 对 $e$ 归纳, 终点自由).

```agda
toLt-tr : ∀ {x y : HB S₀} {a : A} (e : x ≡ y) → toLt (subst (λ z → x ⊲[ a ] z) e hself) ≡ inj₁ e
toLt-tr refl = refl

inj₁-inj : ∀ {X Y : Set} {u v : X} → _≡_ {A = X ⊎ Y} (inj₁ u) (inj₁ v) → u ≡ v
inj₁-inj refl = refl

loop→K : LoopRefl → ∀ {x : HB S₀} (e : x ≡ x) → e ≡ refl
loop→K lr {x} e = inj₁-inj (trans (sym (toLt-tr {a = azero} e)) (lr (subst (λ z → x ⊲[ azero ] z) e hself)))

loop→uip : LoopRefl → UIPᴴ
loop→uip lr e refl = loop→K lr e

uip→loop : UIPᴴ → LoopRefl
uip→loop u {x} r = h (toLt r)
  where
  h : (d : (x ≡ x) ⊎ (x <ᴮ x)) → d ≡ inj₁ refl
  h (inj₁ e) = cong inj₁ (u e refl)
  h (inj₂ s) = ⊥-elim (irr (wf x) s)
```

## §4 够用: 局部 UIP 推出第一条引理

```agda
loc→irr : (∀ w → LgO w → LocUIP w) → IncIrr
loc→irr u w lo {c₀} {c} p₀ p p′ δ = h (dD w lo p p₀) (dD w lo p′ p₀)
  where
  h : (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → incD d δ ≡ incD d′ δ
  h (inj₁ e) (inj₁ e′) = cong (λ q → subst (λ z → HB (G₀ z)) q δ) (u w lo p₀ p e e′)
  h (inj₁ e) (inj₂ ne) = ⊥-elim (ne e)
  h (inj₂ ne) (inj₁ e) = ⊥-elim (ne e)
  h (inj₂ _) (inj₂ _) = refl

irr→lemma1 : IncIrr → Lemma1
irr→lemma1 irr w lo v c₀ p₀ δ l coh c p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (irr w lo p₀ p p′ δ)

loc→lemma1 : (∀ w → LgO w → LocUIP w) → Lemma1
loc→lemma1 u = irr→lemma1 (loc→irr u)
```

## §5 条件: 函数外延

```agda
uipᴴ→uipᴸ : UIPᴴ → UIPᴸ
uipᴴ→uipᴸ u l e = u e refl

fe→uipᴸ : Funext → UIPᴸ
fe→uipᴸ fe = uipᴴ→uipᴸ (fe→uip fe)

fe→lemma1 : Funext → Lemma1
fe→lemma1 fe = loc→lemma1 (uipᴸ→loc (fe→uipᴸ fe))
```

**前提可满足.** `DiagCst w lo` 在对角上 ($q = p_0$) 成立 (`AdmWCmp.dec₀-diag`); 整条 `DiagCst`, `LocUIP`, `UIPᴸ`, `LoopRefl` 在有函数外延时都成立 (`fe→uipᴸ`, `uip→loop ∘ fe→uip`; 外延在立方模型中成立), 所以 §1 到 §4 的条件定理不是空真. 它们在 `--safe --without-K` 里无条件成立与否: 未证, 本篇不否定.
