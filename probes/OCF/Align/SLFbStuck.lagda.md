# 带证据的回灌 (四): 在 `SL` 本身上卡在哪里

> 不含记号. 入口 [SLFb](SLFb.lagda.md), 接口 [SLFbIf](SLFbIf.lagda.md) §4. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 本篇有一条**条件定理** (`rsJ-top`, 前提是一个高度上的 UIP `UIPat`), 它不进闭项, 不进证书.
>
> 任务第 1 条: 在 `SL` 的世界上加证据, 让坐标是高度的种类 (含第 $n\ge2$ 站的层号 `lΩ lz _` 下的) 有精确升界, 不判定含函数的下标. 本路试了 "字面公共上界" 的证据 (`StallDxBdec.bdec`: 两个高度都是同一合法 $\Lambda^*$ 在同一合法世界 $w^*$ 里的第一位置时, 相等可判定). **未找到**; 卡在两处, 下面是编译错误原文 (scratch 实验, 选项同仓库: `--safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns`, 退出码 42):
>
> **卡点 1: `SL` 的世界以 `LH` 为下标, 证据在高度上.** 即使假设**一切**层号都带公共上界证据 (`adm : ∀ k → toHB k ⊲[ w* ] Λ*`, 这个假设本身已不合理), 用 `bdec` 判出的是 `HB SL` 上的相等, 分量的类型却是 `Wd (FL k)`; `ofHB (toHB k)` 与 `k` 只在构造子上互逆 (`LFReTy` 文末), 不定义相等, 证 `≡` 要函数外延:
>
> > `SLFbExpIx.agda:23.79-82: error: [UnequalTerms]`
> > `k != ofHB (toHB k) of type LH`
> > `when checking that the expression w k has type Slot (toHB k)`
>
> **卡点 2: 换成以带证据的高度为下标的世界 (`WJ` 下面), 判等可构造, 但对角上的判等证明不是 `refl`.** `bdec p p` 给出某个 $e : h_0\equiv h_0$, 升后在 $j_0$ 处的新界是 `subst Slot e v`; 不开 K, `HB SL` 含函数分支, 证不出 $e\equiv$ `refl`:
>
> > `SLFbExpUip.agda:30.19-23: error: [UnequalTerms]`
> > `proj₂`
> > `(sel`
> > ` (bdec (proj₂ j₀) (proj₂ j₀) lw* lΛ*`
> > `  | cmpB (proj₂ j₀) (proj₂ j₀) lw* lΛ*)`
> > ` (proj₁ (w j₀) , v) (w j₀))`
> > `!= v of type HB (Lv (ofHB (proj₁ j₀)))`
> > `when checking that the expression refl has type`
> > `proj₂ (rsJ j₀ w v j₀) ≡ v`
>
> 下面把卡点 2 写成编译过的条件定理: 在 $h_0$ 处有 UIP (`UIPat h₀`) 时, `rsJ` 的 `rs-top` 成立. 前提的实例: 不含函数的高度 (例 `hz`) 上 UIP 可证 (`uip-hz`, 局部 Hedberg: `hz` 与一切高度的相等可判定). 第 $n\ge2$ 站的层号的高度 `tw n` 含函数分支, 本路没有找到它的 UIP 证明, 也没有否定 (判断: 不开 K, 不加外延时多半证不出).
>
> **本路的出口 (构造, 见 `SLFbTm`).** 把证据从 "高度的公共上界" 换成 "站号": 下标类型是 $\mathbb N$, 判等对角上是 `refl` (`GenFoldInst.upd-at`), 层号 `kₙ n` 可以含函数而不被比较. 代价: 世界只有站下标的分量 (`SLFbIf.SNᵢ`), 不是 `SL` 的整个世界; 站与站之间的层 (例 $1+c$ 层, $c$ 是可数坐标) 的种类只作为某站 `Lv (kₙ n)` 里的深种类出现, 经坐标下标的那些有损 (`SLFbTm.deep2-lossy`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SLFbStuck where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
open import OCF.Align.StallDxBdec using (bdec)
```

## §1 以带证据的高度为下标的世界, 判等式的升界

```agda
module _ (w* : Wd SL) (Λ* : HB SL) (lw* : LgW SL w*) (lΛ* : LgB Λ*) where
  J : Set
  J = Σ (HB SL) (λ h → h ⊲[ w* ] Λ*)

  Slot : HB SL → Set
  Slot h = Wd (FL (ofHB h))

  WJ : Set
  WJ = (j : J) → Slot (proj₁ j)

  sel : ∀ {h₀ h} → (h₀ ≡ h) ⊎ ¬ (h₀ ≡ h) → Slot h₀ → Slot h → Slot h
  sel (inj₁ e) x y = subst Slot e x
  sel (inj₂ _) x y = y

  rsJ : (j₀ : J) → WJ → HB (Lv (ofHB (proj₁ j₀))) → WJ
  rsJ j₀ w v j = sel (bdec (proj₂ j₀) (proj₂ j) lw* lΛ*) (proj₁ (w j₀) , v) (w j)

  UIPat : HB SL → Set
  UIPat h = ∀ (e : h ≡ h) → e ≡ refl

  sel-top : ∀ {h₀} (d : (h₀ ≡ h₀) ⊎ ¬ (h₀ ≡ h₀)) (x y : Slot h₀) → UIPat h₀ → proj₂ (sel d x y) ≡ proj₂ x
  sel-top {h₀} (inj₁ e) x y u = subst (λ e′ → proj₂ (subst Slot e′ x) ≡ proj₂ x) (sym (u e)) refl
  sel-top (inj₂ ne) x y u = ⊥-elim (ne refl)

  -- 条件定理: 前提是 h₀ 处的 UIP
  rsJ-top : ∀ j₀ w v → UIPat (proj₁ j₀) → proj₂ (rsJ j₀ w v j₀) ≡ v
  rsJ-top j₀ w v u = sel-top (bdec (proj₂ j₀) (proj₂ j₀) lw* lΛ*) (proj₁ (w j₀) , v) (w j₀) u
```

## §2 前提的实例: 不含函数的高度上的 UIP

`hz` 与任一高度的相等可判定 (按构造子); 局部 Hedberg 给出 `hz ≡ hz` 的一切证明都是 `refl`. 不用 K: 唯一的模式匹配 `refl` 都在一端自由的等式上.

```agda
decZ : ∀ (h : HB SL) → (hz ≡ h) ⊎ ¬ (hz ≡ h)
decZ hz = inj₁ refl
decZ (hs h) = inj₂ (λ ())
decZ (hl f) = inj₂ (λ ())
decZ (hΩ κ g) = inj₂ (λ ())

nz : ∀ {h} → hz ≡ h → hz ≡ h
nz {h} p with decZ h
... | inj₁ q = q
... | inj₂ n = ⊥-elim (n p)

nz-const : ∀ {h} (p q : hz ≡ h) → nz p ≡ nz q
nz-const {h} p q with decZ h
... | inj₁ r = refl
... | inj₂ n = ⊥-elim (n p)

trans-sym : ∀ {X : Set} {x y : X} (a : x ≡ y) → trans (sym a) a ≡ refl
trans-sym refl = refl

nz-canon : ∀ {h} (p : hz ≡ h) → trans (sym (nz refl)) (nz p) ≡ p
nz-canon refl = trans-sym (nz refl)

uip-hz : ∀ (e : hz {SL} ≡ hz) → e ≡ refl
uip-hz e = trans (sym (nz-canon e)) (trans (cong (trans (sym (nz refl))) (nz-const e refl)) (nz-canon refl))
```

## 结论 (按档)

- **[条件定理]** `rsJ-top`: 以带公共上界证据的高度为下标的世界上, 判等式升界在 $h_0$ 处精确, 前提 `UIPat h₀`. 前提实例 `uip-hz` (定理).
- **[编译错误, 未找到]** `SL` 本身的世界 (以 `LH` 为下标) 上, 带公共上界证据的判等搬不到分量类型上 (卡点 1); 换成带证据的高度为下标的世界, 对角上的判等不是 `refl` (卡点 2). 写 "未找到", 不写 "不存在".
- **[判断]** 两处卡点都与 "判定含函数的下标" 不同: 判定本身有 (`bdec`), 缺的是 (1) `LH` 与 `HB SL` 之间定义相等的往返, (2) 判等证明的唯一性. 出口: 用对角上 `refl` 的下标类型 ($\mathbb N$ 的站号), 见 `SLFbTm`.
