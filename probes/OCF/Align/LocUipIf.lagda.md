# 局部 UIP 与 "只升 $c_0$": 接口

> **接口定稿 2026-11-05 10:45 (编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 构造一路 `LocUip*` (入口 [LocUip](LocUip.lagda.md)), 否定一路 `LocUipNeg*`, 共用本篇. 本篇只放类型, 不放证明. 依赖 [AdmWIf](AdmWIf.lagda.md) (`SupB`, 最小实例 `Slot`, `RaiseB`, `Coh≡`) 与 [AdmWCoh](AdmWCoh.lagda.md) (`incD`, `dD`, `raise₀ᴮ`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **律的定义域.** 下面每一条律里出现的一对坐标都带同一个外层世界 $w=(a,b)$ 的可入证据 (`AdmE w c`: $c\lhd_{[a]} b$). 唯一的例外是 `UIPᴸ` 与 `LoopRefl`, 它们是对照用的全局陈述 (用来说明局部版本等价于什么), 不是要求的律.
>
> **第一条引理: 局部 UIP** (§1). 作者的目标: `raise₀ᴮ` 无条件保 `Coh≡` (`Lemma1`, 就是 `RaiseCoh Coh≡ raise₀ᴮ`). 卡住的那一步 (`AdmWCoh.incD-irr` 的 `inj₁ e, inj₁ e′`) 写成 `IncIrr`. 三个候选的充分条件:
>
> - `LocUIP w`: 同一合法世界 $w$ 里, 两个可入坐标之间的相等证明唯一.
> - `DiagCst w lo`: 局部 Hedberg 要的 "收缩函数对证据为常值": 同一坐标 $c_0$ 的任意两个证据 $q, p_0$, 判定给出字面的 `inj₁ refl`. (已知: $q=p_0$ 时成立, `AdmWCmp.dec₀-diag`.)
> - `LoopRefl`: "`toLt` 在环上给 `refl`" (简报的第二个候选写法).
>
> 对照: `UIPᴸ` (合法高度上的 K), `UIPᴴ` (`AdmWCoh`, 一切高度上的 UIP).
>
> **证据无关的写法** (§2). 增量不是一个 `HB (G₀ c₀)`, 而是坐标的族 `Inc = (c : HB S₀) → HB (G₀ c)`; 更新在 $c\equiv c_0$ 的分量上接 $\delta\,c$, 只用判定的 "是/否", 不用它给出的相等证明. 记录 `RaiseF` 与 `RaiseB` 的律一一对应, 外加 `cohF` (保 `Coh≡`). `off` 律单列为 `OffF` (只升 $c_0$ 本身的更新满足它; §3 的拷贝更新不满足).
>
> **第二条引理: 只升 $c_0$ 够不够** (§3). 回灌一步 (`HtTowerFFold.κc₁` 的形状: 读出节点种类的界 $b$, 新世界的界是读回值) 要的东西写成 `Feed Coh` (单个增量) 与 `Feedᶠ Coh` (族增量): 新世界变大, 合法, 保相干 `Coh`, 读回值 $b\boxplus\delta$ 在新世界的 $(c_0,\text{槽})$ 种类之下有界. 读回值取 "旧界接增量" 的形式 (`HtTowerFFold` 的第 0 层 `sum W (z Y)` 就是这个形式; 第 1 层的 `rd b z` 是 "在旧界上读", 两者的关系是判断, 见构造一路). $c_0$ 之上的分量: `hs c₀` 的分量 `step (G₀ (hs c₀)) = step (step (G₀ c₀))` 的旧种类部分里装着 $c_0$ 的槽种类的**一份拷贝** (坐标类型同为 `HB (G₀ c₀)`, 定义地); `CopyCoh` 说拷贝的界与 $c_0$ 的槽相同 (`HtTowerNStage.no-wmatch` 那一线要的 "同一种类一个界", 只写了 `hs` 这一步). `SlotOnly R`: 更新只改分量的槽, 不改分量的旧种类部分 (`raiseᴮ`, `raise₀ᴮ` 都是).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipIf where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; toLt)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (incD; dD; raise₀ᴮ)
open Slot
open RaiseIf
```

## §1 第一条引理: 局部 UIP

```agda
-- 目标: raise₀ᴮ 无条件保 Coh≡
Lemma1 : Set
Lemma1 = RaiseCoh Coh≡ raise₀ᴮ

-- 卡住的那一步: 同一坐标 c 的两个证据 p, p′, 搬出的增量相同
IncIrr : Set
IncIrr = ∀ w (lo : LgO w) {c₀ c : HB S₀} (p₀ : AdmE w c₀) (p p′ : AdmE w c) (δ : HB (G₀ c₀)) →
  incD (dD w lo p p₀) δ ≡ incD (dD w lo p′ p₀) δ

-- 局部 UIP: 同一世界里两个可入坐标之间的相等证明唯一
LocUIP : Out → Set
LocUIP w = ∀ {x y : HB S₀} → AdmE w x → AdmE w y → (e e′ : x ≡ y) → e ≡ e′

-- 局部 Hedberg 要的: 对角上的判定对证据为常值
DiagCst : (w : Out) → LgO w → Set
DiagCst w lo = ∀ {c₀ : HB S₀} (q p₀ : AdmE w c₀) → dD w lo q p₀ ≡ inj₁ refl

-- 简报的另一写法: toLt 在环上给 refl
LoopRefl : Set
LoopRefl = ∀ {x : HB S₀} {a : A} (r : x ⊲[ a ] x) → toLt r ≡ inj₁ refl

-- 对照: 合法高度上的 K
UIPᴸ : Set
UIPᴸ = ∀ {x : HB S₀} → LgB x → (e : x ≡ x) → e ≡ refl
```

## §2 证据无关的写法: 增量是坐标的族

```agda
Inc : Set
Inc = (c : HB S₀) → HB (G₀ c)

record RaiseF : Set where
  field
    raiseF : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → Inc → Cmp w
    atF    : ∀ w lo v c₀ p₀ δ → raiseF w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ c₀)
    belowF : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → raiseF w lo v c₀ p₀ δ c p ≡ v c p
    monoF  : ∀ w lo v c₀ p₀ δ → (w , v) ≤ᴮ (w , raiseF w lo v c₀ p₀ δ)
    legalF : ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → LgWᴮ (w , v) → LgWᴮ (w , raiseF w lo v c₀ p₀ δ)
    cohF   : ∀ w lo v c₀ p₀ δ → Coh≡ (w , v) → Coh≡ (w , raiseF w lo v c₀ p₀ δ)
open RaiseF public

-- 可入下标上的 off 律, 单列
OffF : RaiseF → Set
OffF R = ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → ¬ (c₀ ≡ c) → raiseF R w lo v c₀ p₀ δ c p ≡ v c p
```

## §3 第二条引理: 回灌要的更新律

```agda
-- 回灌一步, 单个增量: 读到的界是 (c₀, p₀) 的槽 b, 读回值 b ⊞ δ 在新世界里有界
Feed : (Wᴮ → Set) → Set
Feed Coh = ∀ w (lo : LgO w) (v : Cmp w) c₀ (p₀ : AdmE w c₀) (δ : HB (G₀ c₀)) → LgB δ → LgWᴮ (w , v) → Coh (w , v) →
  Σ (Cmp w) (λ v′ → ((w , v) ≤ᴮ (w , v′)) × LgWᴮ (w , v′) × Coh (w , v′) ×
                    Bdᴮ (c₀ , inj₂ tt) (proj₂ (v c₀ p₀) ⊞ δ) (w , v′))

-- 同上, 族增量
Feedᶠ : (Wᴮ → Set) → Set
Feedᶠ Coh = ∀ w (lo : LgO w) (v : Cmp w) c₀ (p₀ : AdmE w c₀) (δ : Inc) → LgB (δ c₀) → LgWᴮ (w , v) → Coh (w , v) →
  Σ (Cmp w) (λ v′ → ((w , v) ≤ᴮ (w , v′)) × LgWᴮ (w , v′) × Coh (w , v′) ×
                    Bdᴮ (c₀ , inj₂ tt) (proj₂ (v c₀ p₀) ⊞ δ c₀) (w , v′))

-- c₀ 之上的拷贝 (hs 这一步): hs c₀ 的分量的旧种类部分里, c₀ 的槽种类的界 = c₀ 的槽
CopyCoh : Wᴮ → Set
CopyCoh W = ∀ (c₀ : HB S₀) (p₀ : AdmE (proj₁ W) c₀) (p₁ : AdmE (proj₁ W) (hs c₀)) →
  proj₂ (proj₁ (proj₂ W (hs c₀) p₁)) ≡ proj₂ (proj₂ W c₀ p₀)

-- 只改槽: 分量的旧种类部分不动
SlotOnly : RaiseB → Set
SlotOnly R = ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → proj₁ (raiseB R w lo v c₀ p₀ δ c p) ≡ proj₁ (v c p)

-- 更新保拷贝相干
RaiseCopy : RaiseB → Set
RaiseCopy R = ∀ w lo v c₀ p₀ δ → LgB δ → CopyCoh (w , v) → CopyCoh (w , raiseB R w lo v c₀ p₀ δ)
```
