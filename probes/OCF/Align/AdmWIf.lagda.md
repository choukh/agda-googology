# 可入下标上的比较式更新: 接口

> **接口定稿 2026-11-05 10:05.** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 入口 [AdmW](AdmW.lagda.md). 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2 (命题 W⁺), §2.4 (拷贝), §3.3 (最小改动), §5.1 (方向 A). 本篇只放记录与类型, 不放证明; 构造在 `AdmW*`, 否定在 `AdmWNeg*`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **诊断的要点, 写在最前面: 律里出现的每一对下标都带字面公共上界的证据.** 下面每一条律只比较两个坐标 $c, c_0$, 而它们各带一个证据 $p : c \lhd_{[a]} b$, $p_0 : c_0 \lhd_{[a]} b$, 指向**同一个**世界 $(a, b)$ 的同一个界 $b$. 没有一条律对裸坐标陈述; 没有 "别处不变" (`off`) 这种对一切 $c$ 的律. "严格在 $c_0$ 之下" 写成结构子项 `c <ᴮ c₀` (`StallDxBdec`), 同时 $c$ 带证据.
>
> **新的并 `SupB S κ F`** (§1). 外层种类结构 `S` 的一个种类 `κ`, 坐标族 `F : E S κ → KS`.
>
> - 种类 $\Sigma_{c} K(F\,c)$, 与 `HtTowerTy.sup` 相同: 种类出现在高度的结点里, 不能依赖世界, 所以**不带证据**.
> - 世界 `Wᴮ = Σ (w : Wd S) (Cmp w)`, `Cmp w = (c : E S κ) → Bd S κ c w → Wd (F c)`: 外层世界, 加上**只对可入坐标**的分量, 分量以 (坐标, 证据) 为下标. 这是诊断 §3.3 的原文. 理由: 比较式更新要对每个分量用 `cmpB` 比较它的坐标与 $c_0$, 而 `cmpB` 要两个坐标在同一个界之下; 下标带证据, 比较就有了公共上界.
> - 合法 `LgWᴮ`: 外层合法, 每个分量合法 (逐分量; 不含跨证据的相干, 相干单列为 `Coh≡`, `Coh≤`).
> - 变大 `_≤ᴮ_`: 外层变大, 且旧的每个分量 $(c,p)$ 在新世界里**有某个**证据 $p'$ 使分量变大. 取 "某个" 而不取 "同一个 `Bd↑` 搬过去的证据", 是因为后者的传递性要 `Bd↑` 的复合与 `Bd↑` 沿复合定义相等, `KS` 不给这一条.
> - 有界 `Bdᴮ (c,k) x W`: 有某个证据 $p$, $x$ 在分量 $(c,p)$ 的 $k$-界之下. 第一位置 `Prᴮ` 同样取某个证据的分量.
> - **`SupB` 不是 `KS`**, 缺两个字段: `cmpK` (本路的第二条引理, 类型 `CmpK`) 与 `botBd` (不可入的坐标 $c$ 的种类在那个世界里没有任何有界的坐标, 所以 "最小坐标在一切世界里有界" 不成立). 后者只影响 `z⊲ᴮ`, `⊞-fst` 一类引理在 `HB (SupB …)` 上的形状, 本篇不处理.
> - 坐标比较 `CmpK`: 同一种类的两个坐标**各带外层证据** $(p, e)$, $(p', e')$; `CmpKᶜ` 是加上相干前提的同一陈述.
>
> **最小实例** (§2). `S = step S₀`, `κ = inj₂ tt` (坐标是第二数类的高度 `HB S₀`, 外层世界 $(a, b) : A \times \mathrm{HB}\,S_0$, 可入就是 $c \lhd_{[a]} b$). 两个族:
>
> - `Inst = SupB (step S₀) (inj₂ tt) G₀`, `G₀ c = Lev (up c)`: 就是 `Lev (Ωtop S₀) = sup (HB S₀) G₀` (`lev-Ωtop`, `refl`) 把 `sup` 换成 `SupB`.
> - `Slot = SupB (step S₀) (inj₂ tt) (step ∘ G₀)`: 槽族, 每个分量是 `step (G₀ c)`, 被升高的槽是新种类的界 (`UniTrBase.LevSlot` 的 `P`, 下标带证据). `Lev (Ωtop S₀)` 在后继坐标 `hs c` 处的分量定义地就是 `step (G₀ c)`; 更新律在 `Slot` 上陈述, 因为 "接长" 只在槽上有意义.
>
> **更新** (§3). `RaiseB`: `raiseB w lo v c₀ p₀ δ` 给出新的分量函数 (外层世界不变, 所以旧证据仍是新世界的证据, 律可以在同一个证据上陈述); 四条律 `at`, `below`, `mono`, `legal`. `at` 对一切证据 $p_0$ (不只字面 `hself`) 陈述. `RaiseCoh R`: 更新保相干. `Open-buildᴬ`: `UniTrBase.W′.UniTr` 的可入版 (下标 `Adm w = Σ c (c ⊲[a] b)`, 忠实取 `_≡_`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWIf where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.StallDxBdec using (_<ᴮ_)
open import OCF.Align.UniTrBase using (module W′)
```

## §1 新的并 `SupB`

```agda
module SupB (S : KS) (κ : K S) (F : E S κ → KS) where
  Kᴮ : Set
  Kᴮ = Σ (E S κ) (λ c → K (F c))

  Eᴮ : Kᴮ → Set
  Eᴮ k = E (F (proj₁ k)) (proj₂ k)

  -- 只对可入坐标的分量, 以 (坐标, 证据) 为下标
  Cmp : Wd S → Set
  Cmp w = (c : E S κ) → Bd S κ c w → Wd (F c)

  Wᴮ : Set
  Wᴮ = Σ (Wd S) Cmp

  LgWᴮ : Wᴮ → Set
  LgWᴮ W = LgW S (proj₁ W) × (∀ c p → LgW (F c) (proj₂ W c p))

  _≤ᴮ_ : Wᴮ → Wᴮ → Set
  W ≤ᴮ W′ = _≤w_ S (proj₁ W) (proj₁ W′) ×
            (∀ c p → Σ (Bd S κ c (proj₁ W′)) (λ p′ → _≤w_ (F c) (proj₂ W c p) (proj₂ W′ c p′)))

  Bdᴮ : (k : Kᴮ) → Eᴮ k → Wᴮ → Set
  Bdᴮ k x W = Σ (Bd S κ (proj₁ k) (proj₁ W)) (λ p → Bd (F (proj₁ k)) (proj₂ k) x (proj₂ W (proj₁ k) p))

  Prᴮ : (k : Kᴮ) → Wᴮ → Eᴮ k → Eᴮ k → Set
  Prᴮ k W x x′ = Σ (Bd S κ (proj₁ k) (proj₁ W)) (λ p → Pr (F (proj₁ k)) (proj₂ k) (proj₂ W (proj₁ k) p) x x′)

  LgEᴮ : (k : Kᴮ) → Eᴮ k → Set
  LgEᴮ k = LgE (F (proj₁ k)) (proj₂ k)

  -- 跨证据的相干: 同一坐标的两个证据下的分量相等 / 互相变大
  Coh≡ : Wᴮ → Set
  Coh≡ W = ∀ c (p p′ : Bd S κ c (proj₁ W)) → proj₂ W c p ≡ proj₂ W c p′

  Coh≤ : Wᴮ → Set
  Coh≤ W = ∀ c (p p′ : Bd S κ c (proj₁ W)) → _≤w_ (F c) (proj₂ W c p) (proj₂ W c p′)

  -- 第二条引理: 坐标比较, 两个坐标各带外层证据
  CmpK : Set
  CmpK = ∀ {k x x′ W} → Bdᴮ k x W → Bdᴮ k x′ W → LgWᴮ W → Prᴮ k W x′ x ⊎ Prᴮ k W x x′

  CmpKᶜ : (Wᴮ → Set) → Set
  CmpKᶜ Coh = ∀ {k x x′ W} → Bdᴮ k x W → Bdᴮ k x′ W → LgWᴮ W → Coh W → Prᴮ k W x′ x ⊎ Prᴮ k W x x′
```

## §2 最小实例

```agda
G₀ : HB S₀ → KS
G₀ c = Lev (up c)

lev-Ωtop : Lev (Ωtop S₀) ≡ sup (HB S₀) G₀
lev-Ωtop = Relation.Binary.PropositionalEquality.refl

module Inst = SupB (step S₀) (inj₂ tt) G₀
module Slot = SupB (step S₀) (inj₂ tt) (λ c → step (G₀ c))

-- 外层世界 (a, b), 可入: c ⊲[ a ] b
Out : Set
Out = Wd (step S₀)

LgO : Out → Set
LgO = LgW (step S₀)

AdmE : Out → HB S₀ → Set
AdmE w c = c ⊲[ proj₁ w ] proj₂ w

Adm : Out → Set
Adm w = Σ (HB S₀) (AdmE w)
```

## §3 更新与它的律

```agda
module RaiseIf where
  open Slot

  record RaiseB : Set where
    field
      raiseB : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → HB (G₀ c₀) → Cmp w
      -- 在 (c₀, p₀) 处恰好接长, 对一切证据 p₀
      at     : ∀ w lo v c₀ p₀ δ → raiseB w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ)
      -- 严格在 c₀ 之下 (c 也带证据) 的分量不动
      below  : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → raiseB w lo v c₀ p₀ δ c p ≡ v c p
      -- 世界只增
      mono   : ∀ w lo v c₀ p₀ δ → LgB δ → (w , v) ≤ᴮ (w , raiseB w lo v c₀ p₀ δ)
      -- 保合法
      legal  : ∀ w lo v c₀ p₀ δ → LgB δ → LgWᴮ (w , v) → LgWᴮ (w , raiseB w lo v c₀ p₀ δ)
  open RaiseB public

  RaiseCoh : (Wᴮ → Set) → RaiseB → Set
  RaiseCoh Coh R = ∀ w lo v c₀ p₀ δ → LgB δ → Coh (w , v) → Coh (w , raiseB R w lo v c₀ p₀ δ)

-- UniTr 的可入版: 下标是可入坐标 (带证据), 忠实取 ≡
Open-buildᴬ : Set
Open-buildᴬ = ∀ w → LgO w →
  W′.UniTr (Adm w) (λ i → HB (G₀ (proj₁ i))) (λ x → LgB x) (λ x y → x ≡ y)
```
