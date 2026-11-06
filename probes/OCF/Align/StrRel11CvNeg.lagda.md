# 结构关系, 第十一轮: 在 `SumOneFold` 上, 带对齐的目标对经不起 `cv` (否定)

> 不读记号. 入口 [StrRel11](StrRel11.lagda.md). 第十轮 (`StrRel10Kp.¬nw-tgt`) 说: 状态关系 `R∀` 若对**一切**目标对取读数关系, `Kp` 的 `nw wu w` 收不下, 所以目标对要带对齐 `Al`. 本文说另一半: 在 `SumOneFold` 上, **只对带对齐的目标对**取读数关系的 `R∀ₐ`, 换世界 `cv` 保不住. 对任意一族读数关系 `Rl`, 只要它有 $0\sqsubseteq x'$ 并且在第 1 层读数上满足最弱的值可靠性 (`Snd`), "`R∀ₐ` 经 `cv` 保持" 就是假的 (`¬cv-al`), 而 `cv` 的一切前提 (世界 $W\le W'$, 两条 `cv` 路径对齐, 领先量, `Lg` 等式) 都满足.

## 0 为什么

`SumOneFold.cv` 在目标 `inj₁ τ₁` (目标在新世界之下) 上用 `cmpF q τ₁` 决定读旧状态的哪一个目标, 再用 `nw q` 或 `nw τ₁` 包住. 两边世界不同 ($W<W'$) 时, 层 $t$ 夹在中间 ($W\lhd t\lhd W'$) 就会一边读 "目标在世界之上" 的读数 (`inj₂`), 一边读 "目标在世界之下" 的读数 (`inj₁`). 这一对旧目标在 `W⊲wm` 上一边走一步, 一边不走, 对齐 `Al` 不成立, 所以 `R∀ₐ` 对这一对什么也不说; `cv` 之后它们却成了一对对齐的目标. 第 0 层读数不受影响 ($\sqsubseteq^{\mathsf P}$ 的 `wl`, `wr` 让 `nw` 透明, 而且第 0 层目标总在世界之下), 所以 `StrRel5`..`StrRel10` 只读第 0 层时看不到这件事.

主线折叠 `HtFeedFold.cv` 没有这个问题: 那里目标自带世界 $m\ge W$, `cv` 只把路径接长 (`tg↑`), 不比较, 不包 `nw` ([StrRel11Tg](StrRel11Tg.lagda.md) 的 `cvR`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel11CvNeg where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; lg⊲; z⊲; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; n0; n1; nw; sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP)
open import OCF.Align.StrRel4Gen using (adm-self)
open import OCF.Align.StrRel5Nest using (stepA)
open import OCF.Align.StrRel7Coh using (Y∅)
open import OCF.Align.StrRel8Neg using (Nz; nzm; chk-ok)
```

## 1 带对齐的目标对, `R∀ₐ`, 要否定的性质

`TA lW lW′ lt τ τ′`: 两个目标在各自的世界 $W, W'$ 上, 路径 `W⊲wm` 对齐, 顶端有领先量, 两条 `Lg` 等式. 这正是 `StrRel9Nw.snd-nwA` 对 `Kp` 的 `nw wu w` 要的前提 (`wu = W⊲wm τ`). `Rl` 是任意一族读数关系 (第 $t$ 层的树, 两边世界可以不同).

```agda
RelF : Set₁
RelF = ∀ t {V V′} → D t V → D t V′ → Set

TA : ∀ {W W′ t} → Lg W → Lg W′ → Lg t → Tg t W → Tg t W′ → Set
TA {W} {W′} lW lW′ lt τ τ′ =
  Al (F.wm τ) (F.wm τ′) (F.W⊲wm τ) (F.Lg-wm τ lW lt) (F.W⊲wm τ′) (F.Lg-wm τ′ lW′ lt) ×
  Adm W W′ (F.wm τ) (F.wm τ′) ×
  (lW ≡ lg⊲ (F.W⊲wm τ) (F.Lg-wm τ lW lt)) × (lW′ ≡ lg⊲ (F.W⊲wm τ′) (F.Lg-wm τ′ lW′ lt))

R∀ₐ : RelF → ∀ {W W′} → Lg W → Lg W′ → F.St W → F.St W′ → Set
R∀ₐ Rl {W} {W′} lW lW′ Y Y′ =
  (∀ {t} (lt : Lg t) (τ : Tg t W) (τ′ : Tg t W′) → TA lW lW′ lt τ τ′ →
     Rl t (F.yc (F.d Y) τ lt) (F.yc (F.d Y′) τ′ lt)) ×
  Rl azero (F.z Y) (F.z Y′)

-- 要否定的: R∀ₐ 经 cv 保持, 前提给足
CvStable : RelF → Set
CvStable Rl =
  ∀ {W W′ U U′} (lW : Lg W) (lW′ : Lg W′) (lU : Lg U) (lU′ : Lg U′) (q : W ⊲ U) (q′ : W′ ⊲ U′) →
  W ≤ W′ → Al U U′ q lU q′ lU′ → Adm W W′ U U′ → lW ≡ lg⊲ q lU → lW′ ≡ lg⊲ q′ lU′ →
  ∀ (Y : F.St W) (Y′ : F.St W′) → R∀ₐ Rl lW lW′ Y Y′ → R∀ₐ Rl lU lU′ (F.cv q lU Y) (F.cv q′ lU′ Y′)

-- 两条最弱的要求: 0 在下; 第 1 层读数相关时, 从空状态用 Step 跑一遍, 第 0 层读数的值不减
Bot : RelF → Set
Bot Rl = ∀ t {V V′} {x′ : D t V′} → Rl t {V} n0 x′

Snd : RelF → Set
Snd Rl = ∀ {U U′} (lU : Lg U) (lU′ : Lg U′) (l₁ : one ⊲ U) (l₁′ : one ⊲ U′) {x : D one U} {x′ : D one U′} → Rl one x x′ →
  sum azero (F.yc (F.Run ac₁ x C.self lU l₁ stepA n0 Y∅) (inj₁ (z⊲ U)) tt) ≤
  sum azero (F.yc (F.Run ac₁ x′ C.self lU′ l₁′ stepA n0 Y∅) (inj₁ (z⊲ U′)) tt)
```

## 2 反例

世界 $W=0$, $W'=1$; `cv` 到 $U=2$, $U'=3$, 两条路径都是两步, 逐步对齐 (领先量 $\delta=2$, $1$). 左边状态只在目标 "层 1, 在世界之上" (`inj₂ (suc self)`) 上读 `n1`, 别处读 `n0`; 右边全是 `n0`. 这个目标在右边 (世界 1) 没有对齐的伙伴 (`no-pair`), 所以 `R∀ₐ` 成立. `cv` 之后, 层 1 的目标 `inj₁` 两边路径都是 `self`, 对齐; 左边的读数是 `nw τ₁ n1` (经 `cmpF` 读到那个 `inj₂` 读数), 右边是 `nw q′ n0`. 用 `Step` 跑一遍, 左边读数非零, 右边是零.

```agda
two three : A
two = asuc one
three = asuc two

ycB : ∀ {t} (τ : Tg t azero) → Lg t → D t (F.wm τ)
ycB (inj₂ (C.suc C.self)) lt = n1
ycB τ lt = n0

YB : F.St azero
YB = F.st (F.df ycB n0) n0

-- 那个目标在世界 1 上没有对齐的伙伴
no-pair : ∀ {lt : Lg one} (τ′ : Tg one one) → ¬ TA tt tt lt (inj₂ (C.suc C.self)) τ′
no-pair (inj₁ p) (() , _)
no-pair (inj₂ C.self) (() , _)
no-pair (inj₂ (C.suc ())) _

hB : ∀ (Rl : RelF) → Bot Rl → R∀ₐ Rl tt tt YB (Y∅ {one})
hB Rl b = r , b azero
  where
  r : ∀ {t} (lt : Lg t) (τ : Tg t azero) (τ′ : Tg t one) → TA tt tt lt τ τ′ → Rl t (ycB τ lt) n0
  r lt (inj₁ p) τ′ _ = b _
  r lt (inj₂ C.self) τ′ _ = b _
  r lt (inj₂ (C.suc C.self)) τ′ ta with no-pair τ′ ta
  ... | ()
  r lt (inj₂ (C.suc (C.suc p))) τ′ _ = b _
  r lt (inj₂ (C.suc (C.lim n p))) τ′ _ = b _
  r lt (inj₂ (C.lim n p)) τ′ _ = b _

q : azero ⊲ two
q = C.suc (C.suc C.self)
q′ : one ⊲ three
q′ = C.suc (C.suc C.self)

ad₀ : Adm azero one two three
ad₀ = two , ≤-refl two , ≤-refl three
ad₁ : Adm one two two three
ad₁ = one , ≤-refl two , ≤-refl three

alq : Al two three q tt q′ tt
alq = aP (aP (aS C.self tt) z≤ ad₀) (s≤ z≤) ad₁

¬cv-al : ∀ (Rl : RelF) → Bot Rl → Snd Rl → ¬ CvStable Rl
¬cv-al Rl b s cs = nzm le yes
  where
  τ : Tg one two
  τ = inj₁ (C.suc C.self)
  τ′ : Tg one three
  τ′ = inj₁ (C.suc (C.suc C.self))
  h : Rl one (nw (C.suc C.self) n1) (nw q′ n0)
  h = proj₁ (cs tt tt tt tt q q′ z≤ alq ad₀ refl refl YB Y∅ (hB Rl b)) tt τ τ′
        (aS C.self tt , adm-self two three , refl , refl)
  le = s tt tt (C.suc C.self) (C.suc (C.suc C.self)) h
  yes : Nz (sum azero (F.yc (F.Run ac₁ (nw (C.suc C.self) n1) C.self tt (C.suc C.self) stepA n0 Y∅) (inj₁ (z⊲ two)) tt))
  yes = chk-ok 6 _ tt
```

`le` 的右边是 `sum azero n0`, 即 `azero`; `nzm le yes : Nz azero`, 即 $ot$.

## 3 结论 (定理)

`¬cv-al`: 在 `SumOneFold` 上, 对任意满足 `Bot` 与 `Snd` 的读数关系族, "只对带对齐的目标对取读数关系, 且经 `cv` 保持" 不可能. 前提全部可满足 (反例里 $W\le W'$, 两条 `cv` 路径逐步对齐, 领先量, `Lg` 等式都给出了). 范围: 只否定 "`R∀ₐ` 对 `SumOneFold.cv` 封闭" 这一个形状, 不否定别的状态关系 (例如对 "目标在世界之上" 与 "目标在世界之下" 的混合对也取读数关系, 或者 Kripke 式地对一切对齐的扩张取), 不涉及主线折叠.

与 `StrRel10Kp.¬nw-tgt` 合起来: 在 `SumOneFold` 上, 读数关系对一切目标对取不行 (`Kp`), 只对对齐的目标对取也不行 (`cv`). 两条都来自 `SumOneFold` 的目标是 `(t ⊲ W) ⊎ (W ⊲ t)`, `cv` 要用 `cmpF` 重新分类. 主线 `HtFeedFold` 的目标是 "世界 $m\ge W$ 加层的位置", 没有这种重新分类 ([StrRel11Tg](StrRel11Tg.lagda.md)).
