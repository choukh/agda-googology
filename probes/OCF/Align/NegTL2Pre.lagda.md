# 补四条正面判据, 否定一路 (一): 接口定稿之前 — 比平的候选更难排除的候选

> 不含记号. 入口 [NegTL2](NegTL2.lagda.md). 本篇**不依赖**构造一路的新接口 `TL2If` (接口定稿之前写的部分), 只导入上一轮的接口 [TreeLangIf](TreeLangIf.lagda.md) 与构造一路上一轮的 [TreeLangLv](TreeLangLv.lagda.md) (`exact→`, `exact←`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **问题.** 上一轮的平的候选 `NegTreeLangFlat.Fl` 级集合与 `Lev` 相同, 但它的第一位置恒真, 一切合法 Ω-分支是常函数 (`fl-const`). 本轮构造一路要加的第一条判据 "第一位置与坐标高度的 `⊲` 一致" 一眼就排除 `Fl`. 本篇预备**更难排除的候选**: 第一位置**就是**坐标高度的 `⊲`, 界**就是** "在世界的高度分量之下", 合法的 Ω-分支可以非常值; 只把世界里能当界的高度缩小.
>
> **结果.**
>
> 1. **`stepP S P` (构造, 定理: 是合法的 `KS`).** 与 `HtTowerTy.step` 逐字段相同, 只是世界的高度分量取自 $\Sigma\,b{:}\mathrm{HB}\,S.\ P\,b$. `P` 任意. `LevP P` 是对层号的同一递归 ($0\mapsto$ `S₀`, 后继 $\mapsto$ `stepP`, 极限 $\mapsto$ `sup`). 它满足 `LvCrit` 与 `LvUpper` (`CP`, `UP`), 所以由构造一路的定理, **级集合与 `Lev` 相等** (`same-levelsP→`, `same-levelsP←`), 对一切 `P`.
> 2. **Ω-结点合法且非常值, 对一切 `P` (`Lg-upΩP`, `upP-nc`).** 新种类的分支 `upP` 在 `stepP S P` 里合法, 且把 $0$ 与 $1$ 送到不同的值.
> 3. **两个具体的 `P`, 第一位置结构严格变少 (定理).**
>    - `Pz` ($b\equiv 0$, 界只能是 $0$): 新种类的 Ω-结点在第一位置上**塌成第 0 支** (`pz-coll`: $x\lhd\mathrm{h\Omega}\,g\Rightarrow x\equiv\mathrm{h\Omega}\,g\ \vee\ x\lhd g\,0$). 对照: `Lev (hs hz)` 里 $1\lhd \mathrm{h\Omega}\,\mathrm{up}$ (`lev-reach`, 合法世界), `LevP Pz (hs hz)` 里对一切世界都不成立 (`pz-noreach`).
>    - `Pn` (界是有限高度 `NatH`): Ω-结点的第一位置只经过有限坐标 (`pn-coll`); `Lev` 里 $\mathrm{up}(\mathrm{hl}\,\mathrm{ev})\lhd\mathrm{h\Omega}\,\mathrm{up}$ (`lev-reach-lim`), `LevP Pn` 里对一切世界都不成立 (`pn-noreach`).
> 4. **重数 (`stepD`, `LevD`).** 后继一步加**两个**坐标同为 `HB S`, 界同为世界高度分量的新种类. 满足 `LvCrit`, `LvUpper` (所以级集合与 `Lev` 相等, `same-levelsD→/←`), 第一位置也是 `⊲`; 但第 1 层有两个不同的级-0 种类 (`two-at-0`), `Lev` 只有一个 (`one-at-0`).
> 5. **"顺序一致" 的几种写法各被谁满足 (§5, 定理).** 对 "坐标读作高度的种类" 写四个谓词: `PrSup` ($\lhd\Rightarrow$ `Pr`), `PrSub` (`Pr` $\Rightarrow\lhd$), `BdAt` (界 ↔ 在世界的高度分量之下), `Rich` (每个合法高度都是某个合法世界的界). 表 (每格都是本篇的定理):
>
> | 写法 | `Fl` | `LevP Pz` | `LevP Pn` | `Lev` | `LevD` |
> |---|---|---|---|---|---|
> | `PrSup` | 满足 (`fl-sup`) | 满足 | 满足 | 满足 | 满足 |
> | `PrSub` | **不满足** (`fl-not-sub`) | 满足 | 满足 | 满足 | 满足 |
> | `BdAt` | (不适用: 世界没有高度分量) | 满足 | 满足 | 满足 | 满足 |
> | `Rich` | — | **不满足** (`pz-not-rich`) | **不满足** (`pn-not-rich`) | 满足 (`lev-rich`) | 满足 |
>
> **只否定什么 (这一篇).** 不否定任何构造与判据. 只说明: 只要判据把第一位置与界说成 "相对于候选自己的世界", 那么 "世界里有哪些界" 这一项就不被确定, 而它决定 Ω-结点在第一位置上是否塌缩 (`pz-coll`, `pn-coll`). 要排除 `LevP Pz`, `LevP Pn`, 需要 `Rich` 一类的条款 (世界足够多), 而 `Rich` 仍被重数不同的 `LevD` 满足. 后续篇在接口定稿后对真实的四条判据逐条检查.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTL2Pre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω; NatH; no-lim⊲nat; evᴴ; Lg-ev)
open import OCF.Align.NegKindLvLev using (_⊏_; one; snoc; lvK)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR; LevC; LevU; exact→; exact←)
open import OCF.Align.NegTreeLangFlat using (Fl)
```

## §1 `stepP`: 世界的高度分量取自子类型 `P`

```agda
module StepP (S : KS) (P : HB S → Set) where
  K⁺ : Set
  K⁺ = K S ⊎ ⊤

  E⁺ : K⁺ → Set
  E⁺ (inj₁ κ) = E S κ
  E⁺ (inj₂ _) = HB S

  W⁺ : Set
  W⁺ = Wd S × Σ (HB S) P

  β : W⁺ → HB S
  β w = proj₁ (proj₂ w)

  LgW⁺ : W⁺ → Set
  LgW⁺ w = LgW S (proj₁ w) × LgB (β w)

  _≤⁺_ : W⁺ → W⁺ → Set
  w ≤⁺ w′ = _≤w_ S (proj₁ w) (proj₁ w′) × (β w ⊲[ proj₁ w′ ] β w′)

  ≤⁺-rf : ∀ {w} → w ≤⁺ w
  ≤⁺-rf = ≤w-rf S , hself

  ≤⁺-tr : ∀ {u v w} → u ≤⁺ v → v ≤⁺ w → u ≤⁺ w
  ≤⁺-tr (p , b) (q , c) = ≤w-tr S p q , ⊲ᴮ-tr (⊲ᴮ↑ q b) c

  Bd⁺ : (κ : K⁺) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = a ⊲[ proj₁ w ] β w

  Pr⁺ : (κ : K⁺) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w c c′ = Pr S κ (proj₁ w) c c′
  Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′

  Bd↑⁺ : ∀ {κ c w w′} → w ≤⁺ w′ → Bd⁺ κ c w → Bd⁺ κ c w′
  Bd↑⁺ {inj₁ κ} (q , _) e = Bd↑ S q e
  Bd↑⁺ {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b

  cmpK⁺ : ∀ {κ c c′ w} → Bd⁺ κ c w → Bd⁺ κ c′ w → LgW⁺ w → Pr⁺ κ w c′ c ⊎ Pr⁺ κ w c c′
  cmpK⁺ {inj₁ κ} e e′ (lw , lb) = cmpK S e e′ lw
  cmpK⁺ {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb

  LgE⁺ : (κ : K⁺) → E⁺ κ → Set
  LgE⁺ (inj₁ κ) = LgE S κ
  LgE⁺ (inj₂ _) = LgB

  lgBd⁺ : ∀ {κ c w} → Bd⁺ κ c w → LgW⁺ w → LgE⁺ κ c
  lgBd⁺ {inj₁ κ} e (lw , lb) = lgBd S e lw
  lgBd⁺ {inj₂ _} e (lw , lb) = lgB⊲ e lw lb

  bot⁺ : (κ : K⁺) → E⁺ κ
  bot⁺ (inj₁ κ) = bot S κ
  bot⁺ (inj₂ _) = hz

  botBd⁺ : ∀ κ w → Bd⁺ κ (bot⁺ κ) w
  botBd⁺ (inj₁ κ) w = botBd S κ (proj₁ w)
  botBd⁺ (inj₂ _) w = z⊲ᴮ (β w)

stepP : (S : KS) → (HB S → Set) → KS
stepP S P = record
  { K = K⁺ ; E = E⁺ ; Wd = W⁺ ; LgW = LgW⁺ ; _≤w_ = _≤⁺_ ; ≤w-rf = ≤⁺-rf ; ≤w-tr = ≤⁺-tr
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; LgE = LgE⁺ ; lgBd = lgBd⁺ ; bot = bot⁺ ; botBd = botBd⁺ }
  where open StepP S P
```

**嵌入 `upP`, 新种类的分支 `upP` 合法且非常值 (对一切 `P`).**

```agda
module UpP {S : KS} (P : HB S → Set) where
  upP : HB S → HB (stepP S P)
  upP hz = hz
  upP (hs x) = hs (upP x)
  upP (hl f) = hl (λ n → upP (f n))
  upP (hΩ κ g) = hΩ (inj₁ κ) (λ c → upP (g c))

  upP-⊲ : ∀ {a b w} {β : Σ (HB S) P} → a ⊲[ w ] b → upP a ⊲[ (w , β) ] upP b
  upP-⊲ hself = hself
  upP-⊲ (hsuc p) = hsuc (upP-⊲ p)
  upP-⊲ (hlim n p) = hlim n (upP-⊲ p)
  upP-⊲ (hLim e p) = hLim e (upP-⊲ p)

  Lg-upP : ∀ a → LgB a → LgB (upP a)
  Lg-upP hz l = tt
  Lg-upP (hs a) l = Lg-upP a l
  Lg-upP (hl f) (st , l) = (λ n → upP-⊲ (st n)) , (λ n → Lg-upP (f n) (l n))
  Lg-upP (hΩ κ g) (mo , l) = (λ lw e e′ p → upP-⊲ (mo (proj₁ lw) e e′ p)) , (λ c lc → Lg-upP (g c) (l c lc))

  Lg-upΩP : LgB {stepP S P} (hΩ (inj₂ tt) upP)
  Lg-upΩP = (λ lw e e′ q → upP-⊲ q) , (λ c lc → Lg-upP c lc)

  upP-nc : ¬ (upP hz ≡ upP (hs hz))
  upP-nc ()
open UpP public
```

## §2 `LevP`: 同一递归, 级集合与 `Lev` 相等

```agda
LevP : (P : (T : KS) → HB T → Set) → ∀ {S : KS} → HB S → KS
LevP P hz = S₀
LevP P (hs x) = stepP (LevP P x) (P (LevP P x))
LevP P (hl f) = sup ℕ (λ n → LevP P (f n))
LevP P {S} (hΩ κ g) = sup (E S κ) (λ c → LevP P (g c))

module LvP (P : (T : KS) → HB T → Set) where
  lvP : ∀ {S : KS} (c : HB S) → K (LevP P c) → ⊤ ⊎ HB S
  lvP hz κ = inj₁ tt
  lvP (hs x) (inj₁ κ) = lvP x κ
  lvP (hs x) (inj₂ _) = inj₂ x
  lvP (hl f) (n , κ) = lvP (f n) κ
  lvP (hΩ κ g) (e , κ′) = lvP (g e) κ′

  coordP : ∀ {S : KS} (c : HB S) κ → E (LevP P c) κ ≡ Cdᴿ A (LevP P) (lvP c κ)
  coordP hz κ = refl
  coordP (hs x) (inj₁ κ) = coordP x κ
  coordP (hs x) (inj₂ _) = refl
  coordP (hl f) (n , κ) = coordP (f n) κ
  coordP (hΩ κ g) (e , κ′) = coordP (g e) κ′

  RP : ∀ {S : KS} → LvRule S A
  RP = record { L = LevP P ; lv = lvP ; coord = coordP }

  subUpP : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → SubLv y ℓ → SubLv c ℓ
  subUpP q (inj₁ _) _ = tt
  subUpP q (inj₂ z) p = snoc p q

  upUpP : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → UpLv y ℓ → UpLv c ℓ
  upUpP q (inj₁ _) _ = tt
  upUpP q (inj₂ z) p = sn p q

  subP : ∀ {S : KS} (c : HB S) κ → SubLv c (lvP c κ)
  subP hz κ = tt
  subP (hs x) (inj₁ κ) = subUpP ≺s (lvP x κ) (subP x κ)
  subP (hs x) (inj₂ _) = one ≺s
  subP (hl f) (n , κ) = subUpP (≺l n) (lvP (f n) κ) (subP (f n) κ)
  subP (hΩ κ g) (e , κ′) = subUpP (≺Ω e) (lvP (g e) κ′) (subP (g e) κ′)

  inhP : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → InLv RP y ℓ → InLv RP c ℓ
  inhP ≺s ℓ (κ , e) = inj₁ κ , e
  inhP (≺l n) ℓ (κ , e) = (n , κ) , e
  inhP (≺Ω c) ℓ (κ , e) = (c , κ) , e

  CP : ∀ {S : KS} → LvCrit (RP {S})
  CP = record { base0 = tt , refl ; feed = λ x → inj₂ tt , refl ; inherit = inhP ; sub = subP }

  UP : ∀ {S : KS} → LvUpper (RP {S})
  UP hz κ = tt
  UP (hs x) (inj₁ κ) = upUpP ≺s (lvP x κ) (UP x κ)
  UP (hs x) (inj₂ _) = rf
  UP (hl f) (n , κ) = upUpP (≺l n) (lvP (f n) κ) (UP (f n) κ)
  UP (hΩ κ g) (e , κ′) = upUpP (≺Ω e) (lvP (g e) κ′) (UP (g e) κ′)

  same-levelsP→ : ∀ {S : KS} (c : HB S) ℓ → InLv RP c ℓ → InLv (LevR {S}) c ℓ
  same-levelsP→ = exact→ RP CP UP

  same-levelsP← : ∀ {S : KS} (c : HB S) ℓ → InLv (LevR {S}) c ℓ → InLv RP c ℓ
  same-levelsP← = exact← RP CP UP
open LvP public
```

## §3 两个具体的 `P`: Ω-结点在第一位置上塌缩

```agda
Pz : (T : KS) → HB T → Set
Pz T b = b ≡ hz

Pn : (T : KS) → HB T → Set
Pn T b = NatH b

module _ {S : KS} where
  ⊲hz : ∀ {w} {a : HB S} → a ⊲[ w ] hz → a ≡ hz
  ⊲hz hself = refl

  nat⊲ : ∀ {w} {a b : HB S} → a ⊲[ w ] b → NatH b → NatH a
  nat⊲ hself n = n
  nat⊲ (hsuc p) n = nat⊲ p n
  nat⊲ (hlim m p) ()
  nat⊲ (hLim e p) ()

  natUp : ∀ {P : HB S → Set} (c : HB S) → NatH c → NatH (upP P c)
  natUp hz _ = tt
  natUp (hs x) n = natUp x n
  natUp (hl f) ()
  natUp (hΩ κ g) ()
```

**`Pz`: 塌成第 0 支.**

```agda
module _ {S : KS} where
  private T = stepP S (Pz S)

  pz-bd : ∀ {c : HB S} {w : Wd T} → Bd T (inj₂ tt) c w → c ≡ hz
  pz-bd {c} {w} e = ⊲hz (subst (λ b → c ⊲[ proj₁ w ] b) (proj₂ (proj₂ w)) e)

  pz-coll : ∀ {w : Wd T} {x : HB T} (g : HB S → HB T) → x ⊲[ w ] hΩ (inj₂ tt) g →
            (x ≡ hΩ (inj₂ tt) g) ⊎ (x ⊲[ w ] g hz)
  pz-coll g hself = inj₁ refl
  pz-coll {w} {x} g (hLim e p) = inj₂ (subst (λ c → x ⊲[ w ] g c) (pz-bd e) p)

pz-noreach : ∀ (w : Wd (LevP Pz {S₀} (hs hz))) → ¬ (hs hz ⊲[ w ] hΩ (inj₂ tt) (upP (Pz S₀)))
pz-noreach w p with pz-coll (upP (Pz S₀)) p
... | inj₁ ()
... | inj₂ q with ⊲hz q
... | ()

lev-reach : (LgW (Lev {S₀} (hs hz)) (azero , hs hz)) × (hs hz ⊲[ (azero , hs hz) ] hΩ {Lev {S₀} (hs hz)} (inj₂ tt) (λ c → up c))
lev-reach = (tt , tt) , hLim hself hself
```

**`Pn`: 只经过有限坐标.** `Lev` 里 $\mathrm{up}(\mathrm{hl}\,\mathrm{ev})$ 是 Ω-结点的第一位置 (界取 $\mathrm{hl}\,\mathrm{ev}$, 合法世界); `LevP Pn` 里对一切世界不是.

```agda
module _ {S : KS} where
  private T = stepP S (Pn S)

  pn-coll : ∀ {w : Wd T} {x : HB T} (g : HB S → HB T) → x ⊲[ w ] hΩ (inj₂ tt) g →
            (x ≡ hΩ (inj₂ tt) g) ⊎ Σ (HB S) (λ c → NatH c × (x ⊲[ w ] g c))
  pn-coll g hself = inj₁ refl
  pn-coll {w} g (hLim {c = c} e p) = inj₂ (c , nat⊲ e (proj₂ (proj₂ w)) , p)

pn-noreach : ∀ (w : Wd (LevP Pn {S₀} (hs hz))) →
  ¬ (upP (Pn S₀) (hl evᴴ) ⊲[ w ] hΩ (inj₂ tt) (upP (Pn S₀)))
pn-noreach w p with pn-coll (upP (Pn S₀)) p
... | inj₁ ()
... | inj₂ (c , nc , q) = no-lim⊲nat q (natUp {P = Pn S₀} c nc)

lev-reach-lim : (LgW (Lev {S₀} (hs hz)) (azero , hl evᴴ)) ×
  (up (hl evᴴ) ⊲[ (azero , hl evᴴ) ] hΩ {Lev {S₀} (hs hz)} (inj₂ tt) (λ c → up c))
lev-reach-lim = (tt , Lg-ev) , hLim hself hself
```

## §4 重数: 后继一步加两个新种类

`stepD S`: 与 `step S` 相同, 只是新种类有两个 (`Bool`), 坐标都是 `HB S`, 界都是世界的高度分量.

```agda
module StepD (S : KS) where
  open Step S using (W⁺; LgW⁺; _≤⁺_; ≤⁺-rf; ≤⁺-tr)

  K⁺ : Set
  K⁺ = K S ⊎ Bool

  E⁺ : K⁺ → Set
  E⁺ (inj₁ κ) = E S κ
  E⁺ (inj₂ _) = HB S

  Bd⁺ : (κ : K⁺) → E⁺ κ → W⁺ → Set
  Bd⁺ (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bd⁺ (inj₂ _) a w = a ⊲[ proj₁ w ] proj₂ w

  Pr⁺ : (κ : K⁺) → W⁺ → E⁺ κ → E⁺ κ → Set
  Pr⁺ (inj₁ κ) w c c′ = Pr S κ (proj₁ w) c c′
  Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′

  Bd↑⁺ : ∀ {κ c w w′} → w ≤⁺ w′ → Bd⁺ κ c w → Bd⁺ κ c w′
  Bd↑⁺ {inj₁ κ} (q , _) e = Bd↑ S q e
  Bd↑⁺ {inj₂ _} (q , b) e = ⊲ᴮ-tr (⊲ᴮ↑ q e) b

  cmpK⁺ : ∀ {κ c c′ w} → Bd⁺ κ c w → Bd⁺ κ c′ w → LgW⁺ w → Pr⁺ κ w c′ c ⊎ Pr⁺ κ w c c′
  cmpK⁺ {inj₁ κ} e e′ (lw , lb) = cmpK S e e′ lw
  cmpK⁺ {inj₂ _} e e′ (lw , lb) = cmpB e e′ lw lb

  LgE⁺ : (κ : K⁺) → E⁺ κ → Set
  LgE⁺ (inj₁ κ) = LgE S κ
  LgE⁺ (inj₂ _) = LgB

  lgBd⁺ : ∀ {κ c w} → Bd⁺ κ c w → LgW⁺ w → LgE⁺ κ c
  lgBd⁺ {inj₁ κ} e (lw , lb) = lgBd S e lw
  lgBd⁺ {inj₂ _} e (lw , lb) = lgB⊲ e lw lb

  bot⁺ : (κ : K⁺) → E⁺ κ
  bot⁺ (inj₁ κ) = bot S κ
  bot⁺ (inj₂ _) = hz

  botBd⁺ : ∀ κ w → Bd⁺ κ (bot⁺ κ) w
  botBd⁺ (inj₁ κ) w = botBd S κ (proj₁ w)
  botBd⁺ (inj₂ _) w = z⊲ᴮ (proj₂ w)

stepD : KS → KS
stepD S = record
  { K = K⁺ ; E = E⁺ ; Wd = W⁺ ; LgW = LgW⁺ ; _≤w_ = _≤⁺_ ; ≤w-rf = ≤⁺-rf ; ≤w-tr = ≤⁺-tr
  ; Bd = Bd⁺ ; Pr = Pr⁺ ; Bd↑ = Bd↑⁺ ; cmpK = cmpK⁺ ; LgE = LgE⁺ ; lgBd = lgBd⁺ ; bot = bot⁺ ; botBd = botBd⁺ }
  where open StepD S ; open Step S using (W⁺; LgW⁺; _≤⁺_; ≤⁺-rf; ≤⁺-tr)

LevD : ∀ {S : KS} → HB S → KS
LevD hz = S₀
LevD (hs x) = stepD (LevD x)
LevD (hl f) = sup ℕ (λ n → LevD (f n))
LevD {S} (hΩ κ g) = sup (E S κ) (λ c → LevD (g c))

lvD : ∀ {S : KS} (c : HB S) → K (LevD c) → ⊤ ⊎ HB S
lvD hz κ = inj₁ tt
lvD (hs x) (inj₁ κ) = lvD x κ
lvD (hs x) (inj₂ _) = inj₂ x
lvD (hl f) (n , κ) = lvD (f n) κ
lvD (hΩ κ g) (e , κ′) = lvD (g e) κ′

coordD : ∀ {S : KS} (c : HB S) κ → E (LevD c) κ ≡ Cdᴿ A LevD (lvD c κ)
coordD hz κ = refl
coordD (hs x) (inj₁ κ) = coordD x κ
coordD (hs x) (inj₂ _) = refl
coordD (hl f) (n , κ) = coordD (f n) κ
coordD (hΩ κ g) (e , κ′) = coordD (g e) κ′

RD : ∀ {S : KS} → LvRule S A
RD = record { L = LevD ; lv = lvD ; coord = coordD }

subD : ∀ {S : KS} (c : HB S) κ → SubLv c (lvD c κ)
subD hz κ = tt
subD (hs x) (inj₁ κ) = subUpP Pz ≺s (lvD x κ) (subD x κ)
subD (hs x) (inj₂ _) = one ≺s
subD (hl f) (n , κ) = subUpP Pz (≺l n) (lvD (f n) κ) (subD (f n) κ)
subD (hΩ κ g) (e , κ′) = subUpP Pz (≺Ω e) (lvD (g e) κ′) (subD (g e) κ′)

inhD : ∀ {S : KS} {y c : HB S} → y ≺ᴮ c → ∀ ℓ → InLv RD y ℓ → InLv RD c ℓ
inhD ≺s ℓ (κ , e) = inj₁ κ , e
inhD (≺l n) ℓ (κ , e) = (n , κ) , e
inhD (≺Ω c) ℓ (κ , e) = (c , κ) , e

CD : ∀ {S : KS} → LvCrit (RD {S})
CD = record { base0 = tt , refl ; feed = λ x → inj₂ true , refl ; inherit = inhD ; sub = subD }

UD : ∀ {S : KS} → LvUpper (RD {S})
UD hz κ = tt
UD (hs x) (inj₁ κ) = upUpP Pz ≺s (lvD x κ) (UD x κ)
UD (hs x) (inj₂ _) = rf
UD (hl f) (n , κ) = upUpP Pz (≺l n) (lvD (f n) κ) (UD (f n) κ)
UD (hΩ κ g) (e , κ′) = upUpP Pz (≺Ω e) (lvD (g e) κ′) (UD (g e) κ′)

same-levelsD→ : ∀ {S : KS} (c : HB S) ℓ → InLv RD c ℓ → InLv (LevR {S}) c ℓ
same-levelsD→ = exact→ RD CD UD

same-levelsD← : ∀ {S : KS} (c : HB S) ℓ → InLv (LevR {S}) c ℓ → InLv RD c ℓ
same-levelsD← = exact← RD CD UD

-- 重数: 第 1 层, 级 0
two-at-0 : Σ (K (LevD {S₀} (hs hz))) (λ κ → Σ (K (LevD {S₀} (hs hz))) (λ κ′ →
  (lvD (hs hz) κ ≡ inj₂ hz) × (lvD (hs hz) κ′ ≡ inj₂ hz) × ¬ (κ ≡ κ′)))
two-at-0 = inj₂ true , inj₂ false , refl , refl , (λ ())

one-at-0 : ∀ (κ κ′ : K (Lev {S₀} (hs hz))) → lvK (hs hz) κ ≡ inj₂ hz → lvK (hs hz) κ′ ≡ inj₂ hz → κ ≡ κ′
one-at-0 (inj₁ _) _ () _
one-at-0 (inj₂ _) (inj₁ _) _ ()
one-at-0 (inj₂ tt) (inj₂ tt) _ _ = refl
```

## §5 "顺序一致" 的几种写法

对一个种类结构 `T` 里的种类 $\kappa$, 若它的坐标读作某个 `S′` 的高度 (`cd`), 世界有一个 `S′` 的世界分量 (`πw`) 与一个高度分量 (`βw`), 写四个谓词. 都只说 "相对于 `T` 自己的世界".

```agda
record HtKind (T : KS) (κ : K T) (S′ : KS) : Set where
  field
    cd : E T κ → HB S′
    πw : Wd T → Wd S′
open HtKind public

PrSup : ∀ {T κ S′} → HtKind T κ S′ → Set
PrSup {T} {κ} H = ∀ {w c c′} → cd H c ⊲[ πw H w ] cd H c′ → Pr T κ w c c′

PrSub : ∀ {T κ S′} → HtKind T κ S′ → Set
PrSub {T} {κ} H = ∀ {w c c′} → Pr T κ w c c′ → cd H c ⊲[ πw H w ] cd H c′

BdAt : ∀ {T κ S′} → HtKind T κ S′ → (Wd T → HB S′) → Set
BdAt {T} {κ} H βw = ∀ {w c} → (Bd T κ c w → cd H c ⊲[ πw H w ] βw w) × (cd H c ⊲[ πw H w ] βw w → Bd T κ c w)

Rich : ∀ {T κ S′} → HtKind T κ S′ → (Wd T → HB S′) → Set
Rich {T} H βw = ∀ b → LgB b → Σ (Wd T) (λ w → LgW T w × (βw w ≡ b))
```

**实例.** `Fl (hs hz)` 的新种类: `PrSup` 成立, `PrSub` 不成立.

```agda
HFl : HtKind (Fl {S₀} (hs hz)) (inj₂ tt) (Fl {S₀} hz)
HFl = record { cd = λ c → c ; πw = λ _ → tt }

fl-sup : PrSup HFl
fl-sup _ = tt

fl-not-sub : ¬ PrSub HFl
fl-not-sub s with ⊲hz (s {tt} {hs hz} {hz} tt)
... | ()
```

`stepP S P` 的新种类 (对一切 `S`, `P`): `PrSup`, `PrSub`, `BdAt` 都成立 (定义上). `Rich` 对 `Pz`, `Pn` 不成立, 对 `Lev` (即 `step`) 成立.

```agda
HP : ∀ {S : KS} (P : HB S → Set) → HtKind (stepP S P) (inj₂ tt) S
HP P = record { cd = λ c → c ; πw = proj₁ }

βP : ∀ {S : KS} (P : HB S → Set) → Wd (stepP S P) → HB S
βP P w = proj₁ (proj₂ w)

P-sup : ∀ {S : KS} (P : HB S → Set) → PrSup (HP P)
P-sup P q = q

P-sub : ∀ {S : KS} (P : HB S → Set) → PrSub (HP P)
P-sub P q = q

P-bd : ∀ {S : KS} (P : HB S → Set) → BdAt (HP P) (βP P)
P-bd P = (λ e → e) , (λ e → e)

pz-not-rich : ¬ Rich (HP {S₀} (Pz S₀)) (βP (Pz S₀))
pz-not-rich r with r (hs hz) tt
... | (_ , (b , bz)) , _ , e with trans (sym e) bz
... | ()

pn-not-rich : ¬ Rich (HP {S₀} (Pn S₀)) (βP (Pn S₀))
pn-not-rich r with r (hl evᴴ) Lg-ev
... | (_ , b , nb) , _ , refl = nb

HLev : HtKind (Lev {S₀} (hs hz)) (inj₂ tt) S₀
HLev = record { cd = λ c → c ; πw = proj₁ }

lev-sup : PrSup HLev
lev-sup q = q

lev-sub : PrSub HLev
lev-sub q = q

lev-bd : BdAt HLev proj₂
lev-bd = (λ e → e) , (λ e → e)

lev-rich : Rich HLev proj₂
lev-rich b lb = (azero , b) , (tt , lb) , refl

HD : HtKind (LevD {S₀} (hs hz)) (inj₂ true) S₀
HD = record { cd = λ c → c ; πw = proj₁ }

D-all : PrSup HD × PrSub HD × BdAt HD proj₂ × Rich HD proj₂
D-all = (λ q → q) , (λ q → q) , ((λ e → e) , (λ e → e)) , (λ b lb → (azero , b) , (tt , lb) , refl)
```

## §6 结论 (按档)

- **[构造, 定理]** `stepP`, `LevP`, `stepD`, `LevD` (合法的 `KS`, 对一切 `P`).
- **[定理, 盲: 级集合]** `CP`, `UP`, `same-levelsP→/←` (对一切 `P`); `CD`, `UD`, `same-levelsD→/←`. 都用构造一路的 `exact→`, `exact←`.
- **[定理, 非常值]** `Lg-upΩP`, `upP-nc` (对一切 `P`): 与 `Fl` 不同, 这些候选有合法的非常值 Ω-分支.
- **[定理, 差别]** `pz-coll`, `pz-noreach` 对 `lev-reach`; `pn-coll`, `pn-noreach` 对 `lev-reach-lim`; `two-at-0` 对 `one-at-0`.
- **[定理, 写法表]** `fl-sup`, `fl-not-sub`; `P-sup`, `P-sub`, `P-bd` (对一切 `P`); `pz-not-rich`, `pn-not-rich`; `lev-sup`, `lev-sub`, `lev-bd`, `lev-rich`; `D-all`.
- **[判断]** (1) "第一位置与 `⊲` 一致" 若写成 `PrSup`, 平的候选满足; 写成 `PrSub` 或两者, 平的候选被排除, 但 `LevP P` 对一切 `P` 都满足, 其中 `Pz` 的 Ω-结点在第一位置上塌成一支. 所以判据 (i) 单独确定不了 "界有多少", 要配 `Rich` 一类的条款. (2) 判据 (iii) "升界保持世界的序" 若只对候选自己的世界说话, `Pz` 的世界里高度分量只有 $0$, 升界无事可做, 可能空真地满足; `Pn` 的世界里升界只在有限高度之间. 这一条要等接口定稿后对真实陈述检查. (3) 穷尽是判断.
