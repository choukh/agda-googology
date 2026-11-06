# `Lev` 取并 (一): `LevC x` 是种类结构, 拷贝相干

> 不含记号. 入口 [ColimW](ColimW.lagda.md), 接口 [ColimWIf](ColimWIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> - **`pb`**: 任一种类结构 $T$ 沿任一世界映射 $r : W \to \mathrm{Wd}\,T$ 拉回, 是种类结构 (种类、坐标不动, 界、第一位置、合法、世界序都经 $r$). `cmpK` 与 `botBd` 原样拉回, 不新证任何东西.
> - **`LevC x = pb (Lev x) (GW S) (restr x)`**: 对一切 `S`, 一切高度 $x$. 所以 `LevC x` 是 `KS` (`cmpKC`, `botBdC` 是接口 `CmpKC`, `BotBdC` 的实例), `HtTowerTy` 的高度、第一位置、合法、`cmpB` 原样可用.
> - **`glob`, `globPr`** (接口的 `Glob`, `GlobPr`): 一切种类的界与第一位置只由它的层号与世界在那一层的分量决定. 对 $x$ 与种类结构递归, 每一步 `refl`.
> - **拷贝相干** (§4, 都是 `refl`): `κ₂`, `κ₂′`, `κ₂ω` 的界是同一个命题; 底种类的三个拷贝同; ℕ-极限级 `xω` 里的 `λ₂`, `λ₃` 同; 跨级 (`LevC x₀` 的 `κ₂` 与 `LevC xω` 的 `λ₂`) 同. 对照: 原来的和 (`Lev x₀` 自己的世界) 里 `κ₂` 与 `κ₂′` 的界互不推出 (`sum-no-cross→`, `sum-no-cross←`, 与 `CohWNeg.no-cross` 同形).
> - **整体合法与世界序** (`lgG→`, `≤G→`): `LgG` 推出每个 `LevC x` 的合法, `≤G` 推出每个 `LevC x` 的世界序. 合法世界有实例 (`W₀`, `lgW₀`).
> - **`no-retractC`**: `HtTowerNeg.no-retract` 对 `LevC x` 的实例. 定义上的理由见 §5.
> - **`toC`, `toC-⊲`, `Lg-toC`** (§6): 和的高度逐构造子搬进拉回, 保第一位置, 保合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWKS where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.ColimWIf
```

## §1 拉回

```agda
pb : (T : KS) (W : Set) → (W → Wd T) → KS
pb T W r = record
  { K = K T ; E = E T ; Wd = W
  ; LgW = λ v → LgW T (r v)
  ; _≤w_ = λ u v → _≤w_ T (r u) (r v)
  ; ≤w-rf = λ {v} → ≤w-rf T {r v}
  ; ≤w-tr = λ {u} {v} {v′} p q → ≤w-tr T {r u} {r v} {r v′} p q
  ; Bd = λ κ c v → Bd T κ c (r v)
  ; Pr = λ κ v → Pr T κ (r v)
  ; Bd↑ = λ {κ} {c} {u} {v} q e → Bd↑ T {κ} {c} {r u} {r v} q e
  ; cmpK = λ {κ} {c} {c′} {v} e e′ lv → cmpK T {κ} {c} {c′} {r v} e e′ lv
  ; LgE = LgE T
  ; lgBd = λ {κ} {c} {v} e lv → lgBd T {κ} {c} {r v} e lv
  ; bot = bot T
  ; botBd = λ κ v → botBd T κ (r v) }
```

## §2 `LevC x`

```agda
LevC : ∀ {S} → HB S → KS
LevC {S} x = pb (Lev x) (GW S) (restr x)

module _ {S : KS} (x : HB S) where
  open LevCParts {S} x

  cmpKC : CmpKC
  cmpKC = cmpK (LevC x)

  botBdC : BotBdC
  botBdC = botBd (LevC x)
```

## §3 认同律

```agda
glob : ∀ {S} → Glob S
glob hz κ c W = refl
glob (hs x) (inj₁ κ) c W = glob x κ c W
glob (hs x) (inj₂ _) c W = refl
glob (hl f) (n , κ) c W = glob (f n) κ c W
glob (hΩ κ g) (c₀ , κ′) c W = glob (g c₀) κ′ c W

globPr : ∀ {S} → GlobPr S
globPr hz κ W c c′ = refl
globPr (hs x) (inj₁ κ) W c c′ = globPr x κ W c c′
globPr (hs x) (inj₂ _) W c c′ = refl
globPr (hl f) (n , κ) W c c′ = globPr (f n) κ W c c′
globPr (hΩ κ g) (c₀ , κ′) W c c′ = globPr (g c₀) κ′ W c c′
```

**整体的合法与世界序推出每一级的.**

```agda
lgG→ : ∀ {S} (x : HB S) {W : GW S} → LgG W → LgW (Lev x) (restr x W)
lgG→ hz l = proj₁ l
lgG→ (hs x) l = lgG→ x l , proj₂ l x
lgG→ (hl f) l = λ n → lgG→ (f n) l
lgG→ (hΩ κ g) l = λ c → lgG→ (g c) l

≤G→ : ∀ {S} (x : HB S) {W W′ : GW S} → W ≤G W′ → _≤w_ (Lev x) (restr x W) (restr x W′)
≤G→ hz q = proj₁ q
≤G→ (hs x) q = ≤G→ x q , proj₂ q x
≤G→ (hl f) q = λ n → ≤G→ (f n) q
≤G→ (hΩ κ g) q = λ c → ≤G→ (g c) q

≤G-rf : ∀ {S} {W : GW S} → W ≤G W
≤G-rf = C.self , λ y → hself

-- 最小的合法世界
W₀ : ∀ {S} → GW S
W₀ = azero , λ y → hz

lgW₀ : ∀ {S} → LgG (W₀ {S})
lgW₀ = tt , λ y → tt
```

## §4 拷贝相干: 都是 `refl`

Ω-极限级 `x₀ = Ωtop S₀` 里层号 `finH 1` 的三个拷贝 (坐标 2 的新种类, 坐标 3 的旧种类里的它, 坐标 $\omega$ 的第 2 项), 底种类的三个拷贝; ℕ-极限级 `xω` 里的两个拷贝; 跨两级.

```agda
module _ {W : GW S₁} {c : HB S₁} where
  cross₂′ : Bd (LevC x₀) κ₂ c W ≡ Bd (LevC x₀) κ₂′ c W
  cross₂′ = refl

  cross₂ω : Bd (LevC x₀) κ₂ c W ≡ Bd (LevC x₀) κ₂ω c W
  cross₂ω = refl

  crossλ : Bd (LevC xω) λ₂ c W ≡ Bd (LevC xω) λ₃ c W
  crossλ = refl

  cross-lv : Bd (LevC x₀) κ₂ c W ≡ Bd (LevC xω) λ₂ c W
  cross-lv = refl

  -- 读出的就是层号 finH 1 处的分量
  read₂ : Bd (LevC x₀) κ₂ c W ≡ (c ⊲[ restr (finH 1) W ] proj₂ W (finH 1))
  read₂ = refl

module _ {W : GW S₁} {a : A} where
  crossA′ : Bd (LevC x₀) κA a W ≡ Bd (LevC x₀) κA′ a W
  crossA′ = refl

  crossAω : Bd (LevC x₀) κA a W ≡ Bd (LevC x₀) κAω a W
  crossAω = refl

  readA : Bd (LevC x₀) κA a W ≡ (a ⊲ proj₁ W)
  readA = refl
```

**对照: 和的世界里同一对拷贝不相干.** `Lev x₀` 自己的世界是 $\prod_{c} \mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$; `κ₂` 读坐标 2 的分量, `κ₂′` 读坐标 3 的分量. 两个合法世界: `wa` 只在坐标 2 处把层号 1 的界放成 $1$, `wb` 只在坐标 3 处. 坐标 $1$ 在一个里有界, 在另一个里没有. 与 `CohWNeg.no-cross` 同形, 换成本篇的种类.

```agda
-- 和的世界: 每个分量取最小
dWs : ∀ {S} (x : HB S) → Wd (Lev x)
dWs hz = azero
dWs (hs x) = dWs x , hz
dWs (hl f) = λ n → dWs (f n)
dWs (hΩ κ g) = λ c → dWs (g c)

lg-dWs : ∀ {S} (x : HB S) → LgW (Lev x) (dWs x)
lg-dWs hz = tt
lg-dWs (hs x) = lg-dWs x , tt
lg-dWs (hl f) = λ n → lg-dWs (f n)
lg-dWs (hΩ κ g) = λ c → lg-dWs (g c)

one : HB S₁
one = hs hz

wa wb : Wd (Lev x₀)
wa (hs (hs hz)) = dWs {S₁} (finH 1) , one
wa c = dWs (up c)
wb (hs (hs (hs hz))) = (dWs {S₁} (finH 1) , one) , hz
wb c = dWs (up c)

lg-wa : LgW (Lev x₀) wa
lg-wa (hs (hs hz)) = lg-dWs {S₁} (finH 1) , tt
lg-wa hz = lg-dWs (up {S₀} hz)
lg-wa (hs hz) = lg-dWs (up (hs hz))
lg-wa (hs (hs (hs c))) = lg-dWs (up (hs (hs (hs c))))
lg-wa (hs (hs (hl f))) = lg-dWs (up (hs (hs (hl f))))
lg-wa (hs (hs (hΩ κ g))) = lg-dWs (up (hs (hs (hΩ κ g))))
lg-wa (hs (hl f)) = lg-dWs (up (hs (hl f)))
lg-wa (hs (hΩ κ g)) = lg-dWs (up (hs (hΩ κ g)))
lg-wa (hl f) = lg-dWs (up (hl f))
lg-wa (hΩ κ g) = lg-dWs (up (hΩ κ g))

lg-wb : LgW (Lev x₀) wb
lg-wb (hs (hs (hs hz))) = (lg-dWs {S₁} (finH 1) , tt) , tt
lg-wb hz = lg-dWs (up {S₀} hz)
lg-wb (hs hz) = lg-dWs (up (hs hz))
lg-wb (hs (hs hz)) = lg-dWs (up (hs (hs hz)))
lg-wb (hs (hs (hs (hs c)))) = lg-dWs (up (hs (hs (hs (hs c)))))
lg-wb (hs (hs (hs (hl f)))) = lg-dWs (up (hs (hs (hs (hl f)))))
lg-wb (hs (hs (hs (hΩ κ g)))) = lg-dWs (up (hs (hs (hs (hΩ κ g)))))
lg-wb (hs (hs (hl f))) = lg-dWs (up (hs (hs (hl f))))
lg-wb (hs (hs (hΩ κ g))) = lg-dWs (up (hs (hs (hΩ κ g))))
lg-wb (hs (hl f)) = lg-dWs (up (hs (hl f)))
lg-wb (hs (hΩ κ g)) = lg-dWs (up (hs (hΩ κ g)))
lg-wb (hl f) = lg-dWs (up (hl f))
lg-wb (hΩ κ g) = lg-dWs (up (hΩ κ g))

sum-no-cross→ : ¬ (∀ {c w} → LgW (Lev x₀) w → Bd (Lev x₀) κ₂ c w → Bd (Lev x₀) κ₂′ c w)
sum-no-cross→ h with h {one} {wa} lg-wa hself
... | ()

sum-no-cross← : ¬ (∀ {c w} → LgW (Lev x₀) w → Bd (Lev x₀) κ₂′ c w → Bd (Lev x₀) κ₂ c w)
sum-no-cross← h with h {one} {wb} lg-wb hself
... | ()
```

两个前提各自可满足 (同一个坐标 $1$, 各在自己的世界里有界):

```agda
sat-a : Bd (Lev x₀) κ₂ one wa
sat-a = hself

sat-b : Bd (Lev x₀) κ₂′ one wb
sat-b = hself
```

## §5 不违反 `no-retract`

`no-retract` 是对一切种类结构的定理, `LevC x` 是种类结构, 所以它直接适用 (`no-retractC`). 定义上的理由 (判断, 只描述定义的形状): `LevC x` 的种类就是 `Lev x` 的种类, 坐标是 `A` 或 `HB (Lev y)` ($y$ 是 $x$ 的字面子项, 类型 `HB S`); 世界 `GW S` 只含 `A` 与 `HB (Lev y)` ($y$ 取遍 `HB S`). 二者都不含 `HB (LevC x)`, 也不含以 `HB S` 之外的高度为下标的东西; `GW S` 在 `LevC` 之前定义, 只用到和的 `Lev`. 没有 "一个种类的坐标里装着自己所在结构的全部高度".

```agda
no-retractC : ∀ {S} (x : HB S) (κ : K (LevC x)) (e : HB (LevC x) → E (LevC x) κ) (d : E (LevC x) κ → HB (LevC x)) →
  ¬ (∀ y → d (e y) ≡ y)
no-retractC x κ e d = no-retract {LevC x} κ e d
```

## §6 和的高度搬进拉回

拉回不改种类与坐标, 所以 `HB T` 的高度逐构造子搬进 `HB (pb T W r)` (`toC`). 第一位置沿 $r$ 保持; **在和里合法的高度在拉回里合法** (`Lg-toC`): 拉回的合法只对 $r$ 的像里的世界要求单调, 比原来的弱. 反方向不成立是可能的 (拉回只看相干的世界), 这里不证. 用处 (判断): 和的塔上已有的合法高度 (例如 `Ωtop`, `θ`) 可以原样搬到并的塔上.

```agda
module _ {T : KS} {W : Set} {r : W → Wd T} where
  toC : HB T → HB (pb T W r)
  toC hz = hz
  toC (hs a) = hs (toC a)
  toC (hl f) = hl (λ n → toC (f n))
  toC (hΩ κ g) = hΩ κ (λ c → toC (g c))

  toC-⊲ : ∀ {a b} {v : W} → a ⊲[ r v ] b → toC a ⊲[ v ] toC b
  toC-⊲ hself = hself
  toC-⊲ (hsuc p) = hsuc (toC-⊲ p)
  toC-⊲ (hlim n p) = hlim n (toC-⊲ p)
  toC-⊲ (hLim e p) = hLim e (toC-⊲ p)

  Lg-toC : ∀ a → LgB a → LgB (toC a)
  Lg-toC hz l = tt
  Lg-toC (hs a) l = Lg-toC a l
  Lg-toC (hl f) (st , l) = (λ n → toC-⊲ (st n)) , (λ n → Lg-toC (f n) (l n))
  Lg-toC (hΩ κ g) (mo , l) = (λ lv e e′ p → toC-⊲ (mo lv e e′ p)) , (λ c lc → Lg-toC (g c) (l c lc))
```
