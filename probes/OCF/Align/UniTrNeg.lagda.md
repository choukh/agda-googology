# 非选择性的增量搬运 (二): 积世界版的特例, 否定与充分条件

> 不含记号. 入口 [UniTr](UniTr.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 这一篇对积世界版的 W′ ([UniTrBase](UniTrBase.lagda.md) 的 `UniTr` 在槽族上) 做四件事:
>
> 1. **`no-faithful-back`** (对一切 `S`): 增量 $\delta$ 的新种类结点按 "顶对齐" 翻进坐标类型更大的分量 (翻译后的结点 `TrB B` 的分支是 `up ∘ up ∘ B`, $B$ 把新坐标倒译回旧坐标), 只要倒译 $B$ 在旧部分上忠实 ($B(\mathrm{up}\,c)\approx c$), 翻译结果就**不合法**. 推论 `¬Lg-Tr₀′`: `DiagK4Neg.¬Lg-Tr₀` 是它在 `back₀` 上的实例 (`back₀-up`). 常值倒译合法 (`Lg-constB`) 而不忠实 (`const-unfaithful`). 所以顶对齐的翻译恰好分成 "忠实即不合法" 与 "合法即有损" 两类, 对一切 $B$.
> 2. **`lossy-pred`** (对一切 `G`): 从分量 `hs c` 的槽搬进分量 $c$ 的槽的任何映射都没有左逆 (`HtTowerNeg.no-retract` 的实例). 这是审查 "tr 在 $i<i_0$ 处必有损" 的定理形式. 实例 `lossy-Lev`.
> 3. **充分条件 (正面)**: 给出见证 $i_0\lhd i$ 时, 沿见证的嵌入 `emb⊲` 合法 (`Lg-emb⊲`), 在 `hself` 上是恒等. 所以若有选择子 `Selector` (每对下标给出见证或放弃, 对角上给 `hself`), 就有 `UniTr` (`sel→unitr`). 相等可判定时选择子存在 (`dec→sel`, Hedberg). 选择子本身是一种判定.
> 4. **`growL′` 的位置**: 对坐标为 $H_0$ 的槽忠实 (`growL′-faith₀`, 即 `DiagK3Grow.at-lev`), 对 `κ₂` 不忠实 (`growL′-¬faith₁`, 即 `ChainZNeg.no-Ω-cell`).
>
> 以及**开放点的最小陈述** `Open.Open-taboo`, `Open.Open-build` (两个类型, 本篇不证也不否).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniTrNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.HtTowerNStage using (L′)
open import OCF.Align.DiagK4Neg using (S₁; back₀; Tr₀)
open import OCF.Align.DiagK3Grow using (growL′; at-lev)
open import OCF.Align.DiagK3One using (κ₂)
open import OCF.Align.ChainZNeg using (Reach; no-Ω-cell)
open import OCF.Align.UniTrBase
```

## §1 顶对齐: 忠实的倒译不合法

增量是 `step S` 的新种类结点 (坐标 `HB S`), 翻进坐标类型 `HB (step S)` 的新种类 (`step (step S)` 的 `inj₂ tt`). 翻译后的结点在新坐标 $c'$ 处的分支是 $\mathrm{up}(\mathrm{up}(B\,c'))$. `DiagK4Neg.Tr₀` 就是 `S = S₀`, `B = back₀`.

证明: 记 $T=B(\Omega_{\mathrm{top}})$. 世界 $((w_0,\mathrm{hs}\,T),\Omega_{\mathrm{top}})$ 合法; 坐标 $\mathrm{up}(\mathrm{hs}\,T)\lhd\Omega_{\mathrm{top}}$. 单调给出 $\mathrm{up}^2(B(\mathrm{up}(\mathrm{hs}\,T)))\lhd\mathrm{up}^2\,T$; 忠实给出左边与 $\mathrm{hs}(\mathrm{up}^2 T)$ 互模拟; `≈hs⊲` 说这不可能.

```agda
module _ (S : KS) where
  TrB : (HB (step S) → HB S) → HB (step (step S))
  TrB B = hΩ (inj₂ tt) (λ c′ → up (up (B c′)))

  Faithᴮ : (HB (step S) → HB S) → Set
  Faithᴮ B = ∀ c → LgB c → B (up c) ≈ c

  no-faithful-back : (B : HB (step S) → HB S) → Faithᴮ B → LgB (B (Ωtop S)) →
                     (w₀ : Wd S) → LgW S w₀ → ¬ LgB (TrB B)
  no-faithful-back B fa lT w₀ lw₀ (mo , l) = ≈hs⊲ eq st
    where
    T : HB S
    T = B (Ωtop S)
    W : Wd (step (step S))
    W = (w₀ , hs T) , Ωtop S
    lW : LgW (step (step S)) W
    lW = (lw₀ , lT) , Lg-Ωtop S
    e₁ : up (hs T) ⊲[ (w₀ , hs T) ] Ωtop S
    e₁ = hLim {c = hs T} hself hself
    st : up (up (B (up (hs T)))) ⊲[ W ] up (up T)
    st = mo {W} {up (hs T)} {Ωtop S} lW e₁ hself e₁
    eq : up (up (B (up (hs T)))) ≈ hs (up (up T))
    eq = up-≈ (up-≈ (fa (hs T) lT))

  -- 常值倒译: 合法, 不忠实
  Lg-constB : ∀ h → LgB h → LgB (TrB (λ _ → h))
  Lg-constB h lh = (λ lw e e′ p → hself) , (λ c lc → Lg-up (up h) (Lg-up h lh))

  const-unfaithful : ∀ h → LgB h → ¬ Faithᴮ (λ _ → h)
  const-unfaithful h lh fa = ≈-hs (fa (hs h) lh)
```

**实例: `back₀`.** 它在旧部分上忠实 (`back₀-up`, 对结构归纳, 不用外延), 所以 `DiagK4Neg.¬Lg-Tr₀` 是一般定理的推论.

```agda
back₀-up : ∀ c → back₀ (up c) ≈ c
back₀-up hz = ≈z
back₀-up (hs c) = ≈s (back₀-up c)
back₀-up (hl f) = ≈l (λ n → back₀-up (f n))
back₀-up (hΩ tt g) = ≈Ω (λ c → back₀-up (g c))

¬Lg-Tr₀′ : ¬ LgB Tr₀
¬Lg-Tr₀′ = no-faithful-back S₀ back₀ (λ c _ → back₀-up c) tt azero tt
```

## §2 搬进前一个分量必有损

槽族 `LevSlot`: 分量 $c$ 的槽是 `HB (Lev (up c))`, 分量 `hs c` 的槽是 `HB (step (Lev (up c)))`. 后者里有以前者为坐标的种类 (`inj₂ tt`), 所以没有收缩.

```agda
lossy-pred : ∀ (G : KS) (tr : HB (step G) → HB G) (d : HB G → HB (step G)) → ¬ (∀ x → d (tr x) ≡ x)
lossy-pred G tr d = no-retract {step G} (inj₂ tt) tr d

lossy-Lev : ∀ {S} (c : HB S) (tr : HB (Lev (up (hs c))) → HB (Lev (up c))) d → ¬ (∀ x → d (tr x) ≡ x)
lossy-Lev c tr d = lossy-pred (Lev (up c)) tr d
```

## §3 有见证就能忠实地往上搬

沿 $a\lhd_{[w]}b$ 的嵌入: `hself` 是恒等, `hsuc` 是 `up`, ℕ-极限与 $\Omega$-极限是对应分量的 `ι`. 保合法. 这正是 "底对齐": 增量进**更高**的分量时落在同一个种类的副本里, 坐标类型不变, 不要倒译.

```agda
module _ {S : KS} where
  emb⊲ : ∀ {a b : HB S} {w} → a ⊲[ w ] b → HB (Lev a) → HB (Lev b)
  emb⊲ hself x = x
  emb⊲ (hsuc p) x = up (emb⊲ p x)
  emb⊲ (hlim {f = f} n p) x = ι {F = λ k → Lev (f k)} n (emb⊲ p x)
  emb⊲ (hLim {g = g} {c = c} e p) x = ι {F = λ d → Lev (g d)} c (emb⊲ p x)

  Lg-emb⊲ : ∀ {a b : HB S} {w} (p : a ⊲[ w ] b) x → LgB x → LgB (emb⊲ p x)
  Lg-emb⊲ hself x l = l
  Lg-emb⊲ (hsuc p) x l = Lg-up (emb⊲ p x) (Lg-emb⊲ p x l)
  Lg-emb⊲ (hlim {f = f} n p) x l = Lg-ι {F = λ k → Lev (f k)} n (emb⊲ p x) (Lg-emb⊲ p x l)
  Lg-emb⊲ (hLim {g = g} {c = c} e p) x l = Lg-ι {F = λ d → Lev (g d)} c (emb⊲ p x) (Lg-emb⊲ p x l)
```

**选择子.** 每对下标给出 "见证或放弃", 对角上给 `hself`. 由它直接得到 `UniTr` (忠实取 `≡`, 定义相等之后 `cong`). 下标相等可判定时选择子存在 (Hedberg 给出 `i ≡ i` 的证明就是 `refl`).

```agda
module Sel {S : KS} (w : Wd S) where
  open W′ (HB S) (λ c → HB (Lev c)) (λ {c} x → LgB {Lev c} x) (λ {c} x y → x ≡ y)

  Wit : HB S → HB S → Set
  Wit i₀ i = (_⊲[_]_ {S} i₀ w i) ⊎ ⊤

  record Selector : Set where
    field
      sel  : (i₀ i : HB S) → Wit i₀ i
      diag : ∀ i → sel i i ≡ inj₁ hself
  open Selector public

  go : ∀ {i₀ i} → Wit i₀ i → HB (Lev i₀) → HB (Lev i)
  go (inj₁ p) δ = emb⊲ p δ
  go (inj₂ _) δ = hz

  Lg-go : ∀ {i₀ i} (s : Wit i₀ i) δ → LgB δ → LgB (go {i₀} {i} s δ)
  Lg-go (inj₁ p) δ l = Lg-emb⊲ p δ l
  Lg-go (inj₂ _) δ l = tt

  sel→unitr : Selector → UniTr
  sel→unitr Sl = record
    { tr = λ i₀ i → go {i₀} {i} (sel Sl i₀ i)
    ; faith = λ i₀ δ l → cong (λ (s : Wit i₀ i₀) → go {i₀} {i₀} s δ) (diag Sl i₀)
    ; legal = λ i₀ i δ l → Lg-go {i₀} {i} (sel Sl i₀ i) δ l }

  dec→sel : ((a b : HB S) → Dec (a ≡ b)) → Selector
  dec→sel _≟_ = record { sel = s ; diag = d }
    where
    open Decidable⇒UIP _≟_ using (≡-irrelevant)
    s′ : ∀ i₀ i → Dec (i₀ ≡ i) → Wit i₀ i
    s′ i₀ i (yes e) = inj₁ (subst (λ j → _⊲[_]_ {S} i₀ w j) e hself)
    s′ i₀ i (no _) = inj₂ tt
    s : (i₀ i : HB S) → Wit i₀ i
    s i₀ i = s′ i₀ i (i₀ ≟ i)
    d : ∀ i → s i i ≡ inj₁ hself
    d i with i ≟ i
    ... | yes e = cong (λ q → inj₁ {B = ⊤} (subst (λ j → _⊲[_]_ {S} i w j) q hself)) (≡-irrelevant e refl)
    ... | no ne = ⊥-elim (ne refl)
```

## §4 `growL′` 在 W′ 里的位置

`DiagK3Grow.growL′` 是一个非选择性的世界操作 (一切分量接同一个 $H_0$ 增量, 经 `embL`). 它在坐标为 $H_0$ 的 `Lev` 种类 (分量 `hs hz`) 处恰好是 "旧界 ⊞ $h$" (忠实), 在 `κ₂` (分量 `hs (hs hz)`, 槽 `HB S₁`) 处, 含新种类结点的格从不有界 (不忠实). 按 W′ 的语言: 它是常值增量族 $H_0$ 上的 `UniTr` (恒等) 接 `embL`, 增量族比槽族小, 所以只在槽恰好是 $H_0$ 的分量上忠实.

```agda
growL′-faith₀ : ∀ f ffst flg h lh (w : Wd (L′ 1)) →
  proj₂ (growL′ f ffst flg h lh 1 w false (hs hz)) ≡ (proj₂ (w false (hs hz)) ⊞ h)
growL′-faith₀ f ffst flg h lh w = at-lev f ffst flg h lh w

growL′-¬faith₁ : ∀ {w} y → Reach w → ¬ Bd (L′ 1) κ₂ (y ⊞ Ωtop S₀) w
growL′-¬faith₁ = no-Ω-cell
```

## §5 开放点的最小陈述

积世界版 W′ 在 `Lev (Ωtop S)` 的后继分量上: 槽族 `c ↦ HB (Lev (up c))` 上的 `UniTr`. 下面两个类型一个是否定方向 (`UniTr` 推出高度相等的弱判定), 一个是构造方向; 本轮两者都没有居留, 也都没有被否定. 它们只是定义, 不是假设.

```agda
module Open (S : KS) where
  open LevSlot S using (UniTr)

  Open-taboo : Set
  Open-taboo = UniTr → ∀ (c c′ : HB S) → ¬ (c ≡ c′) ⊎ ¬ ¬ (c ≡ c′)

  Open-build : Set
  Open-build = UniTr
```
