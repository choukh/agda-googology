# 树的语言, 第二对 (二): 判据 (ii)–(iv) 与升界

> 不含记号. 入口 [TL2](TL2.lagda.md), 接口 [TL2If](TL2If.lagda.md) ("接口定稿 2026-11-05 21:12 (首次编译通过)"). 只读导入上一对的 [TreeLangRaise](TreeLangRaise.lagda.md) (实例框架 `Pos`, `shape`, `unique`) 与 [NegTreeLangRaise](NegTreeLangRaise.lagda.md) (`supD`, `F₀`, `any-lowers`), 都未改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **结果 (定理, 除非标出).**
>
> 1. **(ii) `Cross` 排除对角定义域.** `no-cross-diag`: 否定一路的 `supD` (定义域只含同一成员, 有合法升界 `diag-raise`) 不满足 (ii). `no-cross-empty`: 空定义域不满足. `pos-cross`: `Pos` 满足. **形状定理 `cross-shape`, `cross-unique`**: 满足 (ii) 的框架上, 任一合法升界在**一切与 $j$ 共界的成员**上的读数, 就是按 `bdec` 的点更新; 任两个合法升界在那里一致. 上一对的 `shape` 只在 "定义域里" 成立, 而定义域可以取空 (`shrink`); 现在定义域被 (ii) 撑到共界的一切对.
> 2. **(iii) 条件形的 `Grow` 不排除 `any-lowers`; `RaiseUp` 排除.** `posGrow`, `grow₀`: 构造一路的实例 `posInst` 满足 `Grow` (逐点序), 而 `any-lowers` 照样成立 (`lowers-anyway`): 条件形的律只管 "往上置值时世界变大", 不禁止往下置值. 无条件的增长 ("任一置值都让世界变大") 在 `F₀` 上没有合法升界 (`grow-all→⊥`). `RaiseUp` (升界只对 `Above` 的值给出): `up-of` (`Raise` + `Grow` ⇒ `RaiseUp`), `no-lower` (读数不降), `lower-blocked` (`any-lowers` 的那一步在 `RaiseUp` 里没有居留: `¬ Above O₀ w1 j₀ 0`).
> 3. **(iv) 读数随成员变: `raise-adj` 解除, κHc 型有界族上有合法升界.** `DPos`: 成员是同一合法界 `Lb` 之下的字面位置 $(a,p)$, **读数类型是 `HB (Lev a)`** (这就是 `SlotIf.κHc a` 的坐标类型), 世界在每个位置放一个 `step (Lev a)` 的世界 (低一级的世界加一个高度作界). `dR` (合法升界, 截面形), `dCross` ((ii)), `dO` (世界序就是逐位置的 `step` 的世界序 `≤⁺`), `dGrow` ((iii)). **`Adj.adj-free`**: 界 `hs hz` 之下的两个成员 `hz`, `hs hz` 的读数类型恰是 `raise-adj` 里互相冲突的两个 $X$ (`tyL`, `tyH`: `E (Lev (hs hz)) (inj₂ tt)` 与 `HB (Lev (hs hz))`), 两者的读数可以各自取任意值. 单一读数类型的框架里这是 `raise-adj` 否定的; (iv) 下它成立. 这个框架的世界就是 `sup (界下位置) (λ (a , p) → step (Lev a))` 的世界 (`supW`, `toSup`, `ofSup`, `sup-rt₁`, `sup-rt₂`, 都是 `refl`), 读数序与界就是那里新种类的第一位置与界 (`ord-same`, `bd-same`, `refl`): **(ii)–(iv) 在 κHc 型族上推出的升界世界, 是现有积木 `sup`, `step`, `Lev` 在界下位置上的组合, 不是新形状**.
> 4. **(iv) 的盲区: 拷贝不相干.** `Copies.copies-split`: 同键 (同一高度 `hz`, 不同证据) 的两个成员, 一次升界后读数不同. 截面形的 `DRaise` 不要求拷贝相干. `keyed`: 截面若是**键的函数** $u : (a : \mathrm{HB}\,S) \to \mathrm{HB}(\mathrm{Lev}\,a)$, 一切同键成员读到同一个 $u\,a$, 拷贝自动相干, 不搬运. 只给一个键处的单个值 $v : \mathrm{HB}(\mathrm{Lev}\,a_0)$ 时, 扩成 $u$ 要沿相等证明搬运 (判断, 与 `ColimARaise.uip→raiseA1` 同一处; 未证, 未否定).
> 5. **界框架: (iii) 推出 "每个高度都能作界" (`up→rich`).** 对一个种类 $\kappa$ 与一个读界的函数 `top`, 界框架 `BdF.bF` 的成员只有一个, 读数是 `top w`. `RaiseUp` 推出: 对一切在 `top w` 之上的坐标 $v$, 有更大的世界以 $v$ 为界. 实例 `levUp`: `step T` 的新种类 (界 = 世界第二分量) 满足. 对照 `frozen T`: 一个种类, 第一位置就是坐标高度的 `⊲` ((i) 的形状, `frozen-ord`), 界固定在 `hz` 之下; 它**没有**界框架上的 `RaiseUp`, 不论 `top` 怎样取 (`no-up-frozen`; 前提可满足: `frozen-top`). 一般形 `no-up-pred`: 一切界满足某个谓词 $Q$, 而某个界之上有不满足 $Q$ 的坐标, 就没有 `RaiseUp`. 这正是否定一路 `NegTL2Pre.LevP` 一类 ((i) 排除不了的 "世界只取一部分高度") 的机制: 把 (iii) 用在界框架上就排除它 (对 `LevP` 本身的实例化在否定一路; 本篇写出一般形 `no-up-pred` 与例 `frozen`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TL2Raise where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (bdec)
open import OCF.Align.TreeLangIf
import OCF.Align.TreeLangRaise as TR
open TR using (pick; posInst)
open import OCF.Align.NegTreeLangRaise using (withEv; supD; F₀; j₀; w1; any-lowers)
open import OCF.Align.TL2If
```

## §1 (ii) 异键对

键就是高度时的 `HKey`.

```agda
hkH : ∀ {S : KS} → HKey (HB S)
hkH {S} = record { Sk = S ; hk = λ a → a ; hk-inj = λ e → e }
```

**排除.** `supD` (定义域 "同一成员"): 键 `hz`, `hs hz` 都在合法界 `hs hz` 之下, (ii) 要这一对在定义域里, 而 `hs hz ≢ hz`. 空定义域: 一个成员与自己共界.

```agda
no-cross-diag : ¬ Cross supD hkH
no-cross-diag C with C (λ c → TR.zW c) {azero} {hs hz} tt tt hz (hs hz) (hsuc hself) hself
... | ()

no-cross-empty : ¬ Cross (withEv F₀ (λ _ _ _ → ⊥)) hkH
no-cross-empty C = C w1 {azero} {hz} tt tt j₀ j₀ hself hself

pos-cross : ∀ {S : KS} {ω : Wd S} {Lb : HB S} (lω : LgW S ω) (lL : LgB Lb) (Vp : Set) →
  Cross (TR.Pos.posF {S} {ω} {Lb} lω lL Vp) hkH
pos-cross lω lL Vp w lω′ lL′ j j′ p q = tt
```

**形状定理.** (ii) 把共界的对放进定义域, 那里的键可判定 (`bdec`), 所以上一对的 `shape`, `unique` 在一切共界的对上适用.

```agda
module _ {F : RaiseFrame} {H : HKey (Key F)} (C : Cross F H) where
  keydec : ∀ {ω Lb} → LgW (Sk H) ω → LgB Lb → ∀ j j′ →
    hk H (key F j) ⊲[ ω ] Lb → hk H (key F j′) ⊲[ ω ] Lb → (key F j′ ≡ key F j) ⊎ ¬ (key F j′ ≡ key F j)
  keydec lω lL j j′ p q with bdec q p lω lL
  ... | inj₁ e = inj₁ (hk-inj H e)
  ... | inj₂ ne = inj₂ (λ k → ne (cong (hk H) k))

  cross-shape : (R : Raise F) → ∀ w {ω Lb} (lω : LgW (Sk H) ω) (lL : LgB Lb) j j′
    (p : hk H (key F j) ⊲[ ω ] Lb) (q : hk H (key F j′) ⊲[ ω ] Lb) v →
    obs F j′ (rs R w j v) ≡ pick (keydec lω lL j j′ p q) v (obs F j′ w)
  cross-shape R w lω lL j j′ p q v = TR.shape R v (C w lω lL j j′ p q) (keydec lω lL j j′ p q)

  cross-unique : (R R′ : Raise F) → ∀ w {ω Lb} (lω : LgW (Sk H) ω) (lL : LgB Lb) j j′
    (p : hk H (key F j) ⊲[ ω ] Lb) (q : hk H (key F j′) ⊲[ ω ] Lb) v →
    obs F j′ (rs R w j v) ≡ obs F j′ (rs R′ w j v)
  cross-unique R R′ w lω lL j j′ p q v = TR.unique R R′ v (C w lω lL j j′ p q) (keydec lω lL j j′ p q)
```

## §2 (iii) 升界保序

`Pos` 上的逐点序 (读数序任取一个自反关系).

```agda
module PosOrd {S : KS} {ω : Wd S} {Lb : HB S} (lω : LgW S ω) (lL : LgB Lb) (Vp : Set)
  (_≼_ : Vp → Vp → Set) (≼-rf : ∀ {x} → x ≼ x) where
  open TR.Pos {S} {ω} {Lb} lω lL Vp

  posO : OrdFrame posF
  posO = record
    { _≤W_ = λ w w′ → ∀ b q → w b q ≼ w′ b q
    ; ≤R = λ _ _ → _≼_
    ; obs-mono = λ j le → le (proj₁ j) (proj₂ j) }

  posGrow : Grow posO posR
  posGrow {w} {a , p} v ab b q with bdec q p lω lL
  ... | inj₁ e = ab (b , q) tt e
  ... | inj₂ _ = ≼-rf

O₀ : OrdFrame F₀
O₀ = PosOrd.posO {S₀} {azero} {hz} tt tt ℕ _≤_ ≤-refl

grow₀ : Grow O₀ posInst
grow₀ = PosOrd.posGrow {S₀} {azero} {hz} tt tt ℕ _≤_ ≤-refl
```

**条件形不排除降值; 无条件形没有实例.**

```agda
lowers-anyway : Grow O₀ posInst × (obs F₀ j₀ (rs posInst w1 j₀ 0) ≡ 0) × (obs F₀ j₀ w1 ≡ 1)
lowers-anyway = grow₀ , any-lowers posInst

grow-all→⊥ : (R : Raise F₀) → (∀ w j v → _≤W_ O₀ w (rs R w j v)) → ⊥
grow-all→⊥ R g = no (subst (λ n → 1 ≤ n) (proj₁ (any-lowers R)) (g w1 j₀ 0 hz hself))
  where
  no : ¬ (1 ≤ 0)
  no ()
```

**`RaiseUp`: 只对 `Above` 的值升界.**

```agda
up-of : ∀ {F : RaiseFrame} {O : OrdFrame F} (R : Raise F) → Grow O R → RaiseUp F O
up-of R g = record
  { rsU = λ w j v _ → rs R w j v
  ; setU = λ {w} {j} {j′} {v} _ ev k → set R v ev k
  ; keepU = λ {w} {j} {j′} {v} _ ev nk → keep R v ev nk
  ; growU = λ {w} {j} {v} a → g v a }

no-lower : ∀ {F : RaiseFrame} {O : OrdFrame F} (U : RaiseUp F O) {w j v} (a : Above O w j v) j′ →
  ≤R O (rsU U w j v a) j′ (obs F j′ w) (obs F j′ (rsU U w j v a))
no-lower {O = O} U a j′ = obs-mono O j′ (growU U a)

lower-blocked : ¬ Above O₀ w1 j₀ 0
lower-blocked ab with ab j₀ tt refl
... | ()

posUp : RaiseUp F₀ O₀
posUp = up-of posInst grow₀
```

## §3 (iv) 读数随成员变: κHc 型的有界族

成员: 合法界 `Lb` 之下的字面位置 $(a, p)$; 键 $a$; 读数类型 `HB (Lev a)`; 世界在每个位置放 `Wd (step (Lev a))` (低一级的世界, 加一个高度作界), 读数是界. 升界: 按 `bdec` 判定, 同键的位置换成截面在**它自己**处的值.

```agda
module DPos {S : KS} {ω : Wd S} {Lb : HB S} (lω : LgW S ω) (lL : LgB Lb) where
  PJ : Set
  PJ = Σ (HB S) (λ a → a ⊲[ ω ] Lb)

  dF : DFrame
  dF = record
    { Wᴰ = (a : HB S) → a ⊲[ ω ] Lb → Wd (step (Lev a)) ; Jᴰ = PJ ; Keyᴰ = HB S ; keyᴰ = proj₁
    ; Vᴰ = λ j → HB (Lev (proj₁ j)) ; obsᴰ = λ j w → proj₂ (w (proj₁ j) (proj₂ j)) ; Evᴰ = λ _ _ _ → ⊤ }

  rsD : Wᴰ dF → PJ → ((j : PJ) → HB (Lev (proj₁ j))) → Wᴰ dF
  rsD w (a , p) vs b q = pick (bdec q p lω lL) (proj₁ (w b q) , vs (b , q)) (w b q)

  setD : ∀ (w : Wᴰ dF) (j j′ : PJ) vs → proj₁ j′ ≡ proj₁ j → proj₂ (rsD w j vs (proj₁ j′) (proj₂ j′)) ≡ vs j′
  setD w (a , p) (b , q) vs k with bdec q p lω lL
  ... | inj₁ _ = refl
  ... | inj₂ ne = ⊥-elim (ne k)

  keepD : ∀ (w : Wᴰ dF) (j j′ : PJ) vs → ¬ (proj₁ j′ ≡ proj₁ j) →
    proj₂ (rsD w j vs (proj₁ j′) (proj₂ j′)) ≡ proj₂ (w (proj₁ j′) (proj₂ j′))
  keepD w (a , p) (b , q) vs nk with bdec q p lω lL
  ... | inj₁ e = ⊥-elim (nk e)
  ... | inj₂ _ = refl

  dR : DRaise dF
  dR = record
    { rsᴰ = rsD
    ; setᴰ = λ {w} {j} {j′} vs _ k → setD w j j′ vs k
    ; keepᴰ = λ {w} {j} {j′} vs _ nk → keepD w j j′ vs nk }

  dCross : DCross dF hkH
  dCross w lω′ lL′ j j′ p q = tt

  -- 世界序: 逐位置就是 step 的世界序; 读数序: 界在该位置的低一级世界里的 ⊲
  dO : DOrd dF
  dO = record
    { _≤Wᴰ_ = λ w w′ → ∀ b q → _≤w_ (step (Lev b)) (w b q) (w′ b q)
    ; ≤Rᴰ = λ w j x y → x ⊲[ proj₁ (w (proj₁ j) (proj₂ j)) ] y
    ; obs-monoᴰ = λ j le → proj₂ (le (proj₁ j) (proj₂ j)) }

  dGrow : DGrow dO dR
  dGrow {w} {a , p} vs ab b q with bdec q p lω lL
  ... | inj₁ e = ≤w-rf (Lev b) , ab (b , q) tt e
  ... | inj₂ _ = ≤w-rf (step (Lev b))

  -- 截面是键的函数时, 同键成员读到同一个值 (拷贝相干, 不搬运)
  keyed : (u : (a : HB S) → HB (Lev a)) → ∀ w j (j′ : PJ) → proj₁ j′ ≡ proj₁ j →
    obsᴰ dF j′ (rsᴰ dR w j (λ i → u (proj₁ i))) ≡ u (proj₁ j′)
  keyed u w j j′ k = setᴰ dR {w} {j} {j′} (λ i → u (proj₁ i)) tt k

  -- 这个世界就是 sup (界下位置) (step ∘ Lev) 的世界; 读数序与界就是那里新种类的第一位置与界
  supW : KS
  supW = sup PJ (λ j → step (Lev (proj₁ j)))

  toSup : Wᴰ dF → Wd supW
  toSup w j = w (proj₁ j) (proj₂ j)

  ofSup : Wd supW → Wᴰ dF
  ofSup u a p = u (a , p)

  sup-rt₁ : ∀ w → ofSup (toSup w) ≡ w
  sup-rt₁ w = refl

  sup-rt₂ : ∀ u → toSup (ofSup u) ≡ u
  sup-rt₂ u = refl

  ord-same : ∀ w (j : PJ) x y → ≤Rᴰ dO w j x y ≡ Pr supW (j , inj₂ tt) (toSup w) x y
  ord-same w j x y = refl

  bd-same : ∀ w (j : PJ) x → Bd supW (j , inj₂ tt) x (toSup w) ≡ (x ⊲[ proj₁ (w (proj₁ j) (proj₂ j)) ] obsᴰ dF j w)
  bd-same w j x = refl
```

**相邻两级同在一个框架里.** 界 `hs hz` (世界 `azero`) 之下的成员 `hz` 与 `hs hz`. 它们的读数类型正是 `NegTreeLangRaise.raise-adj` 里的两个 $X$ (取 $S' =$ `Lev (hs hz)`, $\kappa =$ 新种类): 一个是 $S'$ 的新种类的坐标, 一个是 $S'$ 的高度. 单一读数的框架里两者不能同时 "读数取遍自己的类型" (`raise-adj`); 这里可以.

```agda
module Adj where
  open DPos {S₀} {azero} {hs hz} tt tt

  jL jH : PJ
  jL = hz , hsuc hself
  jH = hs hz , hself

  tyL : Vᴰ dF jL ≡ E (Lev {S₀} (hs hz)) (inj₂ tt)
  tyL = refl

  tyH : Vᴰ dF jH ≡ HB (Lev {S₀} (hs hz))
  tyH = refl

  secLH : HB S₀ → HB (Lev {S₀} (hs hz)) → (j : PJ) → HB (Lev (proj₁ j))
  secLH vL vH (hz , _) = vL
  secLH vL vH (hs hz , _) = vH
  secLH vL vH (a , _) = hz

  adj-free : ∀ (w : Wᴰ dF) (vL : HB S₀) (vH : HB (Lev {S₀} (hs hz))) →
    Σ (Wᴰ dF) (λ w′ → (obsᴰ dF jL w′ ≡ vL) × (obsᴰ dF jH w′ ≡ vH))
  adj-free w vL vH = w₂ , e₁ , e₂
    where
    s : (j : PJ) → HB (Lev (proj₁ j))
    s = secLH vL vH
    w₁ : Wᴰ dF
    w₁ = rsᴰ dR w jL s
    w₂ : Wᴰ dF
    w₂ = rsᴰ dR w₁ jH s
    e₂ : obsᴰ dF jH w₂ ≡ vH
    e₂ = setᴰ dR {w₁} {jH} {jH} s tt refl
    e₁ : obsᴰ dF jL w₂ ≡ vL
    e₁ = trans (keepᴰ dR {w₁} {jH} {jL} s tt (λ ())) (setᴰ dR {w} {jL} {jL} s tt refl)
```

**拷贝不相干 (盲).** 界 `hl (λ _ → hz)` 之下, 高度 `hz` 有两份证据 (`hlim 0`, `hlim 1`), 同键. 截面在两份上取不同的值, 一次升界后两份读数不同.

```agda
module Copies where
  f0 : ℕ → HB S₀
  f0 _ = hz

  open DPos {S₀} {azero} {hl f0} tt ((λ {w} n → hself) , (λ n → tt))

  c₀ c₁ : PJ
  c₀ = hz , hlim 0 hself
  c₁ = hz , hlim 1 hself

  sec : (j : PJ) → HB (Lev (proj₁ j))
  sec (hz , hlim zero _) = hz
  sec (hz , hlim (suc _) _) = hs hz
  sec (a , _) = hz

  copies-split : ∀ w → (obsᴰ dF c₀ (rsᴰ dR w c₀ sec) ≡ hz) × (obsᴰ dF c₁ (rsᴰ dR w c₀ sec) ≡ hs hz)
  copies-split w = setᴰ dR {w} {c₀} {c₀} sec tt refl , setᴰ dR {w} {c₀} {c₁} sec tt refl

  split-ne : ¬ (_≡_ {A = HB S₀} hz (hs hz))
  split-ne ()
```

## §4 `constD`: (iv) 包含单一读数的情形

```agda
D→Raise : ∀ {F : RaiseFrame} → DRaise (constD F) → Raise F
D→Raise R = record
  { rs = λ w j v → rsᴰ R w j (λ _ → v)
  ; set = λ v ev k → setᴰ R (λ _ → v) ev k
  ; keep = λ v ev nk → keepᴰ R (λ _ → v) ev nk }
```

## §5 界框架: (iii) 推出 "每个高度都能作界"

一个种类结构 $T$ 的种类 $\kappa$, 读界的函数 `top` (读到的确是界, `topBd`; 世界变大时界不降, `topMono`). 界框架: 一个成员, 读数 `top w`, 世界序就是 $T$ 的世界序, 读数序是 $\kappa$ 的第一位置.

```agda
module BdF (T : KS) (κ : K T) (top : Wd T → E T κ) (topBd : ∀ w → Bd T κ (top w) w)
  (topMono : ∀ {w w′} → _≤w_ T w w′ → Pr T κ w′ (top w) (top w′)) where

  bF : RaiseFrame
  bF = record { W = Wd T ; J = ⊤ ; Key = ⊤ ; V = E T κ ; key = λ j → j ; obs = λ _ → top ; Ev = λ _ _ _ → ⊤ }

  bO : OrdFrame bF
  bO = record { _≤W_ = _≤w_ T ; ≤R = λ w _ → Pr T κ w ; obs-mono = λ _ le → topMono le }

  above : ∀ {w v} → Pr T κ w (top w) v → Above bO w tt v
  above p j′ _ _ = p

  up→rich : RaiseUp bF bO → ∀ w v → Pr T κ w (top w) v → Σ (Wd T) (λ w′ → _≤w_ T w w′ × Bd T κ v w′)
  up→rich U w v p = w′ , growU U (above p) , subst (λ x → Bd T κ x w′) (setU U (above p) tt refl) (topBd w′)
    where
    w′ : Wd T
    w′ = rsU U w tt v (above p)

  -- 一般形: 一切世界的界都满足 Q, 而某个界之上的坐标不满足 Q, 就没有 RaiseUp
  no-up-pred : (Q : E T κ → Set) → (∀ w → Q (top w)) → ∀ w v → Pr T κ w (top w) v → ¬ Q v →
    ¬ RaiseUp bF bO
  no-up-pred Q q w v p nq U = nq (subst Q (setU U (above p) tt refl) (q (rsU U w tt v (above p))))
```

**实例: `step T` 的新种类.** 界就是世界的第二分量; 升界换第二分量.

```agda
module _ (T : KS) where
  private
    module B = BdF (step T) (inj₂ tt) proj₂ (λ w → hself) (λ le → proj₂ le)

  levUp : RaiseUp B.bF B.bO
  levUp = record
    { rsU = λ w _ v _ → proj₁ w , v
    ; setU = λ _ _ _ → refl
    ; keepU = λ _ _ nk → ⊥-elim (nk refl)
    ; growU = λ a → ≤w-rf T , a tt tt refl }

  levRich : ∀ w v → Pr (step T) (inj₂ tt) w (proj₂ w) v → Σ (Wd (step T)) (λ w′ → _≤w_ (step T) w w′ × Bd (step T) (inj₂ tt) v w′)
  levRich = B.up→rich levUp
```

**对照: 界固定的种类 `frozen T`.** 一个种类, 坐标 `HB T`, 第一位置就是 `⊲` ((i) 的形状, 投影取恒等), 世界就是 $T$ 的世界, 但界固定: 坐标在界下当且仅当它是 `hz` 的第一位置. 这是合法的 `KS`.

```agda
frozen : KS → KS
frozen T = record
  { K = ⊤ ; E = λ _ → HB T ; Wd = Wd T ; LgW = LgW T ; _≤w_ = _≤w_ T ; ≤w-rf = ≤w-rf T ; ≤w-tr = ≤w-tr T
  ; Bd = λ _ a w → a ⊲[ w ] hz ; Pr = λ _ w a a′ → a ⊲[ w ] a′
  ; Bd↑ = λ q e → ⊲ᴮ↑ q e ; cmpK = λ e e′ lw → cmpB e e′ lw tt
  ; LgE = λ _ → LgB ; lgBd = λ e lw → lgB⊲ e lw tt ; bot = λ _ → hz ; botBd = λ _ w → hself }

frozen-ord : ∀ {T : KS} {w : Wd T} {a a′ : HB T} → Pr (frozen T) tt w a a′ ≡ (a ⊲[ w ] a′)
frozen-ord = refl

no-up-frozen : ∀ (T : KS) (top : Wd T → HB T) (tb : ∀ w → Bd (frozen T) tt (top w) w)
  (tm : ∀ {w w′} → _≤w_ T w w′ → Pr (frozen T) tt w′ (top w) (top w′)) → Wd T →
  ¬ RaiseUp (BdF.bF (frozen T) tt top tb tm) (BdF.bO (frozen T) tt top tb tm)
no-up-frozen T top tb tm w₀ U with BdF.up→rich (frozen T) tt top tb tm U w₀ (hs hz) (hsuc (tb w₀))
... | _ , _ , ()

-- 前提可满足: top 取 hz
frozen-top : ∀ (T : KS) → Σ (Wd T → HB T) (λ top → (∀ w → Bd (frozen T) tt (top w) w) ×
  (∀ {w w′} → _≤w_ T w w′ → Pr (frozen T) tt w′ (top w) (top w′)))
frozen-top T = (λ _ → hz) , (λ w → hself) , (λ _ → hself)
```

## §6 结论 (按档)

- **[定理, (ii)]** **`no-cross-diag`**, `no-cross-empty` (排除); `pos-cross` (实例); **`cross-shape`**, **`cross-unique`**, `keydec` (共界成员上升界唯一, 是按 `bdec` 的点更新).
- **[定理, (iii)]** `posGrow`, `grow₀`, **`lowers-anyway`** (条件形的 `Grow` 不排除 `any-lowers`); **`grow-all→⊥`** (无条件增长在 `F₀` 上无实例); `up-of`, **`no-lower`**, **`lower-blocked`**, `posUp` (`RaiseUp` 排除降值).
- **[定理, (iv)]** `DPos.dR`, `dCross`, `dO`, `dGrow`, `keyed` (κHc 型有界族: 合法升界, 满足 (ii), (iii)); **`Adj.adj-free`**, `tyL`, `tyH` (`raise-adj` 的两级同在, 读数各取任意值); **`Copies.copies-split`** (盲: 拷贝不相干); `D→Raise`.
- **[定理, 界框架]** **`BdF.up→rich`**, **`BdF.no-up-pred`** (一切界满足 $Q$ 而某个界之上有不满足 $Q$ 的坐标 ⇒ 无 `RaiseUp`; 否定一路的 `LevP` 取 $Q = (\equiv \mathrm{hz})$ 或 `NatH` 正是这一形, 实例化留给它); `levUp`, `levRich` (实例); `frozen`, `frozen-ord`, **`no-up-frozen`**, `frozen-top` (前提可满足).
- **[判断, 选择]** 界框架的读数类型取坐标类型 `E T κ` 本身, 是选择: 若取 $\Sigma$ (HB S) P, `LevP` 也有 `RaiseUp`. 这一选择与 (i) 同源 ("坐标是高度, 界也是那个类型里的高度").
- **[判断]** 单值形 (只给一个键处的值) 要搬运, 与 `uip→raiseA1` 同处; 本篇绕开 (截面或键的函数), 没有证或否定它. `DPos` 的世界是抽象框架, 没有接到 `K₁` 或 `LevA` 的世界上.
