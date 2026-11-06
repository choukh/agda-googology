# 事件历史世界 (一): 事件表, 重放, 重放的律

> 不含记号. 入口 [EvW](EvW.lagda.md). 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §5.2 (方向 B).
>
> **选择 (写清).** 外层世界固定: 一个种类结构 `S`, 一个合法世界 $w$, 一个合法高度 $b$ (外层的高度界; 在最小实例里 $S=S_0$, $b$ 是 `step S₀` 世界的第二分量, 即 `L′ 1` 里 `κH` 的界). 坐标是 $b$ 在 $w$ 里的字面第一位置 $c\lhd_{[w]}b$. 每个坐标 $c$ 有一个槽, 类型 $X\,c=$ `HB (Lev c)`; 这是 `UniTrBase.LevSlot` 的槽族 (那里坐标 `hs c` 处的槽是 `HB (Lev (up c))`; 对不含 $\Omega$-节点的 $c$ 两者定义相等, 例如 `κ₂` 的坐标类型 `HB (step S₀)` 就是 $X$ (`hs hz`)).
>
> - **事件** `Ev`: 坐标 $c_0$, 可入证据 $p_0 : c_0\lhd_{[w]} b$, 增量 $\delta : X\,c_0$, 增量合法. **世界**是事件的有限表 `Hist` (新事件在表头). 表的下标是位置, 离散.
> - **重放** `rp H c p`: 从 $0$ 起, 对每个事件 (由旧到新) 用 `cmpS p p₀` 比较当前坐标与事件坐标 (两者都在 $b$ 之下: 字面公共上界), 结果是 "$c_0\lhd c$" (带路径 $q$) 或 "$c$ 严格低于 $c_0$". 前者累加 `emb⊲ q δ` (`UniTrNeg`), 后者不动. `cmpS` 就是 `cmpB` 加 `StallDxBdec.toLt`.
>
> 本篇的定理 (对一切 `S`, 一切合法的 $w,b$):
>
> 1. `rp-mono`, `rp-suf`: 加事件只增界 (字面第一位置, 任意内层世界).
> 2. `new-self`: 新事件的路径字面是 `hself` 时, 新事件坐标处的界**定义地**是旧界 ⊞ 增量 (`refl`). `new-gen`: 一般路径时, 是旧界 ⊞ (增量沿某个自环 $e : c_0\equiv c_0$ 的搬运). 不用 K, 所以自环去不掉 (见 §3 的说明).
> 3. `rp-below`: 严格低于事件坐标的坐标, 界不变 (命题相等). `rp-above`: 事件坐标及其上的坐标, 界恰好接上 `emb⊲ q δ`, $q$ 是某条路径.
> 4. `Lg-rp`: 重放的界合法.
> 5. `same`: 是否累加只看坐标, 不看证据 (两个证据下方向一致).
> 6. `wk-suc`: 外层界沿后继长高 ($b\mapsto \mathrm{hs}\,b$, 证据接 `hsuc`), 重放不变 (定义相等加归纳). `wk-⊞`: 外层界接上不含 $\Omega$-节点的增量 ($b\mapsto b\boxplus\delta$, 合法证明取 `Lg-⊞`), 重放不变. 含 $\Omega$-节点的增量在 [EvWGrow](EvWGrow.lagda.md).
> 7. `EvKS`: 带证据的种类 $(c,p)$ 上, 事件表是一个种类结构 (`KS`), 界由重放给出; `HtTowerTy` 的高度, 第一位置, 合法, `cmpB` 原样可用.
>
> 律里出现的每一对坐标都带着在 $b$ 之下的证据 (字面公共上界). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvWBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; wf; irr; toLt)
open import OCF.Align.UniTrNeg using (emb⊲; Lg-emb⊲)
```

## §1 严格子项的传递, 比较的两种结果

`cmpS` 的结果类型 `Cmp c c₀`: 事件坐标 $c_0$ 是 $c$ 的第一位置 (含相等), 或 $c$ 是 $c_0$ 的严格子项. 两者互斥 (`no-both`): 这是 "方向只看坐标" 的全部内容.

```agda
module _ {S : KS} where
  <ᴮ-tr : ∀ {a b c : HB S} → a <ᴮ b → b <ᴮ c → a <ᴮ c
  <ᴮ-tr p <s₀ = <s p
  <ᴮ-tr p (<s q) = <s (<ᴮ-tr p q)
  <ᴮ-tr p (<l₀ n) = <l n p
  <ᴮ-tr p (<l n q) = <l n (<ᴮ-tr p q)
  <ᴮ-tr p (<Ω₀ c) = <Ω c p
  <ᴮ-tr p (<Ω c q) = <Ω c (<ᴮ-tr p q)

  module Cm (w : Wd S) where
    Cmp : HB S → HB S → Set
    Cmp c c₀ = (c₀ ⊲[ w ] c) ⊎ (c <ᴮ c₀)

    no-both : ∀ {c c₀ : HB S} → c₀ ⊲[ w ] c → c <ᴮ c₀ → ⊥
    no-both {c} {c₀} q l = go (toLt q)
      where
      go : (c₀ ≡ c) ⊎ (c₀ <ᴮ c) → ⊥
      go (inj₁ e) = irr (wf c) (subst (λ x → c <ᴮ x) e l)
      go (inj₂ m) = irr (wf c) (<ᴮ-tr l m)

    -- 两个比较结果方向一致 (与证据无关)
    Same : ∀ {c c₀} → Cmp c c₀ → Cmp c c₀ → Set
    Same (inj₁ _) (inj₁ _) = ⊤
    Same (inj₂ _) (inj₂ _) = ⊤
    Same (inj₁ _) (inj₂ _) = ⊥
    Same (inj₂ _) (inj₁ _) = ⊥

    same : ∀ {c c₀} (r r′ : Cmp c c₀) → Same r r′
    same (inj₁ _) (inj₁ _) = tt
    same (inj₁ q) (inj₂ l) = no-both q l
    same (inj₂ l) (inj₁ q) = no-both q l
    same (inj₂ _) (inj₂ _) = tt

    fromLt : ∀ {c c₀} → (c ≡ c₀) ⊎ (c <ᴮ c₀) → Cmp c c₀
    fromLt {c₀ = c₀} (inj₁ e) = inj₁ (subst (λ x → c₀ ⊲[ w ] x) (sym e) hself)
    fromLt (inj₂ l) = inj₂ l

    fix : ∀ {c c₀} → (c₀ ⊲[ w ] c) ⊎ (c ⊲[ w ] c₀) → Cmp c c₀
    fix (inj₁ q) = inj₁ q
    fix (inj₂ r) = fromLt (toLt r)

    -- 一个事件的贡献: 在上者接 emb⊲ q δ, 严格在下者不动 (只依赖内层的 w, 不依赖外层界)
    contrib : ∀ {c c₀} → Cmp c c₀ → HB (Lev c₀) → HB (Lev c) → HB (Lev c)
    contrib (inj₁ q) δ acc = acc ⊞ emb⊲ q δ
    contrib (inj₂ _) δ acc = acc
```

## §2 事件, 世界, 重放

事件表只依赖外层世界 $w$ 与界 $b$, 不依赖它们的合法证明 (`EvT`); 重放要用合法证明 (`cmpB` 要), 所以放在 `Rp` 里.

```agda
module EvT {S : KS} (w : Wd S) (b : HB S) where
  record Ev : Set where
    constructor ev
    field
      ec  : HB S
      ep  : ec ⊲[ w ] b
      eδ  : HB (Lev ec)
      elδ : LgB eδ
  open Ev public

  Hist : Set
  Hist = List Ev

  data Suf : Hist → Hist → Set where
    here  : ∀ {H} → Suf H H
    there : ∀ {H H′} e → Suf H H′ → Suf H (e ∷ H′)

  suf-tr : ∀ {G H K} → Suf G H → Suf H K → Suf G K
  suf-tr s here = s
  suf-tr s (there e t) = there e (suf-tr s t)

  suf-++ : ∀ new H → Suf H (new ++ H)
  suf-++ [] H = here
  suf-++ (e ∷ new) H = there e (suf-++ new H)

module Rp {S : KS} (w : Wd S) (b : HB S) (lw : LgW S w) (lb : LgB b) where
  open Cm {S} w public
  open EvT {S} w b public

  X : HB S → Set
  X c = HB (Lev c)

  -- 比较: 两个坐标都在 b 之下
  cmpS : ∀ {c c₀} → c ⊲[ w ] b → c₀ ⊲[ w ] b → Cmp c c₀
  cmpS p p₀ = fix (cmpB p p₀ lw lb)

  rp : Hist → (c : HB S) → c ⊲[ w ] b → X c
  rp [] c p = hz
  rp (e ∷ es) c p = contrib (cmpS p (ep e)) (eδ e) (rp es c p)
```

**加事件只增界.** `Suf H H′`: $H'$ 是 $H$ 前面加若干事件. 这是世界的 "变大".

```agda
  contrib-fst : ∀ {c c₀} (r : Cmp c c₀) δ acc {v} → acc ⊲[ v ] contrib r δ acc
  contrib-fst (inj₁ q) δ acc = ⊞-fst acc (emb⊲ q δ)
  contrib-fst (inj₂ _) δ acc = hself

  rp-mono : ∀ e es c p {v} → rp es c p ⊲[ v ] rp (e ∷ es) c p
  rp-mono e es c p = contrib-fst (cmpS p (ep e)) (eδ e) (rp es c p)

  rp-suf : ∀ {H H′} → Suf H H′ → ∀ c p {v} → rp H c p ⊲[ v ] rp H′ c p
  rp-suf here c p = hself
  rp-suf (there e s) c p = ⊲ᴮ-tr (rp-suf s c p) (rp-mono e _ c p)
```

**合法性保持.**

```agda
  Lg-contrib : ∀ {c c₀} (r : Cmp c c₀) δ acc → LgB δ → LgB acc → LgB (contrib r δ acc)
  Lg-contrib (inj₁ q) δ acc lδ la = Lg-⊞ acc (emb⊲ q δ) la (Lg-emb⊲ q δ lδ)
  Lg-contrib (inj₂ _) δ acc lδ la = la

  Lg-rp : ∀ H c p → LgB (rp H c p)
  Lg-rp [] c p = tt
  Lg-rp (e ∷ es) c p = Lg-contrib (cmpS p (ep e)) (eδ e) (rp es c p) (elδ e) (Lg-rp es c p)
```

## §3 新事件处忠实

**字面 `hself`.** 事件坐标就是外层界 $b$, 证据字面是 `hself`: `cmpB hself hself` 化到 `inj₁ hself`, `emb⊲ hself` 是恒等. 定义相等.

```agda
  new-self : ∀ δ lδ es → rp (ev b hself δ lδ ∷ es) b hself ≡ rp es b hself ⊞ δ
  new-self δ lδ es = refl
```

**一般路径.** `cmpS p p` 给出某条自环 $q : c\lhd c$. 自环的头构造子一定是 `hself` (`selfH`: 否则 $c$ 是自己的严格子项, 与良基矛盾), 于是 `emb⊲ q δ` 是 δ 沿某个 $e : c\equiv c$ 的搬运 (`embH`). 不开 K 时 $e$ 不能换成 `refl` (`HB S` 有函数分支, 没有 Hedberg), 所以一般情形的忠实只到 "旧界 ⊞ δ 的自环搬运". 折叠里的闭项证据会算到具体的路径; 对具体的路径, `cmpS p p` 可以化到 `inj₁ hself` (实例见 [EvWFeed](EvWFeed.lagda.md)).

```agda
  IsH : ∀ {a a′ : HB S} → a ⊲[ w ] a′ → Set
  IsH hself = ⊤
  IsH (hsuc _) = ⊥
  IsH (hlim _ _) = ⊥
  IsH (hLim _ _) = ⊥

  private
    lt-hs : ∀ {a a′ : HB S} → (a ≡ a′) ⊎ (a <ᴮ a′) → a <ᴮ hs a′
    lt-hs (inj₁ refl) = <s₀
    lt-hs (inj₂ l) = <s l

    lt-hl : ∀ {a} {f : ℕ → HB S} n → (a ≡ f n) ⊎ (a <ᴮ f n) → a <ᴮ hl f
    lt-hl n (inj₁ refl) = <l₀ n
    lt-hl n (inj₂ l) = <l n l

    lt-hΩ : ∀ {a κ} {g : E S κ → HB S} c → (a ≡ g c) ⊎ (a <ᴮ g c) → a <ᴮ hΩ κ g
    lt-hΩ c (inj₁ refl) = <Ω₀ c
    lt-hΩ c (inj₂ l) = <Ω c l

  isH⊎lt : ∀ {a a′} (q : a ⊲[ w ] a′) → IsH q ⊎ (a <ᴮ a′)
  isH⊎lt hself = inj₁ tt
  isH⊎lt (hsuc q) = inj₂ (lt-hs (toLt q))
  isH⊎lt (hlim n q) = inj₂ (lt-hl n (toLt q))
  isH⊎lt (hLim {c = c} e q) = inj₂ (lt-hΩ c (toLt q))

  selfH : ∀ {a} (q : a ⊲[ w ] a) → IsH q
  selfH {a} q = pick (isH⊎lt q)
    where
    pick : IsH q ⊎ (a <ᴮ a) → IsH q
    pick (inj₁ h) = h
    pick (inj₂ l) = ⊥-elim (irr (wf a) l)

  embH : ∀ {a a′} (q : a ⊲[ w ] a′) → IsH q → (δ : X a) →
         Σ (a ≡ a′) (λ e → emb⊲ q δ ≡ subst X e δ)
  embH hself tt δ = refl , refl
  embH (hsuc q) () δ
  embH (hlim n q) () δ
  embH (hLim e q) () δ

  contrib-self : ∀ {c} (r : Cmp c c) δ acc → Σ (c ≡ c) (λ e → contrib r δ acc ≡ acc ⊞ subst X e δ)
  contrib-self (inj₁ q) δ acc = proj₁ (embH q (selfH q) δ) , cong (acc ⊞_) (proj₂ (embH q (selfH q) δ))
  contrib-self {c} (inj₂ l) δ acc = ⊥-elim (irr (wf c) l)

  new-gen : ∀ c p δ lδ es → Σ (c ≡ c) (λ e → rp (ev c p δ lδ ∷ es) c p ≡ rp es c p ⊞ subst X e δ)
  new-gen c p δ lδ es = contrib-self (cmpS p p) δ (rp es c p)
```

## §4 在下者不动, 在上者接长

```agda
  contrib-below : ∀ {c c₀} → c <ᴮ c₀ → (r : Cmp c c₀) → ∀ δ acc → contrib r δ acc ≡ acc
  contrib-below l (inj₁ q) δ acc = ⊥-elim (no-both q l)
  contrib-below l (inj₂ _) δ acc = refl

  rp-below : ∀ e es c p → c <ᴮ ec e → rp (e ∷ es) c p ≡ rp es c p
  rp-below e es c p l = contrib-below l (cmpS p (ep e)) (eδ e) (rp es c p)

  contrib-above : ∀ {c c₀} → c₀ ⊲[ w ] c → (r : Cmp c c₀) → ∀ δ acc →
                  Σ (c₀ ⊲[ w ] c) (λ q → contrib r δ acc ≡ acc ⊞ emb⊲ q δ)
  contrib-above q₀ (inj₁ q) δ acc = q , refl
  contrib-above q₀ (inj₂ l) δ acc = ⊥-elim (no-both q₀ l)

  rp-above : ∀ e es c p → ec e ⊲[ w ] c →
             Σ (ec e ⊲[ w ] c) (λ q → rp (e ∷ es) c p ≡ rp es c p ⊞ emb⊲ q (eδ e))
  rp-above e es c p q₀ = contrib-above q₀ (cmpS p (ep e)) (eδ e) (rp es c p)
```

**方向与证据无关.** 同一坐标 $c$ 的两个证据 $p, p'$, 同一个事件 (甚至事件证据也可以换): 是否累加相同. 所以一个事件到达 $c_0$ 及其上的**每个坐标的每份证据拷贝**; 拷贝之间能不同的只有累加时用的路径 $q$ (见 [EvWNeg](EvWNeg.lagda.md)).

```agda
  dir-indep : ∀ {c c₀} (p p′ : c ⊲[ w ] b) (p₀ p₀′ : c₀ ⊲[ w ] b) → Same (cmpS p p₀) (cmpS p′ p₀′)
  dir-indep p p′ p₀ p₀′ = same (cmpS p p₀) (cmpS p′ p₀′)
```

## §5 外层界沿后继长高, 重放不变

外层世界不变, 界从 $b$ 长到 $\mathrm{hs}\,b$; 证据弱化成 `hsuc p` (`⊲ᴮ-tr p (hsuc hself)` 化到它). `cmpB (hsuc p) (hsuc q)` 化到 `cmpB p q`, 所以重放逐项相同.

```agda
module WkSuc {S : KS} (w : Wd S) (b : HB S) (lw : LgW S w) (lb : LgB b) where
  module O = Rp w b lw lb
  module N = Rp w (hs b) lw lb
  open Cm {S} w using (contrib)

  wkE : O.Ev → N.Ev
  wkE e = N.ev (O.ec e) (hsuc (O.ep e)) (O.eδ e) (O.elδ e)

  wk-suc : ∀ H c p → N.rp (map wkE H) c (hsuc p) ≡ O.rp H c p
  wk-suc [] c p = refl
  wk-suc (e ∷ H) c p = cong (contrib (O.cmpS p (O.ep e)) (O.eδ e)) (wk-suc H c p)
```

**一般化: 外层界接上不含 $\Omega$-节点的增量.** $b\mapsto b\boxplus\delta$ ($\delta$ 只有 $0$, 后继, ℕ-极限), 证据接 `⊞-fst b δ`, 新界的合法证明取 `Lg-⊞ b δ lb lδ` (相干: 沿 `⊞-fst` 走下去回到 `lb`). 这时 `cmpB` 逐项化回旧的 (`cmpB-⊞`, 对 δ 归纳; ℕ-极限处走第 0 项, `<ᴺ-dec 0 0` 化到 `injᶜ refl`), 重放不变 (`wk-⊞`). 合法证明若不相干, 重放可以变 ([EvWNeg](EvWNeg.lagda.md) 的 `no-wk`). 增量含 $\Omega$-节点时见 [EvWGrow](EvWGrow.lagda.md).

```agda
NoΩ : ∀ {S} → HB S → Set
NoΩ hz = ⊤
NoΩ (hs x) = NoΩ x
NoΩ (hl f) = ∀ n → NoΩ (f n)
NoΩ (hΩ κ g) = ⊥

module Wk⊞ {S : KS} (w : Wd S) (b : HB S) (lw : LgW S w) (lb : LgB b) where
  open Cm {S} w using (contrib; fix)

  cmpB-⊞ : ∀ δ → NoΩ δ → (lδ : LgB δ) → ∀ {c c₀} (p : c ⊲[ w ] b) (p₀ : c₀ ⊲[ w ] b) →
    cmpB (⊲ᴮ-tr p (⊞-fst b δ)) (⊲ᴮ-tr p₀ (⊞-fst b δ)) lw (Lg-⊞ b δ lb lδ) ≡ cmpB p p₀ lw lb
  cmpB-⊞ hz n lδ p p₀ = refl
  cmpB-⊞ (hs δ) n lδ p p₀ = cmpB-⊞ δ n lδ p p₀
  cmpB-⊞ (hl f) n (st , lf) p p₀ = cmpB-⊞ (f 0) (n 0) (lf 0) p p₀
  cmpB-⊞ (hΩ κ g) () lδ p p₀

  module _ (δ : HB S) (nδ : NoΩ δ) (lδ : LgB δ) where
    module O = Rp w b lw lb
    module N = Rp w (b ⊞ δ) lw (Lg-⊞ b δ lb lδ)

    wk : ∀ {c} → c ⊲[ w ] b → c ⊲[ w ] b ⊞ δ
    wk p = ⊲ᴮ-tr p (⊞-fst b δ)

    wkE : O.Ev → N.Ev
    wkE e = N.ev (O.ec e) (wk (O.ep e)) (O.eδ e) (O.elδ e)

    wk-⊞ : ∀ H c p → N.rp (map wkE H) c (wk p) ≡ O.rp H c p
    wk-⊞ [] c p = refl
    wk-⊞ (e ∷ H) c p = cong₂ (λ r a → contrib (fix r) (O.eδ e) a) (cmpB-⊞ δ nδ lδ p (O.ep e)) (wk-⊞ H c p)
```

## §6 带证据的种类: 事件表是一个种类结构

外层世界 $(w,b)$ 固定, 内层世界取一个固定的合法族 $v_0\,c$ : `Wd (Lev c)`. 种类是带证据的坐标 $(c,p)$; 坐标是 $X\,c$; 世界是事件表; 界是重放; 世界变大是 `Suf`; 比较是 `cmpB` (同一种类, 同一个界). 同一坐标的两个证据是两个种类 (拷贝); [EvWNeg](EvWNeg.lagda.md) 说它们的界一般不可比, 不能按坐标认同.

```agda
module EvKS {S : KS} (w : Wd S) (b : HB S) (lw : LgW S w) (lb : LgB b)
            (v₀ : (c : HB S) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  open Rp w b lw lb public

  Kᵉ : Set
  Kᵉ = Σ (HB S) (λ c → c ⊲[ w ] b)

  Eᵉ : Kᵉ → Set
  Eᵉ κ = X (proj₁ κ)

  Bdᵉ : (κ : Kᵉ) → Eᵉ κ → Hist → Set
  Bdᵉ κ x H = x ⊲[ v₀ (proj₁ κ) ] rp H (proj₁ κ) (proj₂ κ)

  Prᵉ : (κ : Kᵉ) → Hist → Eᵉ κ → Eᵉ κ → Set
  Prᵉ κ H x x′ = x ⊲[ v₀ (proj₁ κ) ] x′

  Bd↑ᵉ : ∀ {κ x H H′} → Suf H H′ → Bdᵉ κ x H → Bdᵉ κ x H′
  Bd↑ᵉ {κ} s e = ⊲ᴮ-tr e (rp-suf s (proj₁ κ) (proj₂ κ))

  cmpKᵉ : ∀ {κ x x′ H} → Bdᵉ κ x H → Bdᵉ κ x′ H → ⊤ → Prᵉ κ H x′ x ⊎ Prᵉ κ H x x′
  cmpKᵉ {κ} {H = H} e e′ _ = cmpB e e′ (lv₀ (proj₁ κ)) (Lg-rp H (proj₁ κ) (proj₂ κ))

  lgBdᵉ : ∀ {κ x H} → Bdᵉ κ x H → ⊤ → LgB x
  lgBdᵉ {κ} {H = H} e _ = lgB⊲ e (lv₀ (proj₁ κ)) (Lg-rp H (proj₁ κ) (proj₂ κ))

  botBdᵉ : ∀ κ H → Bdᵉ κ hz H
  botBdᵉ κ H = z⊲ᴮ (rp H (proj₁ κ) (proj₂ κ))

  evKS : KS
  evKS = record
    { K = Kᵉ ; E = Eᵉ ; Wd = Hist ; LgW = λ _ → ⊤
    ; _≤w_ = Suf ; ≤w-rf = here ; ≤w-tr = suf-tr
    ; Bd = Bdᵉ ; Pr = Prᵉ ; Bd↑ = λ {κ} {c} {w} {w′} s e → Bd↑ᵉ {κ} {c} {w} {w′} s e
    ; cmpK = λ {κ} {c} {c′} {w} e e′ l → cmpKᵉ {κ} {c} {c′} {w} e e′ l
    ; LgE = λ κ → LgB ; lgBd = λ {κ} {c} {w} e l → lgBdᵉ {κ} {c} {w} e l
    ; bot = λ κ → hz ; botBd = botBdᵉ }
```

`LgW` 取 `⊤`: 合法性由每个事件自带的 `elδ` 给出 (`Lg-rp`).
