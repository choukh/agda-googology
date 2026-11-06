# 种类带证据, 比较取 `cmpB₀` (二): 外层界长高, 旧高度改贴新种类仍合法

> 不含记号. 入口 [AdmEv](AdmEv.lagda.md). 接手清单第 2 条 ([EvW](EvW.lagda.md) §3 "第一个障碍"): 外层界 $b\mapsto b\boxplus\delta$ 之后, 旧事件世界 $K_0$ 的种类 $(c,p)$ 对应新事件世界 $K_1$ 的 $(c,\mathrm{wk}\,p)$; $K_0$ 上的合法高度改贴 $K_1$ 的种类后, 它的 $\Omega$-节点要对 $K_1$ 的**一切**世界给单调数据, 而 $K_1$ 的世界不都是 $K_0$ 世界的像. 本篇证明: **在 `cmpB₀` 之下, 改贴保合法, 对一切合法 δ, 无附加条件** (`Lg-rl`).
>
> 证明的关键不是 "新世界是旧世界的像", 而是 **新世界在旧种类上的读数等于某个旧世界的读数** (`sim`): 对 $K_1$ 的每个事件表 $H$, 有 $K_0$ 的事件表 `rest H`, 使一切旧种类 $(c,p)$ 处 $\mathrm{rp}_1\,H\,c\,(\mathrm{wk}\,p) = \mathrm{rp}_0\,(\mathrm{rest}\,H)\,c\,p$. `rest` 对每个新事件 $(c_0,p_0')$ 用 `cmpB₀ (⊞-fst b δ) p₀'` 把坐标 $c_0$ 与旧界 $b$ 比较 (两者在新界 $b\boxplus\delta$ 之下: 字面公共上界): 若 $c_0\lhd b$ (得到旧证据 $r$), 保留为旧事件 $(c_0,r)$; 否则 $b$ 严格在 $c_0$ 之下, 这个事件不碰任何旧种类, 丢掉.
>
> 用到的引理:
>
> - **`fac`** (因子化): 对一切 $\sigma : 0\lhd\varepsilon$, 一切 $Y : c_0\lhd b\boxplus\varepsilon$, 一切旧证据 $p : c\lhd b$: `cmpB₀ (p ⨾ ⊞-⊲ b σ) Y` 等于先比 `cmpB₀ (⊞-⊲ b σ) Y`, 若结果是 $c_0\lhd b$ 的路径 $r$, 再比 `cmpB₀ p r` (在旧界与旧合法证明之下); 若结果是 $b\lhd c_0$ 的路径 $s$, 就是 $p ⨾ s$. 对 ε 结构递归. 这里用的是 `cmpB₀` 而不是 `cmpB`: $\Omega$-结点处坐标相同时 `cmpB₀` 不调用 δ 的单调数据 (`cmpB` 要调用, 那正是 `EvWGrow` 的条件 `RL` 的来源).
> - `diag-tr`: `cmpB₀ X (p₀ ⨾ X) ≡ inj₁ p₀`, 对一切路径 $X$ (`cmpB₀-diag` 的推广).
> - `inj₂-strict`: `cmpB₀` 的 `inj₂` 结果是严格的.
>
> 推论: `wk-⊞₀` (外层界接上任意合法 δ, 包括含 $\Omega$-节点的, 重放不变; 去掉了 `EvWGrow.RL`), `rest-wm` (`rest` 是 `wm` 的左逆), `bd→`, `bd←`.
>
> **范围.** 外层 `A`-世界 $a$ 不变 (它长高见 [AdmEvGrowA](AdmEvGrowA.lagda.md)); 新界的合法证明取 `Lg-⊞ b δ lb lδ` (相干; 不相干时重放可以变, `EvWNeg.no-wk`); 内层世界族 $v_0$ 不变. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEvGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; lg⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; toLt)
open import OCF.Align.AdmWCmp using (cmpB₀; dec-diag; cmpF-diag; <ᴮ-tr)
open import OCF.Align.AdmEvBase
```

## §1 路径的代数

```agda
module _ {S : KS} where
  tr-assoc : ∀ {a b c d : HB S} {w} (p : a ⊲[ w ] b) (q : b ⊲[ w ] c) (r : c ⊲[ w ] d) →
             ⊲ᴮ-tr (⊲ᴮ-tr p q) r ≡ ⊲ᴮ-tr p (⊲ᴮ-tr q r)
  tr-assoc p q hself = refl
  tr-assoc p q (hsuc r) = cong hsuc (tr-assoc p q r)
  tr-assoc p q (hlim n r) = cong (hlim n) (tr-assoc p q r)
  tr-assoc p q (hLim e r) = cong (hLim e) (tr-assoc p q r)

  ⊞⊲-tr : ∀ (b : HB S) {x y z : HB S} {w} (s : x ⊲[ w ] y) (t : y ⊲[ w ] z) →
          ⊲ᴮ-tr (⊞-⊲ b s) (⊞-⊲ b t) ≡ ⊞-⊲ b (⊲ᴮ-tr s t)
  ⊞⊲-tr b s hself = refl
  ⊞⊲-tr b s (hsuc t) = cong hsuc (⊞⊲-tr b s t)
  ⊞⊲-tr b s (hlim n t) = cong (hlim n) (⊞⊲-tr b s t)
  ⊞⊲-tr b s (hLim e t) = cong (hLim e) (⊞⊲-tr b s t)

  ⊞-steps : ∀ (b : HB S) {f : ℕ → HB S} (st : ∀ {w} n → f n ⊲[ w ] f (suc n)) {w n m} (q : n <ᴺ m) →
            stepsᴮ (λ {w′} k → ⊞-⊲ b (st {w′} k)) {w} q ≡ ⊞-⊲ b (stepsᴮ st {w} q)
  ⊞-steps b st zero = refl
  ⊞-steps b st (suc q) = trans (cong (λ t → ⊲ᴮ-tr t (⊞-⊲ b (st _))) (⊞-steps b st q)) (⊞⊲-tr b (stepsᴮ st q) (st _))

  fst-⊲ : ∀ (b : HB S) ε {w} → ⊞-fst {w = w} b ε ≡ ⊞-⊲ b (z⊲ᴮ ε)
  fst-⊲ b hz = refl
  fst-⊲ b (hs ε) = cong hsuc (fst-⊲ b ε)
  fst-⊲ b (hl f) = cong (hlim 0) (fst-⊲ b (f 0))
  fst-⊲ b (hΩ κ g) = cong (hLim (botBd S κ _)) (fst-⊲ b (g (bot S κ)))
```

## §2 `cmpB₀` 的三条一般性质

```agda
diag-tr : ∀ {M L c₀ : HB S₀} {w} (X : M ⊲[ w ] L) (p₀ : c₀ ⊲[ w ] M) (lw : Lg w) (l : LgB L) →
          cmpB₀ X (⊲ᴮ-tr p₀ X) lw l ≡ inj₁ p₀
diag-tr hself p₀ lw l = refl
diag-tr (hsuc X) p₀ lw l = diag-tr X p₀ lw l
diag-tr (hlim n X) p₀ lw (st , l) rewrite dec-diag n = diag-tr X p₀ lw (l n)
diag-tr (hLim e X) p₀ lw (mo , l) rewrite cmpF-diag e lw = diag-tr X p₀ lw (l _ (lg⊲ e lw))

private
  lt-hs : ∀ {a a′ : HB S₀} → (a ≡ a′) ⊎ (a <ᴮ a′) → a <ᴮ hs a′
  lt-hs (inj₁ refl) = <s₀
  lt-hs (inj₂ l) = <s l

  lt-hl : ∀ {a} {f : ℕ → HB S₀} n → (a ≡ f n) ⊎ (a <ᴮ f n) → a <ᴮ hl f
  lt-hl n (inj₁ refl) = <l₀ n
  lt-hl n (inj₂ l) = <l n l

  lt-hΩ : ∀ {a κ} {g : A → HB S₀} c → (a ≡ g c) ⊎ (a <ᴮ g c) → a <ᴮ hΩ κ g
  lt-hΩ c (inj₁ refl) = <Ω₀ c
  lt-hΩ c (inj₂ l) = <Ω c l

inj₂-strict : ∀ {M L c₀ : HB S₀} {w} (X : M ⊲[ w ] L) (Y : c₀ ⊲[ w ] L) (lw : Lg w) (l : LgB L) {s} →
              cmpB₀ X Y lw l ≡ inj₂ s → M <ᴮ c₀
inj₂-strict hself Y lw l ()
inj₂-strict (hsuc X) hself lw l refl = lt-hs (toLt X)
inj₂-strict (hlim n X) hself lw l refl = lt-hl n (toLt X)
inj₂-strict (hLim {c = c} e X) hself lw l refl = lt-hΩ c (toLt X)
inj₂-strict (hsuc X) (hsuc Y) lw l eq = inj₂-strict X Y lw l eq
inj₂-strict (hlim n X) (hlim m Y) lw (st , l) eq with <ᴺ-dec n m
... | injᵃ n<m = inj₂-strict (⊲ᴮ-tr X (stepsᴮ st n<m)) Y lw (l m) eq
... | injᵇ m<n = inj₂-strict X (⊲ᴮ-tr Y (stepsᴮ st m<n)) lw (l n) eq
... | injᶜ refl = inj₂-strict X Y lw (l n) eq
inj₂-strict (hLim {c = x} e X) (hLim {c = x′} e′ Y) lw (mo , l) eq with cmpF e e′ lw
... | inj₁ C.self = inj₂-strict X Y lw (l x (lg⊲ e lw)) eq
... | inj₁ (C.suc c′c) = inj₂-strict X (⊲ᴮ-tr Y (mo lw e′ e (C.suc c′c))) lw (l x (lg⊲ e lw)) eq
... | inj₁ (C.lim k c′c) = inj₂-strict X (⊲ᴮ-tr Y (mo lw e′ e (C.lim k c′c))) lw (l x (lg⊲ e lw)) eq
... | inj₂ cc′ = inj₂-strict (⊲ᴮ-tr X (mo lw e e′ cc′)) Y lw (l x′ (lg⊲ e′ lw)) eq
```

**因子化.** 旧界 $b$ (合法证明 `lb`) 固定; 新界 $b\boxplus\varepsilon$ 的合法证明取 `Lg-⊞ b ε lb lε`; 旧界到新界的路径取 `⊞-⊲ b σ` 的形状 ($\sigma : 0\lhd\varepsilon$; `⊞-fst` 是 $\sigma$ 取最小坐标脊的特例, `fst-⊲`).

```agda
module Fac (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) where
  post : ∀ {c c₀ : HB S₀} → c ⊲[ a ] b → (c₀ ⊲[ a ] b) ⊎ (b ⊲[ a ] c₀) → (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)
  post p (inj₁ r) = cmpB₀ p r la lb
  post p (inj₂ s) = inj₂ (⊲ᴮ-tr p s)

  fac : ∀ ε (lε : LgB ε) (σ : hz ⊲[ a ] ε) {c₀} (Y : c₀ ⊲[ a ] b ⊞ ε) {c} (p : c ⊲[ a ] b) →
        cmpB₀ (⊲ᴮ-tr p (⊞-⊲ b σ)) Y la (Lg-⊞ b ε lb lε) ≡ post p (cmpB₀ (⊞-⊲ b σ) Y la (Lg-⊞ b ε lb lε))
  fac hz lε hself Y p = refl
  fac (hs ε) lε (hsuc σ) hself p = refl
  fac (hs ε) lε (hsuc σ) (hsuc Y) p = fac ε lε σ Y p
  fac (hl f) (st , l) (hlim n σ) hself p = refl
  fac (hl f) (st , l) (hlim n σ) (hlim m Y) p with <ᴺ-dec n m
  ... | injᵃ n<m =
    trans (cong (λ t → cmpB₀ t Y la (Lg-⊞ b (f m) lb (l m))) (tr-assoc p (⊞-⊲ b σ) S⁺))
          (subst (λ Z → cmpB₀ (⊲ᴮ-tr p Z) Y la (Lg-⊞ b (f m) lb (l m)) ≡ post p (cmpB₀ Z Y la (Lg-⊞ b (f m) lb (l m))))
                 (sym eqZ) (fac (f m) (l m) (⊲ᴮ-tr σ (stepsᴮ st n<m)) Y p))
    where
    S⁺ = stepsᴮ (λ {w′} k → ⊞-⊲ b (st {w′} k)) n<m
    eqZ : ⊲ᴮ-tr (⊞-⊲ b σ) S⁺ ≡ ⊞-⊲ b (⊲ᴮ-tr σ (stepsᴮ st n<m))
    eqZ = trans (cong (⊲ᴮ-tr (⊞-⊲ b σ)) (⊞-steps b st n<m)) (⊞⊲-tr b σ (stepsᴮ st n<m))
  ... | injᵇ m<n = fac (f n) (l n) σ (⊲ᴮ-tr Y (stepsᴮ (λ {w′} k → ⊞-⊲ b (st {w′} k)) m<n)) p
  ... | injᶜ refl = fac (f n) (l n) σ Y p
  fac (hΩ tt g) (mo , l) (hLim e σ) hself p = refl
  fac (hΩ tt g) (mo , l) (hLim {c = x} e σ) (hLim {c = x′} e′ Y) p with cmpF e e′ la
  ... | inj₁ C.self = fac (g x) (l x (lg⊲ e la)) σ Y p
  ... | inj₁ (C.suc c′c) = fac (g x) (l x (lg⊲ e la)) σ (⊲ᴮ-tr Y (⊞-⊲ b (mo la e′ e (C.suc c′c)))) p
  ... | inj₁ (C.lim k c′c) = fac (g x) (l x (lg⊲ e la)) σ (⊲ᴮ-tr Y (⊞-⊲ b (mo la e′ e (C.lim k c′c)))) p
  ... | inj₂ cc′ =
    trans (cong (λ t → cmpB₀ t Y la (Lg-⊞ b (g x′) lb (l x′ (lg⊲ e′ la)))) (tr-assoc p (⊞-⊲ b σ) (⊞-⊲ b π)))
          (subst (λ Z → cmpB₀ (⊲ᴮ-tr p Z) Y la (Lg-⊞ b (g x′) lb (l x′ (lg⊲ e′ la))) ≡
                        post p (cmpB₀ Z Y la (Lg-⊞ b (g x′) lb (l x′ (lg⊲ e′ la)))))
                 (sym (⊞⊲-tr b σ π)) (fac (g x′) (l x′ (lg⊲ e′ la)) (⊲ᴮ-tr σ π) Y p))
    where
    π = mo la e e′ cc′
```

## §3 长高: 弱化, 限制, 模拟

```agda
module Grow₀ (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) (δ : HB S₀) (lδ : LgB δ) where
  open Fac a la b lb
  module O = Rp₀ a b la lb
  module N = Rp₀ a (b ⊞ δ) la (Lg-⊞ b δ lb lδ)

  l⁺ : LgB (b ⊞ δ)
  l⁺ = Lg-⊞ b δ lb lδ

  Xg : b ⊲[ a ] b ⊞ δ
  Xg = ⊞-fst b δ

  wk : ∀ {c} → c ⊲[ a ] b → c ⊲[ a ] b ⊞ δ
  wk p = ⊲ᴮ-tr p Xg

  facg : ∀ {c c₀} (p : c ⊲[ a ] b) (Y : c₀ ⊲[ a ] b ⊞ δ) → cmpB₀ (wk p) Y la l⁺ ≡ post p (cmpB₀ Xg Y la l⁺)
  facg p Y = subst (λ Z → cmpB₀ (⊲ᴮ-tr p Z) Y la l⁺ ≡ post p (cmpB₀ Z Y la l⁺))
                   (sym (fst-⊲ b δ)) (fac δ lδ (z⊲ᴮ δ) Y p)

  -- 弱化的两个证据: 比较不变
  cmp-wk : ∀ {c c₀} (p : c ⊲[ a ] b) (p₀ : c₀ ⊲[ a ] b) → cmpB₀ (wk p) (wk p₀) la l⁺ ≡ cmpB₀ p p₀ la lb
  cmp-wk p p₀ = trans (facg p (wk p₀)) (cong (post p) (diag-tr Xg p₀ la l⁺))

  wkE : O.Ev → N.Ev
  wkE e = N.ev (O.ec e) (wk (O.ep e)) (O.eδ e) (O.elδ e)

  wm : O.Hist → N.Hist
  wm = map wkE

  -- 外层界接上任意合法 δ (可含 Ω-节点): 重放不变, 无附加条件
  wk-⊞₀ : ∀ H c p → N.rp (wm H) c (wk p) ≡ O.rp H c p
  wk-⊞₀ [] c p = refl
  wk-⊞₀ (e ∷ H) c p = cong₂ (λ r t → O.contrib (O.fix r) (O.eδ e) t) (cmp-wk p (O.ep e)) (wk-⊞₀ H c p)
```

**限制.** 新事件 $(c_0,p_0')$: 若 $c_0\lhd b$ (路径 $r$, 由 `cmpB₀ Xg p₀'` 给出), 变成旧事件 $(c_0,r)$; 否则丢掉.

```agda
  restE : ∀ {c₀} → (c₀ ⊲[ a ] b) ⊎ (b ⊲[ a ] c₀) → (δ′ : HB (Lev c₀)) → LgB δ′ → O.Hist → O.Hist
  restE (inj₁ r) δ′ l H = O.ev _ r δ′ l ∷ H
  restE (inj₂ _) δ′ l H = H

  rest : N.Hist → O.Hist
  rest [] = []
  rest (e ∷ H) = restE (cmpB₀ Xg (N.ep e) la l⁺) (N.eδ e) (N.elδ e) (rest H)

  rest-wm : ∀ H → rest (wm H) ≡ H
  rest-wm [] = refl
  rest-wm (e ∷ H) =
    trans (cong (λ R → restE R (O.eδ e) (O.elδ e) (rest (wm H))) (diag-tr Xg (O.ep e) la l⁺)) (cong (e ∷_) (rest-wm H))
```

**模拟: 新世界在旧种类上的读数是某个旧世界的读数.**

```agda
  private
    below-b : ∀ {c c₀} → c ⊲[ a ] b → b <ᴮ c₀ → c <ᴮ c₀
    below-b {c₀ = c₀} p l with toLt p
    ... | inj₁ refl = l
    ... | inj₂ m = <ᴮ-tr m l

  sim : ∀ H c (p : c ⊲[ a ] b) → N.rp H c (wk p) ≡ O.rp (rest H) c p
  sim [] c p = refl
  sim (e ∷ H) c p =
    trans (cong (λ r → N.contrib (N.fix r) (N.eδ e) (N.rp H c (wk p))) (facg p (N.ep e)))
          (stp (cmpB₀ Xg (N.ep e) la l⁺) refl)
    where
    stp : (R : (N.ec e ⊲[ a ] b) ⊎ (b ⊲[ a ] N.ec e)) → cmpB₀ Xg (N.ep e) la l⁺ ≡ R →
          N.contrib (N.fix (post p R)) (N.eδ e) (N.rp H c (wk p)) ≡ O.rp (restE R (N.eδ e) (N.elδ e) (rest H)) c p
    stp (inj₁ r) eq = cong (O.contrib (O.cmpS p r) (N.eδ e)) (sim H c p)
    stp (inj₂ s) eq =
      trans (O.contrib-below (below-b p (inj₂-strict Xg (N.ep e) la l⁺ eq)) (N.fix (inj₂ (⊲ᴮ-tr p s))) (N.eδ e) (N.rp H c (wk p)))
            (sim H c p)
```

## §4 改贴种类保合法

两个事件种类结构, 内层世界族相同: $K_0$ 在旧界 $b$ 之下, $K_1$ 在新界 $b\boxplus\delta$ 之下. 种类映射 $(c,p)\mapsto(c,\mathrm{wk}\,p)$, 坐标类型不变. 高度的改贴 `rl` 只换 $\Omega$-节点的种类.

```agda
module Relabel (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) (δ : HB S₀) (lδ : LgB δ)
               (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  open Grow₀ a la b lb δ lδ
  module K₀ = EvKS₀ a b la lb v₀ lv₀
  module K₁ = EvKS₀ a (b ⊞ δ) la l⁺ v₀ lv₀

  km : K₀.Kᵉ → K₁.Kᵉ
  km κ = proj₁ κ , wk (proj₂ κ)

  rl : HB K₀.evKS₀ → HB K₁.evKS₀
  rl hz = hz
  rl (hs t) = hs (rl t)
  rl (hl f) = hl (λ n → rl (f n))
  rl (hΩ κ g) = hΩ (km κ) (λ x → rl (g x))

  -- 新世界 H 与它的限制 rest H: 旧种类处的界互相搬运
  bd-to : ∀ H κ x → K₀.Bdᵉ κ x (rest H) → K₁.Bdᵉ (km κ) x H
  bd-to H κ x e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sym (sim H (proj₁ κ) (proj₂ κ))) e

  bd-from : ∀ H κ x → K₁.Bdᵉ (km κ) x H → K₀.Bdᵉ κ x (rest H)
  bd-from H κ x e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sim H (proj₁ κ) (proj₂ κ)) e

  rl⊲ : ∀ {H₀ H₁} → (∀ κ x → K₀.Bdᵉ κ x H₀ → K₁.Bdᵉ (km κ) x H₁) →
        ∀ {t t′} → _⊲[_]_ {K₀.evKS₀} t H₀ t′ → _⊲[_]_ {K₁.evKS₀} (rl t) H₁ (rl t′)
  rl⊲ tr hself = hself
  rl⊲ tr (hsuc q) = hsuc (rl⊲ tr q)
  rl⊲ tr (hlim n q) = hlim n (rl⊲ tr q)
  rl⊲ tr (hLim {κ = κ} {c = x} e q) = hLim (tr κ x e) (rl⊲ tr q)

  Lg-rl : ∀ t → LgB {K₀.evKS₀} t → LgB {K₁.evKS₀} (rl t)
  Lg-rl hz l = tt
  Lg-rl (hs t) l = Lg-rl t l
  Lg-rl (hl f) (st , l) = (λ {H} n → rl⊲ (bd-to H) (st {rest H} n)) , (λ n → Lg-rl (f n) (l n))
  Lg-rl (hΩ κ g) (mo , l) =
    (λ {H} {x} {x′} lw e e′ pr → rl⊲ (bd-to H) (mo {rest H} tt (bd-from H κ x e) (bd-from H κ x′ e′) pr)) ,
    (λ x lx → Lg-rl (g x) (l x lx))
```

**旧世界的像: 界双向相同** (`wk-⊞₀`), 所以 `rl` 也把旧世界里的第一位置送到像世界里.

```agda
  bd→ : ∀ κ x H → K₀.Bdᵉ κ x H → K₁.Bdᵉ (km κ) x (wm H)
  bd→ κ x H e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sym (wk-⊞₀ H (proj₁ κ) (proj₂ κ))) e

  bd← : ∀ κ x H → K₁.Bdᵉ (km κ) x (wm H) → K₀.Bdᵉ κ x H
  bd← κ x H e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (wk-⊞₀ H (proj₁ κ) (proj₂ κ)) e

  rl⊲-wm : ∀ {H t t′} → _⊲[_]_ {K₀.evKS₀} t H t′ → _⊲[_]_ {K₁.evKS₀} (rl t) (wm H) (rl t′)
  rl⊲-wm {H} = rl⊲ (λ κ x → bd→ κ x H)
```
