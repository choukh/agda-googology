# 事件历史世界 (四): 外层界接上含 $\Omega$-节点的增量, 重放不变

> 不含记号. 入口 [EvW](EvW.lagda.md). `EvWBase.Wk⊞.wk-⊞` 对不含 $\Omega$-节点的增量证了: 外层界 $b\mapsto b\boxplus\delta$, 证据接 `⊞-fst`, 合法证明取 `Lg-⊞` (相干), 重放不变. `EvWNeg.no-wk` 说合法证明不相干时重放可以变. 这一篇在 `S₀` 上把 `wk-⊞` 推到含 $\Omega$-节点的 $\delta$, 条件是 $\delta$ 的合法数据**在自环上给 `hself`** (`RL`, 只沿 `⊞-fst` 经过的最小坐标那一条脊).
>
> - `dec-nn`: `<ᴺ-dec n n` 化到 `injᶜ refl` (对 $n$ 归纳, 不用 UIP).
> - `cmpF-self`: 同一个 `A`-证据和自己比, 结果是 `inj₁ self`.
> - `cmpB-⊞Ω`, `wk-⊞Ω`: 在 `RL` 之下重放不变.
> - **前提可满足**: `RL` 对 `Ωz` (常值分支) 与 `ΩA` (分支是 `A` 进 `HB S₀` 的嵌入 $\iota_A$, 单调数据沿路径递归) 成立, 后者是 "可数之上第一个 $\Omega$" 的字面形状.
>
> **范围.** 外层世界 $a$ (`A` 的界) 不变, 只长外层高度界 $b$; 只沿 `⊞-fst` 长. $a$ 也长时, `Bd↑` 改写坐标证据 (`⊲-tr e q`), 单调数据还多一个对世界合法证明的依赖 (`mo lw …`), 要再加两条相干条件; 本篇没有做 (判断).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvWGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using ()
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; lg⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvWBase
```

## §1 自比较

```agda
dec-nn : ∀ n → <ᴺ-dec n n ≡ injᶜ refl
dec-nn zero = refl
dec-nn (suc n) rewrite dec-nn n = refl

cmpF-self : ∀ {x L} (e : x ⊲ L) (lL : Lg L) → cmpF e e lL ≡ inj₁ C.self
cmpF-self C.self lL = refl
cmpF-self (C.suc e) lL = cmpF-self e lL
cmpF-self (C.lim n e) (st , w) rewrite dec-nn n = cmpF-self e (w n)
```

## §2 自反的合法数据

`RL a δ lδ`: 沿 `⊞-fst` 的脊 (ℕ-极限走第 0 项, $\Omega$-节点走最小坐标 `azero`), 每个 $\Omega$-节点的单调数据在 "同一坐标, 同一证据, 自环 `self`" 上给 `hself`.

```agda
RL : (a : A) → Lg a → (δ : HB S₀) → LgB δ → Set
RL a la hz l = ⊤
RL a la (hs δ) l = RL a la δ l
RL a la (hl f) (st , l) = RL a la (f 0) (l 0)
RL a la (hΩ tt g) (mo , l) =
  (∀ {c} (e : c ⊲ a) → mo la e e C.self ≡ hself) × RL a la (g azero) (l azero (lg⊲ (z⊲ a) la))
```

## §3 重放不变

```agda
module Grow (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b) where
  open Cm {S₀} a using (contrib; fix)

  cmpB-⊞Ω : ∀ δ (lδ : LgB δ) → RL a la δ lδ → ∀ {c c₀} (p : c ⊲[ a ] b) (p₀ : c₀ ⊲[ a ] b) →
    cmpB (⊲ᴮ-tr p (⊞-fst b δ)) (⊲ᴮ-tr p₀ (⊞-fst b δ)) la (Lg-⊞ b δ lb lδ) ≡ cmpB p p₀ la lb
  cmpB-⊞Ω hz lδ r p p₀ = refl
  cmpB-⊞Ω (hs δ) lδ r p p₀ = cmpB-⊞Ω δ lδ r p p₀
  cmpB-⊞Ω (hl f) (st , l) r p p₀ = cmpB-⊞Ω (f 0) (l 0) r p p₀
  cmpB-⊞Ω (hΩ tt g) (mo , l) (rs , rr) p p₀
    rewrite cmpF-self (z⊲ a) la | rs (z⊲ a) = cmpB-⊞Ω (g azero) (l azero (lg⊲ (z⊲ a) la)) rr p p₀

  module _ (δ : HB S₀) (lδ : LgB δ) (rδ : RL a la δ lδ) where
    module O = Rp a b la lb
    module N = Rp a (b ⊞ δ) la (Lg-⊞ b δ lb lδ)

    wk : ∀ {c} → c ⊲[ a ] b → c ⊲[ a ] b ⊞ δ
    wk p = ⊲ᴮ-tr p (⊞-fst b δ)

    wkE : O.Ev → N.Ev
    wkE e = N.ev (O.ec e) (wk (O.ep e)) (O.eδ e) (O.elδ e)

    wk-⊞Ω : ∀ H c p → N.rp (map wkE H) c (wk p) ≡ O.rp H c p
    wk-⊞Ω [] c p = refl
    wk-⊞Ω (e ∷ H) c p = cong₂ (λ r x → contrib (fix r) (O.eδ e) x) (cmpB-⊞Ω δ lδ rδ p (O.ep e)) (wk-⊞Ω H c p)
```

## §4 前提可满足

```agda
Ωz : HB S₀
Ωz = hΩ tt (λ _ → hz)

lΩz : LgB Ωz
lΩz = (λ lw e e′ pr → hself) , (λ x _ → tt)

rΩz : ∀ a la → RL a la Ωz lΩz
rΩz a la = (λ e → refl) , tt

-- A 进 HB S₀ 的嵌入, 单调数据沿路径递归
ιA : A → HB S₀
ιA azero = hz
ιA (asuc x) = hs (ιA x)
ιA (alim f) = hl (λ n → ιA (f n))

ιA-⊲ : ∀ {x x′ w} → x ⊲ x′ → ιA x ⊲[ w ] ιA x′
ιA-⊲ C.self = hself
ιA-⊲ (C.suc p) = hsuc (ιA-⊲ p)
ιA-⊲ (C.lim n p) = hlim n (ιA-⊲ p)

Lg-ιA : ∀ x → Lg x → LgB (ιA x)
Lg-ιA azero l = tt
Lg-ιA (asuc x) l = Lg-ιA x l
Lg-ιA (alim f) (st , l) = (λ n → ιA-⊲ (st n)) , (λ n → Lg-ιA (f n) (l n))

ΩA : HB S₀
ΩA = hΩ tt ιA

lΩA : LgB ΩA
lΩA = (λ lw e e′ pr → ιA-⊲ pr) , Lg-ιA

rΩA : ∀ a la → RL a la ΩA lΩA
rΩA a la = (λ e → refl) , tt

-- 实例: 外层界 0 接上 ΩA, 一切事件表的重放不变
inst : ∀ (a : A) (la : Lg a) H c p →
  Rp.rp {S₀} a (hz ⊞ ΩA) la (Lg-⊞ hz ΩA tt lΩA) (map (Grow.wkE a la hz tt ΩA lΩA (rΩA a la)) H) c
        (Grow.wk a la hz tt ΩA lΩA (rΩA a la) p)
  ≡ Rp.rp {S₀} a hz la tt H c p
inst a la H c p = Grow.wk-⊞Ω a la hz tt ΩA lΩA (rΩA a la) H c p
```

## §5 长高前后的两个事件世界: 种类与世界的对应, 界双向相同

外层界从 $b$ 长到 $b\boxplus\delta$ (`RL`). 两个事件世界 (`EvKS`, 内层世界族相同) 之间: 种类 $(c,p)\mapsto(c,\mathrm{wk}\,p)$, 坐标类型相同; 世界 $H\mapsto$ `map wkE H`; 界双向相同 (`bd→`, `bd←`, 由 `wk-⊞Ω`). 所以长高后的世界**忠实地含着**长高前的世界; 长高后新加的事件可以落在新坐标 (只在 $b\boxplus\delta$ 之下的坐标) 上.

```agda
module GrowKS (a : A) (la : Lg a) (b : HB S₀) (lb : LgB b)
              (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c))
              (δ : HB S₀) (lδ : LgB δ) (rδ : RL a la δ lδ) where
  module K₀ = EvKS {S₀} a b la lb v₀ lv₀
  module K₁ = EvKS {S₀} a (b ⊞ δ) la (Lg-⊞ b δ lb lδ) v₀ lv₀
  module G = Grow a la b lb

  km : K₀.Kᵉ → K₁.Kᵉ
  km κ = proj₁ κ , G.wk δ lδ rδ (proj₂ κ)

  wm : K₀.Hist → K₁.Hist
  wm = map (G.wkE δ lδ rδ)

  same-E : ∀ κ → K₁.Eᵉ (km κ) ≡ K₀.Eᵉ κ
  same-E κ = refl

  bd→ : ∀ κ x H → K₀.Bdᵉ κ x H → K₁.Bdᵉ (km κ) x (wm H)
  bd→ κ x H e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (sym (G.wk-⊞Ω δ lδ rδ H (proj₁ κ) (proj₂ κ))) e

  bd← : ∀ κ x H → K₁.Bdᵉ (km κ) x (wm H) → K₀.Bdᵉ κ x H
  bd← κ x H e = subst (λ t → x ⊲[ v₀ (proj₁ κ) ] t) (G.wk-⊞Ω δ lδ rδ H (proj₁ κ) (proj₂ κ)) e

  -- 世界变大与对应可交换: 加事件后再对应 = 对应后再加 (定义相等)
  wm-∷ : ∀ e H → wm (e ∷ H) ≡ G.wkE δ lδ rδ e ∷ wm H
  wm-∷ e H = refl
```
