# 路径记在折叠输出上, 否定一路 (三): 路径是数据; 自选终点的路径等于裸下标; 链内有公共上界, 链间没有

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路要把折叠的输出改成 "带路径的高度". 任务里的两个问题: (a) 路径若用 $\Sigma$ 存证据, 会不会出现同一高度不同路径的拷贝; (b) 回灌时路径能否被下一层用作公共上界, 还是退化成裸下标.
>
> **结果.**
>
> 1. **`paths-not-prop`, `copies` (定理).** 第一位置不是命题: 合法的 $t_0=\lim(0,0,\dots)$ 里 $0\lhd t_0$ 有两条不同的路径 (经第 0 项与经第 1 项). 所以 $\Sigma\,d.\,d\lhd B$ 里有同一高度的两个不同元素 (`copies`). 用 $\Sigma$ 存路径的输出类型带拷贝; 读路径的运算可以分开它们.
> 2. **`exact-tag` (定理, 对一切层号与种类).** 两个都精确的决定 (Fab4LOm 的 `Exact`) 标签相同 (留/同层/在上). 所以只要决定精确, 从哪条路径算出来不影响标签; 拷贝只可能落在载荷 (读回函数) 上. 实例: Fab4LOm 的 `exact₂`.
> 3. **`own→⊥` (定理).** 若决定要求种类的坐标带一条到**自选**合法界的路径 (界可以随坐标取), 精确的决定仍不存在: 每个坐标都有到自己的路径 (`hself`), 所以这种路径不带信息, 回到 [NegPathOutCmp](NegPathOutCmp.lagda.md) 的 `no-exact-c₁`. 只有与目标**共享**的界才有用; 而 $c_1$ 与 $t_0$ 没有合法的共享界 (`shared-empty-c₁`, 由 `no-join-lim`).
> 4. **`chain-common` (定理, 构造).** [Fab3Typed](Fab3Typed.lagda.md) 的链: 第 $n$ 个界 $B_n=b\boxplus d_n$ 是一切更后的界 $B_{k+n}$ 的第一位置, 目标在 $b$ 之下的坐标也在 $B_{k+n}$ 之下. 链内的路径有公共上界.
> 5. **`cross-chain-nojoin` (定理).** 两条链的起始界若是 $\lim\mathrm{ev}$ 与 $\lim\mathrm{od}$, 它们的任何链坐标 $\lim\mathrm{ev}\boxplus d$, $\lim\mathrm{od}\boxplus d'$ 都没有合法的字面公共上界 (任一合法世界). 链间的路径不能合成公共上界.
>
> **前提实例.** 1: $t_0$ 合法 (`NegPathOutCmp.Lg-t₀`). 2: `exact₂` (Fab4LOm). 3: 前提是一个决定族与它的精确性, 被否定的就是它们合起来; 决定族本身可满足 (例如一律同层, `constD`). 4: 任一 `T`, 世界, 界, 分支. 5: 任一合法世界 (例如 `S⊥` 的 `tt`).
>
> **只否定什么.** 只否定: (a) "$\Sigma$ 存路径的输出不带拷贝"; (b) "坐标带到自选界的路径就能精确决定"; (c) "不同起始界的链的路径可合成公共上界". **不否定**: 路径的终点由折叠统一给出且与目标共享 (链内, `chain-common` 是构造); 把路径只当证据用、不让输出值依赖它 (2 说明精确决定的标签与路径无关); 商掉路径 (本系统无商, 未讨论). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutPath where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupIf using (Dc; keep; same; above)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; no-joinᴮ)
open import OCF.Align.Fab3Typed using (module Fold)
open import OCF.Align.Fab4LOm
  using (_⊑ᴸ_; _⊏ᴸ_; ⊑self; ⊑suc; ⊑ᴸ-tr; anti; Exact; X₁; X₂; κ₂; dec₂; exact₂; κ; t₀; t₁)
  renaming (irr to irrᴸ)
open import OCF.Align.NegPathOutCmp using (c₁; u₁; v₁; Lg-c₁; Lg-t₀; no-exact-c₁; no-join-lim; s≢z)
```

## §1 路径不是命题

```agda
p₀ p₁ : hz ⊲[ tt ] t₀
p₀ = hlim 0 hself
p₁ = hlim 1 hself

idx : ∀ {d} → d ⊲[ tt ] t₀ → ℕ
idx hself = 0
idx (hlim n _) = n

0≢1 : ¬ (0 ≡ 1)
0≢1 ()

paths-not-prop : ¬ (∀ (p q : hz ⊲[ tt ] t₀) → p ≡ q)
paths-not-prop h = 0≢1 (cong idx (h p₀ p₁))

PO : Set
PO = Σ (HB S⊥) (λ d → d ⊲[ tt ] t₀)

copies : (proj₁ {B = λ d → d ⊲[ tt ] t₀} (hz , p₀) ≡ proj₁ {B = λ d → d ⊲[ tt ] t₀} (hz , p₁)) ×
         ¬ (_≡_ {A = PO} (hz , p₀) (hz , p₁))
copies = refl , (λ e → 0≢1 (cong (λ (z : PO) → idx (proj₂ z)) e))
```

## §2 精确的决定, 标签与路径无关

```agda
tag : ∀ {X t} {k : K (Lv X)} → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X t k → ℕ
tag (keep _ _) = 0
tag (same _) = 1
tag (above _ _ _ _) = 2

-- 留与在上不能同时精确: 层号与目标互为子层号, 于是相等, 再与严格矛盾
private
  ka : ∀ {a t} → ls a ⊑ᴸ t → ls t ⊑ᴸ a → ⊥
  ka {a} {t} p q = irrᴸ t (subst (λ z → ls z ⊑ᴸ t) e p)
    where
    e : a ≡ t
    e = anti t a (⊑ᴸ-tr (⊑suc ⊑self) p) (⊑ᴸ-tr (⊑suc ⊑self) q)

exact-tag : ∀ {X t} {k : K (Lv X)} (d d′ : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X t k) → Exact k d → Exact k d′ → tag d ≡ tag d′
exact-tag (keep _ _) (keep _ _) _ _ = refl
exact-tag (same _) (same _) _ _ = refl
exact-tag (above _ _ _ _) (above _ _ _ _) _ _ = refl
exact-tag {t = t} (keep _ _) (same _) lt e = ⊥-elim (irrᴸ t (subst (λ z → z ⊏ᴸ t) e lt))
exact-tag {t = t} (same _) (keep _ _) e lt = ⊥-elim (irrᴸ t (subst (λ z → z ⊏ᴸ t) e lt))
exact-tag {t = t} (keep _ _) (above _ _ _ _) lt (ei , q) = ⊥-elim (ka lt (subst (λ z → ls t ⊑ᴸ z) ei q))
exact-tag {t = t} (above _ _ _ _) (keep _ _) (ei , q) lt = ⊥-elim (ka lt (subst (λ z → ls t ⊑ᴸ z) ei q))
exact-tag {t = t} (same _) (above _ _ _ _) e (ei , q) =
  ⊥-elim (irrᴸ t (subst (λ z → ls t ⊑ᴸ z) (trans ei e) q))
exact-tag {t = t} (above _ _ _ _) (same _) (ei , q) e =
  ⊥-elim (irrᴸ t (subst (λ z → ls t ⊑ᴸ z) (trans ei e) q))

-- 实例: X₂ 上的精确决定 (Fab4LOm)
exact-tag-inst : ∀ c → tag (dec₂ c) ≡ 1
exact-tag-inst c = exact-tag (dec₂ c) (dec₂ c) (exact₂ c) (exact₂ c)
```

## §3 自选终点的路径等于裸下标

决定族 `o` 对每个坐标 $c$ 与每条到合法界 $B$ 的路径给出决定. 取 $B=c$, 路径 `hself`, 就是裸下标上的决定; $c_1$ 处精确的决定不存在.

```agda
OwnDec : Set
OwnDec = ∀ (c B : HB S⊥) → c ⊲[ tt ] B → LgB B → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ t₁ (κ c)

own→⊥ : (o : OwnDec) → ¬ (∀ c B p l → Exact (κ c) (o c B p l))
own→⊥ o ex = no-exact-c₁ (o c₁ c₁ hself Lg-c₁) (ex c₁ c₁ hself Lg-c₁)

-- 决定族本身可满足 (一律同层; 不精确)
constD : OwnDec
constD c B p l = same (λ _ → hz)

-- 与目标共享的合法界: c₁ 与 t₀ 没有
shared-empty-c₁ : ¬ Σ (HB S⊥) (λ L → LgB L × (c₁ ⊲[ tt ] L) × (t₀ ⊲[ tt ] L))
shared-empty-c₁ = no-join-lim u₁ v₁ (λ _ → tt) (λ _ → tt) s≢z
```

## §4 链内: 后来的界盖住先前的界与目标

```agda
module ChainCommon (T : KS) where
  open Fold T using (chain; L)

  module _ (w : Wd T) (b : HB T) (k : Wd L → HB T → HB T) where
    B : ℕ → HB T
    B n = b ⊞ chain w b k n

    B-step : ∀ {v} n → B n ⊲[ v ] B (suc n)
    B-step n = ⊞-⊲ b (⊞-fst (chain w b k n) _)

    B-later : ∀ {v} n j → B n ⊲[ v ] B (j + n)
    B-later n zero = hself
    B-later n (suc j) = ⊲ᴮ-tr (B-later n j) (B-step (j + n))

    chain-common : ∀ {v c} → c ⊲[ v ] b → ∀ n j → (c ⊲[ v ] B (j + n)) × (B n ⊲[ v ] B (j + n))
    chain-common p n j = ⊲ᴮ-tr p (⊞-fst b _) , B-later n j
```

## §5 链间: 起始界没有公共上界, 链坐标也没有

```agda
cross-chain-nojoin : ∀ {S : KS} {w} → LgW S w → ∀ (d d′ : HB S) →
  ¬ Σ (HB S) (λ L → LgB L × (hl evᴴ ⊞ d ⊲[ w ] L) × (hl odᴴ ⊞ d′ ⊲[ w ] L))
cross-chain-nojoin {S} lw d d′ (L , l , p , q) =
  no-joinᴮ lw (L , l , ⊲ᴮ-tr (⊞-fst (hl evᴴ) d) p , ⊲ᴮ-tr (⊞-fst (hl odᴴ) d′) q)

cross-inst : ∀ (d d′ : HB S⊥) →
  ¬ Σ (HB S⊥) (λ L → LgB L × (hl evᴴ ⊞ d ⊲[ tt ] L) × (hl odᴴ ⊞ d′ ⊲[ tt ] L))
cross-inst = cross-chain-nojoin {S⊥} {tt} tt
```

## 结论 (按档)

- **[定理]** `p₀`, `p₁`, `idx`, **`paths-not-prop`**, **`copies`**; `tag`, **`exact-tag`** (对一切层号), `exact-tag-inst`; `OwnDec`, **`own→⊥`**, `constD`, `shared-empty-c₁`; `ChainCommon.B-step`, `B-later`, **`chain-common`**; **`cross-chain-nojoin`**, `cross-inst`.
- **[判断]** "构造一路的输出路径的终点若由链统一给出, 链内可用作公共上界" 依据 4, 要对实例查; "下一层用到的两条路径来自不同起始界时退化" 依据 5, 是否发生取决于实例.
