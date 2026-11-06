# 底对 LH 递归, 否定一路 (二): 接口 `LHRecIf` 的盲区与边界

> 不含记号. 入口 [NegLHRec](NegLHRec.lagda.md). 只读导入构造一路的接口 [LHRecIf](LHRecIf.lagda.md) 与 [LHRecTy](LHRecTy.lagda.md) ("接口定稿 2026-11-06 08:06"), [CRwBase](CRwBase.lagda.md), 与否定一路的 [NegRecBPre](NegRecBPre.lagda.md), [NegLHRecPre](NegLHRecPre.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **接口.** 对每个层号 $k$, 世界的一层 `WL k` $=$ `Wd (step (Lv k))` $=$ (第 $k$ 层的世界 $u$, 第 $k$ 层的界 $B$), 序 `LeW k` $=$ `step (Lv k)` 的世界序 ($u\le u'$ 且 $B\lhd_{u'}B'$). 字段 `Adm`, `nxt`, `sh`, `adm-sh` (对一切坐标), `nx-up`, `lg-nx`, `adm↓`, `W₀`, `o₀`, `lW₀`. 没有坐标对的比较律.
>
> **结果.**
>
> 1. **辅助 (正面, 对一切层号).** `rfL`: 每个 `Lv k` 的世界序自反 (`CRwBase.KS` 没有这个字段, 对 `LH` 递归证出). `w₀L`, `lw₀L`: 每个 `Lv k` 有合法世界.
> 2. **盲 (`stayL`, `kripkeC`).** `stayL`: 可入恒真, 进入后世界不动, 回灌恒为 $0$, 是实例. 后果 **`stay-no-cover`**: 接口不要求进入的坐标落在新世界的界之下 (第 $0$ 层, 坐标 $2$, 新界 $1$). `kripkeC`: 下面第 3 条的 Kripke 实例取合法化 $c\mapsto 0$, 回灌 $B\boxplus 0=B$ 与坐标无关 (**`kripkeC-const`**, refl). 所以 "回灌依赖坐标", "进入的坐标被界住" 都不是接口的律.
> 3. **边界: 可入要对低层世界作 Kripke 式量化 (`naive-adm↓-fails`, `naive-adm↓-lz`, `Kr.inst`).** 把 `CRw.I₁` 的规则原样抬到第 $k$ 层, 可入写成 "$B\lhd_u e$ 且 $e$ 合法" (在**当前**低层世界 $u$ 里), 则在第 $1$ 层 (`ls lz`) **`adm↓` 不成立**: $((\mathrm{tt},0),1)\le((\mathrm{tt},1),1)$, 坐标 $\Omega$ 在后者可入, 在前者不可入 (`Top.not-top0`). 在第 $0$ 层同一规则满足 `adm↓` (`naive-adm↓-lz`, 第 $0$ 层的世界只有 `tt`). 正面: 可入写成 "存在更大的合法低层世界 $u'\ge u$, 使 $B\lhd_{u'}e$ 且 $e$ 合法", 进入后世界 $(u', e+1)$, 回灌 $B\boxplus\mathrm{leg}\,c$: 对任一合法化族 `leg` (每层一个, 输出合法) 是实例 (`Kr.inst`). **`kripke-covers`**: 它把进入的坐标界住.
> 4. **回灌必须合法化 (`fb-must-legalize`, `no-plain-sh`).** 对任一实例与任一层 $k$: 若进入后新界是 $e+1$ (`nxt` 的界是 `hs e`), 则在一切合法世界里, 对一切坐标 $c$, `sh k W c` 合法. 所以这样的实例里, 回灌不能是 $B\boxplus c$ (不合法化): 对一切 $k$ 都被反驳.
>
> **前提实例.** 2: `stayL`, `kripkeC` 是完整的实例. 3: 两个世界都合法 (`lg-Lo`, `lg-Lh′`), 坐标 $\Omega$ 合法; `Kr.inst` 的前提 `leg` 取 $c\mapsto0$ 即 `kripkeC`. 4: `nb-kripke`: 一切 `Kr.inst` 满足 "新界是 $e+1$", 所以 `kripkeC` 满足 `no-plain-sh` 的前提.
>
> **只否定什么.** 2 不否定接口, 只说律不约束: 回灌依赖坐标; 进入的坐标被界住; 世界真的移动. 3 只否定 "可入只读当前低层世界" 这条具体规则在第 $k\geq1$ 层是实例; **不否定**接口 (Kripke 式的规则是实例), 也不否定第 $0$ 层的 `I₁`. 4 只否定 "新界是 $e+1$ 且回灌不合法化"; 不否定别的 `nxt` 形状. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLHRecIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecIf
open import OCF.Lean.NegRecBPre using (Ωˢ; Lg-Ωˢ; one; module Top)
open import OCF.Lean.NegLHRecPre using (module Fb)
open LHRecIf
```

## §1 辅助: 世界序自反, 合法世界

```agda
rfL : ∀ k {w} → _≤w_ (Lv k) w w
rfL lz = tt
rfL (ls x) = rfL x , hself
rfL (ll f) = λ n → rfL (f n)
rfL (lΩ k g) (inj₁ _) = rfL k , hself
rfL (lΩ k g) (inj₂ c) = rfL (g c)

w₀L : (k : LH) → Wd (Lv k)
lw₀L : (k : LH) → LgW (Lv k) (w₀L k)
w₀L lz = tt
w₀L (ls x) = w₀L x , hz
w₀L (ll f) = λ n → w₀L (f n)
w₀L (lΩ k g) (inj₁ _) = w₀L k , hz
w₀L (lΩ k g) (inj₂ c) = w₀L (g c)
lw₀L lz = tt
lw₀L (ls x) = lw₀L x , tt
lw₀L (ll f) = λ n → lw₀L (f n)
lw₀L (lΩ k g) (inj₁ _) = lw₀L k , tt
lw₀L (lΩ k g) (inj₂ c) = lw₀L (g c)

rfW : ∀ k {W : WL k} → LeW k W W
rfW k = rfL k , hself
```

## §2 盲: 世界不动的实例

```agda
stayL : LHRecIf
stayL = record
  { Adm = λ _ _ _ → ⊤ ; nxt = λ k W e a → W ; sh = λ k W c → hz
  ; adm-sh = λ k c lW → tt ; nx-up = λ k a → rfW k ; lg-nx = λ k a l → l
  ; adm↓ = λ k q a′ → tt , q
  ; W₀ = λ k → w₀L k , hs hz ; o₀ = λ k → hself ; lW₀ = λ k → lw₀L k , tt }

stayL-stay : ∀ k W e a → nxt stayL k W e a ≡ W
stayL-stay k W e a = refl

two : Cd
two = hs (hs hz)

no21 : ¬ (two ⊲ hs hz)
no21 (hsuc ())

-- 进入坐标 2 后, 新世界的界仍是 1: 进入的坐标不被界住
stay-no-cover : ¬ (two ⊲[ proj₁ (nxt stayL lz (W₀ stayL lz) two tt) ] proj₂ (nxt stayL lz (W₀ stayL lz) two tt))
stay-no-cover = no21
```

## §3 边界: 可入只读当前低层世界, 在第 1 层不满足 `adm↓`

```agda
AdmN : ∀ k → WL k → HB (Lv k) → Set
AdmN k W e = (proj₂ W ⊲[ proj₁ W ] e) × LgB e

k₁ : LH
k₁ = ls lz

Lo Lh′ : WL k₁
Lo = (tt , hz) , one {step S⊥}
Lh′ = (tt , one {S⊥}) , one {step S⊥}

lg-Lo : LgWL k₁ Lo
lg-Lo = (tt , tt) , tt

lg-Lh′ : LgWL k₁ Lh′
lg-Lh′ = (tt , tt) , tt

Lo≤Lh′ : LeW k₁ Lo Lh′
Lo≤Lh′ = (tt , hsuc hself) , hself

admΩ : AdmN k₁ Lh′ (Ωˢ {S⊥})
admΩ = Top.in-top1 {S⊥} tt , Lg-Ωˢ {S⊥}

naive-adm↓-fails : ¬ (∀ {W W′ : WL k₁} → LeW k₁ W W′ → ∀ {e} → AdmN k₁ W′ e → AdmN k₁ W e)
naive-adm↓-fails all = Top.not-top0 {S⊥} tt (proj₁ (all {Lo} {Lh′} Lo≤Lh′ {Ωˢ {S⊥}} admΩ))

-- 第 0 层: 同一规则满足 adm↓
naive-adm↓-lz : ∀ {W W′ : WL lz} → LeW lz W W′ → ∀ {e} → AdmN lz W′ e → AdmN lz W e
naive-adm↓-lz (_ , q) (p , le) = ⊲ᴮ-tr q p , le
```

**Kripke 式的可入 (正面).** 对任一合法化族 `leg` (每层一个, 输出合法).

```agda
module Kr (leg : ∀ k → HB (Lv k) → HB (Lv k)) (Lg-leg : ∀ k c → LgB (leg k c)) where
  AdmK : ∀ k → WL k → HB (Lv k) → Set
  AdmK k W e = Σ (Wd (Lv k)) (λ u′ → _≤w_ (Lv k) (proj₁ W) u′ × LgW (Lv k) u′ × (proj₂ W ⊲[ u′ ] e) × LgB e)

  nxtK : ∀ k (W : WL k) e → AdmK k W e → WL k
  nxtK k W e a = proj₁ a , hs e

  shK : ∀ k → WL k → HB (Lv k) → HB (Lv k)
  shK k W c = proj₂ W ⊞ leg k c

  adm-shK : ∀ k {W} c → LgWL k W → AdmK k W (shK k W c)
  adm-shK k {W} c (lu , lB) = proj₁ W , rfL k , lu , ⊞-fst (proj₂ W) (leg k c) , Lg-⊞ (proj₂ W) (leg k c) lB (Lg-leg k c)

  nx-upK : ∀ k {W e} (a : AdmK k W e) → LeW k W (nxtK k W e a)
  nx-upK k (u′ , q , lu′ , p , le) = q , hsuc p

  lg-nxK : ∀ k {W e} (a : AdmK k W e) → LgWL k W → LgWL k (nxtK k W e a)
  lg-nxK k (u′ , q , lu′ , p , le) _ = lu′ , le

  adm↓K : ∀ k {W W′} → LeW k W W′ → ∀ {e} (a′ : AdmK k W′ e) →
          Σ (AdmK k W e) (λ a → LeW k (nxtK k W e a) (nxtK k W′ e a′))
  adm↓K k (q , b) (u′ , q′ , lu′ , p′ , le) =
    (u′ , ≤w-tr (Lv k) q q′ , lu′ , ⊲ᴮ-tr (⊲ᴮ↑ q′ b) p′ , le) , rfW k

  inst : LHRecIf
  inst = record
    { Adm = AdmK ; nxt = nxtK ; sh = shK ; adm-sh = adm-shK ; nx-up = nx-upK ; lg-nx = lg-nxK
    ; adm↓ = adm↓K ; W₀ = λ k → w₀L k , hs hz ; o₀ = λ k → hself ; lW₀ = λ k → lw₀L k , tt }

  -- 进入的坐标被新世界的界住
  kripke-covers : ∀ k W e (a : AdmK k W e) → e ⊲[ proj₁ (nxtK k W e a) ] proj₂ (nxtK k W e a)
  kripke-covers k W e a = hsuc hself

  nb-kripke : ∀ k W e a → proj₂ (nxt inst k W e a) ≡ hs e
  nb-kripke k W e a = refl

kripkeC : LHRecIf
kripkeC = Kr.inst (λ k c → hz) (λ k c → tt)

kripkeC-const : ∀ k W c → sh kripkeC k W c ≡ proj₂ W
kripkeC-const k W c = refl
```

## §4 回灌必须合法化

```agda
fb-must-legalize : ∀ (I : LHRecIf) k → (∀ W e a → proj₂ (nxt I k W e a) ≡ hs e) →
  ∀ {W} → LgWL k W → ∀ c → LgB (sh I k W c)
fb-must-legalize I k nb {W} lW c =
  subst LgB (nb W (sh I k W c) (adm-sh I k c lW)) (proj₂ (lg-nx I k (adm-sh I k c lW) lW))

no-plain-sh : ∀ (I : LHRecIf) k → (∀ W e a → proj₂ (nxt I k W e a) ≡ hs e) →
  ¬ (∀ W c → sh I k W c ≡ proj₂ W ⊞ c)
no-plain-sh I k nb eq =
  Fb.no-plain-fb {Lv k} (w₀L k)
    (subst LgB (eq (w₀L k , hz) (Fb.bad {Lv k} (w₀L k)))
       (fb-must-legalize I k nb {w₀L k , hz} (lw₀L k , tt) (Fb.bad {Lv k} (w₀L k))))

-- 前提实例
no-plain-sh-C : ∀ k → ¬ (∀ W c → sh kripkeC k W c ≡ proj₂ W ⊞ c)
no-plain-sh-C k = no-plain-sh kripkeC k (Kr.nb-kripke (λ k c → hz) (λ k c → tt) k)
```

## 结论 (按档)

- **[定理, 正面]** `rfL`, `w₀L`, `lw₀L`, `rfW` (对一切层号); `naive-adm↓-lz`; `Kr.inst` (对一切合法化族), `Kr.kripke-covers`, `Kr.nb-kripke`.
- **[定理, 盲]** `stayL`, `stayL-stay`, **`stay-no-cover`**; `kripkeC`, **`kripkeC-const`**.
- **[定理, 否定]** **`naive-adm↓-fails`** (第 1 层); **`fb-must-legalize`**, **`no-plain-sh`** (对一切实例与层号, 前提 "新界是 $e+1$"), 实例 `no-plain-sh-C`.
- **[判断]** 构造一路若照 `I₁` 写可入, 第 $k\geq1$ 层要 Kripke 式量化低层世界 (或别的满足 `adm↓` 的写法); 合法化族 `leg` 对一切层要对旧种类的坐标累加, 本篇没有写 (只用了平凡的 $c\mapsto0$, 它使回灌与坐标无关).
