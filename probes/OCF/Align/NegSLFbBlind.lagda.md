# `SL` 上带证据的回灌, 否定一路 (三): 接口 `SLFbIf` 的盲区

> 不含记号. 入口 [NegSLFb](NegSLFb.lagda.md). 对着接口 [SLFbIf](SLFbIf.lagda.md) ("接口定稿 2026-11-05 20:06 (首次编译通过)"; 变更记录: 一条, 只改文字, 按本篇 `akConst` 更正 `AK` 的盲区说明) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **本篇说什么 (都是定理).** 接口的每个记录都有不看数据的实例:
>
> - **`AK` 被常数读法满足, 对一切种类结构, 一切种类** (`akConst`): `fr e = 0`, `fr-mono` 由 `A` 的第一位置自反给出. 接口文件头原来写的 "`AK` 被常数 `fr` 满足当且仅当 `Pr` 只在相等时成立 (一般不满足)" 与此不符; 构造一路已按本定理在接口的变更记录里更正 (只改文字).
> - **`KC` 被 `ad b a = b` 满足** (`kcTriv`, 对一切 `step S` 的新种类; 接口已说), 精确升界是配对 (`NegKindLvUpd.upd-step` 的形状).
> - **`HdFb` 被读回恒取起点, 级层为 $0$ 的实例满足** (`hdTriv`, 对一切站下标 `ix` 与一切 $\Lambda$): 头种类的 `KLv` 用 $\mathbb N$ 上的点更新 (`GenFoldInst.upd`), 读回 `rd b x = b` 不看数据 (`hd-rd-blind`), 级层 `ℓ = 0` (`hd-ℓ0`); 一切深种类有损 (`deep-lossy`). 所以 `HdFb` 只说 "每站头种类有一个精确升界", 不说回灌读了什么; 读回的内容要在构造文件里看.
> - **`RsSLᴾ` 被空证据类满足** (`rsSLᴾ-empty`), 证据类不含基世界时它什么也不说 (接口已提醒).
> - **`RsEv` 的强度由 $\Lambda^*$ 决定.** $\Lambda^*=0$ 时只有层号 `lz` 带证据, `RsEv tpL w* hz` 有实例 (`rsEv-hz`, `lz` 处的点更新是模式). 对 $\Lambda^*=\Lambda$, 第 $n$ 站都带证据 (`FabLFReGen.stage-fst`), 见 [NegSLFbBd](NegSLFbBd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFbBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; tpK)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.GenFoldInst using (topSupG; upd; upd-at; upd-R; upd-Q)
open import OCF.Align.KindLvIf using (KLv; LvFb; ℓ; rd)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv; FL; SL; νL; ofHB)
open import OCF.Align.FabLFReGen using (GL; topLv)
open import OCF.Align.RsOwnIf using (RsK; RsInv)
open import OCF.Align.NegRsOwnShape using (rsInv-empty)
open import OCF.Align.SLFbIf
```

## §1 `AK`: 常数读法

```agda
akConst : ∀ (Q : KS) (κ : K Q) → AK Q
akConst Q κ = record
  { κa = κ ; fr = λ _ → azero ; fr-lg = λ _ → tt ; fr-mono = λ _ _ _ _ → C.self }

akConst-blind : ∀ Q κ e → fr (akConst Q κ) e ≡ azero
akConst-blind Q κ e = refl
```

## §2 `KC`: 不加的 `ad`, 配对的升界

```agda
kcTriv : ∀ {S : KS} (tp : TopG S) → KC (step S) (topStepG tp) (inj₂ tt)
kcTriv {S} tp = record
  { ad = λ b a → b
  ; ad-fst = λ b a → hself
  ; ad-lg = λ lb la → lb
  ; rk = record
    { rs = λ w v → proj₁ w , v
    ; rs≤ = λ pre → ≤w-rf S , pre
    ; rsLg = λ lw lv → proj₁ lw , lv
    ; rs-top = refl } }

kcTriv-blind : ∀ {S : KS} (tp : TopG S) b a → ad (kcTriv tp) b a ≡ b
kcTriv-blind tp b a = refl
```

## §3 `HdFb`: 读回恒取起点, 级层为 $0$

站下标子结构 `SNᵢ ix` 的顶坐标: 每个分量 `FL (ix n) = step (Lv (ix n))` 用 `FabLFReGen.topLv`. 头种类 $(n,\mathrm{new})$ 的升界在 $\mathbb N$ 上点更新.

```agda
tpN : (ix : ℕ → LH) → TopG (SNᵢ ix)
tpN ix = topSupG ℕ (λ n → FL (ix n)) (λ n → topStepG (topLv (ix n)))

module HdTriv (ix : ℕ → LH) (Λ : HB (step (SNᵢ ix))) where
  T : KS
  T = SNᵢ ix

  P : ℕ → Set
  P m = Wd (FL (ix m))

  rsN : (n : ℕ) → Wd T → HB (Lv (ix n)) → Wd T
  rsN n w v = upd {P} w n (proj₁ (w n) , v)

  Ltriv : (n : ℕ) → KLv T (tpN ix) Λ (n , inj₂ tt)
  Ltriv n = record
    { ℓ = hz
    ; ℓ⊲ = z⊲ᴮ Λ
    ; rd = λ lW b x → b
    ; rd-fst = λ lW b x → hself
    ; rd-lg = λ lW b x lb → lb
    ; rs = rsN n
    ; rs≤ = λ {w} {v} pre → upd-R {P} (λ m a b → _≤w_ (FL (ix m)) a b) w n (proj₁ (w n) , v)
                              (λ m → ≤w-rf (FL (ix m))) (≤w-rf (Lv (ix n)) , pre)
    ; rsLg = λ {w} {v} lw lv → upd-Q {P} (λ m a → LgW (FL (ix m)) a) w n (proj₁ (w n) , v) lw (proj₁ (lw n) , lv)
    ; rs-top = λ {w} {v} → upd-at {P} w n (proj₁ (w n) , v) (λ y → proj₂ y ≡ v) refl }

  lvT : LvFb T (tpN ix) Λ
  lvT (n , inj₂ tt) = inj₁ (Ltriv n)
  lvT (n , inj₁ κ) = inj₂ tt

  hdTriv : HdFb ix (tpN ix) Λ lvT
  hdTriv n = Ltriv n , refl

  -- 盲: 读回不看数据, 级层是 0, 深种类有损
  hd-rd-blind : ∀ n {W} (lW : LgW (step T) W) b x → rd (Ltriv n) lW b x ≡ b
  hd-rd-blind n lW b x = refl

  hd-ℓ0 : ∀ n → ℓ (Ltriv n) ≡ hz
  hd-ℓ0 n = refl

  deep-lossy : ∀ n κ → lvT (n , inj₁ κ) ≡ inj₂ tt
  deep-lossy n κ = refl
```

## §4 `RsSLᴾ` 与空证据; `RsEv` 在 $\Lambda^*=0$ 处

```agda
tpL : TopG SL
tpL = tpK GL

rsSLᴾ-empty : RsSLᴾ (λ _ → ⊥) tpL
rsSLᴾ-empty k = rsInv-empty

-- lz 处的精确升界: 按模式点更新
rsLz : Wd SL → HB (Lv lz) → Wd SL
rsLz w v lz = proj₁ (w lz) , v
rsLz w v (ls x) = w (ls x)
rsLz w v (ll f) = w (ll f)
rsLz w v (lΩ k g) = w (lΩ k g)

rkLz : RsK SL tpL (νL lz)
rkLz = record { rs = rsLz ; rs≤ = le ; rsLg = lg ; rs-top = refl }
  where
  le : ∀ {w v} → Pr SL (νL lz) w (top tpL (νL lz) w) v → _≤w_ SL w (rsLz w v)
  le {w} pre lz = tt , pre
  le {w} pre (ls x) = ≤w-rf (FL (ls x))
  le {w} pre (ll f) = ≤w-rf (FL (ll f))
  le {w} pre (lΩ k g) = ≤w-rf (FL (lΩ k g))
  lg : ∀ {w v} → LgW SL w → LgE SL (νL lz) v → LgW SL (rsLz w v)
  lg lw lv lz = tt , lv
  lg lw lv (ls x) = lw (ls x)
  lg lw lv (ll f) = lw (ll f)
  lg lw lv (lΩ k g) = lw (lΩ k g)

rsEv-hz : ∀ (w* : Wd SL) → RsEv tpL w* hz
rsEv-hz w* .hz hself = rkLz
```

## §5 结论 (按档)

- **[定理, 盲]** **`akConst`**, `akConst-blind` (`AK` 被常数读法满足, 对一切 `Q`, κ; 更正接口文件头的一句判断); **`kcTriv`**, `kcTriv-blind`; **`hdTriv`** (对一切 `ix`, $\Lambda$), **`hd-rd-blind`**, `hd-ℓ0`, `deep-lossy`; **`rsSLᴾ-empty`**; `rkLz`, **`rsEv-hz`**.
- **只说明什么.** 接口的记录都可被不读数据的东西满足; 所以 "回灌读了什么", "深种类是否有回灌", "级层是哪一层" 只能在构造文件里查 (见 [NegSLFbInst](NegSLFbInst.lagda.md), 若已写). 本篇不否定接口, 不否定任何路线.
