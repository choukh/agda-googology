# 补四条正面判据, 否定一路 (四): 构造一路的界框架对 `LevP` 与 `LevD`

> 不含记号. 入口 [NegTL2](NegTL2.lagda.md). 对着接口 [TL2If](TL2If.lagda.md) ("接口定稿 2026-11-05 21:12 (首次编译通过)", 变更记录: 无) 写; 只读导入构造一路的 [TL2Raise](TL2Raise.lagda.md) (界框架 `BdF`, `levUp`), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **构造一路的界框架.** `TL2Raise.BdF T κ top topBd topMono`: 单成员, 读数 `top w` (世界 $w$ 的一个 $\kappa$-界), 世界序是 $T$ 自己的 `≤w`, 读数序是 $\kappa$ 的 `Pr`. `up→rich`: `RaiseUp` ⇒ 当前界之上的坐标都能作某个更大世界的界. `no-up-pred`: 一切界满足 $Q$, 某界之上有 $\neg Q$ 的坐标 ⇒ 无 `RaiseUp`. 构造一路说 `LevP Pz`/`LevP Pn` 应是它的实例, 留给本篇.
>
> **结果 (定理).**
>
> 1. **`pz-no-bdF`, `pn-no-bdF`.** `LevP Pz` (`LevP Pn`) 第 1 层的新种类, **对一切** `top`, `topBd`, `topMono`, 界框架上没有 `RaiseUp`. 前提可满足 (`pz-top`, `pn-top`: `top` 取世界的高度分量). 所以 "新种类在界框架上有 `RaiseUp`" 这一条 (不在接口里, 在构造一路的文件里) 排除 [NegTL2Ord](NegTL2Ord.lagda.md) 的 `blind-i`, `blind-iω` 的候选.
> 2. **`levD-up` (实例).** 重数为 2 的 `LevD` (第 1 层两个级-0 的新种类, `NegTL2Pre.two-at-0`) 的两个新种类在界框架上都有 `RaiseUp`, 与 `levUp` 同一个证明 (世界类型相同).
> 3. **`blind-final` (盲).** `Lev` 与 `LevD` 同时满足: 上一对的 `LvCrit`, `LvUpper`; 本对接口的全部四条 (`All4`, 框架非平凡); 构造一路的界框架 `RaiseUp` (第 1 层的每个新种类). 而第 1 层级为 $0$ 的种类, `Lev` 只有一个 (`one-at-0`), `LevD` 有两个不同的 (`two-at-0`). 这是 "现有翻译形状 `Lev` 与一个不同的形状同时满足全部判据".
>
> **只否定什么.** 只否定推断 "四条判据 (加界框架) 确定了定义": 至少种类的重数不定. **不否定**: 界框架排除 `LevP Pz`/`Pn` (本篇证明它确实排除, 对一切 `top`); 构造一路的任何定理. 本篇没有证明 `LevD` 与 `Lev` 的序数值或第一位置结构相同或不同 (判断: 两个拷贝共用世界的同一个界, 读法相同; 未写定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTL2Bd where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (NatH; evᴴ)
open import OCF.Align.NegKindLvLev using (lvK)
open import OCF.Align.TreeLangIf
open import OCF.Align.TreeLangLv using (LevR)
open import OCF.Align.TL2If
open import OCF.Align.TL2Raise using (module BdF; levUp)
open import OCF.Align.NegTL2Pre using (stepP; Pz; Pn; pz-bd; nat⊲; ⊲hz; stepD; LevD; RD; lvD; two-at-0; one-at-0)
open import OCF.Align.NegTL2Raise using (All4; all-Lev; all-D)
```

## §1 `LevP Pz`, `LevP Pn`: 对一切 `top`, 界框架上没有 `RaiseUp`

```agda
private
  TZ TN : KS
  TZ = stepP S₀ (Pz S₀)
  TN = stepP S₀ (Pn S₀)

  1≢z : ¬ (hs (hz {S₀}) ≡ hz)
  1≢z ()

pz-no-bdF : ∀ (top : Wd TZ → HB S₀) (tb : ∀ w → Bd TZ (inj₂ tt) (top w) w)
  (tm : ∀ {w w′} → _≤w_ TZ w w′ → Pr TZ (inj₂ tt) w′ (top w) (top w′)) →
  ¬ RaiseUp (BdF.bF TZ (inj₂ tt) top tb tm) (BdF.bO TZ (inj₂ tt) top tb tm)
pz-no-bdF top tb tm =
  BdF.no-up-pred TZ (inj₂ tt) top tb tm (λ x → x ≡ hz) (λ w → pz-bd (tb w)) w₀ (hs hz) pr 1≢z
  where
  w₀ : Wd TZ
  w₀ = azero , (hz , refl)
  pr : top w₀ ⊲[ azero ] hs hz
  pr = subst (λ x → x ⊲[ azero ] hs hz) (sym (pz-bd (tb w₀))) (hsuc hself)

pn-no-bdF : ∀ (top : Wd TN → HB S₀) (tb : ∀ w → Bd TN (inj₂ tt) (top w) w)
  (tm : ∀ {w w′} → _≤w_ TN w w′ → Pr TN (inj₂ tt) w′ (top w) (top w′)) →
  ¬ RaiseUp (BdF.bF TN (inj₂ tt) top tb tm) (BdF.bO TN (inj₂ tt) top tb tm)
pn-no-bdF top tb tm =
  BdF.no-up-pred TN (inj₂ tt) top tb tm NatH (λ w → nat⊲ (tb w) (proj₂ (proj₂ w))) w₀ (hl evᴴ) pr (λ n → n)
  where
  w₀ : Wd TN
  w₀ = azero , (hz , tt)
  pr : top w₀ ⊲[ azero ] hl evᴴ
  pr = subst (λ x → x ⊲[ azero ] hl evᴴ) (sym (⊲hz (tb w₀))) (z⊲ᴮ (hl evᴴ))

-- 前提可满足: top 取世界的高度分量
pz-top : Σ (Wd TZ → HB S₀) (λ top → (∀ w → Bd TZ (inj₂ tt) (top w) w) ×
  (∀ {w w′} → _≤w_ TZ w w′ → Pr TZ (inj₂ tt) w′ (top w) (top w′)))
pz-top = (λ w → proj₁ (proj₂ w)) , (λ w → hself) , (λ le → proj₂ le)

pn-top : Σ (Wd TN → HB S₀) (λ top → (∀ w → Bd TN (inj₂ tt) (top w) w) ×
  (∀ {w w′} → _≤w_ TN w w′ → Pr TN (inj₂ tt) w′ (top w) (top w′)))
pn-top = (λ w → proj₁ (proj₂ w)) , (λ w → hself) , (λ le → proj₂ le)
```

## §2 `LevD`: 两个新种类在界框架上都有 `RaiseUp`

```agda
levD-up : ∀ (T : KS) (b : Bool) →
  RaiseUp (BdF.bF (stepD T) (inj₂ b) proj₂ (λ w → hself) (λ le → proj₂ le))
          (BdF.bO (stepD T) (inj₂ b) proj₂ (λ w → hself) (λ le → proj₂ le))
levD-up T b = record
  { rsU = λ w _ v _ → proj₁ w , v
  ; setU = λ _ _ _ → refl
  ; keepU = λ _ _ nk → ⊥-elim (nk refl)
  ; growU = λ a → ≤w-rf T , a tt tt refl }
```

## §3 盲: `Lev` 与 `LevD` 同时满足全部判据, 重数不同

```agda
blind-final :
  (All4 (LevR {S₀}) × All4 (RD {S₀})) ×
  RaiseUp (BdF.bF (step S₀) (inj₂ tt) proj₂ (λ w → hself) (λ le → proj₂ le))
          (BdF.bO (step S₀) (inj₂ tt) proj₂ (λ w → hself) (λ le → proj₂ le)) ×
  (∀ b → RaiseUp (BdF.bF (stepD S₀) (inj₂ b) proj₂ (λ w → hself) (λ le → proj₂ le))
                 (BdF.bO (stepD S₀) (inj₂ b) proj₂ (λ w → hself) (λ le → proj₂ le))) ×
  (∀ (κ κ′ : K (Lev {S₀} (hs hz))) → lvK (hs hz) κ ≡ inj₂ hz → lvK (hs hz) κ′ ≡ inj₂ hz → κ ≡ κ′) ×
  Σ (K (LevD {S₀} (hs hz))) (λ κ → Σ (K (LevD {S₀} (hs hz))) (λ κ′ →
    (lvD (hs hz) κ ≡ inj₂ hz) × (lvD (hs hz) κ′ ≡ inj₂ hz) × ¬ (κ ≡ κ′)))
blind-final = (all-Lev , all-D) , levUp S₀ , levD-up S₀ , one-at-0 , two-at-0
```

## §4 结论 (按档)

- **[定理]** **`pz-no-bdF`**, **`pn-no-bdF`** (对一切 `top`); 前提实例 `pz-top`, `pn-top`.
- **[定理, 实例]** `levD-up`.
- **[定理, 盲]** **`blind-final`**.
- **[判断]** (1) 界框架把 "界够多" 写成了树侧的条款, 它确实排除 `LevP` 一类; 但它在构造一路的文件里, 不在接口里, 而且框架仍是对一个种类单独给的 (没有字段要求 "候选的每个新种类都配一个界框架"). (2) 重数的自由度 (`LevD`) 不被任何一条判据看见: 判据都是 "对每个种类" 或 "对每个框架" 的陈述, 多一个与已有种类同形的种类, 每条都照样成立 (本篇只对第 1 层写成定理). (3) 穷尽是判断.
