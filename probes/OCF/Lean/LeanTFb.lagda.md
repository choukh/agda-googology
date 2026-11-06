# LeanT: 级回灌参数的两个实例

> 不含记号. 入口 [LeanT](LeanT.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞. 不在闭项 `TΛ′` 的切片里 (`TΛ′` 取 "一切有损").
>
> [LeanTFold](LeanTFold.lagda.md) 的折叠只有一个级回灌参数 `fb : K T → Fb ⊎ ⊤`. 这里把原来的两种用法写成它的实例:
>
> - **`GenFoldRun` 的 A-回灌** (`GenFoldIf.FBA` 加 `FbLgAt`): 级层 $0$, 起点 $z$ (自当前世界以来第 0 层的输出), 升界 $w\mapsto \mathrm{rsA}\,w\,(\mathrm{sum}(\mathrm{tpA}\,w, x))$ (`fromFBA`).
> - **`KindLvRun` 的按级回灌** (`KindLvIf.KLv`): 级层 $\ell$, 起点是累计输出在 $\ell$ 上的值, 升界 $w\mapsto\mathrm{rs}\,w\,(\mathrm{rd}(\mathrm{top}_\kappa w, x))$ (`fromKLv`). 原 `KLv` 的坐标合法用 `LgE`; 这里 `KS` 没有 `LgE` ([LeanTBase](LeanTBase.lagda.md) 头), 所以合法谓词 `LgK` 是记录自己的字段.
> - **`KindLvRun` 退回 `GenFoldRun`**: `kindLvFb lv fbA` 先查 `lv κ`, 没有级回灌就用 `fbA κ` (`KindLvRun.RKv` 的第二行); `lv` 恒为 `inj₂ tt` 时与 `genFoldFb fbA` 逐点定义相等 (`no-lv`).
>
> `κcF` 在两个实例上的展开与 `GenFoldRun.κcA`, `KindLvRun.κcL` 的式子逐项相同 (`A-zero`, `A-suc`, `L-zero`, `L-suc`, 都是 `refl`); 与原文件的对照是读代码的判断 (两边类型不同).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanTFb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
import OCF.Lean.LeanTFold as FoldM

module Inst (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open Tree T
  open FoldTy T Λ
```

## §1 A-回灌

```agda
  record FBA : Set where
    field
      tpA  : Wd T → HB S⊥
      rsA  : Wd T → HB S⊥ → Wd T
      rs≤  : ∀ {w v} → tpA w ⊲[ w₀ S⊥ ] v → _≤w_ T w (rsA w v)
      rsLg : ∀ {w v} → LgW T w → LgB v → LgW T (rsA w v)
      tpLg : ∀ {w} → LgW T w → LgB (tpA w)
  open FBA public

  fromFBA : FBA → Fb
  fromFBA F = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ ; d₀ = λ lW Y → z Y
    ; nx = λ {W} lW x → rsA F (proj₁ W) (sum (tpA F (proj₁ W)) x)
    ; nx≤ = λ lW x → rs≤ F (sum-fst _ x)
    ; nxLg = λ lW x → rsLg F (proj₁ lW) (Lg-sum _ x (tpLg F (proj₁ lW))) }

  genFoldFb : ((κ : K T) → FBA ⊎ ⊤) → K T → Fb ⊎ ⊤
  genFoldFb fbA κ = map₁ fromFBA (fbA κ)
```

## §2 按级回灌

```agda
  record KLv (κ : K T) : Set₁ where
    field
      ℓᴸ     : HB L₀
      ℓ⊲ᴸ    : ∀ {w} → ℓᴸ ⊲[ w ] Λ
      LgK    : E T κ → Set
      top-lg : ∀ {w} → LgW T w → LgK (top T κ w)
      rd     : ∀ {W} → LgW L₀ W → E T κ → D ℓᴸ W → E T κ
      rd-fst : ∀ {W} (lW : LgW L₀ W) b x → Pr T κ (proj₁ W) b (rd lW b x)
      rd-lg  : ∀ {W} (lW : LgW L₀ W) b x → LgK b → LgK (rd lW b x)
      rs     : Wd T → E T κ → Wd T
      rs≤    : ∀ {w v} → Pr T κ w (top T κ w) v → _≤w_ T w (rs w v)
      rsLg   : ∀ {w v} → LgW T w → LgK v → LgW T (rs w v)
  open KLv public

  fromKLv : ∀ {κ} → KLv κ → Fb
  fromKLv {κ} L = record
    { ℓ = ℓᴸ L ; ℓ⊲ = ℓ⊲ᴸ L ; d₀ = λ lW Y → yc (d Y) (tg ≤rf (ℓ⊲ᴸ L) lW)
    ; nx = λ {W} lW x → rs L (proj₁ W) (rd L lW (top T κ (proj₁ W)) x)
    ; nx≤ = λ lW x → rs≤ L (rd-fst L lW _ x)
    ; nxLg = λ lW x → rsLg L (proj₁ lW) (rd-lg L lW _ x (top-lg L (proj₁ lW))) }

  kindLvFb : ((κ : K T) → KLv κ ⊎ ⊤) → ((κ : K T) → FBA ⊎ ⊤) → K T → Fb ⊎ ⊤
  kindLvFb lv fbA κ = [ (λ L → inj₁ (fromKLv L)) , (λ _ → genFoldFb fbA κ) ]′ (lv κ)

  no-lv : ∀ fbA κ → kindLvFb (λ _ → inj₂ tt) fbA κ ≡ genFoldFb fbA κ
  no-lv fbA κ = refl
```

## §3 `κcF` 在两个实例上的展开

对任意 `fb` 打开折叠; `κcF` 的回灌记录是显式参数, 与 `fb` 无关.

```agda
  module Unfold (fb : K T → Fb ⊎ ⊤) where
    open FoldM T bk Λ lΛ one⊲ fb

    A-zero : ∀ {ly W₀ W} (ac : AccY ly) (F : FBA) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll : LW ly W)
             (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             wA (κcF ac (fromFBA F) u q₀ lW ll A₀ w Y zero) ≡ rsA F (proj₁ W) (sum (tpA F (proj₁ W)) (z Y))
    A-zero ac F u q₀ lW ll A₀ w Y = refl

    A-suc : ∀ {ly W₀ W} (ac : AccY ly) (F : FBA) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll : LW ly W)
            (A₀ : Ig ly W) (w : D ly W) (Y : St W) n →
            let c₀ = κcF ac (fromFBA F) u q₀ lW ll A₀ w Y n in
            wA (κcF ac (fromFBA F) u q₀ lW ll A₀ w Y (suc n))
              ≡ rsA F (wA c₀) (sum (tpA F (wA c₀)) (yc (κΔA ac u q₀ lW ll A₀ c₀) (τ₀ (lwA c₀ , proj₂ lW))))
    A-suc ac F u q₀ lW ll A₀ w Y n = refl

    L-zero : ∀ {ly W₀ W κ} (ac : AccY ly) (L : KLv κ) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll : LW ly W)
             (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
             wA (κcF ac (fromKLv L) u q₀ lW ll A₀ w Y zero)
               ≡ rs L (proj₁ W) (rd L lW (top T κ (proj₁ W)) (yc (d Y) (tg ≤rf (ℓ⊲ᴸ L) lW)))
    L-zero ac L u q₀ lW ll A₀ w Y = refl

    L-suc : ∀ {ly W₀ W κ} (ac : AccY ly) (L : KLv κ) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W) (ll : LW ly W)
            (A₀ : Ig ly W) (w : D ly W) (Y : St W) n →
            let c₀ = κcF ac (fromKLv L) u q₀ lW ll A₀ w Y n in
            wA (κcF ac (fromKLv L) u q₀ lW ll A₀ w Y (suc n))
              ≡ rs L (wA c₀) (rd L (lwA c₀ , proj₂ lW) (top T κ (wA c₀))
                   (yc (κΔA ac u q₀ lW ll A₀ c₀) (tg ≤rf (ℓ⊲ᴸ L) (lwA c₀ , proj₂ lW))))
    L-suc ac L u q₀ lW ll A₀ w Y n = refl
```

**行数 (参数化的代价; 切片脚本 `probes/Survey/scripts/leant/locslice_leant.py`).** 折叠里与级回灌有关的块: `Fb` 8, `κcF` 14, `RKa` 6 (两行), `ClA` 8, `κΔA` 4, 共 40; `GenFoldRun` 的 A-回灌对应: `FBA` 7, `FbLgAt` 3, `FbLg` 2, `κcA` 20, `RKa` 6, `ClA` 8, `κΔA` 4, 共 50. 两个实例 (`fromFBA`, `fromKLv`, 它们的记录, `genFoldFb`, `kindLvFb`) 在本篇, 共 38 行, 不进闭项的切片. 原来按级回灌要整份拷贝折叠 (`KindLvRun` 236 行代码).
