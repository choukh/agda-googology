# LeanFb (四): 回灌计划, 无条件闭项, FGH

> 不含记号. 入口 [LeanFb](LeanFb.lagda.md), 接口 [LeanFbIf](LeanFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 闭项、证书、FGH 无模块参数.
>
> **回灌计划 `plan`** (接口 `Plan`):
>
> | 种类 | 回灌 | 级层 | 读回 | 一起升的成员 |
> |---|---|---|---|---|
> | 第 0 站的头 `νS 0`; 一切站里级为 `lz` 的新种类 | `feed0` | $0$ | `sum` | 一切级为 `lz` 的拷贝 (`slotUp 0`) |
> | 第 1 站的头 `νS 1`; 一切站里级为 `ls lz` 的新种类 | `feed1` | $1$ | `rdX newAK` (级 0 的结点读成 $\Omega$-结点) | 一切级为 `ls lz` 的拷贝 (`slotUp 1`) |
> | 第 $n\ge2$ 站的头 | `feedH n` | $1$ | `rdX` 进 `Lv (st n)`, 种类由 `find0` 找 | 只有自己 (`headUp n`, ℕ 点更新) |
> | 其余深种类 (级不是 `lz`, `ls lz`) | 有损 | — | — | — |
>
> 由计划得折叠参数 `fb = map₁ toFb ∘ plan`: 级层与读回取自 `LvRd`, 起点是累计输出在级层上的值 (同 `LeanTFb.fromKLv`), 升界是 `Up` 的 `rz` 加上读回的增量.
>
> **闭项** `TF`: 同 [LeanT](LeanT.lagda.md) §2 的写法 (基世界, 输入是 "当前状态的一步", 第 0 层前接 $1$, 求和), 换成 `T = SLs`, 最高层 `ΛF`, 底种类 `νS 0`, 参数 `fb`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanT using (FGH)
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbSlot
open import OCF.Lean.LeanFbRd
import OCF.Lean.LeanTFold as Fold
open Tree SLs
open FoldTy SLs ΛF
```

## §1 底种类与回灌计划

```agda
bkS : BotK
bkS = record
  { aK = νS 0 ; frE = λ e → e
  ; frE-lg = λ lw e → lgB⊲ e (proj₁ (lw 0)) (proj₂ (lw 0))
  ; frE-mono = λ _ _ _ p → ⊲ᴮ↑ (λ ()) p }

feed0 : ∀ {κ} → Σ (J (slotUp 0)) (λ i → κJ (slotUp 0) i ≡ κ) → Feed SLs ΛF κ
feed0 m = record { Q = S⊥ ; R = R0 ; U = slotUp 0 ; mem = m }

feed1 : ∀ {κ} → Σ (J (slotUp 1)) (λ i → κJ (slotUp 1) i ≡ κ) → Feed SLs ΛF κ
feed1 m = record { Q = step S⊥ ; R = RX newAK ; U = slotUp 1 ; mem = m }

feedH : ∀ n → AK0 (Lv (stL n)) → Feed SLs ΛF (νS n)
feedH n a = record { Q = Lv (stL n) ; R = RX a ; U = headUp n ; mem = tt , refl }

planK : ∀ m (κ : K (FS m)) → Feed SLs ΛF (m , κ) ⊎ ⊤
planK m (inj₁ κ) = [ (λ q → inj₁ (feed0 q)) , (λ _ → map₁ feed1 (memS 1 m (inj₁ κ))) ]′ (memS 0 m (inj₁ κ))
planK zero (inj₂ tt) = inj₁ (feed0 ((0 , inj₁ refl) , refl))
planK (suc zero) (inj₂ tt) = inj₁ (feed1 ((1 , inj₁ refl) , refl))
planK (suc (suc n)) (inj₂ tt) = map₁ (feedH (suc (suc n))) (find0 (stL (suc (suc n))))

plan : Plan SLs ΛF
plan (m , κ) = planK m κ
```

## §2 由计划得折叠参数

```agda
toFb : ∀ {κ} → Feed SLs ΛF κ → Fb
toFb F = record
  { ℓ = LvRd.ℓ (R F) ; ℓ⊲ = LvRd.ℓ⊲ (R F)
  ; d₀ = λ lW Y → yc (d Y) (tg ≤rf (LvRd.ℓ⊲ (R F)) lW)
  ; nx = λ {W} lW x → rz (U F) (LvRd.δ (R F) lW x) (proj₁ W)
  ; nx≤ = λ {W} lW x → rz≤ (U F) (LvRd.δ (R F) lW x) (proj₁ W)
  ; nxLg = λ lW x → rzLg (U F) (LvRd.δLg (R F) lW x) (proj₁ lW) }

fb : K SLs → Fb ⊎ ⊤
fb κ = map₁ toFb (plan κ)
```

## §3 闭项与 FGH

```agda
open Fold SLs bkS ΛF lΛF oneF fb

Act : ∀ {ly W} → Ig ly W
Act p lW′ _ Y = Stp Y

ΨF : D hz (w₀ L₀)
ΨF = n1 ⨾ yc (Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself Act n0 (st zeroD n0 n0)) (τ₀ (lw₀ L₀))

TF : HB S⊥
TF = sum hz ΨF

Lg-TF : LgB TF
Lg-TF = Lg-sum hz ΨF tt

fghF : ℕ → ℕ
fghF = FGH TF
```
