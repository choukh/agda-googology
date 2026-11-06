# LamIso (三): 每站的头按自己的级读回, 闭项 `TI`, FGH

> 不含记号. 入口 [LamIso](LamIso.lagda.md), 接口 [LamIsoIf](LamIsoIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 闭项、证书、FGH 无模块参数.
>
> **读回.** 第 $n$ 站的头 (一切 $n\ge2$) 的级层是 `L n` ([LamIsoL](LamIsoL.lagda.md)), 读回沿 `L n` 与 `st n` 的忠实同形 (忘成 `Sim⁺`, `toS`) 读进 `Lv (st n)` 本身 ([LeanLvRdS](LeanLvRdS.lagda.md) 的 `readS`, 嵌入 `idE`): 层号就是头的坐标的层号, 嵌入是恒等, 对一切 $n$ (对照否定一路 `NegLeanLvBlind.no-own-sim`: 在 `ΛF` 上 $n\ge3$ 不可能). 一起升的成员只有头自己 (`headUp`). 头 0, 头 1 与级 `lz`, `ls lz` 的同级拷贝同 [LeanLvTmS](LeanLvTmS.lagda.md) (级层 $0$, $1$ 也是 `L 0`, `L 1`), 只是最高层换成 $\Lambda'$; 其余深种类有损.
>
> **闭项** `TI`: 同 `TVs` 的写法, 折叠取 `T = SLs`, 最高层 $\Lambda'$, 底种类 `νS 0`, 参数 `fbI`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoTm where

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
open import OCF.Lean.LeanFbSt using (FS; SLs; νS; headUp) renaming (st to stL)
open import OCF.Lean.LeanFbSlot using (slotUp; memS)
open import OCF.Lean.LeanFbRd using (AK0; newAK; rdX; Lg-rdX)
open import OCF.Lean.LeanLvIf using (Emb; Sim; sz; ss; sl; sΩ; Sim⁺; sz⁺; ss⁺; sl⁺; sΩ⁺; LvSim; cv)
open import OCF.Lean.LeanLvEmb using (idE)
open import OCF.Lean.LamIsoIf using (Prt; pz; ps; pl; pΩ; OwnRd)
open import OCF.Lean.LamIsoL using (L; L⊲; prtL; Λ′; lΛ′; one′)
import OCF.Lean.LeanLvRdS as RdM
import OCF.Lean.LeanTFold as Fold
open RdM SLs using (readS; Lg-readS)
open Tree SLs
open FoldTy SLs Λ′
```

## §1 忠实同形忘成同形

```agda
module _ {T : KS} where
  toS : ∀ {a x} → Prt T a x → Sim⁺ T a x
  toS pz = sz⁺
  toS (ps σ) = ss⁺ (toS σ)
  toS (pl σ sk) = sl⁺ (λ n → toS (σ n)) sk
  toS (pΩ Em σ sk) = sΩ⁺ (cv Em) (λ e → toS (σ e)) sk

  toSim : ∀ {a x} → Prt T a x → Sim T a x
  toSim pz = sz
  toSim (ps σ) = ss (toSim σ)
  toSim (pl σ sk) = sl (λ n → toSim (σ n))
  toSim (pΩ Em σ sk) = sΩ (cv Em) (λ e → toSim (σ e))
```

## §2 读回, 回灌, 计划

底种类 `bkS` 与 [LeanFbTm](LeanFbTm.lagda.md) 的同名定义逐字相同 (在这里重写四行, 免得定义级切片经 `LeanFbTm` 根上的模块应用把旧计划带进来).

```agda
bkS : BotK
bkS = record
  { aK = νS 0 ; frE = λ e → e
  ; frE-lg = λ lw e → lgB⊲ e (proj₁ (lw 0)) (proj₂ (lw 0))
  ; frE-mono = λ _ _ _ p → ⊲ᴮ↑ (λ ()) p }

R0′ : LvRd SLs Λ′ S⊥
R0′ = record { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ′ ; δ = λ lW x → sum hz x ; δLg = λ lW x → Lg-sum hz x tt ; δ-n1 = λ lW → refl }

RX′ : ∀ {X} → AK0 X → LvRd SLs Λ′ X
RX′ a = record { ℓ = hs hz ; ℓ⊲ = one′ ; δ = λ lW x → rdX a lW hz x ; δLg = λ lW x → Lg-rdX a lW hz x tt ; δ-n1 = λ lW → refl }

Rown : ∀ n → LvRd SLs Λ′ (Lv (stL n))
Rown n = record
  { ℓ = L n ; ℓ⊲ = L⊲ n
  ; δ = λ lW x → readS (toS (prtL n)) idE lW hz x
  ; δLg = λ lW x → Lg-readS (toS (prtL n)) idE lW hz x tt
  ; δ-n1 = λ lW → refl }

own : ∀ n → OwnRd Λ′ n
own n = record { R = Rown n ; π = prtL n }

lvSimI : ∀ n → LvSim SLs Λ′ (Lv (stL n))
lvSimI n = record { R = Rown n ; x = stL n ; σ = toSim (prtL n) ; em = idE }

feed0′ : ∀ {κ} → Σ (J (slotUp 0)) (λ i → κJ (slotUp 0) i ≡ κ) → Feed SLs Λ′ κ
feed0′ m = record { Q = S⊥ ; R = R0′ ; U = slotUp 0 ; mem = m }

feed1′ : ∀ {κ} → Σ (J (slotUp 1)) (λ i → κJ (slotUp 1) i ≡ κ) → Feed SLs Λ′ κ
feed1′ m = record { Q = step S⊥ ; R = RX′ newAK ; U = slotUp 1 ; mem = m }

feedOwn : ∀ n → Feed SLs Λ′ (νS n)
feedOwn n = record { Q = Lv (stL n) ; R = Rown n ; U = headUp n ; mem = tt , refl }

planKI : ∀ m (κ : K (FS m)) → Feed SLs Λ′ (m , κ) ⊎ ⊤
planKI m (inj₁ κ) = [ (λ q → inj₁ (feed0′ q)) , (λ _ → map₁ feed1′ (memS 1 m (inj₁ κ))) ]′ (memS 0 m (inj₁ κ))
planKI zero (inj₂ tt) = inj₁ (feed0′ ((0 , inj₁ refl) , refl))
planKI (suc zero) (inj₂ tt) = inj₁ (feed1′ ((1 , inj₁ refl) , refl))
planKI (suc (suc m)) (inj₂ tt) = inj₁ (feedOwn (suc (suc m)))

planI : Plan SLs Λ′
planI (m , κ) = planKI m κ

toFbI : ∀ {κ} → Feed SLs Λ′ κ → Fb
toFbI F = record
  { ℓ = LvRd.ℓ (R F) ; ℓ⊲ = LvRd.ℓ⊲ (R F)
  ; d₀ = λ lW Y → yc (d Y) (tg ≤rf (LvRd.ℓ⊲ (R F)) lW)
  ; nx = λ {W} lW x → rz (U F) (LvRd.δ (R F) lW x) (proj₁ W)
  ; nx≤ = λ {W} lW x → rz≤ (U F) (LvRd.δ (R F) lW x) (proj₁ W)
  ; nxLg = λ lW x → rzLg (U F) (LvRd.δLg (R F) lW x) (proj₁ lW) }

fbI : K SLs → Fb ⊎ ⊤
fbI κ = map₁ toFbI (planI κ)
```

## §3 闭项与 FGH

```agda
open Fold SLs bkS Λ′ lΛ′ one′ fbI

ActI : ∀ {ly W} → Ig ly W
ActI p lW′ _ Y = Stp Y

ΨI : D hz (w₀ L₀)
ΨI = n1 ⨾ yc (Run accᴸ (Ωd Λ′) ≤rf (lw₀ L₀) hself ActI n0 (st zeroD n0 n0)) (τ₀ (lw₀ L₀))

TI : HB S⊥
TI = sum hz ΨI

Lg-TI : LgB TI
Lg-TI = Lg-sum hz ΨI tt

fghI : ℕ → ℕ
fghI = FGH TI
```
