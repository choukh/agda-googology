# 对一般种类结构的折叠 (五): 求值, `EvSysK` 的实例, 第 1 站的决定性实验

> 不含记号. 入口 [GenFold](GenFold.lagda.md), 接口 [GenFoldIf](GenFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 `EvAt`**: 层 $L$ (在 `HB (step T)`, 合法, 第 1 层是一切世界里的第一位置) 上的数据, 用 `GenFoldRun.Run` 求到第 2 层 (目标 `tg ≤rf e lW`), 经 `rd₂` 读成 `Ht`. 与 `DnFoldEv.EvAt` 同一个式子, 层与世界换成一般的 `step T`, 读回换成 `rd₂`. **合法由读回的形状给出** (`lg-evAt`, 对一切数据).
> - **§2 `evSysG`: 对一切种类结构 $T$ (带 `GenK T`, `LgDn T`, `FbLg`) 一条, 给出 `EvSysK T`** (层的类型就是 `LayK T`, `refl`).
> - **§3 第 1 站 (`K₁ = Kc 1`) 的决定性实验**: `DK K₁` 就是接口的数据树 (一个闭包结点对 `step K₁` 的一切种类); `RunK₁` 是折叠在 `K₁` 上的实例; `evK₁ : EvSysK K₁`. 停机: 对数据结构递归 (`Run` 的定义被检查器接受); 合法: `lg-evAt`. 第 1 站的种类里 A-回灌有的与没有的各举一个 (`fb-old`, `fb-new`, `fb-rd`, `refl`).
> - **§4 两种种类 (`S₀`)**: `evS₀ : EvSysK S₀`, 层就是 `Ht` (`LayK S₀ ≡ Ht`, `refl`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldEv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; S₁)
open import OCF.Align.LvKtIf using (Kc)
open import OCF.Align.KcFoldIf using (LayK)
open import OCF.Align.DnFoldIf using (EvSys; EvSysK)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; accᴸ)
open import OCF.Align.GenFoldInst
import OCF.Align.GenFoldRun as GR
import OCF.Align.GenFoldRd as GD
```

## §1 在层 $L$ 上求值

```agda
module EvAt (T : KS) (G : GenK T) (Ld : LgDn T) (fl : FbLg G)
  (L : HB (step T)) (lL : LgB L) (o : ∀ {w} → hs hz ⊲[ w ] L) where
  open Tree T
  open GR T G Ld fl L lL o
  open GD T G Ld using (rd₂; Lg-rd₂)
  open FoldTy T L using (Ig; St; st; tg)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  out₂ : ∀ {W} → LgW L₀ W → hs (hs hz) ⊲[ W ] L → D L W → D (hs (hs hz)) W
  out₂ {W} lW e X = yc (Run {W = W} accᴸ X ≤rf lW hself Act n0 Y₀) (tg ≤rf e lW)

  evAt : ∀ {W} → LgW L₀ W → hs (hs hz) ⊲[ W ] L → D L W → Ht
  evAt lW e X = rd₂ lW hz (out₂ lW e X)

  lg-evAt : ∀ {W} (lW : LgW L₀ W) e X → LgB (evAt lW e X)
  lg-evAt lW e X = Lg-rd₂ lW hz (out₂ lW e X) tt
```

## §2 `EvSysK` 的实例, 对一切种类结构一条

```agda
OkG : (T : KS) → HB (step T) → Wd (step T) → Set
OkG T L W = Σ (LgB L) (λ _ → (∀ {w} → hs hz ⊲[ w ] L) × (hs (hs hz) ⊲[ W ] L))

evSysG : ∀ {T : KS} (G : GenK T) → LgDn T → FbLg G → EvSysK T
evSysG {T} G Ld fl =
  record
    { Lay = HB (step T) ; Wor = Wd (step T) ; LgWo = LgW (step T) ; Dat = DK T ; Ok = OkG T
    ; evH = λ {L} ok lW X → EvAt.evAt T G Ld fl L (proj₁ ok) (proj₁ (proj₂ ok)) lW (proj₂ (proj₂ ok)) X
    ; lgEv = λ {L} ok lW X → EvAt.lg-evAt T G Ld fl L (proj₁ ok) (proj₁ (proj₂ ok)) lW (proj₂ (proj₂ ok)) X }
  , refl
```

## §3 第 1 站的决定性实验 (`K₁ = Kc 1`)

```agda
G₁ : GenK K₁
G₁ = genKc 1

Ld₁ : LgDn K₁
Ld₁ = ldKc 1

fl₁ : FbLg G₁
fl₁ = flKc 1

-- 数据树: 接口的 DK, 层在 HB (step K₁), 世界在 Wd (step K₁)
D₁ᴷ : LayK K₁ → Wd (step K₁) → Set
D₁ᴷ = DK K₁

-- 折叠在 K₁ 上的实例 (对一切合法, 以第 1 层为第一位置的最高层 Λ)
module RunK₁ (Λ : HB (step K₁)) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) = GR K₁ G₁ Ld₁ fl₁ Λ lΛ o

evK₁ : EvSysK K₁
evK₁ = evSysG G₁ Ld₁ fl₁

-- K₁ 的三类种类: 旧站 (S₀) 的种类有 A-回灌; 读回分量里的种类没有; step K₁ 的新种类没有
fb-old : fbA G₁ (inj₁ tt , tt) ≡ inj₁ (liftL {S₀} fbS₀)
fb-old = refl

fb-rd : fbA G₁ (inj₂ (hs hz) , inj₁ tt) ≡ inj₂ tt
fb-rd = refl

fb-new : fbA (genStep G₁) (inj₂ tt) ≡ inj₂ tt
fb-new = refl
```

## §4 两种种类 (`S₀`)

```agda
evS₀ : EvSysK S₀
evS₀ = evSysG genS₀ ldS₀ flS₀

lay-S₀ : LayK S₀ ≡ Ht
lay-S₀ = refl
```
