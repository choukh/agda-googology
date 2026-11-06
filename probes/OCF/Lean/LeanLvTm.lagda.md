# LeanLv (三): 头 2 的级层同形, 回灌计划, 无条件闭项, FGH

> **不是主候选.** 主候选是 [LeanLvTmS](LeanLvTmS.lagda.md) 的 `TVs`; 本篇的 `TV` 沿 `Sim` 读, 过极限一支本身的结点 (包括 $\Omega_{\mathrm{Sg}\,1}$ 的主结点) 有损 (`LeanLvShape.x₂-lossy-Sim`; 否定一路 `NegLeanLvInst.rdΩ-top-lossy`). 留着不改: 否定一路对它编译过; `σ₂` 被 `LeanLvTmS.lvSims` 用.

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md), 接口 [LeanLvIf](LeanLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 闭项、证书、FGH 无模块参数.
>
> **级层.** `Sg m = up (1 ⊞ tws m)` 是最高层 `ΛF` 的第 $m$ 项 (对一切世界是字面第一位置, `hlim m hself`). 第 1 项 `Sg 1` 与第 2 站的层号 `st 2` 同形 (`σ₂`, 坐标映射是恒等, 对坐标 $c$ : `HB S⊥` 结构递归 `simC`): `Sg 1` 的 $\Omega$-结点是头 0 的旧种类 `inj₁ (νS 0)` (坐标 `HB S⊥`), `st 2 = lΩ lz g₂` 的坐标也是 `HB S⊥`; 第 $c$ 支两边都是 "$1+c$".
>
> **回灌计划 `planV`.** 与 [LeanFbTm](LeanFbTm.lagda.md) 的 `plan` 只差一行: 第 $n=2+m$ 站的头 `νS (2+m)` 的回灌 `feedLv m` 的级层是 `Sg 1` (不是 $1$), 读回是沿 `σ₂` 的级读回 `readS σ₂ (emb2 m)` ([LeanLvRd](LeanLvRd.lagda.md)): 读进 `Lv (st 2)`, 经嵌入 `emb2 m` ([LeanLvEmb](LeanLvEmb.lagda.md) §3) 放进头的坐标 `Lv (st (2+m))`; 一起升的成员只有头自己 (`headUp`). 不再要 `find0`, 对一切 $m$ 无条件. 其余种类 (头 0, 头 1, 级 `lz`, `ls lz` 的同级拷贝, 有损的深种类) 原样取 `LeanFbTm.planK`.
>
> **读法 [判断].** 对 $m=0$ (头 2), 级层 `Sg 1` 与 `st 2` 同形, 嵌入是恒等: 按接口头的定义是 "**自己的级**". 对 $m\ge1$ (头 $n\ge3$), 级层仍是 `Sg 1` (层号 `st 2`), 经嵌入读进 `Lv (st n)`: **不是**自己的级. 否定一路 `NegLeanLvBlind.no-sim` (引用, 复核由主审做): 在基世界里是 `ΛF` 第一位置的层与 `st (3+n)` 之间没有任何 `Sim` (对任意坐标映射); 而级层必须对一切世界是第一位置 (`LvRd.ℓ⊲`). 所以在现有的 `ΛF` 上, 头 $n\ge3$ 的级层只能取 `st n` 以外的层号, 本篇取 `st 2`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanT using (FGH)
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (bkS; planK; toFb)
open import OCF.Lean.LeanLvIf hiding (here; inS; inL; inΩ)
open import OCF.Lean.LeanLvEmb
import OCF.Lean.LeanLvRd as RdM
import OCF.Lean.LeanTFold as Fold
open RdM SLs using (readS; Lg-readS)
open Tree SLs
open FoldTy SLs ΛF
```

## §1 级层 `Sg 1` 与 `st 2` 的同形

```agda
Sg : ℕ → HB L₀
Sg m = up (hs hz ⊞ tws m)

Sg⊲ : ∀ m {w} → Sg m ⊲[ w ] ΛF
Sg⊲ m = hlim m hself

simC : (c : HB S⊥) → Sim SLs (up (hs hz ⊞ (hz ⊞ ιS 0 (up c)))) (ofHB (hs hz ⊞ ι lz (up c)))
simC hz = ss sz
simC (hs c) = ss (simC c)
simC (hl f) = sl (λ n → simC (f n))
simC (hΩ (() , _) g)

σ₂ : Sim SLs (Sg 1) (stL 2)
σ₂ = sΩ (λ c → c) simC
```

## §2 头 $2+m$ 的回灌

```agda
RLv : ∀ m → LvRd SLs ΛF (Lv (stL (suc (suc m))))
RLv m = record
  { ℓ = Sg 1 ; ℓ⊲ = Sg⊲ 1
  ; δ = λ lW x → readS σ₂ (emb2 m) lW hz x
  ; δLg = λ lW x → Lg-readS σ₂ (emb2 m) lW hz x tt
  ; δ-n1 = λ lW → refl }

lvSim : ∀ m → LvSim SLs ΛF (Lv (stL (suc (suc m))))
lvSim m = record { R = RLv m ; x = stL 2 ; σ = σ₂ ; em = emb2 m }

feedLv : ∀ m → Feed SLs ΛF (νS (suc (suc m)))
feedLv m = record { Q = Lv (stL (suc (suc m))) ; R = RLv m ; U = headUp (suc (suc m)) ; mem = tt , refl }

planKV : ∀ m (κ : K (FS m)) → Feed SLs ΛF (m , κ) ⊎ ⊤
planKV m (inj₁ κ) = planK m (inj₁ κ)
planKV zero (inj₂ tt) = planK zero (inj₂ tt)
planKV (suc zero) (inj₂ tt) = planK (suc zero) (inj₂ tt)
planKV (suc (suc m)) (inj₂ tt) = inj₁ (feedLv m)

planV : Plan SLs ΛF
planV (m , κ) = planKV m κ

fbV : K SLs → Fb ⊎ ⊤
fbV κ = map₁ toFb (planV κ)
```

## §3 闭项与 FGH

```agda
open Fold SLs bkS ΛF lΛF oneF fbV

ActV : ∀ {ly W} → Ig ly W
ActV p lW′ _ Y = Stp Y

ΨV : D hz (w₀ L₀)
ΨV = n1 ⨾ yc (Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself ActV n0 (st zeroD n0 n0)) (τ₀ (lw₀ L₀))

TV : HB S⊥
TV = sum hz ΨV

Lg-TV : LgB TV
Lg-TV = Lg-sum hz ΨV tt

fghV : ℕ → ℕ
fghV = FGH TV
```
