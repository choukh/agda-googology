# LeanLv (三′): 主候选闭项 `TVs` (头 $n\ge2$ 沿 `Sim⁺` 读回)

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md), 接口 [LeanLvIf](LeanLvIf.lagda.md) §6. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 闭项、证书、FGH 无模块参数.
>
> 计划 `planS` 的前三行与 [LeanFbTm](LeanFbTm.lagda.md) 的 `planK` 逐字相同 (头 0, 头 1, 级 `lz`/`ls lz` 的同级拷贝, 其余深种类有损), 只是不经 `planK` (那样会把头 $n\ge2$ 的旧回灌 `feedH`/`find0` 带进切片). 与 [LeanLvTm](LeanLvTm.lagda.md) 的 `TV` 只差读回: 头 $2+m$ 的读回是 [LeanLvRdS](LeanLvRdS.lagda.md) 的 `readS σ₂⁺ (emb2 m)`. `σ₂⁺ : Sim⁺ SLs (Sg 1) (st 2)` 与 `σ₂` 同形, 另在 $\Omega$-结点的坐标 $c$ 处带后继种类的嵌入 `supE (inj₂ (hs c))`: `st 2 = lΩ lz g₂` 的分量 `inj₂ (hs c)` 是 `Lv (g₂ (hs c))`, 而 `g₂ (hs c)` 定义相等于 `ls (g₂ c)` (第 $c$ 支 "$1+c$" 的后继), 它的新种类以 `HB (Lv (g₂ c))` 为坐标, 正是过第 $c$ 支本身的结点的分支所读的类型 (否定一路 `NegLeanLvPre.succK-co` 的种类). 内层 (`1 + c`, $c$ : `HB S⊥`) 的 $\mathbb N$-极限不带后继种类 (`inj₂ tt`: 那里 $g\,(n+1)$ 不是 $g\,n$ 的后继).
>
> `LvSim` 的 `σ` 字段要 `Sim`, 取 [LeanLvTm](LeanLvTm.lagda.md) 的 `σ₂` (同一个层与层号; `σ₂⁺` 去掉后继种类就是它, 判断: 逐构造子对照).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvTmS where

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
open import OCF.Lean.LeanFbTm using (bkS; feed0; feed1; toFb)
open import OCF.Lean.LeanFbSlot using (memS)
open import OCF.Lean.LeanLvIf hiding (here; inS; inL; inΩ)
open import OCF.Lean.LeanLvEmb
open import OCF.Lean.LeanLvTm using (σ₂)
import OCF.Lean.LeanLvRdS as RdM
import OCF.Lean.LeanTFold as Fold
open RdM SLs using (readS; Lg-readS)
open Tree SLs
open FoldTy SLs ΛF
```

## §1 带后继种类的同形

级层 `Sg m` 与 [LeanLvTm](LeanLvTm.lagda.md) 的同名定义逐字相同 (在这里重写两行, 免得定义级切片经 `LeanLvTm` 的模块应用把 `TV` 的读回带进 `TVs` 的切片).

```agda
Sg : ℕ → HB L₀
Sg m = up (hs hz ⊞ tws m)

Sg⊲ : ∀ m {w} → Sg m ⊲[ w ] ΛF
Sg⊲ m = hlim m hself

simC⁺ : (c : HB S⊥) → Sim⁺ SLs (up (hs hz ⊞ (hz ⊞ ιS 0 (up c)))) (ofHB (hs hz ⊞ ι lz (up c)))
simC⁺ hz = ss⁺ sz⁺
simC⁺ (hs c) = ss⁺ (simC⁺ c)
simC⁺ (hl f) = sl⁺ (λ n → simC⁺ (f n)) (λ n → inj₂ tt)
simC⁺ (hΩ (() , _) g)

σ₂⁺ : Sim⁺ SLs (Sg 1) (stL 2)
σ₂⁺ = sΩ⁺ (λ c → c) simC⁺ (λ c → inj₁ (supE (inj₂ (hs c))))
```

## §2 头 $2+m$ 的回灌, 计划

```agda
RLs : ∀ m → LvRd SLs ΛF (Lv (stL (suc (suc m))))
RLs m = record
  { ℓ = Sg 1 ; ℓ⊲ = Sg⊲ 1
  ; δ = λ lW x → readS σ₂⁺ (emb2 m) lW hz x
  ; δLg = λ lW x → Lg-readS σ₂⁺ (emb2 m) lW hz x tt
  ; δ-n1 = λ lW → refl }

lvSims : ∀ m → LvSim SLs ΛF (Lv (stL (suc (suc m))))
lvSims m = record { R = RLs m ; x = stL 2 ; σ = σ₂ ; em = emb2 m }

feedLs : ∀ m → Feed SLs ΛF (νS (suc (suc m)))
feedLs m = record { Q = Lv (stL (suc (suc m))) ; R = RLs m ; U = headUp (suc (suc m)) ; mem = tt , refl }

planKs : ∀ m (κ : K (FS m)) → Feed SLs ΛF (m , κ) ⊎ ⊤
planKs m (inj₁ κ) = [ (λ q → inj₁ (feed0 q)) , (λ _ → map₁ feed1 (memS 1 m (inj₁ κ))) ]′ (memS 0 m (inj₁ κ))
planKs zero (inj₂ tt) = inj₁ (feed0 ((0 , inj₁ refl) , refl))
planKs (suc zero) (inj₂ tt) = inj₁ (feed1 ((1 , inj₁ refl) , refl))
planKs (suc (suc m)) (inj₂ tt) = inj₁ (feedLs m)

planS : Plan SLs ΛF
planS (m , κ) = planKs m κ

fbS : K SLs → Fb ⊎ ⊤
fbS κ = map₁ toFb (planS κ)
```

## §3 闭项与 FGH

```agda
open Fold SLs bkS ΛF lΛF oneF fbS

ActS : ∀ {ly W} → Ig ly W
ActS p lW′ _ Y = Stp Y

ΨVs : D hz (w₀ L₀)
ΨVs = n1 ⨾ yc (Run accᴸ (Ωd ΛF) ≤rf (lw₀ L₀) hself ActS n0 (st zeroD n0 n0)) (τ₀ (lw₀ L₀))

TVs : HB S⊥
TVs = sum hz ΨVs

Lg-TVs : LgB TVs
Lg-TVs = Lg-sum hz ΨVs tt

fghVs : ℕ → ℕ
fghVs = FGH TVs
```
