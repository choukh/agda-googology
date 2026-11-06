# 新塔 (二): 最终坍缩 = GenFold 的一般折叠, 在 `step T` 上 (决定性实验)

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md), 接口 [NewTwrIf](NewTwrIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 `collG : CollGenTy`.** 对一切带 `GenK T`, `LgDn T`, `FbLg` 的种类结构 $T$: 层 $h$ (在 `HB (step T)`, 合法) 前面接 $1$ 成 $\Lambda=1\boxplus h$, 用 [GenFoldRun](GenFoldRun.lagda.md) 把 $\Omega_\Lambda$ 的数据 (`Ωd`, $\Omega$-行对一切种类一条) 在基世界 `(w₀ G , 0)` 里折到第 0 层, 再 `sum` 成 `A`. 与 `HtTowerFClosed.At` (对 `Ht = HB (step S₀)` 专门写) 同一个式子, 层与世界换成一般的 `step T`. **合法**: `Lg-sum` 一次调用 (第 0 层的数据读成 `A` 由形状合法). **停机**: `GenFoldRun.Run` 对数据结构递归, 节点经 `AccY`, 检查器接受.
> - **§2 `T = KΛc` 的实例** (决定性实验): `GΛ = genSupℕ Kc genKc`, `LdΛ`, `flΛ` 由 [GenFoldInst](GenFoldInst.lagda.md) 对构造子递归的实例组装; `collΛ : CollK KΛc`. 层在 `HB (step KΛc)`: 对角之上一步, 不是 `Ht`.
> - **§3 前提实例** (`FbBd`, 接口 GenFold §8): `bdΛ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrColl where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ)
open import OCF.Align.GenFoldInst
import OCF.Align.GenFoldRun as GR
open import OCF.Align.NewTwrIf
```

## §1 一般坍缩

```agda
module At {T : KS} (G : GenK T) (Ld : LgDn T) (fl : FbLg G)
          (Λ : HB (step T)) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open Tree T
  open Om (topStepG (tpK G))
  open GR T G Ld fl Λ lΛ o
  open FoldTy T Λ using (Ig; St; st; Df)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  W₁ : Wd L₀
  W₁ = w₀ G , hz

  lW₁ : LgW L₀ W₁
  lW₁ = lw₀ G , tt

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ {W₁}) ≤rf lW₁ hself Act n0 Y₀

  ΨΩ : D hz W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ lW₁)

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

-- 接在第 1 层后面: 第 1 层字面地是第一位置
one⊞ : ∀ {T : KS} → HB (step T) → HB (step T)
one⊞ h = hs hz ⊞ h

collG : CollGenTy
collG {T} G Ld fl = record
  { col   = λ h lh → At.Tψ G Ld fl (one⊞ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)
  ; lgCol = λ h lh → At.Lg-Tψ G Ld fl (one⊞ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h) }
```

## §2 在 `KΛc` 上 (决定性实验)

```agda
GΛ : GenK KΛc
GΛ = genSupℕ Kc genKc

LdΛ : LgDn KΛc
LdΛ = ldSup ℕ Kc ldKc

flΛ : FbLg GΛ
flΛ = flSupℕ Kc genKc flKc

collΛ : CollK KΛc
collΛ = collG GΛ LdΛ flΛ
```

## §3 前提实例: A-回灌绑到种类上

```agda
bdΛ : FbBd GΛ
bdΛ = bdSupℕ Kc genKc bdKc
```
