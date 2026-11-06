# 读回包 (五): 第 ω+1 级折叠读 ω 层的槽 (接口实例与形状定理)

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md) §4–§6. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> - `RaiseI` (在 [LvRdWorld](LvRdWorld.lagda.md)), **`foldΩ1 : FoldΩ1 RaiseI`**, **`shapeΩ1 : ShapeΩ1 RaiseI`**: 接口的三个记录都有实例, 无前提.
> - **`ωslot-s`**: `kω` 的槽在链的第 $n+1$ 步接上第 $n+1$ 级级顶的读回 (由 `at`). **`fin-zero`**: 有限码的槽在链上不动 (由 `off`).
> - **`reads₀`, `fold-reads`**: 第 $\omega+1$ 级折叠在 `V∞` 里遇到新种类的结点 $\mathrm{h\Omega}\,\kappa_{new}\,g$ 时, 是一条世界链上的 ℕ-极限, 链从 `V∞` 起, 第 0 项的分支是 $g$ 作用在 `kω` 的槽上, 而这个槽是 $0\boxplus\mathrm{hl}(N\mapsto V_{N+1}(\mathrm{k}\omega))$: **ω 层的槽被读回**.
> - **`lv1`, `lv2`** (对具体级数的计算): $V_1$, $V_2$ 的 `kω` 槽的第 2 格最外是第 1, 第 2 级新种类的结点 (同 `LvFbFold.lv1`, `lv2`, 换成本路的读回包). 这是有限的计算, 不是对一切 $n$ 的定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (Wd₂; nl)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.LvRdIf using (Gω; Gω1; Pc; kω; kfin; Wld; FoldΩ1; ShapeΩ1)
open import OCF.Align.LvRdWorld using (raise; at; off; v₀; lv₀; RaiseI)
open import OCF.Align.LvRdFold
```

## §1 接口实例

```agda
foldΩ1 : FoldΩ1 RaiseI
foldΩ1 = record
  { fold = FΩ.fold ; inc = incΩ ; lg-inc = lg-incΩ ; chain = FΩ.chain
  ; ch-z = λ v g → refl ; ch-s = FΩ.ch-s ; fold-Ω = FΩ.fold-Ω ; ch-lg = FΩ.ch-lg lg-incΩ }

shapeΩ1 : ShapeΩ1 RaiseI
shapeΩ1 = record
  { rt = rt ; V = V ; V-z = lv₀ ; V-s = λ n → refl ; V∞ = V∞ ; slot∞ = at v₀ kω slotLim }
```

## §2 ω 层的槽

```agda
ωslot-s : ∀ n → V (suc n) kω ≡ V n kω ⊞ ιω n
ωslot-s n = at (V n) kω (ιω n)

kω≢kfin : ∀ m → ¬ (kω ≡ kfin m)
kω≢kfin m ()

fin-zero : ∀ n m → V n (kfin m) ≡ hz
fin-zero zero m = refl
fin-zero (suc n) m = trans (off (V n) kω (ιω n) (kfin m) (kω≢kfin m)) (fin-zero n m)

-- 第 ω+1 级折叠的链从 V∞ 起, 第 0 项读 kω 的槽, 它是有限级回灌的 ℕ-极限
reads₀ : ∀ (g : HB Gω → HB Gω1) → FΩ.chain V∞ g zero kω ≡ hz ⊞ hl (λ N → V (suc N) kω)
reads₀ g = at v₀ kω slotLim

fold-reads : ∀ (g : HB Gω → HB Gω1) W →
  FΩ.fold V∞ (hΩ (inj₂ tt) g) W ≡ nl (λ k → FΩ.fold (FΩ.chain V∞ g k) (g (FΩ.chain V∞ g k kω)) W)
fold-reads g W = refl
```

## §3 计算: 槽里出现的级

`lvOf x`: `HB Gω` 的最外结点若是第 $j\ge1$ 个分量的新种类 (`inj₂ tt`), 记作 `NewAt j`.

```agda
cellsOf : ∀ {S} → HB S → ℕ → HB S
cellsOf (hl f) = f
cellsOf _ = λ _ → hz

NewAt : ℕ → HB Gω → Set
NewAt k (hΩ (suc j , inj₂ tt) _) = suc j ≡ k
NewAt k (hΩ (suc j , inj₁ _) _) = ⊥
NewAt k (hΩ (zero , _) _) = ⊥
NewAt k hz = ⊥
NewAt k (hs _) = ⊥
NewAt k (hl _) = ⊥

lv1 : NewAt 1 (cellsOf (V 1 kω) 2)
lv1 = refl

lv2 : NewAt 2 (cellsOf (V 2 kω) 2)
lv2 = refl

-- 第 ω+1 级级顶的读回里, 沿格 (1, j, 3) 是 ω 层槽里第 j 级的新种类结点, 种类原样读回
rd1 : NewAt 1 (cellsOf (cellsOf (cellsOf (idxΩ (Ωtop Gω)) 1) 1) 3)
rd1 = refl

rd2 : NewAt 2 (cellsOf (cellsOf (cellsOf (idxΩ (Ωtop Gω)) 1) 2) 3)
rd2 = refl

-- 比较器有分辨力: 同一格不是第 1 级
rd2≢1 : ¬ NewAt 1 (cellsOf (cellsOf (cellsOf (idxΩ (Ωtop Gω)) 1) 2) 3)
rd2≢1 ()
```
