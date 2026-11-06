# `T⁺` 对输入单调 (三): 后继一步的展开与归结

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). `HtCrossInst.Hs`/`HsS` (单种类主线) 在两种种类的折叠上的对应, **对一切合法输入 $h$** (含两种种类的 $\Omega$-极限):
>
> - **`hs-unfold`, `hs-strict`** (定理, 无前提): `T⁺ (hs h)` 的折叠实例是 $\Lambda'=1\boxplus(h+1)=(1\boxplus h)+1$, $\Omega_{\Lambda'}=1⨾(\text{层 }L=1\boxplus h\text{ 的节点})$. 节点在第 0 层目标上上升 (`rkT` 在这里可算: `cmpB` 的第一个位置是 `hself`), 链的第 0 项是状态在层 $L$ 上的差 $0⨾\omega\cdot(\Omega_L⨾0)$, 于是 `T⁺ (hs h)` 不低于在那个上下文、状态里再折叠一次 $\Omega_L$ (`X`), 第二格非零, 所以严格.
> - **`hs-reduce`** (条件定理): `Steps.s-hs` 在 $h$ 处归结为两条:
>   - `ChangeHs h`: 同一次折叠 (同一个世界、上下文、状态) 在实例 $L$ 里 (`X′`) 不高于在实例 $L+1$ 里 (`X`). 跨实例, 同一个世界.
>   - `MonoStepHs h`: 实例 $L$ 之内, 空状态、基 $1$ 的折叠不高于大状态、基 $b_0$ 的折叠. 一个实例之内.
>
> 两条前提都是值的不等式, 对一切 $h$ 写出类型. 前提的实例与第一个障碍见 [TpMono](TpMono.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoHs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (s≤; ≤l; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (module At; T⁺; top⁺; one; W₁)
open import OCF.Align.HtTowerFGrow using (nz≤; nzL; nz-Ωd; module G)
```

## §1 展开

```agda
b₀ : A
b₀ = sum {W₁} one (nl (λ _ → n1 ⨾ n0))

lW₁ : LgW₂ W₁
lW₁ = tt , tt

module Hs (h : Ht) (lh : LgB h) where
  L : Ht
  L = top⁺ h

  -- 实例 L + 1 (就是 T⁺ (hs h) 的实例) 与实例 L (T⁺ h 的实例)
  module P = At (top⁺ (hs h)) (Lg-⊞ (hs hz) (hs h) tt lh) (⊞-fst (hs hz) (hs h))
  module Q = At (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)

  -- 节点 (层 L+1, 坐标层 L) 的坐标动作
  A² : P.Ig L W₁
  A² = P.Ai accᴸ (accK {(azero , hz)} (ss hself)) (ss hself) (λ _ _ _ → n1) (z⊲ one , hself) (hsuc hself) hself P.Act
            (n0 ⨾ nw (z⊲ one , hself) n1)

  Y₂ᴾ : P.St W₁
  Y₂ᴾ = P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀)) lW₁ P.zeroD

  -- 实例 L+1 里, 链的第 0 项的第 0 格
  X : D₀ W₁
  X = P.yc (P.Run (accK {(azero , hz)} (ss hself)) (Ωd L {W₁}) ≤rf lW₁ (hsuc hself) A² (n0 ⨾ nw ≤rf n0) Y₂ᴾ) (P.τ₀ lW₁)

  hs-unfold : sum b₀ X ≤ᴬ T⁺ (hs h) lh
  hs-unfold = ≤l 1 (≤l 1 (≤-refl _))
```

## §2 严格: 第二格非零

```agda
  module GG = G (top⁺ (hs h)) (Lg-⊞ (hs hz) (hs h) tt lh) (⊞-fst (hs hz) (hs h))

  Rq = P.Rpt (accK {(azero , hz)} (ss hself)) (λ _ → Ωd L {W₁} ⨾ n0) ≤rf lW₁ (hsuc hself) A² (n0 ⨾ nw ≤rf n0) Y₂ᴾ 1

  hs-strict : asuc (sum b₀ X) ≤ᴬ T⁺ (hs h) lh
  hs-strict = ≤l 1 (≤l 2 (nz≤ (sum b₀ X)
    (GG.L3 (accK {(azero , hz)} (ss hself)) {x = Ωd L {W₁} ⨾ n0} ≤rf lW₁ (hsuc hself) A² (P.τ₀ lW₁)
       (GG.na (λ w Y → GG.nz-Step Y (P.τ₀ lW₁))) (nzL (nz-Ωd L)) (proj₁ Rq) (proj₂ Rq))))
```

## §3 归结

```agda
  Y₂ᑫ : Q.St W₁
  Y₂ᑫ = Q._⊕⟨_⟩_ (Q._⊕⟨_⟩_ Q.Y₀ lW₁ (Q.Stp Q.Y₀)) lW₁ Q.zeroD

  -- 实例 L 里的同一次折叠
  X′ : D₀ W₁
  X′ = Q.yc (Q.Run accᴸ (Ωd L {W₁}) ≤rf lW₁ hself Q.Act (n0 ⨾ nw ≤rf n0) Y₂ᑫ) (Q.τ₀ lW₁)

  -- 跨实例 (同一个世界, 同一棵树, 同一个上下文与状态)
  ChangeHs : Set
  ChangeHs = sum b₀ X′ ≤ᴬ sum b₀ X

  -- 实例 L 之内: 输入世界 (0,0)→(1,0), 基 1→b₀, 上下文与状态各多一段
  MonoStepHs : Set
  MonoStepHs = T⁺ h lh ≤ᴬ sum b₀ X′

  hs-reduce : ChangeHs → MonoStepHs → asuc (T⁺ h lh) ≤ᴬ T⁺ (hs h) lh
  hs-reduce c m = ≤-trans (s≤ (≤-trans m c)) hs-strict
```
