# `T⁺` 对输入单调 (五): ℕ-极限一步的展开与归结

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). `HtCrossInst.Hl`/`HlS` 在两种种类的折叠上的对应, 对一切合法的 $\mathrm{hl}\,f$ (各项可含两种种类的 $\Omega$-极限):
>
> - 实例是 $1\boxplus\mathrm{hl}\,f=\mathrm{hl}\,(n\mapsto 1\boxplus f(n))$ (定义相等), $\Omega=1⨾\mathrm{nl}\,(n\mapsto\text{层 }1\boxplus f(n)\text{ 的节点})$. 第 $n$ 个节点在第 0 层目标上上升 (`rk0`: 对变量 $n$ 不能计算, 用相等搬). 链的第 0 项是状态在层 $1\boxplus f(n)$ 上的差, 读数不低于最左一段 (`nest`).
> - **`hl-unfold`, `hl-strict`** (定理, 无前提): `T⁺ (hl f)` 不低于 (严格高于) 在第 $n$ 段的上下文、状态里再折叠一次 $\Omega_{1\boxplus f(n)}$ 的和 (`X`).
> - **`hl-reduce`** (条件定理): `Steps.s-hl` 在 $(f, n)$ 处归结为一条 `MonoHl n : T⁺ (f n) ≤ sum β X`. 与后继一步不同, 这里不能把跨实例与实例之内拆开: 第 $n$ 段的状态是在实例 $1\boxplus\mathrm{hl}\,f$ 里走过前 $n$ 个节点得到的, 它的类型属于这个实例 (`Tg` 里有到最高层的位置), 在实例 $1\boxplus f(n)$ 里没有同一个状态.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoHl where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (s≤; ≤l; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (module At; T⁺; top⁺; one; W₁)
open import OCF.Align.HtTowerFGrow using (nz≤; nzL; nz-Ωd; sum≥; module G)
open import OCF.Align.TpMonoHs using (b₀; lW₁)
```

## §1 展开

```agda
module Hl (f : ℕ → Ht) (lf : LgB (hl f)) where
  Λ′ : Ht
  Λ′ = top⁺ (hl f)

  module P = At Λ′ (Lg-⊞ (hs hz) (hl f) tt lf) (⊞-fst (hs hz) (hl f))

  Fi : ℕ → D Λ′ (azero , hz)
  Fi j = ni (sl j hself) (λ _ _ _ → n1)

  Rp : ℕ → D Λ′ W₁ × P.St W₁
  Rp = P.Rpt accᴸ Fi (z⊲ one , hself) lW₁ hself P.Act (n0 ⨾ nw (z⊲ one , hself) n1) (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))

  d : ℕ → D₀ W₁
  d j = P.yc (P.Run accᴸ (Fi j) (z⊲ one , hself) lW₁ hself P.Act (proj₁ (Rp j)) (proj₂ (Rp j))) (P.τ₀ lW₁)

  T⁺≡ : T⁺ (hl f) lf ≡ alim (pt b₀ d)
  T⁺≡ = refl

  rk0 : ∀ {k m} (x : P.Rk k hz m) → x ≡ P.rise
  rk0 (P.keep ())
  rk0 P.rise = refl

  module N (n : ℕ) where
    L : Ht
    L = top⁺ (f n)

    r : StH (azero , hz) L Λ′
    r = sl n hself

    hk : L ⊲[ W₁ ] Λ′
    hk = hlim n hself

    A² : P.Ig L W₁
    A² = P.Ai accᴸ (accK r) r (λ _ _ _ → n1) (z⊲ one , hself) hk hself P.Act (proj₁ (Rp n))

    β : A
    β = pt b₀ d n

    RK : P.Rk L hz W₁ → D₀ W₁
    RK x = P.RKi accᴸ (accK r) r (λ _ _ _ → n1) (z⊲ one , hself) lW₁ hself P.Act (proj₁ (Rp n)) (proj₂ (Rp n)) (P.τ₀ lW₁) x

    dn≡ : d n ≡ RK P.rise
    dn≡ = cong RK (rk0 _)

    Tk : P.Tg W₁ L W₁
    Tk = P.tg ≤rf hk lW₁

    -- 第 n 段的状态在层 L 上的差: 读数不低于最左一段
    nest : ∀ m (A₀ : P.Ig L W₁) (w : D L W₁) (Y : P.St W₁) b →
           sum b (P.yc (P.Run (accK r) (P.yc (P.d (P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Stp P.Y₀))) Tk) ≤rf lW₁ hk A₀ w Y) (P.τ₀ lW₁)) ≤ᴬ
           sum b (P.yc (P.Run (accK r) (P.yc (P.d (proj₂ (Rp m))) Tk) ≤rf lW₁ hk A₀ w Y) (P.τ₀ lW₁))
    nest zero A₀ w Y b = ≤-refl _
    nest (suc m) A₀ w Y b = ≤-trans (nest m A₀ w Y b) (sum≥ _ _)

    X : D₀ W₁
    X = P.yc (P.Run (accK r) (Ωd L {W₁}) ≤rf lW₁ hk A² (n0 ⨾ nw ≤rf n0) (P._⊕⟨_⟩_ (proj₂ (Rp n)) lW₁ P.zeroD)) (P.τ₀ lW₁)

    hl-unfold : sum β X ≤ᴬ T⁺ (hl f) lf
    hl-unfold = ≤l (suc n) (subst (λ y → sum β X ≤ᴬ sum β y) (sym dn≡)
                  (≤l 1 (≤-trans (≤l 1 (≤-refl _)) (nest n A² n0 (proj₂ (Rp n)) β))))
```

## §2 严格与归结

```agda
    module GG = G Λ′ (Lg-⊞ (hs hz) (hl f) tt lf) (⊞-fst (hs hz) (hl f))

    Rq = P.Rpt (accK r) (λ _ → Ωd L {W₁} ⨾ n0) ≤rf lW₁ hk A² (n0 ⨾ nw ≤rf n0) (P._⊕⟨_⟩_ (proj₂ (Rp n)) lW₁ P.zeroD) 1

    hl-strict : asuc (sum β X) ≤ᴬ T⁺ (hl f) lf
    hl-strict = ≤l (suc n) (subst (λ y → asuc (sum β X) ≤ᴬ sum β y) (sym dn≡)
                  (≤l 1 (≤-trans (≤l 2 (nz≤ (sum β X)
                            (GG.L3 (accK r) {x = Ωd L {W₁} ⨾ n0} ≤rf lW₁ hk A² (P.τ₀ lW₁) (GG.na (λ w Y → GG.nz-Step Y (P.τ₀ lW₁))) (nzL (nz-Ωd L))
                               (proj₁ Rq) (proj₂ Rq))))
                          (nest n A² n0 (proj₂ (Rp n)) β))))

    -- 跨实例与实例之内合在一起的一条
    MonoHl : Set
    MonoHl = T⁺ (f n) (proj₂ lf n) ≤ᴬ sum β X

    hl-reduce : MonoHl → asuc (T⁺ (f n) (proj₂ lf n)) ≤ᴬ T⁺ (hl f) lf
    hl-reduce m = ≤-trans (s≤ m) hl-strict
```
