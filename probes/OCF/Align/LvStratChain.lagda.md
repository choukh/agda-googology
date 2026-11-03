# 分层的 $\approx$: 目标 $K$ 的证书, 链, 与到 `Family` 的桥 (底座)

> 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). §1 `Cert∀`: 与 [LevelKTower](LevelKTower.lagda.md) 同形的定理在新阶段上还成立. §2 `Chain.WithHE`: [LevelKChain](LevelKChain.lagda.md) 的搬运, 条件于 `he`. §3 `Bridge`: `Family` 的第一步 $\psi_0(\Omega_{\Omega_k})$ **恰好等价于** 目标 0 上那一族 (`T-from`, 与 `must`, `must-step` 两个方向), 这一族里节点在第 0 层上升. 这里没有证明这一族: 见 [LvStratNeg](LvStratNeg.lagda.md) §3, §4.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvStratChain where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; up; Ω; toLv; iter)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; sib; chM; asN; module PF)
open import OCF.Align.LvStratBase using (Stage; module Leaf; Fl)
open import OCF.Align.LvStratFin using (IsK)
open import OCF.Align.LvStratLvP using (module LvPs)
open import OCF.Align.LvStratTower using (St₀; Twr; tower; WorldK; Choice; W-ω; canon; module Next)
import OCF.Align.EBOTopStage as St
import OCF.Align.EBOTopRaw
open OCF.Align.EBOTopRaw using (module Must)
open import OCF.Align.EBOTopRaw using (rd)
```

## §1 目标 $K$, 一个定理

```agda
module AtK (S : Sib) (W₀ : WorldK 0 St₀) (ch : Choice) (K : ℕ) where
  Stᴷ : Stage
  Stᴷ = proj₁ (tower W₀ ch K)

  isK : IsK K Stᴷ
  isK = proj₁ (proj₂ (tower W₀ ch K))

  open LvPs S Stᴷ public
  open K-stage K isK public

Cert∀ : ∀ (S : Sib) W₀ (ch : Choice) K θ → AtK.LvP S W₀ ch K θ → AtK.WFᴬ S W₀ ch K (toLv (PF.ψⁿ S K (Ω θ)))
Cert∀ S W₀ ch K θ p = AtK.Cert S W₀ ch K θ p

Cert∀ₙ : ∀ (S : Sib) W₀ (ch : Choice) K n → AtK.WFᴬ S W₀ ch K (toLv (PF.ψⁿ S K (Ω (natL n))))
Cert∀ₙ S W₀ ch K n = AtK.Cert S W₀ ch K (natL n) (AtK.lvp-nat S W₀ ch K n)
```

## §2 目标 $K$ 的链

`he`: 判决在链点的层号上正确. 链点的第 $K$ 层以下的分支都在地板上, 所以 `he` 只问地板. 自然数之外问 `S`.

```agda
module Chain (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open LvPs S St
  open K-stage K isK

  y : ℕ → Ordᴸ (natL K)
  y ℕ.zero    = Ω (natL K)
  y (ℕ.suc m) = ψⁿ K (Ω (toLv (y m)))

  Kk : Lv
  Kk = limᴼ (natL K) toLv

  chk : ℕ → Ordᴸ (natL K)
  chk = iter (λ t → ψᵖ (chM Kk (inj₁ (inj₁ tt))) (up t (Ω (toLv t)))) (Ω (natL K))

  chM-K : chM Kk (inj₁ (inj₁ tt)) ≡ fin K refl
  chM-K rewrite asN-nat K = refl

  chk≡y : ∀ m → chk m ≡ y m
  chk≡y ℕ.zero    = refl
  chk≡y (ℕ.suc m) = trans (help chM-K (chk m)) (cong (λ t → ψⁿ K (Ω (toLv t))) (chk≡y m))
    where
    help : ∀ {M} → M ≡ fin K refl → ∀ t → ψᵖ M (up t (Ω (toLv t))) ≡ ψⁿ K (Ω (toLv t))
    help refl t = refl

  module WithHE (he : ∀ m → LvG (toLv (y m))) where
    good : ∀ m → GoodT (natL K) (y m) × Eq (natL K) (y m) (y m)
    lvp  : ∀ m → LvP (toLv (y m))

    good ℕ.zero =
      GΩ-K , Ω-self (natL K) (proj₁ (lvp-nat K)) (proj₁ (proj₂ (lvp-nat K)))
    good (ℕ.suc m) =
      let p = lvp m in
      Good-F (toLv (y m)) p , Eq-ψᴷ (Ω-self (toLv (y m)) (proj₁ p) (proj₁ (proj₂ p)))

    lvp m = lvp-cx (toLv (y m)) (lo-toLv bl-K (y m) (eq→tw bl-K (y m) (proj₂ (good m))))
              (cx-tree bl-K (proj₁ (good m)) (proj₂ (good m))) (he m)

    y-cert : ∀ m → WFᴬ (toLv (y m))
    y-cert m = wf bl-K (proj₁ (good m))
```

## §2′ 字面目标的链

$x_3$ 的节点在 $\Omega_1$ 层上升, 链的目标是 $\Omega_1$, 不是自然数. 模式走过 `up` 就是 `sib`: **每个节点都问 `S`** ([EBOTop](EBOTop.lagda.md) 的 `asked`). `ChainL`: 任何 `BL` 的好目标 $L$, 链上每一点好, 层号好, **条件于 `oks` 与 `he`**. 这两个前提就是这条链对 `S` 的全部要求. 链点的层号都是 `Lo` (`lo-y`), 所以由 `lo-adm`, `S` 只在地板的路径上被问到. 实例: $L=\Omega_1$ 在 [LvStratOmega](LvStratOmega.lagda.md) 的 `Stω` 上满足全部无条件的前提 (`lvp-Ω₁`, `bl-Ω₁`).

```agda
module ChainL (S : Sib) (St : Stage) (L : Lv) where
  open LvPs S St

  yL : ℕ → Ordᴸ L
  yL ℕ.zero    = Ω L
  yL (ℕ.suc m) = ψᵖ sib (Ω (toLv (yL m)))

  module WithHE (b : BL L) (ti : Ti L) (pL : LvP L)
                (oks : ∀ m → OK (toLv (yL m)) (sib {i = L}))
                (he : ∀ m → LvG (toLv (yL m))) where
    good : ∀ m → GoodT L (yL m) × Eq L (yL m) (yL m)
    lvp  : ∀ m → LvP (toLv (yL m))

    good ℕ.zero =
      Good-Ω L pL , Ω-self L (proj₁ pL) (proj₁ (proj₂ pL))
    good (ℕ.suc m) =
      let p = lvp m in
      Good-ψ sib (oks m) ti (Good-Ω L pL) (Good-Ω _ p) (Ω-self _ (proj₁ p) (proj₁ (proj₂ p))) ,
      ψ≃ sib sib (oks m) (oks m) (tgOf ti) (Ω-self _ (proj₁ p) (proj₁ (proj₂ p)))

    lo-y : ∀ m → Lo (toLv (yL m))
    lo-y m = lo-toLv b (yL m) (eq→tw b (yL m) (proj₂ (good m)))

    lvp m = lvp-cx (toLv (yL m)) (lo-y m) (cx-tree b (proj₁ (good m)) (proj₂ (good m))) (he m)

    y-cert : ∀ m → WFᴬ (toLv (yL m))
    y-cert m = wf b (proj₁ (good m))

    -- `S` 在链点的层号上只被问地板的路径
    only-floor : ∀ m r → AdmB (toLv (yL m)) r → Adm (toLv (yL m)) r
    only-floor m r d = lo-adm (toLv (yL m)) (lo-y m) r d
```

## §3 到 `Family` 的桥

`Must` ([EBOTopRaw](EBOTopRaw.lagda.md) §7) 说 `Family` 蕴含目标 $k$ 的链上每一点的 $\psi_0$ 输出 `HS` 且相邻步进. 反方向是 `T-from`, 只用 `hl`: 所以 $\psi_0(\Omega_{\Omega_k})$ 的 `HS` **等价于** 这一族. 对 $k=1$ 的 $L_{\ldots}$ 就是 `Family` 里 $\psi_0(\Omega_{\Omega_2})$ 的那一项. 这一族的每一项的目标都是 0: 第 $k$ 层的节点上升, 第 0 层的节点也上升.

```agda
module Bridge (S : Sib) where
  open Must S

  T-from : ∀ k → (∀ m → St.HS (rd (OCF.Align.EBOTopRaw.Raw.X S (toLv (chk k m))))) →
           (∀ m → rd (OCF.Align.EBOTopRaw.Raw.X S (toLv (chk k m))) St.⊑⁰ rd (OCF.Align.EBOTopRaw.Raw.X S (toLv (chk k (ℕ.suc m))))) →
           St.HS (rd (OCF.Align.EBOTopRaw.Raw.X S (Kk k)))
  T-from k h st = St.hl h st
```
