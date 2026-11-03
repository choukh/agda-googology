# 证书与阶段无关: 目标 $K$ 的链 (对 `EBOTop` 的 `must`)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). [EBOTopRaw](EBOTopRaw.lagda.md) 的 `must` 说: `Family` 逼出目标 $k$ 的链 $y_0=\Omega_k$, $y_{m+1}=\psi_k(\Omega_{y_m})$ 上每一点的层号的输出 `HS`, 对一切 $k$. 这里的 `y-cert`, `y-step`: 第 $K$ 阶段, 只要 `S` 在这条链的层号的 $\Omega$ 节点上正确 (`he`), 链上每一点好, 自相似, 层号好, 相邻步进. `chk≡y` 说这就是 `Must.chk` 的同一个表达式. **它给的是层号的证书 `WFᴬ`, 不是 $\psi_0$ 的输出的 `HS`**: 第 $K\ge1$ 阶段目标 0 不是观测 (`¬Zt₀`). `he` 对自然数层号之外要问 `S`, 见 [LevelKNeg](LevelKNeg.lagda.md) §7.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKChain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; up; Ω; toLv; iter)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; chM; asN)
open import OCF.Align.LevelKBase using (Stage; module Leaf)
open import OCF.Align.LevelKFin using (IsK)
open import OCF.Align.LevelKLvP using (module LvPs)

module Chain (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open LvPs S St
  open K-stage K isK

  y : ℕ → Ordᴸ (natL K)
  y zero    = Ω (natL K)
  y (suc m) = ψⁿ K (Ω (toLv (y m)))

  -- 这是 `EBOTopRaw.Must.chk` 的同一个表达式
  Kk : Lv
  Kk = limᴼ (natL K) toLv

  chk : ℕ → Ordᴸ (natL K)
  chk = iter (λ t → ψᵖ (chM Kk (inj₁ (inj₁ tt))) (up t (Ω (toLv t)))) (Ω (natL K))

  chM-K : chM Kk (inj₁ (inj₁ tt)) ≡ fin K refl
  chM-K rewrite asN-nat K = refl

  chk≡y : ∀ m → chk m ≡ y m
  chk≡y zero    = refl
  chk≡y (suc m) = trans (help chM-K (chk m)) (cong (λ t → ψⁿ K (Ω (toLv t))) (chk≡y m))
    where
    help : ∀ {M} → M ≡ fin K refl → ∀ t → ψᵖ M (up t (Ω (toLv t))) ≡ ψⁿ K (Ω (toLv t))
    help refl t = refl

  module WithHE (he : ∀ m → LvG (toLv (y m))) where
    good : ∀ m → GoodT (natL K) (y m) × Eq (natL K) (y m) (y m)
    lvp  : ∀ m → LvP (toLv (y m))

    good zero =
      GΩ-K , Ω-self (natL K) (proj₁ (lvp-nat K)) (proj₁ (proj₂ (lvp-nat K)))
    good (suc m) =
      let p = lvp m in
      Good-F (toLv (y m)) p , Eq-ψᴷ (Ω-self (toLv (y m)) (proj₁ p) (proj₁ (proj₂ p)))

    lvp m = lvp-cx (toLv (y m)) (lo-toLv bl-K (y m)) (cx-tree bl-K (proj₁ (good m)) (proj₂ (good m))) (he m)

    y-cert : ∀ m → WFᴬ (toLv (y m))
    y-cert m = wf bl-K (proj₁ (good m))

    y-step : ∀ m → toLv (y m) ⊑ᴬ toLv (y (suc m))
    y-step zero =
      let p = lvp zero in
      ΩB (fin K refl) (ok-K (toLv (y zero))) (≃→⊑ᵒ (Ωi≃ {natL K} Ti-K))
         (Ω-self (toLv (y zero)) (proj₁ p) (proj₁ (proj₂ p)))
         (idO {b = bl-K} {b′ = bl-K})
    y-step (suc m) =
      Ω-mono (toLv (y m)) (toLv (y (suc m))) (y-cert m) (y-cert (suc m))
        (lo-toLv bl-K (y m)) (lo-toLv bl-K (y (suc m))) (lvp m) (lvp (suc m)) (y-step m)
        (ψo (fin K refl) (fin K refl) (ok-K _) (ok-K _) Ti-K (idO {b = bl-K} {b′ = bl-K}))

module NoTop (St : Stage) where
  open Stage St
  open Leaf fl

  -- 第 K ≥ 1 阶段, 目标 0 不合法: 观测里没有 ψ₀
  ¬Zt₀ : ∀ j → Lw j → (Σ (Pre Lv.zero) λ r → at Lv.zero r ≡ j) → ⊥
  ¬Zt₀ j l (() , _)

  -- 低层不含 `limᴼ`: Ω₁ 的层号, 所以 Ω₁+1, Ω·2 这样的目标不在这个 `Stage` 的范围里
  ¬lowΩ₁ : Lw (toLv (Ω (natL 1))) → ⊥
  ¬lowΩ₁ l = low-noo _ l
```
