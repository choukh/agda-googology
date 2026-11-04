# 值判据 (十四): 规格对带标签的树

> **判决: PARTIAL (条件定理).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 实例 `HS₂` 的有限部分: `V (fin 0) 0`, `V (fin 1) 0` 与 `LadderNFTree` 的树同值 (`ValueJudgeBridgeN`), 它们带标签 $\psi_0(\Omega_\Omega)$, $\psi_0(\Omega_{\Omega\cdot2})$. 这里的输入是**字面的** $\Omega_\Omega$ ($\Omega$ `LΩ`), $\Omega_{\Omega\cdot2}$ ($\Omega$ `LΩ·2`), 不是替身.
>
> **都是条件定理, 前提写在类型里, 没有一条被证明.** 前提经典地成立 (判断): `H` 是下面各站的规格; 切口是 Buchholz 的引理; 三条层号性质见 [ValueJudgeSpec](ValueJudgeSpec.lagda.md) §3. 证明它们要一般的托架定理 ([OCFSpec](OCFSpec.lagda.md) 的估计: 6000–9000 行). 这个文件证的只是: **这些前提足够, 而且类型上不再有 `rejected-if-gap` 的问题.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeSpecInst where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Free.Level using (Ordᶜ; _≅_; ≅-sym)
import OCF.Free.Level as FL
open import OCF.Align.InaccTreeBase using (Lv; Ordᴸ; Tree; Ω; toLv; _+_; Sim; add)
import OCF.Align.InaccTreeBase as L
open import OCF.Align.OCFSpecLv using (_≼ᴸ_; _≺ᴸ_; IsPsiᴸ; LΩ; rf)
open import OCF.Align.ValueJudgeSpec
open import OCF.Align.LadderInfTop2 using (HS₂; fin; top)
open import OCF.Align.LadderNFTree using (zero; suc)
import OCF.Align.ValueJudgeLadder
import OCF.Align.ValueJudgeRowV
import OCF.Align.ValueJudgeSpecTree
module J₂ = OCF.Align.ValueJudgeLadder HS₂
module R₂ = OCF.Align.ValueJudgeRowV HS₂
module T₂ = OCF.Align.ValueJudgeSpecTree HS₂

LΩ·2 : Lv
LΩ·2 = toLv (Ω (L.suc L.zero) + Ω (L.suc L.zero))

BR : R₂.BaseRow
BR = R₂.base-row refl

ysΩ : ℕ → Ordᶜ FL.zero
ysΩ = R₂.ysᵇ BR

xΩ : ℕ → Ordᴸ L.zero
xΩ zero    = Tree.suc Tree.zero
xΩ (suc n) = T₂.emb (ysΩ n)

-- ψ₀(Ω_Ω): 字面的输入, 带标签的树
spec-ΩΩ : (H : ∀ n → IsPsiᴸ L.zero (Ω (toLv (xΩ n))) (T₂.emb (ysΩ n))) →
          (stx : ∀ n → xΩ n ≺ᴸ T₂.emb (ysΩ n)) →
          (ΩRefl : ∀ u → Ω u ≺ᴸ Ω LΩ → rf u ≺ᴸ Ω (L.suc L.zero)) →
          (ΩStep : ∀ n u → rf u ≺ᴸ T₂.emb (ysΩ n) → Ω (L.suc u) ≼ᴸ Ω (toLv (xΩ (suc n)))) →
          (ΩPrin : ∀ n {m k} {y : Ordᴸ m} {z : Ordᴸ k} (σ : Sim k m) → y ≺ᴸ Ω (toLv (xΩ n)) → z ≺ᴸ Ω (toLv (xΩ n)) → add y σ z ≺ᴸ Ω (toLv (xΩ n))) →
          IsPsiᴸ L.zero (Ω LΩ) (T₂.emb (J₂.V (fin 0) FL.zero))
spec-ΩΩ H stx ΩRefl ΩStep ΩPrin =
  Sup-t (T₂.emb-≼ (≅-sym (R₂.valueᵇ BR))) (T₂.emb-≼ (R₂.valueᵇ BR))
        (CutΩΩ.ψ₀ΩΩ xΩ (λ n → T₂.emb (ysΩ n)) H stx ΩRefl ΩStep ΩPrin)

-- ψ₀(Ω_{Ω·2}): 上升的层号由使用者给, 切口是条件
spec-Ω·2 : ∀ {lvs : ℕ → Lv} (a : (i : ℕ) → Ordᴸ (lvs i)) →
           (∀ k → IsPsiᴸ L.zero (a k) (T₂.emb (J₂.ys (J₂.clos-row {fin 0} {fin 1} (fin zero) refl) k))) →
           (∀ k → a k ≼ᴸ a (suc k)) → (∀ k → a k ≼ᴸ Ω LΩ·2) →
           (∀ k {m′} {y : Ordᴸ m′} → Cᴸ L.zero (a k) y → y ≺ᴸ Ω LΩ·2 → y ≺ᴸ a (suc k)) →
           IsPsiᴸ L.zero (Ω LΩ·2) (T₂.emb (J₂.V (fin 1) FL.zero))
spec-Ω·2 a = T₂.spec-clos a (Ω LΩ·2) {fin 0} {fin 1} (fin zero) refl
```
