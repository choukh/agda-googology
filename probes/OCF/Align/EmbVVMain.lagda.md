# 值验收 (主定理): 层号去头不改值

> 入口 [EmbVV](EmbVV.lagda.md). 不读记号.
>
> - `V-≃`: 对一切 `HtB`: $a\simeq b\Rightarrow V_m a\approx^{\mathsf v}V_m b$. 这就是要比较的 $\dot\Omega_n(\mathrm{lv}\,y)$ 与 $\dot\Omega_n(\mathrm{lv}\,y')$, 两边只同值不 $\cong$. 不在 `Ψ⁰-mono` (`V-≼`) 的范围: $\mathrm{suc}\,\omega$ 与 $\mathrm{suc}\,\omega^+$ 不 $\sqsubseteq^{\mathsf I}$ 相关 ([EmbVVGap](EmbVVGap.lagda.md) 的 `succ-gap`).
> - `Y-val`: 主线的树与去头的树: $a\simeq b$, 两边有证书, 则计值同值. 右边的证书从哪来不管.
> - 层号: 两棵计值树 `Hd⁰` 相关, 层号就 `≃ᴵ` 相关 ([EmbVVForce](EmbVVForce.lagda.md) 的 `Hd-lvl`), 可以再喂回去.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.EmbVVMain (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.ValueJudgeBase using (_≈ᵛ_; ≼-trans; ≅→≼)
open import OCF.Align.EmbVVEq
open import OCF.Align.EmbVVForce
import OCF.Align.EmbVVSame
open import OCF.Align.EmbVVMode 𝕊 using (HdM)
import OCF.Align.EmbVVSim
import OCF.Align.EmbVVTree
open import OCF.Align.ValLabLadder 𝕊 using (V; V-G; GV; ev₀)
open import OCF.Align.LadderOrdTree 𝕊 using (Ht)

private module Sm = OCF.Align.EmbVVSame 𝕊

≈-≅ˡ : ∀ {a a′ b : Ordᶜ zero} → a ≅ a′ → a′ ≈ᵛ b → a ≈ᵛ b
≈-≅ˡ e (p , q) = ≼-trans (≅→≼ e) p , ≼-trans q (≅→≼ (≅-sym e))

≈-≅ʳ : ∀ {a b b′ : Ordᶜ zero} → a ≈ᵛ b′ → b ≅ b′ → a ≈ᵛ b
≈-≅ʳ (p , q) e = ≼-trans p (≅→≼ (≅-sym e)) , ≼-trans (≅→≼ e) q

-- 层号去头不改值
V-≃ : ∀ m {a b} → a ≃ᴵ b → V m a ≈ᵛ V m b
V-≃ m {a} {b} d =
  ≈-≅ˡ (≅-sym (V-G m a (GV m a))) (≈-≅ʳ (force≈ (toZ-≃ (Sm.simᴴ m a b d ev₀ zero ev₀ zero z≃)) (GV m a) (GV m b)) (≅-sym (V-G m b (GV m b))))

V-Hd : ∀ m {a b} → a ≃ᴵ b → Hd⁰ (forceᴺ _ (GV m a)) (forceᴺ _ (GV m b))
V-Hd m {a} {b} d = force≃ (toZ-≃ (Sm.simᴴ m a b d ev₀ zero ev₀ zero z≃)) (GV m a) (GV m b)

-- 去头的树: 右边的证书任意
module WithY (dr : ∀ m → HdM m) where
  private module I = OCF.Align.EmbVVTree 𝕊 dr
  private module Y = OCF.Align.EmbVVSim 𝕊 dr

  Y-val : ∀ m {a b} → a ≃ᴵ b → (G : Goodᴺ (toZ (I.Tᵠ m b ev₀ zero))) → V m a ≈ᵛ forceᴺ _ G
  Y-val m {a} {b} d G = ≈-≅ˡ (≅-sym (V-G m a (GV m a))) (force≈ (toZ-≃ (Y.simᴴ m a b d ev₀ zero ev₀ zero z≃)) (GV m a) G)

  Y-Hd : ∀ m {a b} → a ≃ᴵ b → (G : Goodᴺ (toZ (I.Tᵠ m b ev₀ zero))) → Hd⁰ (forceᴺ _ (GV m a)) (forceᴺ _ G)
  Y-Hd m {a} {b} d G = force≃ (toZ-≃ (Y.simᴴ m a b d ev₀ zero ev₀ zero z≃)) (GV m a) G
```
