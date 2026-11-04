# 证书 (五): $\psi_0(\Omega_{\Omega+1})$ 的 `Goodᴺ`

> 不含记号. 结论写在 [GuardCert](GuardCert.lagda.md). `Good-Ω+1`: **`T₀ʷ` ([GuardWeakTree](GuardWeakTree.lagda.md)) 在 $\Omega+1$ 上有 `Goodᴺ`, 由 [OCF.Free.Main](../Free/Main.lagda.md) 的 `GᴺΩ̇ 1` 经 `Good-≲` 搬来.** 没有模块参数作假设. `value-Ω+1`: 计值与对面 $\cong$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.GuardTightCum hiding (ψ; _+_)
open import OCF.Free.Prefix using (Z; toZ; Ordˢ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
import OCF.Free.Tree as FT
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; Good-≲)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTree using (O; Ω̇; omk; owk; oΩ; rdZ; module Emb)
open import OCF.Align.GuardTightTab Dom₀ using (st-suc)
open import OCF.Align.GuardWeakTree
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardCertRel
open import OCF.Align.GuardCertHi
open import OCF.Align.GuardCertFold

open FoldW cT wf₁ (Lv.s≈ sf₁) tcʷ

E₀ : Ents
E₀ = ∅ zero

ev₀ : Ev (suc zero) FT.Fl
ev₀ = tt , (λ q → q)

-- 链: 左边 chainᵒ, 右边 FT.chainᵒ. 状态是空地板上的, 不必写出来
module Top (st : St E₀ tz tz) where
  Tr₀ : Tr tz st
  Tr₀ = trim tz st {Lv.zero} tt

  stc : St E₀ tz (tz ∪ tz)
  stc = stChain tz (bkᵗ Tr₀) (wkᵗ Tr₀) st

  FL : O c₁ tz → O c₁ tz
  FL z = ψ E₀ Tz stc (ι₁ z)

  FR : FT.O zero FT.Fl → FT.O zero FT.Fl
  FR z = FT.owk (λ v → v , (v , v)) (FT.ψᵒ {α = suc zero} {t = zero} zero (FT.owk proj₁ (FT.ι {zero} {suc zero} zero z)))

  chain-rel : ∀ n → Rc pre (chainᵒ tcʷ FL n) (FT.chainᵒ (λ e → e) FR n)
  chain-rel zero = cwl (cwr RΩ̇₀)
  chain-rel (suc n) = cwr (R-ψᵒ stc (λ _ ()) (λ { (ml ()) ; (mr ()) }) (cwr {y = FT.ι {zero} {suc zero} zero (FT.chainᵒ (λ e → e) FR n)} (ι-Rc (chain-rel n))))

  top-rel : Rs zero fr (ψ E₀ t0 st (Ω̇ cT tcʷ)) (FT.ψ̄ (FT.Ω̇ (suc zero)) ev₀ zero)
  top-rel = rl (λ n → R-ψ E₀ t0 tg0 (stBody tz (wkᵗ Tr₀) st) (λ { (ml ()) ; (mr ()) }) (λ ()) {y = FT.owk proj₁ (FT.ι {zero} {suc zero} zero (FT.chainᵒ (λ e → e) FR n))} (cwr (ι-Rc (chain-rel n))) (ev₀ , ev₀) zero)

≲-Ω+1 : T₀ʷ cT (wf₁ , Lv.s≈ sf₁) tcʷ ≲ᶻ toZ (FT.ψ̄ (FT.Ω̇ (suc zero)) ev₀ zero)
≲-Ω+1 = Rz (Top.top-rel _)

Good-Ω+1 : Goodᴺ (T₀ʷ cT (wf₁ , Lv.s≈ sf₁) tcʷ)
Good-Ω+1 = proj₁ (Good-≲ ≲-Ω+1 (GᴺΩ̇ (suc zero) ev₀ zero))

value-Ω+1 : forceᴺ _ Good-Ω+1 ≅ forceᴺ _ (GᴺΩ̇ (suc zero) ev₀ zero)
value-Ω+1 = proj₂ (Good-≲ ≲-Ω+1 (GᴺΩ̇ (suc zero) ev₀ zero))
```
