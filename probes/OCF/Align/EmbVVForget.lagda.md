> **机械克隆, 验收用.** 由 `OrdLabForget` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVForget where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.EmbVVOZPrefix using (Z; ĉᴸ; toZ)
import OCF.Align.EmbVVOZGoodLBase as GL
open GL using (Goodᴸ; forceᴸ; forceᴸ-HS; Ptᴸ; ptsᴸ; lvᴸ)
open import OCF.Free.Force
open import OCF.Free.Eq using (_≅ᶻ_)
```

## §1 遗忘标签

与 [NotFree](NotFree.lagda.md) §3 同形, 证书是标签阶梯世界的 `Goodᴸ`.

```agda
ofL   : ∀ {x} → Goodᴸ x → Goodᴺ x
ofL-≅ : ∀ {x} (G : Goodᴸ x) → forceᴺ x (ofL G) ≅ forceᴸ x G

ofL GL.gz = gz
ofL (GL.gs G) = gs (ofL G)
ofL (GL.gl G st) = gl (λ n → ofL (G n))
  (λ n → ⊑-trans (≅→⊑ (ofL-≅ (G n))) (⊑-trans (st n) (≅→⊑ (≅-sym (ofL-≅ (G (suc n)))))))
ofL {ĉᴸ c t₀ g o₀ o} (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc (λ m → Ptᴸ.x (P m)) (λ m → Ptᴸ.hx (P m)) (λ m → Ptᴸ.dx (P m))
     (ofL G₀) (ofL-≅ G₀) (λ m → ofL (Gm m)) (λ m → ofL-≅ (Gm m))
     (ofL Go₀) (λ k → ofL (Go k))
     (⊑-trans (≅→⊑ (ofL-≅ Go₀)) (⊑-trans mo₀ (≅→⊑ (≅-sym (ofL-≅ (Go 0))))))
     (λ k → ⊑-trans (≅→⊑ (ofL-≅ (Go k))) (⊑-trans (mo k) (≅→⊑ (≅-sym (ofL-≅ (Go (suc k)))))))
  where
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  Gm : ∀ m → Goodᴸ (g (lvᴸ (P m)) (Ptᴸ.dx (P m)))
  Gm m = Gg m (Ptᴸ.x (P m)) (Ptᴸ.hx (P m)) (Ptᴸ.lx (P m)) (Ptᴸ.dx (P m))

ofL-≅ GL.gz = z≅
ofL-≅ (GL.gs G) = s≅ (ofL-≅ G)
ofL-≅ (GL.gl G st) = l≅ (λ n → ofL-≅ (G n))
ofL-≅ (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = l≅ eo
  where
  eo : ∀ n → _
  eo zero    = ofL-≅ Go₀
  eo (suc k) = ofL-≅ (Go k)

-- 同一个 Z 上两个证书的计值互模拟
same : ∀ {x} → x ≅ᶻ x → (G : Goodᴺ x) (L : Goodᴸ x) → forceᴺ x G ≅ forceᴸ x L
same d G L = ≅-trans (forceᴺ-≅ d G (ofL L)) (ofL-≅ L)
```

