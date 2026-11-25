# 一般折叠引理在 k = 1 的实例: 重新得到 ψ₀(Ω_Ω+Ω₂) 的下界 (无前提)

验收文件. 接口 [YiRelKFold](YiRelKFold.lagda.md) `Pf` 在 k = 1 (前缀 `G₂`, 目标层 0, 1) 上的实例 `P₁ᴵ`, 字段全是编译定理 (对角线用 [YiSyncDiag](YiSyncDiag.lagda.md) 的 `Diag`, 经 `Z⊴`). 编译定理, 无前提: `e₂⊴γ₂ᴷ`, `sync₂ᴷ`, `X₂≼TΛᴷ : S2.X₂ ≼ NA.read W.TΛ`, 即 [YiSyncTwo](YiSyncTwo.lagda.md) 的 `X₂≼TΛ` 经一般引理重新证出.
参照 `S2.X₂` 读作 ψ₀(Ω_Ω+Ω₂), 读法是判断. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRelKOne where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiDlVBtbo using (btbo-Tw2)
open import OCF.Lean.YiShpOne using (σA)
open import OCF.Lean.YiShpSq using (s₂; G₂; A; Asuc; Atop; ψ₁)
open import OCF.Lean.YiShpEps using (G₂mono; G₂suc)
open import OCF.Lean.YiShpTwo using (σB; e₂; γ₂; Sync₂; X₂≅; X₂′≼ᶜ)
open import OCF.Lean.YiSyncFold using (Z⊴)
open import OCF.Lean.YiSyncTwo using (e₂-self)
open import OCF.Lean.YiStepFold2 using (thrp)
open import OCF.Lean.YiIntoTw3 using (T⁺ʷ≼TΛ)
import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiRelK
open import OCF.Lean.YiRelKInst using (from1)
open import OCF.Lean.YiRelKFold
```

## 1 目标层与实例

```agda
T1 : ℕ → Set
T1 zero = ⊤
T1 (suc zero) = ⊤
T1 (suc (suc _)) = ⊥

open FoldK S2.ℓ₀ T1

ψu : ∀ t → Raw (tw 2) → Raw (Lk t)
ψu zero = Ψ₀
ψu (suc zero) = ψ₁
ψu (suc (suc t)) _ = G.zero

ψu-s : ∀ t → T1 t → ∀ {A B} → Cp (tw 2) A B → Cp (Lk t) (ψu t A) (ψu t B)
ψu-s zero _ c = W.Ψ-cp zero V2 (λ _ → fold) c
ψu-s (suc zero) _ c = W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) c

ψu-ss : ∀ t → T1 t → ∀ {A B} → Cp (tw 2) (G.suc A) B → Cp (Lk t) (succ (Lk t) (ψu t A)) (ψu t B)
ψu-ss zero _ c = W.Ψ-cp zero V2 (λ _ → fold) c
ψu-ss (suc zero) _ c = W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) c

limR : ∀ t {ℓ} {F : ℕ → L.Ordᶜ ℓ} {H : ℕ → Raw (Lk t)} → (∀ n → Rel t (F n) (H n)) → Rel t (L.lim F) (G.lim H)
limR t h = Rel-ll t (λ n → Rel-cp t (h n) (inj₂ (n , inj₁ refl)))

pb : ∀ {K j} → Path K j → j ≤ K
pb here = ≤-refl
pb (there π) = ≤-trans (n≤1+n _) (pb π)

no2 : ∀ {j} → suc (suc j) ≤ 1 → ⊥
no2 (s≤s ())

no1 : ∀ {j} → suc j ≤ 0 → ⊥
no1 ()

Zᴳ : ∀ (B : Raw (tw 2)) t → T1 t → ∀ {i} (q : i <ᴵ S2.ℓ₀) → i ≅ᴵ ℓk t →
  Rel t (L.ψ q (λ r → r) (L.Ω S2.ℓ₀)) (ψu t (plus (tw 2) G.top B))
Zᴳ B zero _ q L.z≅ = ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r} (L.Ω-refl S2.ℓ₀))))
  (≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top B)))
Zᴳ B (suc zero) _ q (L.s≅ L.z≅) =
  ≅⊴ (L.ψ-≅ {p = q} {σ = λ r → r} {p′ = σB L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _) (L.Ω-refl S2.ℓ₀))
    (from1 (Z⊴ B))

mA : ∀ {a b} → Cp zero a b → Cp (tw 2) (A a) (A b)
mA (inj₁ refl) = inj₁ refl
mA {a} {b} (inj₂ d) = G₂mono {a = G.em tt a} {b = G.em tt b} (inj₂ (refl , d))

P₀ᴵ : Pf zero (λ t a → ψu t (A a))
P₀ᴵ = record
  { Z = λ t tg q ei η → Zᴳ _ t tg q ei
  ; mΦ = λ t tg c → ψu-s t tg (mA c)
  ; sΦ = λ t tg η → ψu-ss t tg (Asuc η)
  ; tgN = λ π → ⊥-elim (no1 (pb π))
  ; kΦ = λ t tg π → ⊥-elim (no1 (pb π))
  ; fΦ = λ t tg π → ⊥-elim (no1 (pb π))
  ; dkΦ = λ m tg ()
  ; dfΦ = λ ()
  ; tp = λ t tg → ψu-ss t tg Atop
  ; dn = tt }

kΦ₁ : ∀ t → T1 t → ∀ {j} (π : Path 1 (suc j)) → ℓk j ≺ᴵ ℓk t →
  ∀ {i ℓ} {p : i <ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} {g : Raw (Lk j) → Raw (Lk 1)} → i ≅ᴵ ℓk j →
  (∀ (y : L.Ordᶜ i) a → Rel j y a → y L.≅ y → Rel t (f (L.into (L.<→◃ p) y)) (ψu t (G₂ (g a)))) →
  Rel t (L.limᵢ p f) (ψu t (G₂ (bld π (inj₁ tt) g)))
kΦ₁ zero _ here (L.via e ())
kΦ₁ (suc zero) _ here lt e h = nd e h
kΦ₁ t _ (there π) = ⊥-elim (no2 (pb π))

fΦ₁ : ∀ t → T1 t → ∀ {j} (π : Path 1 (suc j)) → ¬ (ℓk j ≺ᴵ ℓk t) →
  ∀ {g : Raw (Lk j) → Raw (Lk 1)} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
  (∀ n → Rel t (F n) (ψu t (G₂ (g (chain (Lk j) (λ a → ψu j (G₂ (g a))) n))))) →
  Rel t (L.lim F) (ψu t (G₂ (bld π (inj₁ tt) g)))
fΦ₁ zero _ here nl h = limR zero h
fΦ₁ (suc zero) _ here nl h = ⊥-elim (nl (zero≺ 0))
fΦ₁ t _ (there π) = ⊥-elim (no2 (pb π))

dkΦ₁ : ∀ m → T1 (suc m) → ∀ {r} (z : Z0 1 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
  (∀ n a → Cp zero thr a → Rel (suc m) (F n) (ψu (suc m) (G₂ (g (toA z a))))) →
  Rel (suc m) (L.lim F) (ψu (suc m) (G₂ (G.lc r g)))
dkΦ₁ zero _ z1 h = dg z1 h
dkΦ₁ m _ (zs ())

dfΦ₁ : ∀ {r} (z : Z0 1 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
  (∀ n a → Cp zero thr a → Rel zero (F n) (Ψ₀ (G₂ (g (toA z a))))) → Rel zero (L.lim F) (Ψ₀ (G₂ (G.lc r g)))
dfΦ₁ z1 h = Rel-ll zero (λ n → Rel-cp zero (h n _ (thrp _)) (inj₂ (1 , inj₁ refl)))
dfΦ₁ (zs ())

tp₁ : ∀ t → ψu t (G₂ G.top) ≡ ψu t (G₂ (G.lc (inj₁ tt) (λ a → G.em tt a)))
tp₁ zero = refl
tp₁ (suc zero) = refl
tp₁ (suc (suc t)) = refl

P₁ᴵ : Pf 1 (λ t a → ψu t (G₂ a))
P₁ᴵ = record
  { Z = λ t tg q ei η → Zᴳ _ t tg q ei
  ; mΦ = λ t tg c → ψu-s t tg (G₂mono c)
  ; sΦ = λ t tg η → ψu-ss t tg (G₂suc η)
  ; tgN = λ { here → tt ; (there π) → ⊥-elim (no2 (pb π)) }
  ; kΦ = kΦ₁ ; fΦ = fΦ₁ ; dkΦ = dkΦ₁ ; dfΦ = dfΦ₁
  ; tp = tp₁
  ; dn = P₀ᴵ }
```

## 2 ψ₀(Ω_Ω+Ω₂)

```agda
e₂⊴γ₂ᴷ : ∀ n → Rel 1 (e₂ n) (γ₂ n)
e₂⊴γ₂ᴷ zero = Ω⊴top 0
e₂⊴γ₂ᴷ (suc n) = Rel-+ˡ 0 (γ₂ n) (Fold 1 P₁ᴵ 1 tt (σB L.zero) (L.≅ᴵ-refl _) σA (e₂⊴γ₂ᴷ n) (e₂-self n))

q₀ : L.zero <ᴵ S2.ℓ₀
q₀ = L.lim 0 L.zero

sync₂ᴷ : Sync₂
sync₂ᴷ n = ≼-trans (≅→≼ (L.ψ⁰≅ψ {p = q₀} {σ = λ r → r} (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) (e₂-self n))))
  (Fold 1 P₁ᴵ 0 tt q₀ L.z≅ σA (e₂⊴γ₂ᴷ n) (e₂-self n))

X₂≼TΛᴷ : S2.X₂ ≼ NA.read W.TΛ
X₂≼TΛᴷ = ≼-trans (≼-trans (≅→≼ X₂≅) (X₂′≼ᶜ sync₂ᴷ)) T⁺ʷ≼TΛ
```
