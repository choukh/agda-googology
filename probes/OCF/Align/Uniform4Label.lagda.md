# 统一形 (四): 标签定理

> 接 [Uniform4Eval](Uniform4Eval.lagda.md). 结论先说:
>
> 1. **`TΩ-label : ∀ c → … Lab₀ (ψ̄ (Ω̇ c) ev z) (ψ₀(Ω_{Ω+c}))`: 对一切 $c$, 无条件.** `T₂-label` 是 $c=2$ 的实例, 记号 `t₂` 与 Uniform4Expt 相同 (`refl`).
> 2. `TΩ+1-label`, `TΩ·2-label`: $\psi_0(\Omega_{\Omega+c}+1)$, $\psi_0(\Omega_{\Omega+c}\cdot2)$, 对一切 $c$.
> 3. **`Tω-label`: 对角线 $\psi_0(\Omega_{\Omega+\omega})$.** 树是 `lim_c ψ̄ (Ω̇ c)`, 记号的基本列 `fs-tω`.
> 4. **与 Uniform3 对照 (§4).** `Tsq-label`: $\psi_0(\Omega_\Omega^2)$ 在这里是 `ψᵒ zero (ι zero (Ω̇ 0))`, 只用深度 0 的行. `agree-sq`, `agree-O1`: 与 Uniform3 的 `TΩ2-label`, `TO-label` 计值后 $\cong$.
>
> 标准形 `NF-Ω`: 对 $c$ 一致, 下标 $\mu_c$ 是 `sΩ` 的可数尾. 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≡-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; bnd[]; Flat; f[]; f∷; f1; flatBnd; NF₁-fsn; NF₁-pred)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW; fsnΣ)
open import OCF.Align.Closure using (cmpᵀ-refl; cmpᴾ-refl) renaming (Pen to CPen)
open import OCF.Align.StandardOmega using ()
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.Uniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.Uniform4Head
open import OCF.Align.Uniform4Base
open import OCF.Align.Uniform4Class
open import OCF.Align.Uniform4Close
open import OCF.Align.Uniform4Tail
open import OCF.Align.Uniform4Psi
open import OCF.Align.Uniform4Rel
open import OCF.Align.Uniform4Eval
open import OCF.Align.Uniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.Uniform4Expt using (t₂)
open import OCF.Align.StandardOmega using (Vis₁; vh; vd; vs; vt)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.OmegaPlus1Base using (nfγ)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Uniform3Full using (TΩ2-label)
open import OCF.Align.Uniform3OmegaPlus1 using (TO-label)
```

## §1 标准形, 对 $c$ 一致

```agda
nf𝟏 : NFᴾ₁ 𝟏
nf𝟏 = nψ n[] (sC c[]) n[] bnd[]

nfNat : ∀ n → NF₁ (natT n)
nfNat zero = n[]
nfNat (suc zero) = n∷ nf𝟏 n[] tt
nfNat (suc (suc n)) = n∷ nf𝟏 (nfNat (suc n)) (inj₂ refl)

ctNat : ∀ n → Ctbl (natT n)
ctNat zero = c[]
ctNat (suc n) = c∷ (ctNat n)

flNat : ∀ n → Flat (natT n)
flNat zero = f[]
flNat (suc n) = f∷ f[] (flNat n)

nfΩp : NFᴾ₁ Ωp
nfΩp = nψ nf1 (sC (c∷ c[])) n[] bnd[]

nfμ′ : ∀ n → NF₁ (Ωp ∷ natT n)
nfμ′ zero = n∷ nfΩp n[] tt
nfμ′ (suc n) = n∷ nfΩp (nfNat (suc n)) (inj₁ refl)

nfμ : ∀ c → NF₁ (μ c)
nfμ c = subst (λ t → NF₁ (Ωp ∷ t)) (sym (tailμ≡ c)) (nfμ′ c)

sbμ : ∀ c → Sb (μ c)
sbμ c = subst (λ t → Sb (Ωp ∷ t)) (sym (tailμ≡ c)) (sΩ (ctNat c))

flμ : ∀ c → Flat (μ c)
flμ c = subst (λ t → Flat (Ωp ∷ t)) (sym (tailμ≡ c)) (f∷ f1 (flNat c))

nfΩμ : ∀ c → NFᴾ₁ (ψᵗ (μ c) [])
nfΩμ c = nψ (nfμ c) (sbμ c) n[] bnd[]

Flat-Ω : ∀ c → Flat (Ωt (μ c))
Flat-Ω c = f∷ (flμ c) f[]

NF-Ω : ∀ c → NF₁ (ψ₀ᵗ (Ωt (μ c)))
NF-Ω c = n∷ (nψ n[] (sC c[]) (n∷ (nfΩμ c) n[] tt) (flatBnd (Flat-Ω c))) n[] tt

_ : ψ₀ᵗ (Ωt (μ 2)) ≡ t₂
_ = refl

FlFl : ∀ {u} → FlrLab Fl u
FlFl (inr ink) = inj₁ z≅
```

## §2 标签定理

$\psi_0(\Omega_{\Omega+c})$ 对一切 $c$, 以及 $+1$, $\cdot2$.

```agda
TΩ-label : ∀ c {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω̇ c) ev z) (ψ₀ᵗ (Ωt (μ c)))
TΩ-label c = label (LdΩ̇ c hon) (RΩ̇ c) (NF-Ω c)

T₂-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω̇ 2) ev z) t₂
T₂-label = TΩ-label 2

T₂-closed : Lab₀ (ψ̄ (Ω̇ 2) {i = zero} {ℓ = suc zero} (tt , (λ q → q)) zero) t₂
T₂-closed = T₂-label (tt , (λ q → q)) zero

one₀ᵗ : Ordˢ zero
one₀ᵗ = Ord₊ˢ.suc Ord₊ˢ.zero

Ω·2ᵒ : ∀ c → O c (Fl ⊔ Fl)
Ω·2ᵒ c = Ω̇ c ⊕ Ω̇ c

Ω+1ᵒ : ∀ c → O c (Fl ⊔ fz)
Ω+1ᵒ c = Ω̇ c ⊕ tl fz (cvFlo zero) one₀ᵗ

TΩ+1-label : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ fz)) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω+1ᵒ c) ev z) (ψ₀ᵗ (Ωt (μ c) ++ (𝟏 ∷ [])))
TΩ+1-label c =
  label (Ld-⊕ (LdΩ̇ c hon) FlFl (tlA (Zu-flo hon zero) (ls refl (lz refl))))
        (R-⊕ (∼ᶠ-refl Fl) (RΩ̇ c) (R-tl (≅ᴵ-refl zero) (∼ᶠ-refl fz) (sᴬ zᴬ)))
        (n∷ (nψ n[] (sC c[]) (n∷ (nfΩμ c) (n∷ nf𝟏 n[] tt) (inj₁ refl)) (flatBnd (f∷ (flμ c) f1))) n[] tt)

TΩ·2-label : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω·2ᵒ c) ev z) (ψ₀ᵗ (Ωt (μ c) ++ Ωt (μ c)))
TΩ·2-label c =
  label (Ld-⊕ (LdΩ̇ c hon) FlFl (LdΩ̇ c hon)) (R-⊕ (∼ᶠ-refl Fl) (RΩ̇ c) (RΩ̇ c))
        (n∷ (nψ n[] (sC c[]) (n∷ (nfΩμ c) (n∷ (nfΩμ c) n[] tt) (inj₂ (cmpᴾ-refl (ψᵗ (μ c) [])))) (flatBnd (f∷ (flμ c) (f∷ (flμ c) f[])))) n[] tt)
```

## §3 对角线 $\psi_0(\Omega_{\Omega+\omega})$

```agda
ωp : PT
ωp = ψᵗ [] (𝟏 ∷ [])

uω : T
uω = Ωp ∷ ωp ∷ []

tω : T
tω = ψ₀ᵗ (Ωt uω)

Tω : Run Fl
Tω = limA 0 (λ n → ψ̄ (Ω̇ n))

bnd-ω : ∀ {ζ} → Vis₁ [] ζ (ψᵗ uω [] ∷ []) → ζ <ᵗ (ψᵗ uω [] ∷ [])
bnd-ω (vh _) = E.[]<
bnd-ω (vd _ ())
bnd-ω (vs _ (vh _)) = E.[]<
bnd-ω (vs _ (vd _ ()))
bnd-ω (vs _ (vs _ (vh _))) = E.[]<
bnd-ω (vs _ (vs _ (vd _ ())))
bnd-ω (vs _ (vs _ (vs _ ())))
bnd-ω (vs _ (vs _ (vt ())))
bnd-ω (vs _ (vt (vh _))) = E.hd< (E.lv< E.[]<)
bnd-ω (vs _ (vt (vd _ (vh _)))) = E.[]<
bnd-ω (vs _ (vt (vd _ (vd _ ()))))
bnd-ω (vs _ (vt (vd _ (vs _ ()))))
bnd-ω (vs _ (vt (vd _ (vt ()))))
bnd-ω (vs _ (vt (vs _ ())))
bnd-ω (vs _ (vt (vt ())))
bnd-ω (vt ())

NF-ω : NF₁ tω
NF-ω = n∷ (nψ n[] (sC c[]) (n∷ (nψ (n∷ nfΩp (n∷ (nψ n[] (sC c[]) (n∷ nf𝟏 n[] tt) (flatBnd f1)) n[] tt) (inj₁ refl)) (sΩ (c∷ c[])) n[] bnd[]) n[] tt) bnd-ω) n[] tt

repN : ∀ n → replicate n 𝟏 ≡ natT n
repN zero = refl
repN (suc n) = cong (𝟏 ∷_) (repN n)

fs-uω : ∀ n → fsn uω n ≡ μ n
fs-uω n = trans (fsnΣ (Ωp ∷ []) ωp [] n)
                (cong (Ωp ∷_) (trans (repW [] [] 𝟏 [] refl n) (trans (repN n) (sym (tailμ≡ n)))))

fs-tω : ∀ n → fsn tω n ≡ ψ₀ᵗ (Ωt (μ n))
fs-tω n = trans (ωW [] [] (ψᵗ uω []) [] refl n)
                (cong (λ a → ψ₀ᵗ a) (trans (E.fsn0-eq Ωp (ωp ∷ []) n refl) (cong Ωt (fs-uω n))))

Tω-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (Tω ev z) tω
Tω-label ev z =
  limᴸ NF-ω refl (λ n → proj₁ (TΩ-label n ev z)) (λ n → subst (Lab _) (sym (fs-tω n)) (proj₂ (TΩ-label n ev z)))
```

## §4 与 Uniform3 的对照

$\Omega_{\Omega+1}$ 与 $(\Omega_\Omega)^2$ 在这里只用深度 0 的行就得到标签 (没有 `Wd` 的后继层、没有 `HΩ̂ᵍ`). 与 Uniform3 的树计值后 $\cong$ (`Lab-uniq`).

```agda
tsqᵒ : O 0 (Fl ⊔ Fl)
tsqᵒ = ψᵒ zero (ι zero (Ω̇ 0))

Tsq-label : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ tsqᵒ ev z) tΩ2
Tsq-label = label (Ld-ψ zero (Ld-ι zero (LdΩ̇ 0 hon))) (R-ψ zero zero (R-ι zero (RΩ̇ 0))) (nfγ 1)

agree-sq : ∀ {ℓ ℓ′} ev (z : zero <ᴵ ℓ) (ev′ : Ev ℓ′ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z′ : zero <ᴵ ℓ′) →
           forceᴸ _ (proj₁ (Tsq-label ev z)) ≅ forceᴸ _ (proj₁ (TΩ2-label ev′ z′))
agree-sq ev z ev′ z′ = Lab-uniq (proj₂ (Tsq-label ev z)) (proj₂ (TΩ2-label ev′ z′))

agree-O1 : ∀ {ℓ ℓ′} ev (z : zero <ᴵ ℓ) ev′ (z′ : zero <ᴵ ℓ′) →
           forceᴸ _ (proj₁ (TΩ-label 1 ev z)) ≅ forceᴸ _ (proj₁ (TO-label ev′ z′))
agree-O1 ev z ev′ z′ = Lab-uniq (proj₂ (TΩ-label 1 ev z)) (proj₂ (TO-label ev′ z′))
```
