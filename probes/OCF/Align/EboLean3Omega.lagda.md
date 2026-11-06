# EboLean3Omega: $\mathbb W$ 对 Ω 封闭, 一切 EBO 标准形良基

> **记号侧验收工作**, 读记号, 不进成品. [EboLean3](EboLean3.lagda.md) 的出口.
>
> **结论 (编译过的定理, 无前提).**
>
> 1. `𝕎-Ωs : 𝕎 (Ωt l) → 𝕎 (Ωs l)` (Setzer 4.23 (c) 的 EBO 版, $\Omega_l\mapsto\Omega_l^+=\Omega_{l+1}$).
> 2. `L430` (Setzer 4.30): $a\in M(\mathbb W)$, $\tau^{\mathbb W}(a)$ 被一个集合 $B\subseteq\mathbb W|a$ 盖住 ⟹ $a\in\mathbb W$.
> 3. `𝕎-Ω : 𝕎 a → 𝕎 (Ωt a)` (Setzer 4.31 (a)).
> 4. `𝕎-all : NF t → 𝕎 t`: 一切 EBO 标准形 (不限可数) 属于 $\mathbb W$; `wf : NF t → Acc′ t`: **一切 EBO 标准形上 $<^\mathsf T$ 良基** (`Acc′` 的分支限于标准形).
>
> 与 Setzer 的差别: 4.23 (c) 的 $A^+$ 只对一个元素 $\Omega_l$ 造 ($Y'=(\mathcal W(Y)\cap\Omega_{l+1})\cup\{\Omega_{l+1}\}$), 不取并. 4.31 (a) 不分后继与极限: 盖住 $\tau^{\mathbb W}(\Omega_a)$ 的集合取 $\{0\}\cup\{\Omega_{y+1}\mid y\in\tau^X(a)\}$, $a$ 为后继 $s+1$ 时 $\Omega_{s+1}$ 本身就在里面 (由 1). EBO 没有 Ω 的不动点, 所以没有 Setzer 的 `Ω-view` 三支. 最后一步不经 4.21 (c) (可数部分): $\mathbb W$ 已含一切标准形, 4.21 (a) 直接给出良基.
>
> `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Omega where

open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; sucT; _<ᵀ_; []<; hd<; lv<)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-trans; <ᵀ-irrefl; <ᵀ-asym; ≤-trans′; ≤-<; ≤¬>;
  NF; NFP; n[]; n∷; nψ; nf-hd; nfp-u; nf-Ω; nf-ψ)
open import OCF.Align.EboLean2 using (Pred; hs; C; cl; c+; cΩ; cψ; M; τ; 𝒲; sup; Ag; 𝕎)
open import OCF.Align.EboLean3Base
open import OCF.Align.EboLean3Close using (module L417)
open import OCF.Align.EboLean3Dist

module W = AgL Ag𝕎
```

## §1 $\Omega_l\in\mathbb W\Rightarrow\Omega_{l+1}\in\mathbb W$

$Y$ 是 $\Omega_l$ 的见证. $Y'$ 与 $Y$ 在 $\Omega_l$ 以下一致, 所以 $\mathcal W(Y')$ 与 $\mathcal W(Y)$ 在 $K=\Omega_{l+1}$ 以下一致; $K\in\mathcal W(Y')$: $l+1\in\mathcal W(Y)$ (`W-suc`), $\tau^{Y'}(K)$ 的元素由 `under` 落进 $\mathcal W(Y)$.

```agda
𝕎-Ωs : ∀ {l} → 𝕎 (Ωt l) → 𝕎 (Ωs l)
𝕎-Ωs {l} (Y , agY , yΩ) = Y′ , agY′ , inj₂ refl
  where
    module Y = AgL agY
    open L417 Y Y.h l (Y.E yΩ)
    Y′ : Pred 0ℓ
    Y′ = Top (λ z → 𝒲 Y z × z <ᵀ K) K
    ΩK : Ωt l <ᵀ K
    ΩK = hd< (lv< (<-sucT l))
    agΩ : Agree (Ωt l) Y Y′
    agΩ p = (λ yz → inj₁ (proj₁ (Y.E yΩ p) yz , <ᵀ-trans p ΩK))
          , (λ { (inj₁ (w , _)) → proj₂ (Y.E yΩ p) w ; (inj₂ refl) → ⊥-elim (<ᵀ-asym p ΩK) })
    nK : NF K
    nK = nf-Ω (nf-suc (nfp-u (nf-hd (Y.nfA yΩ))))
    WK : 𝒲 Y′ K
    WK = sup nK (cΩ (cl (inj₁ (sl , <Ωt (sucT l))) (<Ωt (sucT l))))
             (λ (nd , cd , p) → 𝒲-cong agΩ (lvl p) (under zw nd cd p))
      where
        sl = W-suc (W-hs (Y.A⊆W yΩ)) (<Ωt (sucT l))
        zw : ∀ {z} → Y′ z → z <ᵀ K → 𝒲 Y z
        zw (inj₁ (w , _)) _ = w
        zw (inj₂ refl)    p = ⊥-elim (<ᵀ-irrefl p)
    agY′ : Ag Y′
    agY′ = Ag-top proj₂ WK (λ p → (λ (w , _) → 𝒲-cong agΩ (lvl p) w) , (λ w → 𝒲-cong (flip agΩ) (lvl p) w , p))
```

## §2 Lemma 4.30

$g(b)$ 是 $b\in B$ 的见证; $S=(\bigcup_{b\in B}g(b))\cap a$ 是集合, 是突出集 (`⊑𝕎⇒Ag`), 且 $S\cong\mathbb W\cap a$. $S'=S\cup\{a\}$ 是突出集. 关键一步 `WS→S`: $d\in\mathcal W(S)$, $d<a$ ⟹ $d\in\mathbb W$: $\tilde d=\Omega_{\mathrm{hs}(d)}\in\tau^{\mathbb W}(a)\subseteq\mathbb W$, 再由 §1 得 $d<\Omega_{\mathrm{hs}(d)+1}\in\mathbb W$.

```agda
module _ {a : T} (na : NF a) (ma : M 𝕎 a) (B : Pred 0ℓ)
         (cover : ∀ {y} → τ 𝕎 a y → Σ T λ b → B b × y ≤ᵀ b)
         (B⊆ : ∀ {b} → B b → 𝕎 b × b ≤ᵀ a) where
  private
    g : Σ T B → Pred 0ℓ
    g (_ , bb) = proj₁ (proj₁ (B⊆ bb))
    agg : ∀ i → Ag (g i)
    agg (_ , bb) = proj₁ (proj₂ (proj₁ (B⊆ bb)))
    gb : ∀ i → g i (proj₁ i)
    gb (_ , bb) = proj₂ (proj₂ (proj₁ (B⊆ bb)))

    S : Pred 0ℓ
    S x = Σ (Σ T B) (λ i → g i x) × x <ᵀ a
    S⊆𝕎 : ∀ {x} → S x → 𝕎 x
    S⊆𝕎 ((i , gx) , _) = g i , agg i , gx
    agS : Ag S
    agS = ⊑𝕎⇒Ag S⊆𝕎 (λ { ((i , gx) , xa) (_ , agZ , zz) zx → (i , agree (agg i) agZ gx zz zx) , ≤-< zx xa })
    module S = AgL agS

    τ⊆𝕎 : ∀ {y} → τ 𝕎 a y → 𝕎 y
    τ⊆𝕎 t@(ny , cy , _) with cover t
    ... | b , bb , inj₂ refl = proj₁ (B⊆ bb)
    ... | b , bb , inj₁ yb   = W.Ag-τ (proj₁ (B⊆ bb)) (ny , C-anti W.h (hs-mono (proj₂ (B⊆ bb))) cy , yb)

    S← : ∀ {x} → 𝕎 x → x <ᵀ a → S x
    S← wx@(_ , agX , xx) xa with cover (W.nfA wx , C-lift (hs-mono (inj₁ xa)) (λ _ → wx) (W.h wx) , xa)
    ... | b , bb , xb = ((b , bb) , agree (agg (b , bb)) agX (gb (b , bb)) xx xb) , xa

    agS𝕎 : Agree a S 𝕎
    agS𝕎 p = S⊆𝕎 , (λ w → S← w p)

    WS→S : ∀ {d} → 𝒲 S d → d <ᵀ a → S d
    WS→S {d = []} _ da = S← 0∈𝕎 da
    WS→S {ψ v e ∷ ds} wd da =
      S← (W.seg← wK (inj₁ (lvl⁻ {y = ψ v e ∷ ds} (inj₂ refl))) (𝒲-cong≤ agS𝕎 (inj₁ da) wd)) da
      where
        nv = nfp-u (nf-hd (𝒲-NF wd))
        cΩv : C S (hs a) (Ωt v)
        cΩv = cΩ (C-up (hs-mono (inj₁ da)) nv (<Ωt v) (C-hs (𝒲-M wd)))
        wK : 𝕎 (Ωs v)
        wK = 𝕎-Ωs (τ⊆𝕎 (nf-Ω nv , C-cong (λ _ → S⊆𝕎) cΩv , ≤-< (Ω≤ v e ds) da))

    S′ : Pred 0ℓ
    S′ = Top S a
    ag𝕎S′ : Agree a 𝕎 S′
    ag𝕎S′ p = (λ w → inj₁ (S← w p)) , (λ { (inj₁ s) → S⊆𝕎 s ; (inj₂ refl) → ⊥-elim (<ᵀ-irrefl p) })

    Wa : 𝒲 S′ a
    Wa = sup na (C-cong-at ag𝕎S′ ma)
             (λ (ny , cy , ya) → 𝒲-cong≤ (Top-agree {P = S}) (inj₁ ya)
                                   (S.A⊆W (S← (τ⊆𝕎 (ny , C-cong-at (flip ag𝕎S′) cy , ya)) ya)))

    agS′ : Ag S′
    agS′ = Ag-top proj₂ Wa (λ p → (λ s → 𝒲-cong≤ (Top-agree {P = S}) (inj₁ p) (S.A⊆W s))
                                , (λ w → WS→S (𝒲-cong≤ (flip (Top-agree {P = S})) (inj₁ p) w) p))

  L430 : 𝕎 a
  L430 = S′ , agS′ , inj₂ refl
```

## §3 Lemma 4.31 (a): $a\in\mathbb W\Rightarrow\Omega_a\in\mathbb W$

对 $a\in\mathbb W$ 用 4.21 (a). $d\in\tau^{\mathbb W}(\Omega_a)$, $d\ne0$: 对 $d$ 的推导递归得 $\mathrm{hs}(d)\in\mathbb W$, $\mathrm{hs}(d)<a$ (`hsW`), 于是 $\mathrm{hs}(d)\in\tau^X(a)$, $d<\Omega_{\mathrm{hs}(d)+1}\in B$.

```agda
𝕎-Ω : ∀ {a} → 𝕎 a → 𝕎 (Ωt a)
𝕎-Ω = Ag-ind {B = λ a → 𝕎 (Ωt a)} Ag𝕎 step
  where
    step : ∀ {a} → 𝕎 a → (∀ {z} → 𝕎 z → z <ᵀ a → 𝕎 (Ωt z)) → 𝕎 (Ωt a)
    step {a} wa@(X , agX , xa) ih = L430 (nf-Ω (W.nfA wa)) (cΩ (cl wa (<Ωt a))) B cover B⊆
      where
        module X = AgL agX
        B : Pred 0ℓ
        B b = (b ≡ []) ⊎ Σ T (λ y → τ X a y × b ≡ Ωs y)
        hsW : ∀ {v e ds} → NF (ψ v e ∷ ds) → C 𝕎 a (ψ v e ∷ ds) → (ψ v e ∷ ds) <ᵀ Ωt a → 𝕎 v
        hsW nd (cl w _) _          = W.Ag-hs w
        hsW nd (c+ dx _) p         = hsW (nf-h nd) dx (<ᵀ-trans h<s p)
        hsW nd (cΩ dv) p           = W.Ag-τ wa (nfp-u (nf-hd nd) , C-anti W.h (hs≤ a) dv , hd<Ω p)
        hsW nd (cψ q _ _) p        = ⊥-elim (≤¬> q (hd<Ω p))
        cover : ∀ {y} → τ 𝕎 (Ωt a) y → Σ T λ b → B b × y ≤ᵀ b
        cover {y = []} _ = [] , inj₁ refl , inj₂ refl
        cover {ψ v e ∷ ds} (nd , cd , p) =
          Ωs v , inj₂ (v , X.Rem xa (agree agX agV xa vv (inj₁ (hd<Ω p))) (hd<Ω p) , refl)
               , inj₁ (lvl⁻ {y = ψ v e ∷ ds} (inj₂ refl))
          where
            wv = hsW nd cd p
            agV = proj₁ (proj₂ wv)
            vv = proj₂ (proj₂ wv)
        B⊆ : ∀ {b} → B b → 𝕎 b × b ≤ᵀ Ωt a
        B⊆ (inj₁ refl) = 0∈𝕎 , inj₁ []<
        B⊆ (inj₂ (y , t@(_ , _ , y<a) , refl)) =
          𝕎-Ωs (ih (X , agX , X.Ag-τ xa t) y<a) , Ωt-mono (sucT≤ y<a)
```

## §4 一切标准形属于 $\mathbb W$, 良基

对 `NF` 的推导结构递归. $\psi_w(c)$ 用 4.23 (b) (`Ag-ψ`, 要 $\Omega_{w+1}\in\mathbb W$, 由 §1, §3); 和 $\psi_v(b)+y$ 用 4.23 (a) (`Ag-+`), 界取 $\Omega_{v+1}$.

```agda
𝕎-all : ∀ {t} → NF t → 𝕎 t
𝕎P    : ∀ {v e} → NFP (ψ v e) → 𝕎 (ψ v e ∷ [])
𝕎-all n[] = 0∈𝕎
𝕎-all (n∷ {ψ _ _} p _ n[]) = 𝕎P p
𝕎-all nt@(n∷ {ψ v _} {_ ∷ _} p@(nψ nv _ _) _ nys) =
  W.Ag-+ (𝕎P p) (𝕎-all nys) (𝕎-Ωs (𝕎-Ω (𝕎-all nv))) (hd< (lv< (<-sucT v))) nt
𝕎P {e = []} (nψ nv _ _) = 𝕎-Ω (𝕎-all nv)
𝕎P {e = _ ∷ _} (nψ nv nc g) = W.Ag-ψ wv (𝕎-Ωs (𝕎-Ω wv)) (𝕎-all nc) (nf-ψ nv nc g)
  where wv = 𝕎-all nv

data Acc′ (t : T) : Set where
  acc : (∀ {b} → NF b → b <ᵀ t → Acc′ b) → Acc′ t

wf : ∀ {t} → NF t → Acc′ t
wf nt = Ag-ind {B = Acc′} Ag𝕎 (λ _ ih → acc (λ nb b<t → ih (𝕎-all nb) b<t)) (𝕎-all nt)
```
