# EboLean3Dist: 突出集 (Setzer §4.4–4.5 的 EBO 版)

> **记号侧验收工作**, 读记号, 不进成品. [EboLean3](EboLean3.lagda.md) 的通用层.
>
> **结论 (编译过的定理, 无前提).** 对任意突出集 $A$ (`Ag A`): $A$ 上的超限归纳 (`Ag-ind`, Setzer 4.21 (a)); $A$ 对和、ψ 封闭, 对首项下标向下封闭 (`AgL.Ag-+`, `Ag-ψ`, `Ag-hs`, Setzer 4.23 (a)(b)). 两个突出集在公共部分一致 (`agree`, Setzer 4.24 与 4.26 (a)); $\mathbb W$ 的段是突出集 (`⊑𝕎⇒Ag`, 4.26 (b)); `Ag𝕎` (4.27); $0\in\mathbb W$.
>
> 与 Setzer 的差别: 4.24 不经 "截段" $D_0\subseteq D_1$ 的一般形, 直接证 4.26 (a) 要的那一句 (对 $Y$ 归纳, 里面对 $X$ 副归纳); 4.28 (a)(b) 不要, 4.30 里的集合直接用 `⊑𝕎⇒Ag`. 4.23 (a) 的上界不必取三个元素的最大者: (ii) 的结论只要合成项 $<K$, 取 $K$ 为界元素 $c$ 的下一层 $\Omega_{\mathrm{hs}(c)+1}$ 即可.
>
> `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Dist where

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; _<ᵀ_)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-trans; <ᵀ-irrefl; ≤-trans′; <-≤; dec≤; idx<; NF; n[]; ≤[])
open import OCF.Align.EboLean2 using (Pred; hs; M; τ; 𝒲; Ag; 𝕎)
open import OCF.Align.EboLean3Base
open import OCF.Align.EboLean3Close using (module L417)

private variable
  ℓ ℓ′ : Level
```

## §1 一个突出集的性质

`seg→`, `seg←`: $A$ 与 $\mathcal W(A)$ 在每个元素以下一致. `E`: 于是在 $\Omega_{\mathrm{hs}(m)}$ 以下一致 ($m\in A$), 这就是 [EboLean3Close](EboLean3Close.lagda.md) 的前提. `Rem`: Setzer Remark 4.20 的 ⊇ 半.

```agda
module AgL {A : Pred ℓ} (ag : Ag A) where
  nfA : ∀ {x} → A x → NF x
  nfA = proj₁ ag

  seg→ : ∀ {m z} → A m → z ≤ᵀ m → A z → 𝒲 A z
  seg→ am zm = proj₁ (proj₂ ag am zm)

  seg← : ∀ {m z} → A m → z ≤ᵀ m → 𝒲 A z → A z
  seg← am zm = proj₂ (proj₂ ag am zm)

  A⊆W : ∀ {x} → A x → 𝒲 A x
  A⊆W ax = seg→ ax (inj₂ refl) ax

  h : ∀ {y} → A y → M A y
  h ay = 𝒲-M (A⊆W ay)

  E : ∀ {m} → A m → Agree (Ωt (hs m)) A (𝒲 A)
  E am p = seg→ am (Ωhs≤ p) , seg← am (Ωhs≤ p)

  Ag-τ : ∀ {a y} → A a → τ A a y → A y
  Ag-τ aa t@(_ , _ , y<a) = seg← aa (inj₁ y<a) (𝒲-τ (A⊆W aa) t)

  Rem : ∀ {a z} → A a → A z → z <ᵀ a → τ A a z
  Rem aa az z<a = nfA az , C-lift (hs-mono (inj₁ z<a)) (λ _ → az) (h az) , z<a

  Ag-hs : ∀ {v e ds} → A (ψ v e ∷ ds) → A v
  Ag-hs {v} {e} {ds} ad = seg← ad (inj₁ (idx< v e ds)) (W-hs (A⊆W ad))

  Ag-+ : ∀ {v e ys c} → A (ψ v e ∷ []) → A ys → A c → (ψ v e ∷ ys) <ᵀ c → NF (ψ v e ∷ ys) → A (ψ v e ∷ ys)
  Ag-+ {c = c} ax ay ac p n =
    seg← ac (inj₁ p) (L417.W-+ A h (hs c) (E ac) (A⊆W ax) (A⊆W ay) n (<ᵀ-trans p (lvl⁻ {y = c} (inj₂ refl))))

  ψ-at : ∀ {w c m} → A w → A c → A m → Ωs w ≤ᵀ m → c ≤ᵀ m → NF (ψ w c ∷ []) → A (ψ w c ∷ [])
  ψ-at {w} {c} {m} aw ac am Ωm cm n =
    seg← am (inj₁ (<-≤ (lvl⁻ {y = ψ w c ∷ []} (inj₂ refl)) Ωm))
         (L417.W-ψ A h (hs m) (E am) (A⊆W ac) (hs-mono cm) (A⊆W aw) (inj₁ (<-≤ (<-sucT w) (hs-mono Ωm))) n)

  Ag-ψ : ∀ {w c} → A w → A (Ωs w) → A c → NF (ψ w c ∷ []) → A (ψ w c ∷ [])
  Ag-ψ {w} {c} aw aΩ ac n with dec≤ c (Ωs w)
  ... | inj₁ cΩ = ψ-at aw ac aΩ (inj₂ refl) cΩ n
  ... | inj₂ Ωc = ψ-at aw ac ac (inj₁ Ωc) (inj₂ refl) n
```

## §2 归纳原理 (4.21 (a))

$\mathcal W$-归纳加上 `Rem`: $y\in A$ 时 $A\cap y\subseteq\tau^A(y)$.

```agda
Ag-ind : ∀ {A : Pred ℓ} {B : Pred ℓ′} → Ag A
       → (∀ {x} → A x → (∀ {z} → A z → z <ᵀ x → B z) → B x) → ∀ {x} → A x → B x
Ag-ind {A = A} {B} ag pr ax =
  𝒲-ind {B = λ y → A y → B y} (λ _ ih ay → pr ay (λ az z<y → ih (Rem ay az z<y) az)) (A⊆W ax) ax
  where open AgL ag
```

## §3 两个突出集的一致 (4.24, 4.26 (a))

$a\in X$, $y\in Y$, $y\le a$ ⟹ $y\in X$. 对 $y\in Y$ 归纳; 要 $\mathcal W(Y)(y)\Rightarrow\mathcal W(X)(y)$, 就要 $X$, $Y$ 在 $y$ 以下一致: $Y\to X$ 是归纳假设, $X\to Y$ 再对 $X$ 归纳.

```agda
agree : ∀ {X : Pred ℓ} {Y : Pred ℓ′} → Ag X → Ag Y → ∀ {a y} → X a → Y y → y ≤ᵀ a → X y
agree {X = X} {Y} agX agY {a} xa = Ag-ind {B = λ y → y ≤ᵀ a → X y} agY outer
  where
    module X = AgL agX
    module Y = AgL agY
    outer : ∀ {y} → Y y → (∀ {z} → Y z → z <ᵀ y → z ≤ᵀ a → X z) → y ≤ᵀ a → X y
    outer {y} yy ih ya = X.seg← xa ya (𝒲-cong≤ ag (inj₂ refl) (Y.A⊆W yy))
      where
        inner : ∀ {z} → X z → z <ᵀ y → Y z
        inner = Ag-ind {B = λ z → z <ᵀ y → Y z} agX
          (λ {z} xz ih′ zy → Y.seg← yy (inj₁ zy)
            (𝒲-cong≤ (λ p → (λ xz′ → ih′ xz′ p (<ᵀ-trans p zy))
                           , (λ yz′ → ih yz′ (<ᵀ-trans p zy) (inj₁ (<-≤ (<ᵀ-trans p zy) ya))))
                     (inj₂ refl) (X.A⊆W xz)))
        ag : Agree y Y X
        ag p = (λ yz → ih yz p (inj₁ (<-≤ p ya))) , (λ xz → inner xz p)
```

## §4 $\mathbb W$ 的段是突出集 (4.26 (b)), `Ag𝕎` (4.27), $0\in\mathbb W$

```agda
⊑𝕎⇒Ag : ∀ {B : Pred ℓ} → (∀ {x} → B x → 𝕎 x) → (∀ {a z} → B a → 𝕎 z → z ≤ᵀ a → B z) → Ag B
⊑𝕎⇒Ag {B = B} B⊆ B⊒ = (λ bx → let (_ , agY , yx) = B⊆ bx in proj₁ agY yx) , seg
  where
    seg : ∀ {a} → B a → ∀ {z} → z ≤ᵀ a → (B z → 𝒲 B z) × (𝒲 B z → B z)
    seg {a} ba {z} za = to , from
      where
        Y = proj₁ (B⊆ ba)
        agY = proj₁ (proj₂ (B⊆ ba))
        ya = proj₂ (proj₂ (B⊆ ba))
        module Y = AgL agY
        toY : ∀ {z} → B z → z ≤ᵀ a → Y z
        toY bz za = let (_ , agZ , zz) = B⊆ bz in agree agY agZ ya zz za
        ag : Agree a Y B
        ag p = (λ yz → B⊒ ba (Y , agY , yz) (inj₁ p)) , (λ bz → toY bz (inj₁ p))
        to : B z → 𝒲 B z
        to bz = 𝒲-cong≤ ag za (Y.seg→ ya za (toY bz za))
        from : 𝒲 B z → B z
        from wz = B⊒ ba (Y , agY , Y.seg← ya za (𝒲-cong≤ (flip ag) za wz)) za

Ag𝕎 : Ag 𝕎
Ag𝕎 = ⊑𝕎⇒Ag (λ w → w) (λ _ w _ → w)

0∈𝕎 : 𝕎 []
0∈𝕎 = (λ z → z ≡ []) , ((λ { refl → n[] }) , λ { refl za → let e = ≤[] za in
                                                   (λ _ → subst (𝒲 _) (sym e) 0∈𝒲) , (λ _ → e) }) , refl
```

**加一个顶元.** $P$ 在 $t$ 以下, $t\in\mathcal W(P\cup\{t\})$, 且 $t$ 以下 $P$ 与 $\mathcal W(P\cup\{t\})$ 一致 ⟹ $P\cup\{t\}$ 是突出集. 4.23 (c) 与 4.30 的新见证都是这个形状.

```agda
Top : Pred ℓ → T → Pred ℓ
Top P t z = P z ⊎ z ≡ t

Top-agree : ∀ {P : Pred ℓ} {t} → Agree t P (Top P t)
Top-agree p = inj₁ , (λ { (inj₁ s) → s ; (inj₂ refl) → ⊥-elim (<ᵀ-irrefl p) })

Ag-top : ∀ {P : Pred ℓ} {t} → (∀ {z} → P z → z <ᵀ t) → 𝒲 (Top P t) t
       → (∀ {z} → z <ᵀ t → (P z → 𝒲 (Top P t) z) × (𝒲 (Top P t) z → P z)) → Ag (Top P t)
Ag-top {P = P} {t} bd wt iso = (λ { (inj₁ q) → 𝒲-NF (proj₁ (iso (bd q)) q) ; (inj₂ refl) → 𝒲-NF wt }) , seg
  where
    up : ∀ {x} → Top P t x → x ≤ᵀ t
    up (inj₁ q)    = inj₁ (bd q)
    up (inj₂ refl) = inj₂ refl
    seg : ∀ {x} → Top P t x → ∀ {z} → z ≤ᵀ x → (Top P t z → 𝒲 (Top P t) z) × (𝒲 (Top P t) z → Top P t z)
    seg px zx with ≤-trans′ zx (up px)
    ... | inj₂ refl = (λ _ → wt) , (λ _ → inj₂ refl)
    ... | inj₁ p    = (λ { (inj₁ q) → proj₁ (iso p) q ; (inj₂ refl) → ⊥-elim (<ᵀ-irrefl p) })
                    , (λ w → inj₁ (proj₂ (iso p) w))
```
