# `T⊤` 的值 (一): $\psi_0(\Omega_{\Omega^2})$ 的参照树

> 验收文件, 读记号. **定理, 无条件:** `Y⊤-lab`: 带 `OrdLabZCorrespond.Lab` 标签 $\psi_0(\Omega_{\psi_1(\Omega)})=\psi_0(\Omega_{\Omega^2})$ 的树 `Y⊤ = lim Z⊤`, 由 `EboLeanLab.lab-NF′` 逐构造子搬过来; `Lab-uniq`: 同标签的树 $\cong$.
> 不说 `T⊤` 的值; 条件定理在 [TTopVal](TTopVal.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TTopValRef where

open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Free.Level using (Ordᶜ; zero; suc; lim; _≅_; z≅; s≅; l≅; ≅-sym; ≅-trans; ≅-refl⁰)
import OCF.Align.EBO as E
open E using (T; cof; fsn; pred; c0; c1; cω; cΩ; []<; ψ; 𝟏; fsT; cmpᵀ; sucT; lt; gt; eq)
import OCF.Align.EboLeanDef as D
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω)
open import OCF.Align.CrossMAccept using (tψΩ; cof-top; u; one; Ω₁)
open import OCF.Align.EBO using (Ωt)
open import OCF.Align.EboLeanBase using (NF; GB; _≤ᵀ_; c∷; c[]; nf-ψ; nf-Ω; n[]; gp; gtl; gh; gw; gc; lt→<)
import OCF.Align.EboLeanTree as LT
import OCF.Align.EboLeanLab as LL
```

## §1 记号一侧: 标准形

```agda
nf⊤ : NF tψΩ
nf⊤ = nf-ψ n[] (nf-Ω nu) g₀
  where
  nf1 : NF one
  nf1 = nf-Ω n[]
  no1 : ∀ {A : Set} → one ≤ᵀ [] → A
  no1 (inj₁ ())
  no1 (inj₂ ())
  g₁ : GB one Ω₁ Ω₁
  g₁ (gp (gh _)) = []<
  g₁ (gp (gw _ (gp (gh l)))) = no1 l
  g₁ (gp (gw _ (gp (gw l _)))) = no1 l
  g₁ (gp (gw _ (gp (gc l _)))) = no1 l
  g₁ (gp (gw _ (gtl ())))
  g₁ (gp (gc _ ()))
  g₁ (gtl ())
  nu : NF u
  nu = nf-ψ nf1 (nf-Ω nf1) g₁
  g₀ : GB [] (Ωt u) (Ωt u)
  g₀ (gp (gh _)) = []<
  g₀ (gp (gw _ (gp (gh _)))) = lt→< _ _ refl
  g₀ (gp (gw _ (gp (gw _ (gp (gh _)))))) = []<
  g₀ (gp (gw _ (gp (gw _ (gp (gw _ ()))))))
  g₀ (gp (gw _ (gp (gw _ (gp (gc _ ()))))))
  g₀ (gp (gw _ (gp (gw _ (gtl ())))))
  g₀ (gp (gw _ (gp (gc _ (gp (gh _)))))) = []<
  g₀ (gp (gw _ (gp (gc _ (gp (gw _ (gp (gh _)))))))) = []<
  g₀ (gp (gw _ (gp (gc _ (gp (gw _ (gp (gw _ ()))))))))
  g₀ (gp (gw _ (gp (gc _ (gp (gw _ (gp (gc _ ()))))))))
  g₀ (gp (gw _ (gp (gc _ (gp (gw _ (gtl ())))))))
  g₀ (gp (gw _ (gp (gc _ (gp (gc _ ()))))))
  g₀ (gp (gw _ (gp (gc _ (gtl ())))))
  g₀ (gp (gw _ (gtl ())))
  g₀ (gp (gc _ ()))
  g₀ (gtl ())
```

## §2 搬到 `OCF.Free.Level`

`fsn≡` 逐字取自 `EboLeanCmp` (那个模块导入归档, 这里只要这一条).

```agda
fsn≡  : ∀ t n → D.fsn t n ≡ fsn t n
fsn≡ˣ : ∀ x xs n → D.fsn (x ∷ xs) n ≡ E.trm (E.fsn↓ x xs n)
fsn≡0 : ∀ w ws c (e : cof (w ∷ ws) ≡ c) n → D.fsn0 (w ∷ ws) c n ≡ E.trm (E.fsn↓0 w ws c e n)
fsn≡₊ : ∀ u y ys c (e : cof (y ∷ ys) ≡ c) n → D.fsn₊ u (y ∷ ys) c n ≡ E.trm (E.fsn↓₊ u y ys c e n)
fsn≡c : ∀ u y ys ν (e : cof (y ∷ ys) ≡ cΩ ν) m n → D.fsnc u (y ∷ ys) ν m n ≡ E.trm (E.fsn↓c u y ys ν e m n)

fsn≡ [] n = refl
fsn≡ (x ∷ xs) n = fsn≡ˣ x xs n

fsn≡ˣ x (y ∷ ys) n = cong (x ∷_) (fsn≡ˣ y ys n)
fsn≡ˣ (ψ u (y ∷ ys)) [] n = fsn≡₊ u y ys (cof (y ∷ ys)) refl n
fsn≡ˣ (ψ (w ∷ ws) []) [] n = fsn≡0 w ws (cof (w ∷ ws)) refl n
fsn≡ˣ 𝟏 [] n = refl

fsn≡0 w ws c0 e n = refl
fsn≡0 w ws c1 e n = refl
fsn≡0 w ws cω e n = cong (λ z → ψ z [] ∷ []) (fsn≡ˣ w ws n)
fsn≡0 w ws (cΩ ν) e n = cong (λ z → ψ z [] ∷ []) (sym (E.fsT↓-trm (w ∷ ws) e (E.natT<Ωs n ν)))

fsn≡₊ u y ys c0 e n = refl
fsn≡₊ u y ys c1 e n = sym (E.rep-trm u (E.pred-< (y ∷ ys) e) n)
fsn≡₊ u y ys cω e n = cong (λ z → ψ u z ∷ []) (fsn≡ˣ y ys n)
fsn≡₊ u y ys (cΩ ν) e n = fsn≡c u y ys ν e (cmpᵀ (sucT ν) u) n

fsn≡c u y ys ν e gt n =
  cong (λ z → ψ u z ∷ [])
       (sym (trans (E.fsT↓-trm (y ∷ ys) e (E.dec (E.γ↓ (y ∷ ys) ν e n))) (cong (fsT (y ∷ ys)) (E.γ↓-trm (y ∷ ys) ν e n))))
fsn≡c u y ys ν e lt n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
fsn≡c u y ys ν e eq n = cong (λ z → ψ u z ∷ []) (sym (E.fsT↓-trm (y ∷ ys) e (E.natT<Ωs n ν)))
```

```agda
ι : LT.Ord → Ordᶜ zero
ι LT.zero = zero
ι (LT.suc a) = suc (ι a)
ι (LT.lim f) = lim (λ n → ι (f n))

ι-≅ : ∀ {a b} → a LL.≅ b → ι a ≅ ι b
ι-≅ LL.z≅ = z≅
ι-≅ (LL.s≅ e) = s≅ (ι-≅ e)
ι-≅ (LL.l≅ h) = l≅ (λ n → ι-≅ (h n))

lab-ι : ∀ {X t} → LL.Labᴸ X t → Lab (ι X) t
lab-ι (LL.l0 c e) = l0 c (ι-≅ e)
lab-ι (LL.l1 c e l) = l1 c (ι-≅ e) (lab-ι l)
lab-ι {t = t} (LL.lω {F = F} c e h) = lω c (ι-≅ e) (λ n → subst (Lab (ι (F n))) (fsn≡ t n) (lab-ι (h n)))

lab-ω : ∀ {X t} → Lab X t → cof t ≡ cω → Σ (ℕ → Ordᶜ zero) λ F → ∀ n → Lab (F n) (fsn t n)
lab-ω (l0 c e) w with trans (sym c) w
... | ()
lab-ω (l1 c e l) w with trans (sym c) w
... | ()
lab-ω (lω {F = F} c e h) w = F , h

Lab-uniq : ∀ {A B t} → Lab A t → Lab B t → A ≅ B
Lab-uniq (l0 c e) (l0 c′ e′) = ≅-trans e (≅-sym e′)
Lab-uniq (l0 c e) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (l0 c e) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l1 c′ e′ l′) = ≅-trans e (≅-trans (s≅ (Lab-uniq l l′)) (≅-sym e′))
Lab-uniq (l1 c e l) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (lω c′ e′ h′) = ≅-trans e (≅-trans (l≅ (λ n → Lab-uniq (h n) (h′ n))) (≅-sym e′))
```

## §3 参照树

树沿良基证明算出, 放 `opaque`; 只导出分支与标签.

```agda
opaque
  Rf : Σ (ℕ → Ordᶜ zero) λ F → ∀ n → Lab (F n) (fsn tψΩ n)
  Rf = lab-ω (lab-ι (LL.lab-NF′ nf⊤ (c∷ c[]))) cof-top

Z⊤ : ℕ → Ordᶜ zero
Z⊤ = proj₁ Rf

Z⊤-lab : ∀ n → Lab (Z⊤ n) (fsn tψΩ n)
Z⊤-lab = proj₂ Rf

Y⊤ : Ordᶜ zero
Y⊤ = lim Z⊤

Y⊤-lab : Lab Y⊤ tψΩ
Y⊤-lab = lω cof-top (≅-refl⁰ Y⊤) Z⊤-lab
```
