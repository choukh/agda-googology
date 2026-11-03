> **机械克隆.** 由 `Uniform3Depth2Class` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 一切深度 (一) 类与行引理

> 接 [Uniform3Full](Uniform3Full.lagda.md) 与 [Uniform3Plus1](Uniform3Plus1.lagda.md). 本文把深度 1 的好性拆成三个按深度递归的类:
>
> 1. `Wd c d X u`: 输出带标签且诚实 (W), 在 $\succeq c$ 的目标上; **Kripke 形**: 高一层的类对一切 $c'\succeq c$ 量化. 这不是装饰, $\ge2$ 层的 `limᵢ` 穿透行要把整个输入栈抬到目标 $i\succ j$.
> 2. `Od d X u`: 目标 0 的标签 (`L0` 的高阶形).
> 3. `Rd d X X′`: 层对齐互模拟 (`≈ᴬ`, `≈₁ᴬ`, `≈₂ᴬ`, … 的统一形).
>
> 每个行引理 (`lim`, `ĉ`, `ŝ`, `clo`, `limᵢ`) 都按深度递归得到: 从深度 $d$ 到 $d+1$ 只是把前缀换成输入的标签 $\rho$, 把 "头" 换成 $\psi_\Omega(ps+y)$. **这一步对 $d$ 是一致的**, 用的只有 Uniform3Depth1 的 `cωΩ`/`cΩΩ`/`ωW`/`penΩ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform3Depth2Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI)
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; repW; ωW; snoc; πw)
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base
open import OCF.Align.ScafLadderZUniform3Depth1 using (c1Ω; cωΩ; cΩΩ; penΩ; wkL0)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3SqA using (Up0; LW0→LW)
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; limᵢ0ᴾ; GRH; GA0ʰ; wkGRH)
open GRᴬ
```

## §1 地板

`FLΩ[c]`: 帧的地板项或在 $c$ 下可忽略, 或被一个在一切 $\psi_\Omega(\zeta+b)$ 里出现的带 `Idx` 下标支配. 深度 $\ge1$ 的输入都用它; 深度 0 的输入用 `FlrLab[c]`.

```agda
FLΩ[_] : Ordᴵ → Flr → T → Set
FLΩ[ c ] φ ζ = ∀ {K} (k : InF K φ) → IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × (∀ b → Occ w (ψᵗ Ωᵗ (ζ ++ b) ∷ []))

FL : Ordᴵ → ℕ → Flr → T → Set
FL c zero    φ π = FlrLab[ c ] φ π
FL c (suc d) φ ζ = FLΩ[ c ] φ ζ

FLΩ→[] : ∀ {c φ ζ} → FlrLabΩ φ ζ → FLΩ[ c ] φ ζ
FLΩ→[] F k with F k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ w = inj₂ w

FLΩ-up : ∀ {c c′ φ ζ} → Up c c′ → FLΩ[ c ] φ ζ → FLΩ[ c′ ] φ ζ
FLΩ-up u F k with F k
... | inj₁ (inj₁ (inj₁ e0)) = inj₁ (inj₁ (inj₁ e0))
... | inj₁ (inj₁ (inj₂ kc)) = inj₁ (inj₁ (inj₂ (≼-trans kc u)))
... | inj₁ (inj₂ (b , le)) = inj₁ (inj₂ (b , ⊑ᴵ-trans le (sB u)))
... | inj₂ w = inj₂ w

FL-up : ∀ d {c c′ φ ζ} → Up c c′ → FL c d φ ζ → FL c′ d φ ζ
FL-up zero    = FlrLab[]-up
FL-up (suc d) = FLΩ-up

FLΩ-⊔ : ∀ {c a b ζ} → FLΩ[ c ] a ζ → FLΩ[ c ] b ζ → FLΩ[ c ] (a ⊔ b) ζ
FLΩ-⊔ F G (inl k) = F k
FLΩ-⊔ F G (inr k) = G k

FLΩ-ext : ∀ {c φ ζ} y → FLΩ[ c ] φ ζ → FLΩ[ c ] φ (ζ ++ y)
FLΩ-ext {ζ = ζ} y F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ b → subst (λ u → Occ w (ψᵗ Ωᵗ u ∷ [])) (sym (++-assoc ζ y b)) (o (y ++ b)))

-- 帧的标签 ψ_Ω(b) 出现在任何前缀之后
occΩ : ∀ {w} b → (∀ c → Occ w (ψᵗ Ωᵗ (b ++ c) ∷ [])) → Occ w (ψᵗ Ωᵗ b ∷ [])
occΩ {w} b o = subst (λ u → Occ w (ψᵗ Ωᵗ u ∷ [])) (++-identityʳ b) (o [])

FLΩ-rep₀ : ∀ {c φ b} → FLΩ[ c ] φ b → ∀ m → FlrLab[ c ] φ (replicate (suc m) (ψᵗ Ωᵗ b))
FLΩ-rep₀ {b = b} F m k with F k
... | inj₁ g = inj₁ g
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (occΩ b o))

FLΩ-repₛ : ∀ {c φ ρ b} → FLΩ[ c ] φ b → ∀ m → FLΩ[ c ] φ (ρ ++ replicate (suc m) (ψᵗ Ωᵗ b))
FLΩ-repₛ {ρ = ρ} {b = b} F m k with F k
... | inj₁ g = inj₁ g
... | inj₂ (w , Iw , kw , o) =
  inj₂ (w , Iw , kw , λ c → subst (λ u → Occ w (ψᵗ Ωᵗ u ∷ [])) (sym (++-assoc ρ _ c)) (od (OccΣ ρ (occ-hd (occΩ b o)))))

FL-rep : ∀ d {c fl ψ′ ρ b} → FL c d fl ρ → FLΩ[ c ] ψ′ b → ∀ m → FL c d (fl ⊔ ψ′) (ρ ++ replicate (suc m) (ψᵗ Ωᵗ b))
FL-rep zero    F G m = FlrLab[]-⊔ F (FLΩ-rep₀ G m)
FL-rep (suc d) F G m = FLΩ-⊔ (FLΩ-ext _ F) (FLΩ-repₛ G m)
```

## §2 类 `Wd`

```agda
Wd : Ordᴵ → ∀ d {φ} → A d φ → T → Set
Wd c zero    R u = LWʰ[ c ] R u
Wd c (suc d) X ζ = ∀ {c′} → Up c c′ → ∀ {fl} {Q : A d fl} {ρ} → FL c′ d fl ρ → Wd c′ d Q ρ → Wd c′ d (X Q) (ρ ++ ψΩᵗ ζ)

≼-refl : ∀ i → i ≼ i
≼-refl i = inj₂ (≅ᴵ-refl i)

W-up : ∀ d {c c′ φ} {X : A d φ} {u} → Up c c′ → Wd c d X u → Wd c′ d X u
W-up zero    u h = LWʰ-up u h
W-up (suc d) u h u′ = h (≼-trans u u′)

wkW : ∀ d {c φ ψ} {X : A d φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → Wd c d X u → Wd c d (wk d le X) u
wkW zero    le h = wkLWʰ le h
wkW (suc d) le h u F hQ = wkW d _ (h u F hQ)

-- 帧的应用, 目标不变
apW : ∀ d {c φ} {X : A (suc d) φ} {ζ fl} {Q : A d fl} {ρ} → Wd c (suc d) X ζ → FL c d fl ρ → Wd c d Q ρ → Wd c d (X Q) (ρ ++ ψΩᵗ ζ)
apW d {c} h = h (≼-refl c)

copyW : ∀ d {c ψ′ fl} {Q : A d fl} {ρ b} {fr : A (suc d) ψ′} → FL c d fl ρ → FLΩ[ c ] ψ′ b → Wd c d Q ρ → Wd c (suc d) fr b →
        ∀ m → Wd c d (repA d Q fr m) (ρ ++ replicate m (ψᵗ Ωᵗ b))
copyW d {c} {ρ = ρ} F G hQ hF zero = subst (Wd c d _) (sym (++-identityʳ ρ)) (wkW d proj₁ hQ)
copyW d F G hQ hF (suc zero) = apW d hF F hQ
copyW d {c} {ρ = ρ} {b = b} F G hQ hF (suc (suc m)) =
  wkW d _ (subst (Wd c d _) (snoc ρ (suc m) (ψᵗ Ωᵗ b)) (apW d hF (FL-rep d F G m) (copyW d F G hQ hF (suc m))))
```

## §3 $W$ 的行引理

```agda
limWd : ∀ d {c φ ps y ys} {F : ℕ → A d φ} → cof (y ∷ ys) ≡ cω → (∀ n → Wd c d (F n) (ps ++ fsn (y ∷ ys) n)) → Wd c d (limA d F) (ps ++ (y ∷ ys))
limWd zero {ps = ps} {y} {ys} {F} cc h = limWʰ {ps = ps} {y = y} {ys = ys} {F = F} cc h
limWd (suc d) {ps = ps} {y} {ys} {F} cc h {c′} u {Q = Q} {ρ} Fl hQ =
  limWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} (cωΩ ps cc)
       (λ m → subst (λ v → Wd c′ d (F m Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cc m)) (h m u Fl hQ))

ĉWd : ∀ d {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps y ys} {O₀ : A d φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
     cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) → Wd c d O₀ (ps ++ fsn (y ∷ ys) 0) →
     (∀ k → Wd c d (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Wd c d (ĉA d c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
ĉWd zero {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk = ĉWʰ {ps = ps} {y = y} {ys = ys} {O₀ = O₀} {O = O} cw K h₀ hk
ĉWd (suc d) {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk {c′} u {Q = Q} {ρ} Fl hQ =
  ĉWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {O₀ = O₀ Q} {O = λ η e → O η e Q} (cωΩ ps cw) K
     (subst (λ v → Wd c′ d (O₀ Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw 0)) (h₀ u Fl hQ))
     (λ k → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw (suc k))) (hk k u Fl hQ))

Ob↑ : ∀ {w ps y ys} ρ → cof (y ∷ ys) ≡ cΩ [] → Ob w ps y ys → Ob w ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []
Ob↑ {w} {ps} ρ cs ob θ = subst (λ u → Occ w (ρ ++ u)) (sym (penΩ ps cs I0 θ)) (OccΣ ρ (od (ob θ)))

ŝWd : ∀ d {c φ c₀ w′ ps y ys} {T₀ : A d φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
     cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys → Wd c d T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
     (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Wd c d (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
     Wd c d (ŝA d c₀ T₀ G) (ps ++ (y ∷ ys))
ŝWd zero {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg = ŝWʰ {ps = ps} {y = y} {ys = ys} {T₀ = T₀} {G = G} cs Iw′ bw ob h₀ hg
ŝWd (suc d) {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg {c′} u {Q = Q} {ρ} Fl hQ =
  ŝWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {T₀ = T₀ Q} {G = λ η e → G η e Q} (cΩΩ ps cs I0) Iw′ bw (Ob↑ ρ cs ob)
     (subst (λ v → Wd c′ d (T₀ Q) (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (h₀ u Fl hQ))
     (λ θ Y hY lY nθ lt e → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (hg θ Y hY lY nθ lt e u Fl hQ))

FWd : Ordᴵ → ℕ → Flr → T → PT → T → Set
FWd c zero    φ ps y ys = FW[ c ] (φ ⊔ fk zero) ps y ys
FWd c (suc d) φ ps y ys = ∀ {c′} → Up c c′ → ∀ {fl ρ} → FL c′ d fl ρ → FWd c′ d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []

cloWd : ∀ d {c φ ps y ys} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)} → FWd c d φ ps y ys → cof (y ∷ ys) ≡ cΩ [] →
       Wd c d t (ps ++ fsT (y ∷ ys) (natT 1)) →
       (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → Wd c d (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
       Wd c d (cloA d t g) (ps ++ (y ∷ ys))
cloWd zero {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg = cloWʰ {ps = ps} {y = y} {ys = ys} {t = t} {g = g} fw cs h₀ hg
cloWd (suc d) {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg {c′} u {fl} {Q} {ρ} Fl hQ =
  wkW d _ (cloWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} (fw u Fl) (cΩΩ ps cs I0)
    (subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (wkW d _ (h₀ u Fl hQ)))
    (λ θ Y hY lY nθ lt → subst (λ v → Wd c′ d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (wkW d _ (hg θ Y hY lY nθ lt u Fl hQ))))
```

**`limᵢ` 行.** Uniform3Hon `limᵢWᴾ` 的高阶形, 改了两处. (1) 穿透行的前提直接写成 "对一切 $i\succ j$ 的 `Wd i`": 这正是 Kripke 形要提供的, 输入栈被抬到 $i$. (2) 链点的闭合 `hClose` **不提栈**: 链点是 `hOut` 在目标 $j$ 的输出, 下一点属于 `Inp` 只看 `Out`. 所以 `hStep` 不再是一条要逐层搬运的前提.

```agda
limᵢWd : ∀ d {c φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
         (∀ {v x′} → kd j ≡ false → Out x′ (ψᵗ ν v ∷ []) → Inp (ψᵗ ν v ∷ []) x′) →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Up c i → Wd i d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ {η x} → Inp η x → Wd c d (H x) (ps ++ fsT (y ∷ ys) η)) →
         Wd c d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢWd zero {ps = ps} {y} {ys} {ac} {H} cc Iν ej Inp i₀ hClose hPen hOut =
  limᵢWᴾ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} cc Iν ej Inp i₀
    (λ η x l {i} ev p Iw ei ki u s → hPen η x l s u ev p Iw ei ki (≼-refl i))
    (λ ix kj uj ev → hClose kj (hOut ix ev (ac ev) Iν ej kj uj))
    hOut
limᵢWd (suc d) {ps = ps} {y} {ys} {ac} {H} cc Iν ej Inp i₀ hClose hPen hOut {c′} u {fl} {Q} {ρ} Fl hQ =
  limᵢWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         (cΩΩ ps cc Iν) Iν ej Inp i₀ hClose
         (λ η x l {i} s ui → subst (λ v → Wd i d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η))
                                   (hPen η x l s (≼-trans u ui) (≼-refl i) (FL-up d ui Fl) (W-up d ui hQ)))
         (λ {η} {x} ix → subst (λ v → Wd c′ d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hOut ix u Fl hQ))

-- 普通形: 一切带标签的输入都好
limᵢWs : ∀ d {c φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → Wd c d (H x) (ps ++ fsT (y ∷ ys) η)) → Wd c d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢWs d {ps = ps} {y} {ys} {ac} {H} cc Iν ej hW =
  limᵢWd d {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} cc Iν ej (λ η x → LabL x η)
         (LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej)
         (λ kj o → frL₊ kj (proj₁ o))
         (λ η x l s ui → W-up d ui (hW η x l))
         (λ {η} {x} l → hW η x l)
```

## §4 互模拟 `Rd`

`Rd 0 = ≈ᴬ`, `Rd 1 = ≈₁ᴬ`, `Rd 2 = ≈₂ᴬ` (定义相等). 这就是 Uniform3Plus1 预言的双边 $\approx_2^\mathsf A$; 它的行引理同样按深度递归.

```agda
Rd : ∀ d {φ ψ} → A d φ → A d ψ → Set
Rd zero    R R′ = R ≈ᴬ R′
Rd (suc d) X X′ = ∀ {fl fl′} {Q : A d fl} {Q′ : A d fl′} → fl ∼ᶠ fl′ → Rd d Q Q′ → Rd d (X Q) (X′ Q′)

wkRd : ∀ d {φ φ′ ψ ψ′} {X : A d φ} {X′ : A d φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       Rd d X X′ → Rd d (wk d le X) (wk d le′ X′)
wkRd zero    le le′ h = wkRᴬ le le′ h
wkRd (suc d) le le′ h s H = wkRd d _ _ (h s H)

limRd : ∀ d {φ ψ} {F : ℕ → A d φ} {G : ℕ → A d ψ} → (∀ n → Rd d (F n) (G n)) → Rd d (limA d F) (limA d G)
limRd zero    h = limRᴬ h
limRd (suc d) h s H = limRd d (λ n → h n s H)

limᵢRd : ∀ d {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → A d φ} {H′ : Ordˢ j′ → A d ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → Rd d (H x) (H′ y)) → Rd d (limᵢA d ac H) (limᵢA d ac′ H′)
limᵢRd zero    {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h = limᵢRᴬ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h
limᵢRd (suc d) {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h {Q = Q} {Q′ = Q′} s H₀ =
  limᵢRd d {ac = λ ev → ac (proj₂ ev)} {ac′ = λ ev → ac′ (proj₂ ev)} {H = λ x → H x Q} {H′ = λ x → H′ x Q′} e (λ x y dd → h x y dd s H₀)

ĉRd : ∀ d {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
      {O₀ : A d φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → A d φ} {O₀′ : A d ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → A d ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      Rd d O₀ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rd d (O η e) (O′ η′ e′)) → Rd d (ĉA d c t₀ g O₀ O) (ĉA d c′ t₀′ g′ O₀′ O′)
ĉRd zero    ec dt dg h₀ h = ĉRᴬ ec dt dg h₀ h
ĉRd (suc d) ec dt dg h₀ h s H = ĉRd d ec dt dg (h₀ s H) (λ η e η′ e′ eη → h η e η′ e′ eη s H)

ŝRd : ∀ d {φ ψ c c′} {T₀ : A d φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → A d φ} {T₀′ : A d ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → A d ψ} →
      c ≅ᴵ c′ → Rd d T₀ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rd d (G η e) (G′ η′ e′)) → Rd d (ŝA d c T₀ G) (ŝA d c′ T₀′ G′)
ŝRd zero    ec h₀ h = ŝRᴬ ec h₀ h
ŝRd (suc d) ec h₀ h s H = ŝRd d ec (h₀ s H) (λ η e η′ e′ eη → h η e η′ e′ eη s H)

cloRd : ∀ d {φ φ′} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)}
        {t′ : A d (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → A d (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
        Rd d t t′ → (∀ η η′ → η ≅ᴵ η′ → Rd d (g η) (g′ η′)) → Rd d (cloA d t g) (cloA d t′ g′)
cloRd zero    {t = t} {g = g} {t′ = t′} {g′ = g′} s ht hg = cloRᴬ {t = t} {g = g} {t′ = t′} {g′ = g′} s ht hg
cloRd (suc d) sφ ht hg s H =
  wkRd d _ _ (cloRd d (⊔∼ s sφ) (wkRd d _ _ (ht s H)) (λ η η′ eη → wkRd d _ _ (hg η η′ eη s H)))

repRd : ∀ d {fl fl′ ψ ψ′} {Q : A d fl} {Q′ : A d fl′} {fr : A (suc d) ψ} {fr′ : A (suc d) ψ′} →
        fl ∼ᶠ fl′ → ψ ∼ᶠ ψ′ → Rd d Q Q′ → Rd (suc d) fr fr′ → ∀ m → Rd d (repA d Q fr m) (repA d Q′ fr′ m)
repRd d s sψ H F zero          = wkRd d proj₁ proj₁ H
repRd d s sψ H F (suc zero)    = F s H
repRd d s sψ H F (suc (suc m)) = wkRd d _ _ (F (⊔∼ s sψ) (repRd d s sψ H F (suc m)))
```

## §5 全类 `Gc` 与 `Od`

`Hd`: 不含地板的部分; `Gc`: 地板 + `Hd`. 把地板分开是因为 `wk` 只动证据不动类型地板 (`copy` 的第 0 份). `Gc 0` 就是 `GA0ʰ`, `Gc 1` 就是 `GA1ʰ` (见 Uniform3Depth2Fold 的桥). 递归: `Od (suc d)` 调 `Gc d`, `Gc (suc d)` 调 `Od (suc d)`.

```agda
FLg : ℕ → Flr → T → Set
FLg zero    φ π = FlrLab φ π
FLg (suc d) φ ζ = FlrLabΩ φ ζ

FLg→FL : ∀ d {c φ ζ} → FLg d φ ζ → FL c d φ ζ
FLg→FL zero    = FlrLab→[]
FLg→FL (suc d) = FLΩ→[]

Od : ∀ d {φ} → A d φ → T → Set
Hd : ∀ d {φ} → A d φ → T → Set
Gc : ∀ d {φ} → A d φ → T → Set

Od zero    R u = L0 R u
Od (suc d) X ζ = ∀ {fl} {Q : A d fl} {ρ} → Gc d Q ρ → Od d (X Q) (ρ ++ ψΩᵗ ζ)

Hd zero    R u = GRH R u
Hd (suc d) X ζ = (∀ {c} → Wd c (suc d) X ζ) × Od (suc d) X ζ × Rd (suc d) X X

Gc d {φ} X u = FLg d φ u × Hd d X u

LWʰ-z : ∀ {c φ} {R : Run φ} {u} → LWʰ[ zero ] R u → LWʰ[ c ] R u
LWʰ-z h ev p Iw ei ki _ = h ev p Iw ei ki (Up0 Iw ei ki)

H→W : ∀ d {c φ} {X : A d φ} {u} → Hd d X u → Wd c d X u
H→W zero    (_ , h) = LWʰ-z h
H→W (suc d) h = proj₁ h

H→O : ∀ d {φ} {X : A d φ} {u} → Hd d X u → Od d X u
H→O zero    (g , _) = g0ᴬ g
H→O (suc d) h = proj₁ (proj₂ h)

H→R : ∀ d {φ} {X : A d φ} {u} → Hd d X u → Rd d X X
H→R zero    (g , _) = gRᴬ g
H→R (suc d) h = proj₂ (proj₂ h)

G→FL : ∀ d {c φ} {X : A d φ} {u} → Gc d X u → FL c d φ u
G→FL d G = FLg→FL d (proj₁ G)

G→W : ∀ d {c φ} {X : A d φ} {u} → Gc d X u → Wd c d X u
G→W d G = H→W d (proj₂ G)

wkO : ∀ d {φ ψ} {X : A d φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → Od d X u → Od d (wk d le X) u
wkO zero    {X = X} le h = wkL0 {R = X} le h
wkO (suc d) le h G = wkO d _ (h G)

wkH : ∀ d {φ ψ} {X : A d φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → Hd d X u → Hd d (wk d le X) u
wkH zero    le h = wkGRH le h
wkH (suc d) le h = wkW (suc d) le (proj₁ h) , wkO (suc d) le (proj₁ (proj₂ h)) , wkRd (suc d) le le (proj₂ (proj₂ h))

apH : ∀ d {φ} {X : A (suc d) φ} {ζ fl} {Q : A d fl} {ρ} → Hd (suc d) X ζ → Gc d Q ρ → Hd d (X Q) (ρ ++ ψΩᵗ ζ)
apH zero    {fl = fl} HX G = grᴬ (LW0→LW (LWʰ→ h)) (proj₁ (proj₂ HX) G) (proj₂ (proj₂ HX) (∼ᶠ-refl fl) (H→R zero (proj₂ G))) , h
  where h = proj₁ HX {zero} (≼-refl zero) (G→FL zero G) (G→W zero G)
apH (suc d) {fl = fl} HX G =
  (λ {c} → proj₁ HX {c} (≼-refl c) (G→FL (suc d) G) (G→W (suc d) G)) ,
  proj₁ (proj₂ HX) G ,
  proj₂ (proj₂ HX) (∼ᶠ-refl fl) (H→R (suc d) (proj₂ G))

FlrLabΩ-rep₀ : ∀ {φ b} → FlrLabΩ φ b → ∀ m → FlrLab φ (replicate (suc m) (ψᵗ Ωᵗ b))
FlrLabΩ-rep₀ {b = b} F m k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (occΩ b o))

FlrLabΩ-repₛ : ∀ {φ ρ b} → FlrLabΩ φ b → ∀ m → FlrLabΩ φ (ρ ++ replicate (suc m) (ψᵗ Ωᵗ b))
FlrLabΩ-repₛ {ρ = ρ} {b = b} F m k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) =
  inj₂ (w , Iw , kw , λ c → subst (λ u → Occ w (ψᵗ Ωᵗ u ∷ [])) (sym (++-assoc ρ _ c)) (od (OccΣ ρ (occ-hd (occΩ b o)))))

FLg-rep : ∀ d {fl ψ′ ρ b} → FLg d fl ρ → FlrLabΩ ψ′ b → ∀ m → FLg d (fl ⊔ ψ′) (ρ ++ replicate (suc m) (ψᵗ Ωᵗ b))
FLg-rep zero    F G m = FlrLab-⊔ F (FlrLabΩ-rep₀ G m)
FLg-rep (suc d) F G m = FlrLabΩ-⊔ (FlrLabΩ-ext _ F) (FlrLabΩ-repₛ G m)

copyH : ∀ d {ψ′ fl} {Q : A d fl} {ρ b} {fr : A (suc d) ψ′} → Gc d Q ρ → FlrLabΩ ψ′ b → Hd (suc d) fr b →
        ∀ m → Hd d (repA d Q fr m) (ρ ++ replicate m (ψᵗ Ωᵗ b))
copyH d {ρ = ρ} G Fψ hF zero = subst (Hd d _) (sym (++-identityʳ ρ)) (wkH d proj₁ (proj₂ G))
copyH d G Fψ hF (suc zero) = apH d hF G
copyH d {ρ = ρ} {b = b} G Fψ hF (suc (suc m)) =
  wkH d _ (subst (Hd d _) (snoc ρ (suc m) (ψᵗ Ωᵗ b)) (apH d hF (FLg-rep d (proj₁ G) Fψ m , copyH d G Fψ hF (suc m))))
```

## §6 $O$ 的行引理

```agda
limOd : ∀ d {φ ps y ys} {F : ℕ → A d φ} → cof (y ∷ ys) ≡ cω → (∀ n → Od d (F n) (ps ++ fsn (y ∷ ys) n)) → Od d (limA d F) (ps ++ (y ∷ ys))
limOd zero {ps = ps} {y} {ys} {F} cc h = lim0 {ps = ps} {y = y} {ys = ys} {F = F} cc h
limOd (suc d) {ps = ps} {y} {ys} {F} cc h {Q = Q} {ρ} G =
  limOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} (cωΩ ps cc)
        (λ m → subst (λ v → Od d (F m Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cc m)) (h m G))

ĉOd : ∀ d {φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps y ys} {O₀ : A d φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
      cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) → Od d O₀ (ps ++ fsn (y ∷ ys) 0) →
      (∀ k → Od d (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Od d (ĉA d c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
ĉOd zero {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk = ĉ0 {ps = ps} {y = y} {ys = ys} {O₀ = O₀} {O = O} cw K h₀ hk
ĉOd (suc d) {ps = ps} {y} {ys} {O₀} {O} cw K h₀ hk {Q = Q} {ρ} G =
  ĉOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {O₀ = O₀ Q} {O = λ η e → O η e Q} (cωΩ ps cw) K
      (subst (λ v → Od d (O₀ Q) (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw 0)) (h₀ G))
      (λ k → subst (λ v → Od d _ (ρ ++ v)) (sym (ωW Ωᵗ ps y ys cw (suc k))) (hk k G))

ŝOd : ∀ d {φ c₀ w′ ps y ys} {T₀ : A d φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → A d φ} →
      cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys → Od d T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
      (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Od d (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
      Od d (ŝA d c₀ T₀ G) (ps ++ (y ∷ ys))
ŝOd zero {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg = ŝ0 {ps = ps} {y = y} {ys = ys} {T₀ = T₀} {G = G} cs Iw′ bw ob h₀ hg
ŝOd (suc d) {ps = ps} {y} {ys} {T₀} {G} cs Iw′ bw ob h₀ hg {Q = Q} {ρ} GQ =
  ŝOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {T₀ = T₀ Q} {G = λ η e → G η e Q} (cΩΩ ps cs I0) Iw′ bw (Ob↑ ρ cs ob)
      (subst (λ v → Od d (T₀ Q) (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (h₀ GQ))
      (λ θ Y hY lY nθ lt e → subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (hg θ Y hY lY nθ lt e GQ))

FWo : ℕ → Flr → T → PT → T → Set
FWo zero    φ ps y ys = FW (φ ⊔ fk zero) ps y ys
FWo (suc d) φ ps y ys = ∀ {fl ρ} → FLg d fl ρ → FWo d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []

cloOd : ∀ d {φ ps y ys} {t : A d (φ ⊔ fk zero)} {g : (η : Ordᴵ) → A d (φ ⊔ fk η)} → FWo d φ ps y ys → cof (y ∷ ys) ≡ cΩ [] →
        Od d t (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → Od d (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
        Od d (cloA d t g) (ps ++ (y ∷ ys))
cloOd zero {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg = clo0 {ps = ps} {y = y} {ys = ys} {t = t} {g = g} fw cs h₀ hg
cloOd (suc d) {ps = ps} {y} {ys} {t} {g} fw cs h₀ hg {fl} {Q} {ρ} G =
  wkO d _ (cloOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} (fw (proj₁ G)) (cΩΩ ps cs I0)
    (subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 (natT 1))) (wkO d _ (h₀ G)))
    (λ θ Y hY lY nθ lt → subst (λ v → Od d _ (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (wkO d _ (hg θ Y hY lY nθ lt G))))

limᵢOᴬ : ∀ d {φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → Wd zero d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → LabL x η → x ≅ᴬ x → Od d (H x) (ps ++ fsT (y ∷ ys) η) × Rd d (H x) (H x)) →
         Od d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢOᴬ zero {ps = ps} {y} {ys} {ac} {H} cc Iν ej hW h0 =
  limᵢ0ᴬ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} cc Iν ej (λ η x l → LW0→LW (LWʰ→ (hW η x l))) h0
limᵢOᴬ (suc d) {ps = ps} {y} {ys} {ac} {H} cc Iν ej hW h0 {fl} {Q} {ρ} G =
  limᵢOᴬ d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         (cΩΩ ps cc Iν) Iν ej
         (λ η x l → subst (λ v → Wd zero d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hW η x l (≼-refl zero) (G→FL d G) (G→W d G)))
         (λ η x l xx → subst (λ v → Od d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (proj₁ (h0 η x l xx) G) ,
                       proj₂ (h0 η x l xx) (∼ᶠ-refl fl) (H→R d (proj₂ G)))

limᵢOᴾ : ∀ d {φ j ν ps y ys} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → A d φ} →
         kd j ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
         (∀ {v x′} → Out x′ (ψᵗ ν v ∷ []) → x′ ≅ᴬ x′ → Inp (ψᵗ ν v ∷ []) x′) →
         (∀ {η x} → Inp η x → Wd j d (H x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ {η x} → Inp η x → Rd d (H x) (H x)) →
         (∀ {η x} → Inp η x → Od d (H x) (ps ++ fsT (y ∷ ys) η)) →
         Od d (limᵢA d ac H) (ps ++ (y ∷ ys))
limᵢOᴾ zero {j = j} {ps = ps} {y} {ys} {ac} {H} kj cc Iν ej Inp i₀ hClose hW hR hO =
  limᵢ0ᴾ {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} kj cc Iν ej Inp i₀
    (λ ix ev → hClose (hW ix ev (ac ev) Iν ej kj (≼-refl j)) (hR ix ev (ac ev) ev (ac ev) (≅ᴵ-refl j))) hO
limᵢOᴾ (suc d) {j = j} {ps = ps} {y} {ys} {ac} {H} kj cc Iν ej Inp i₀ hClose hW hR hO {fl} {Q} {ρ} G =
  limᵢOᴾ d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {ac = λ ev → ac (proj₂ ev)} {H = λ x → H x Q}
         kj (cΩΩ ps cc Iν) Iν ej Inp i₀ hClose
         (λ {η} {x} ix → subst (λ v → Wd j d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hW ix (≼-refl j) (G→FL d G) (G→W d G)))
         (λ ix → hR ix (∼ᶠ-refl fl) (H→R d (proj₂ G)))
         (λ {η} {x} ix → subst (λ v → Od d (H x Q) (ρ ++ v)) (sym (penΩ ps cc Iν η)) (hO ix G))
```
