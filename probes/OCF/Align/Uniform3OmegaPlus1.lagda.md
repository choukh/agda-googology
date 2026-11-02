# 统一形 (三): $\psi_0(\Omega_{\Omega+1})$ 的无条件标签

> 接 [Uniform3Depth2Fold](Uniform3Depth2Fold.lagda.md) 与 [OmegaPlus1Base](OmegaPlus1Base.lagda.md), [OmegaPlus1](OmegaPlus1.lagda.md). 结论先说:
>
> 1. **`TO-label`, `TO+1-label`, `TO·2-label` (§4): $\psi_0(\Omega_{\Omega+1})$, $\psi_0(\Omega_{\Omega+1}+1)$, $\psi_0(\Omega_{\Omega+1}\cdot2)$ 的无条件标签.** 对一切环境与证据. OmegaPlus1 的同名定理以 `HΩ̂` 为前提, 那个前提在修正的树上已是定理 (`HΩ̂ᵍ`).
> 2. **决定性检验 (§4).** `TΨ³-label`: $\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))=\psi_0(\Omega_{\Omega+1})[2]$ 的标签, 树用到 `Ω̂A 2`. `Pts.TO-pt n`: 第 $n$ 点, 对一切 $n$.
> 3. **非空 (§5).** 前提已被证明, 所以没有空真的问题; `TO-closed` 是闭合环境上的具体证书. 第 1 点与 Uniform3Full 的 `TΩ2-label` 计值后 $\cong$ (`agree-pt1`). `H1-again` 经一般定理重证 `H1ʰ`.
> 4. **没有改树.** 没有新的折叠子句, 没有新的编译否定.
>
> OmegaPlus1 的 `Tower` 不能直接实例化: 它把深度 0 写死成 Uniform2 的 `GA0`, 而且建在 Uniform2 的树上. 本文在修正的树上把同一组规则对全类 `Gc` 重放一遍. 后续阶段的评估在 §6, 那是纸面的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3OmegaPlus1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; walkˢ; kind; kl; kc)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; cmpᵀ; sucT; gt) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; tO-NF; walk)
open import OCF.Align.Stage2 using (Ωᵗ; tO; Lab-uniq)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Decouple using (Idx)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (πw; γW; gtW; cofW)
open import OCF.Align.OmegaPlus1Base using (Ω⁺¹; gtΩ; gtΩΩ; γΩ; fs-tO; nfγ; tO+1; tO·2; tO+1-NF; tO·2-NF; fs-tO·2)
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3SqA using (LW0→LW)
open import OCF.Align.Uniform3Hon
open GRᴬ
open import OCF.Align.Uniform3 using (one₀; lab-one₀)
open import OCF.Align.Uniform3Full using (∅ᴿ-goodʰ; TΩ2-label; GA1ʰ; ga1ʰ)
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2Fold using (HΩ̂ᵍ; G1-of)
```

## §1 全类上的规则

```agda
FLg-re : ∀ d {φ ψ ζ} → (∀ {K} → InF K ψ → InF K φ) → FLg d φ ζ → FLg d ψ ζ
FLg-re zero    f F k = F (f k)
FLg-re (suc d) f F k = F (f k)

wkG : ∀ d {φ ψ} {X : A d φ} {u} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) → Gc d X u → Gc d (wk d le X) u
wkG d le f G = FLg-re d f (proj₁ G) , wkH d le (proj₂ G)

appG : ∀ d {φ} {X : A (suc d) φ} {ζ fl} {Q : A d fl} {ρ} → Gc (suc d) X ζ → Gc d Q ρ → Gc d (X Q) (ρ ++ ψΩᵗ ζ)
appG d GX GQ = FLg-rep d (proj₁ GQ) (proj₁ GX) 0 , apH d (proj₂ GX) GQ

GSd : ∀ d {φ} → Sym φ → T → Set
GSd d X x = ∀ {fl} {P : A d fl} {π} → Gc d P π → Gc d (X d P) (π ++ x)

GEd : ∀ d {φ} → Sym φ → T → Set
GEd d X x = ∀ {fl} {P : A d fl} → Gc d P [] → Gc d (X d P) x

strip∅ : ∀ {φ K} → InF K (φ ⊔ fz) → InF K φ
strip∅ (inl k) = k
strip∅ (inr ())

good∅d : ∀ d → GSd d ∅ᵀ []
good∅d d {fl} {P} {π} GP = subst (Gc d (∅ᵀ d P)) (sym (++-identityʳ π)) (wkG d proj₁ strip∅ GP)

GE∅ : ∀ d → GEd d ∅ᵀ []
GE∅ d = good∅d d

reassoc : ∀ {a b c K} → InF K (a ⊔ (b ⊔ c)) → InF K ((a ⊔ b) ⊔ c)
reassoc (inl k) = inl (inl k)
reassoc (inr (inl k)) = inl (inr k)
reassoc (inr (inr k)) = inr k

goodE⊕ : ∀ d {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GEd d X x → GSd d Y y → GEd d (X ⊕ Y) (x ++ y)
goodE⊕ d GX GY GP = wkG d _ reassoc (GY (GX GP))

goodΨ : ∀ d {φ} {Y : Sym φ} {y} → GEd (suc d) Y y → GSd d (Ψ Y) (ψΩᵗ y)
goodΨ d GY GP = appG d (GY (HΩ̂ᵍ d)) GP
```

## §2 $\Omega$ 层的行

目标在 $\Omega$ 或可数处, `cmpᵀ (Ω+1) w` 都是 `gt`, 共尾度坍缩为 $\omega$. 所以 **$\ge1$ 层的行就是普通的 `limWd`**: `limΩ` 不需要对 $d$ 另做归纳, 只在深度 0 用一次 `gtΩ`.

```agda
module _ {ps : T} {y : PT} {ys : T} (c : cof (y ∷ ys) ≡ cΩ Ωᵗ) where
  cωΩ⁺ : cof (ψᵗ Ωᵗ (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  cωΩ⁺ = trans (cofW Ωᵗ ps y ys) (trans (cong (E.cofA Ωᵗ) c) (cong (E.cofψ₊ Ωᵗ Ωᵗ) gtΩΩ))

  fsΩ⁺ : ∀ n → fsn (ψᵗ Ωᵗ (ps ++ (y ∷ ys)) ∷ []) n ≡ ψΩᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))
  fsΩ⁺ n = gtW Ωᵗ ps y ys Ωᵗ c gtΩΩ n

  limΩW : ∀ d {c′ φ} {F : ℕ → A d φ} → (∀ n → Wd c′ d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → Wd c′ d (limA d F) (ps ++ (y ∷ ys))
  limΩW zero {F = F} h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w Ωᵗ) (gtΩ Iw))))
       (λ n → subst (LabL₊ _ Ll _) (sym (gtW w ps y ys Ωᵗ c (gtΩ Iw) n)) (proj₁ (h n ev p Iw ei ki u))) ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (gtW w ps y ys Ωᵗ c (gtΩ Iw) n)) (proj₂ (h n ev p Iw ei ki u)))
  limΩW (suc d) {c′} {F = F} h = λ u {_} {Q} {ρ} Fl hQ →
    limWd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} cωΩ⁺
          (λ m → subst (λ v → Wd _ d (F m Q) (ρ ++ v)) (sym (fsΩ⁺ m)) (h m u Fl hQ))

  limΩO : ∀ d {φ} {F : ℕ → A d φ} → (∀ n → Od d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → Od d (limA d F) (ps ++ (y ∷ ys))
  limΩO zero {F = F} h = λ ev p nu →
    let cω′ = trans (cofW [] ps y ys) (cong (E.cofA []) c) in
    let Rn = λ n → h n ev p (subst NF₁ (gtW [] ps y ys Ωᵗ c refl n) (NF₁-fsn nu cω′ n)) in
    limᴸ nu cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (gtW [] ps y ys Ωᵗ c refl n)) (proj₂ (Rn n)))
  limΩO (suc d) {F = F} h {Q = Q} {ρ = ρ} G =
    limOd d {ps = ρ} {y = ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {ys = []} {F = λ m → F m Q} cωΩ⁺
          (λ m → subst (λ v → Od d (F m Q) (ρ ++ v)) (sym (fsΩ⁺ m)) (h m G))

  limΩH : ∀ d {φ} {F : ℕ → A d φ} → (∀ n → Hd d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → Hd d (limA d F) (ps ++ (y ∷ ys))
  limΩH zero {F = F} h =
    grᴬ (LW0→LW (LWʰ→ w)) (limΩO zero {F = F} (λ n → g0ᴬ (proj₁ (h n)))) (limRd zero (λ n → gRᴬ (proj₁ (h n)))) , w
    where
    w = limΩW zero {F = F} (λ n → proj₂ (h n))
  limΩH (suc d) {F = F} h =
    (λ {c′} → limΩW (suc d) {F = F} (λ n → proj₁ (h n))) ,
    limΩO (suc d) {F = F} (λ n → proj₁ (proj₂ (h n))) ,
    limRd (suc d) (λ n → proj₂ (proj₂ (h n)))
```

## §3 $\Omega_{\Omega+1}$ 的替身

`ΓS`/`Ω⁺` 与 OmegaPlus1Base §3 逐字, 只是建在修正的树上. 归约定理不再有 `HΩ̂` 前提: `goodΨ` 里已经用了 `HΩ̂ᵍ`. 地板见证经 `FLg-ext`: 空标签底的地板在 $d=0$ 没有出现可用 (`Occ w []` 空), 在 $d\ge1$ 是 "一切 $\psi_\Omega(b)$".

```agda
module OmegaPlus {φ} (X : Sym φ) where
  ΓF : ℕ → Flr
  ΓF zero    = φ ⊔ (fk zero ⊔ fz)
  ΓF (suc n) = φ ⊔ (fk zero ⊔ ΓF n)

  ΓS : ∀ n → Sym (ΓF n)
  ΓS zero    = X ⊕ Ψ ∅ᵀ
  ΓS (suc n) = X ⊕ Ψ (ΓS n)

  evΓ : ∀ n {ℓ} → Ev ℓ (φ ⊔ fk zero) → Ev ℓ (ΓF n)
  evΓ zero    e = proj₁ e , (proj₂ e , tt)
  evΓ (suc n) e = proj₁ e , (proj₂ e , evΓ n e)

  leΓ : ∀ n {fl ℓ} → Ev ℓ (fl ⊔ (φ ⊔ fk zero)) → Ev ℓ (fl ⊔ ΓF n)
  leΓ n e = proj₁ e , evΓ n (proj₂ e)

  Ω⁺ : Sym (φ ⊔ fk zero)
  Ω⁺ d P = limA d (λ n → wk d (leΓ n) (ΓS n d P))

FLg-ext : ∀ d {φ ζ} y → FLg d φ ζ → FLg d φ (ζ ++ y)
FLg-ext zero    y F = FlrLab-mono (OccPre y) F
FLg-ext (suc d) y F = FlrLabΩ-ext y F

FLg-⊔ : ∀ d {a b ζ} → FLg d a ζ → FLg d b ζ → FLg d (a ⊔ b) ζ
FLg-⊔ zero    F G (inl k) = F k
FLg-⊔ zero    F G (inr k) = G k
FLg-⊔ (suc d) F G (inl k) = F k
FLg-⊔ (suc d) F G (inr k) = G k

FLg-z : ∀ d {ζ} → FLg d (fk zero) ζ
FLg-z zero    ink = inj₁ z≅
FLg-z (suc d) ink = inj₁ z≅

module Reduce {φ} (X : Sym φ) where
  open OmegaPlus X

  goodΓ : ∀ {x} → (∀ d → GEd d X x) → ∀ n d → GEd d (ΓS n) (x ++ γΩ x n)
  goodΓ {x} GX zero d =
    goodE⊕ d {X = X} {Y = Ψ ∅ᵀ} {x = x} {y = ψΩᵗ []} (GX d) (goodΨ d {Y = ∅ᵀ} {y = []} (GE∅ (suc d)))
  goodΓ {x} GX (suc n) d =
    goodE⊕ d {X = X} {Y = Ψ (ΓS n)} {x = x} {y = ψΩᵗ (x ++ γΩ x n)} (GX d)
           (goodΨ d {Y = ΓS n} {y = x ++ γΩ x n} (goodΓ GX n (suc d)))

  goodΩ⁺ : ∀ {x} → (∀ d → GEd d X x) → ∀ d → GEd d Ω⁺ (x ++ (Ω⁺¹ ∷ []))
  goodΩ⁺ {x} GX d {fl} {P} GP =
    FLg-⊔ d (FLg-ext d (x ++ (Ω⁺¹ ∷ [])) (proj₁ GP))
            (FLg-⊔ d (FLg-ext d (Ω⁺¹ ∷ []) (FLg-re d inr (proj₁ (GX d GP)))) (FLg-z d)) ,
    limΩH {ps = x} {y = Ω⁺¹} {ys = []} refl d {F = λ n → wk d (leΓ n) (ΓS n d P)}
          (λ n → wkH d (leΓ n) (proj₂ (goodΓ GX n d GP)))
```

## §4 决定性检验与标签定理

```agda
labelE : ∀ {φ} {X : Sym φ} {x} → GEd 0 X x → NF₁ (ψ₀ᵗ x) → ∀ {ℓ} (ev : Ev ℓ (fz ⊔ φ)) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ X ev z) (ψ₀ᵗ x)
labelE G nf ev z = H→O 0 (proj₂ (G ∅ᴿ-goodʰ)) ev z nf

-- 深度 2 的闭包
H2 : Gc 3 {fk zero} (Ω̂A 2) []
H2 = HΩ̂ᵍ 2

-- ψ₀(ψ_Ω(ψ_Ω(Ω_Ω))) = ψ₀(Ω_{Ω+1})[2]: 用到 Ω̂A 2
TΨ³-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ (Ψ ∅ᵀ))) ev z) (ψ₀ᵗ (γΩ [] 2))
TΨ³-label = labelE {X = Ψ (Ψ (Ψ ∅ᵀ))} {x = γΩ [] 2}
  (goodΨ 0 {Y = Ψ (Ψ ∅ᵀ)} {y = γΩ [] 1} (goodΨ 1 {Y = Ψ ∅ᵀ} {y = γΩ [] 0} (goodΨ 2 {Y = ∅ᵀ} {y = []} (GE∅ 3))))
  (nfγ 2)

GEΩ⁺ : ∀ d → GEd d (OmegaPlus.Ω⁺ ∅ᵀ) (Ω⁺¹ ∷ [])
GEΩ⁺ = Reduce.goodΩ⁺ ∅ᵀ {x = []} GE∅

-- 第 n 点: 对一切 n, 无条件
module Pts where
  open OmegaPlus ∅ᵀ

  pt : ℕ → ∀ {ℓ} → Ev ℓ (fz ⊔ (fz ⊔ fk zero)) → zero <ᴵ ℓ → Ordˢ zero
  pt n ev z = wk 0 (leΓ n) (ΓS n 0 ∅ᴿ) ev z

  pt-walk : ∀ n {ℓ} ev (z : zero <ᴵ ℓ) → walkˢ (ψᵀ Ω⁺ ev z) (n ∷ []) ≡ pt n ev z
  pt-walk n ev z = refl

  TO-pt : ∀ n {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (pt n ev z) (ψ₀ᵗ (γΩ [] n))
  TO-pt n ev z = H→O 0 (wkH 0 (leΓ n) (proj₂ (Reduce.goodΓ ∅ᵀ {x = []} GE∅ n 0 ∅ᴿ-goodʰ))) ev z (nfγ n)

-- ψ₀(Ω_{Ω+1})
TO-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ) ev z) tO
TO-label = labelE {X = OmegaPlus.Ω⁺ ∅ᵀ} {x = Ω⁺¹ ∷ []} (GEΩ⁺ 0) tO-NF

goodTl0ʰ : ∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ᴬ t → FlrLab (flo k) y → GSd 0 (tlᵀ (flo k) (cvFlo k) t) y
goodTl0ʰ l ex Fl (F , GP , HP) = FlrLab-⊔ F Fl , tlGRᴬ GP l ex , TlWʰ.tlWVʰ HP l

-- ψ₀(Ω_{Ω+1}+1)
TO+1-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀) ev z) tO+1
TO+1-label = labelE {X = OmegaPlus.Ω⁺ ∅ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀} {x = Ω⁺¹ ∷ 𝟏 ∷ []}
  (goodE⊕ 0 {X = OmegaPlus.Ω⁺ ∅ᵀ} {Y = tlᵀ (flo zero) (cvFlo zero) one₀} {x = Ω⁺¹ ∷ []} {y = 𝟏 ∷ []}
          (GEΩ⁺ 0) (goodTl0ʰ lab-one₀ (sᴬ zᴬ) FlrLab-fz))
  tO+1-NF

-- ψ₀(Ω_{Ω+1}·2)
TO·2-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ (OmegaPlus.Ω⁺ ∅ᵀ)) ev z) tO·2
TO·2-label = labelE {X = OmegaPlus.Ω⁺ (OmegaPlus.Ω⁺ ∅ᵀ)} {x = Ω⁺¹ ∷ Ω⁺¹ ∷ []} (Reduce.goodΩ⁺ (OmegaPlus.Ω⁺ ∅ᵀ) {x = Ω⁺¹ ∷ []} GEΩ⁺ 0) tO·2-NF
```

## §5 复查

**非空.** 闭合的环境 `(tt , (tt , λ q → q))` 上 `TOᵀ` 的证书是真实的项; 树的种类与 OmegaPlus1Base §6 相同. **与旧结果一致.** 第 1 点与 Uniform3Full 的 `TΩ2-label` 同一标签, 计值后 $\cong$ (`agree-pt1`). `H1ʰ` 由一般定理重新得到 (`H1-again`), 证明不经过 Uniform3Full 的 `Main`. **记号侧.** `walk tO [2]` 字面是 $\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))$.

```agda
TOᵀ : Ordˢ zero
TOᵀ = ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ) {i = zero} {ℓ = one} (tt , (tt , (λ q → q))) zero

TO-closed : Lab₀ TOᵀ tO
TO-closed = TO-label (tt , (tt , (λ q → q))) zero

_ : kind TOᵀ ≡ kl
_ = refl
_ : kind (walkˢ TOᵀ (0 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ TOᵀ (1 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ TOᵀ (2 ∷ [])) ≡ kc one
_ = refl

_ : walk tO (2 ∷ []) ≡ ψ₀ᵗ (ψΩᵗ (ψΩᵗ (ΩΩ ∷ [])))
_ = refl

_ : ψ₀ᵗ (γΩ [] 1) ≡ tΩ2
_ = refl

agree-pt1 : ∀ {ℓ ℓ′} ev (z : zero <ᴵ ℓ) (ev′ : Ev ℓ′ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z′ : zero <ᴵ ℓ′) →
            forceᴸ _ (proj₁ (Pts.TO-pt 1 ev z)) ≅ forceᴸ _ (proj₁ (TΩ2-label ev′ z′))
agree-pt1 ev z ev′ z′ = Lab-uniq (proj₂ (Pts.TO-pt 1 ev z)) (proj₂ (TΩ2-label ev′ z′))

G1-back : ∀ {φ} {E : A 1 φ} {ζ} → Gc 1 E ζ → GA1ʰ E ζ
G1-back G = ga1ʰ (proj₁ G) (λ {c} F hP → proj₁ (proj₂ G) {c} (≼-refl c) F hP) (proj₁ (proj₂ (proj₂ G))) (proj₂ (proj₂ (proj₂ G)))

H1-again : ∀ {fl} {E : A 1 fl} {ζ} → GA1ʰ E ζ → GA1ʰ (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
H1-again G = G1-back (appG 1 {fk zero} {Ω̂A 1} (HΩ̂ᵍ 1) (G1-of G))
```

## §6 后续阶段的评估 (纸面)

**深度.** 深度 $d$ 与深度 1 是同一个证明, 这条现在是编译事实, 不是猜测: `goodΩ̂ d` 对 $d$ 没有归纳, 对 $d$ 递归的只有行引理, 每一步都只用 `cωΩ`/`cΩΩ`/`ωW`/`penΩ`. 随 $d$ 增长的东西是空的. 从深度 1 走到一般深度新增三件: Kripke 量化 (`Wd`), 双边互模拟 (`Rd`, 这是 Uniform3Plus1 的预言), 以及 `FWh-step` 里 $d=0$ 对 $d\ge1$ 的一处分情形. 这三件都不进树, 也不新增记号比较. 深度 0 仍是独立的 (`fold 0` 的后继子句是 `iter`, 不是 `repA`), 所以 `HΩ̂ᵍ 0` 走桥 `G1-of`.

**与 OmegaPlus1 §3–§4 的估计对照.** "换记录只需重做约 70 行" 偏低: 本文 186 行, 因为 `Tower` 写死了深度 0 和旧树; 其中 `limΩ` 行约 35 行, 比旧的 95 行少, 因为 $\ge1$ 层的行就是 `limWd`. "闭包定理是定义的 3–5 倍" 没有被推翻, 只是位置变了: 三个一般文件共 803 行, 依赖的深度 0 行引理 (Uniform3Base, Uniform3Hon, Uniform3SqABase) 不重写. 这个倍数实际落在**新阶段的深度 0 行**上, 深度因子本身消失了.

**$\psi_0(\Omega_{\Omega+2})$.** §3 的障碍原样在: `goodΩ⁺` 的结论只到 `GEd` (空底), 因为 `Ω⁺ X` 只重放 $X$. $\psi_i(P+\psi_{\Omega+1}(\zeta+\Omega_{\Omega+1}))$ 的链点含整个外层前缀 $P$, 这要求塔以 `Sym` 为底. 本文的一般化没有碰到这一点. 另有一处 §3 没有明说: 行引理的头固定是 $\psi_\Omega$. 换成 $\psi_{\Omega+1}$ 时, 共尾度 $\Omega_{\nu+1}$ 对 $\nu=\Omega$ 走 `eq` (穿透), 这是一个输入在层 $\Omega$ 上的 `limᵢ`, 而 `limᵢA` 的输入是 `Ordˢ j`, $j$ 可数. 所以这里的输入要是符号项, 是设计层的改动, 不是把 `Ωᵗ` 换成参数. §3 的 "约 300 行 + 每级 150–250 行" 没有证据支持也没有证据反对; 我认为 `A⁺` 那一层的量是对的, 行引理部分可以按本文的递归写一次, 不必每级重写, 但这也未验证.

**$\psi_0(\Omega_{\Omega\cdot2})$.** §3 的预期仍然成立: 弹出是闭包, 地板下标形如 $\Omega+c$, 没有 `Idx`. 本文把地板见证集中到 `FLΩ[_]`, `FWh`, `FHc` 三处, 所以 "`gŝ` 地板字段推广" 在深度方向上不再扩散, 但 `pickMax` 与 `Lab-oc` 仍在记号上比较, 要一起推广. 400–600 行的估计未被检验.

**未做.** $\psi_0(\Omega_{\Omega+1}\cdot k)$ 与 $\psi_0(\psi_\Omega(\Omega_{\Omega+1}))$ 的树侧由 `goodΩ⁺` 直接给出 (`GEd` 对一切深度), 缺的只是记号侧的 `NF₁`, 本文没有写. Uniform3Plus1 的字面 `GAʰ`/`HΩ̂ʰ` (输入只有 "把好帧送到好帧", 没有地板和互模拟) 既没有证明也没有否定: 这里证明的是 `Gc`, 它的输入带这两个字段, 而这两个字段确实被用到 (`copyH` 用地板, `foldR` 用互模拟).
