# 数据树上的无符号闭包定理 (十二): 证书

> 接 [UniformNF4Omega](UniformNF4Omega.lagda.md), [UniformNF4Eval](UniformNF4Eval.lagda.md). 结论先说:
>
> 1. **`Gᴺof : Gᵀ c 𝓥 x → Goodᴺ (toZ (ψ̄ x ev z))`: 闭包定理的出口.** 一行.
> 2. **`GᴺΩ̇ c`: $\psi_0(\Omega_{\Omega+c})$, 对一切 $c$, 一个定理.** `GᴺΩ̇ 0` 是 $\psi_0(\Omega_\Omega)$, `GᴺΩ̇ 1` 是 $\psi_0(\Omega_{\Omega+1})$. `GᴺΩ2 c`: $\psi_0(\Omega_{\Omega+c}\cdot2)$. `Gᴺsq`: $\psi_0(\Omega_\Omega^2)$ = `ψ̄ (ψᵒ zero (ι zero (Ω̇ 0)))`.
> 3. **`GᴺTω`: 对角线 $\psi_0(\Omega_{\Omega+\omega})$.** 单调性要 `ι` 不改变值: `Rῑ`, `R-ψι` (层号比较 `cmp<` 对 $\iota$ 透明).
> 4. **一般形式 (§2).** `good-ψ`, `good-ι`, `good-os`, `good-⊕`; `Gᴺtow n`: 塔 $x_{n+1}=\psi_\Omega(x_n+1)$, 深度任意.
> 5. **构造不读记号.** 本文件与它的依赖 (`UniformNF4Base/Rules/Strict/Class/ClassF/Good/Add/Psi/Eval/Tail/Omega`) 只用 `Uniform4Base`、值层的树与 `Goodᴺ`. 验收在 [UniformNF4Accept](UniformNF4Accept.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR; ≅ˢ-sym)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Run; InF; inl; inr; ink; Dem; _∼ᶠ_; ∼ᶠ-refl; ⊔∼; flo; cvFlo; limA)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base
open import OCF.Align.UniformNF4Base
open import OCF.Align.UniformNF4Rules
open import OCF.Align.UniformNF4Strict
open import OCF.Align.UniformNF4Class
open import OCF.Align.UniformNF4ClassF
open import OCF.Align.UniformNF4Good
open import OCF.Align.UniformNF4Add
open import OCF.Align.UniformNF4Psi
open import OCF.Align.UniformNF4Eval
open import OCF.Align.UniformNF4Tail
open import OCF.Align.UniformNF4Omega

open EvalM Ω̇G public using (T̄)
open PsiM Ω̇G public using (Psi)

Gᴺof : ∀ {c φ ℓ} {x : O c φ} → Gᵀ c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ x ev z))
Gᴺof g ev z = Good→N refl (T̄ {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺΩ̇ : ∀ c {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ c) ev z))
GᴺΩ̇ c = Gᴺof (Ω̇G c)

wfΩ̇ : ∀ c → WFl (Ω̇ c)
wfΩ̇ c = wfl (RΩ̇ c) (𝟏⊑Ω̇ c)

hoΩ̇ : ∀ c {C} → 𝓥 C → HonT (Ω̇ c) C
hoΩ̇ c x G (inr ink) = inj₂ z≅

Ω·2ᵒ : ∀ c → O c (Fl ⊔ Fl)
Ω·2ᵒ c = Ω̇ c ⊕ Ω̇ c

gΩ2 : ∀ c → Gᵀ c 𝓥 (Ω·2ᵒ c)
gΩ2 c = AddT.Add {𝓐 = 𝓥} (Ω̇G c) (wfΩ̇ c) (λ x o _ → x) (λ _ f → cxoᵀ f) (λ x → x) (hoΩ̇ c)
                 {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → wfΩ̇ c , x) (Ω̇G c)

GᴺΩ2 : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω·2ᵒ c) ev z))
GᴺΩ2 c = Gᴺof (gΩ2 c)

tsqᵒ : O 0 (Fl ⊔ Fl)
tsqᵒ = ψᵒ zero (ι zero (Ω̇ 0))

gsq : Gᵀ 0 𝓥 tsqᵒ
gsq = Psi zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Iota zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Ω̇G 0))

Gᴺsq : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ tsqᵒ ev z))
Gᴺsq = Gᴺof gsq
```

## §1 对角线

`R-ψι`: $\psi_{\Omega+t}$ 不看 $\iota$. `Rῑ`: $\bar\psi(\iota\,x)\approx\bar\psi\,x$. 跨层号的互模拟只在这里出现: 都是逐构造子.

```agda
R-ψι : ∀ {c d t φ ψ} (r r′ : t <ᴸ c) (q : c <ᴸ d) {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → Rᵒ t (ψᵒ (tr< r q) (ι q x)) (ψᵒ r′ x′)
R-ψιΩ : ∀ {c d t k φ ψ} (r r′ : t <ᴸ c) (q : c <ᴸ d) {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r₀ r₀′ : k <ᴸ c}
        {h : ∀ ξ → Us c r₀ ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r₀′ ξ → O c (ξ ⊔ ψ)} → φ ∼ᶠ ψ → LRᵒ c r₀ {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
        (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LRᵒ c r₀ z z′ → Rᵒ c (h ξ (intoU r₀ z)) (h′ ξ′ (intoU r₀′ z′))) →
        (p : Pen k t) → Rᵒ t (ψᵒΩ (tr< r q) fe (tr< r₀ q) (λ ξ z → ι q (h ξ (intoU r₀ (outU (tr< r₀ q) z)))) p) (ψᵒΩ r′ fe′ r₀′ h′ p)
chι : ∀ {c d k φ ψ} (q : c <ᴸ d) {r₀ r₀′ : k <ᴸ c} {h : ∀ ξ → Us c r₀ ξ → O c (ξ ⊔ φ)} {h′ : ∀ ξ → Us c r₀′ ξ → O c (ξ ⊔ ψ)} → φ ∼ᶠ ψ → LRᵒ c r₀ {Fl} {Fl} (Ω̇ k) (Ω̇ k) →
      (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k ξ′) → LRᵒ c r₀ z z′ → Rᵒ c (h ξ (intoU r₀ z)) (h′ ξ′ (intoU r₀′ z′))) →
      ∀ n → Rᵒ k (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ (tr< r₀ q) (ι q (h (Fl ⊔ φ) (intoU r₀ (outU (tr< r₀ q) (intoU (tr< r₀ q) z))))))) n)
                 (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r₀′ (h′ (Fl ⊔ ψ) (intoU r₀′ z)))) n)
R-ψι {t = t} r r′ q rz = rwk (RΩ̇ t)
R-ψι r r′ q (rs sa e) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-ψι r r′ q e))
R-ψι r r′ q (rl h) = rl (λ n → R-ψι r r′ q (h n))
R-ψι r r′ q (ri e h) = ri e (λ x y d → R-ψι r r′ q (h x y d))
R-ψι r r′ q (rŝ e u h) = rŝ e (R-ψι r r′ q u) (λ η ee η′ e′ d → R-ψι r r′ q (h η ee η′ e′ d))
R-ψι r r′ q (rĉ e dz dg u h) = rĉ e dz dg (R-ψι r r′ q u) (λ η ee η′ e′ d → R-ψι r r′ q (h η ee η′ e′ d))
R-ψι r r′ q (rclo s u h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψι r r′ q u)) (λ η η′ d → rwk (R-ψι r r′ q (h η η′ d))))
R-ψι r r′ q (rwkˡ u) = rwkˡ (R-ψι r r′ q u)
R-ψι r r′ q (rwkʳ u) = rwkʳ (R-ψι r r′ q u)
R-ψι {t = t} r r′ q (rΩ {k = k} {fe = fe} {fe′ = fe′} {r = r₀} {r′ = r₀′} {h = h} {h′ = h′} refl s b f) = R-ψιΩ r r′ q {fe} {fe′} {r₀} {r₀′} {h} {h′} s b f (cmp< k t)

R-ψιΩ {t = t} r r′ q {r₀ = r₀} {r₀′ = r₀′} {h = h} {h′ = h′} s b f (pen p) =
  rΩ {r = p} {r′ = p} refl (⊔∼ (∼ᶠ-refl Fl) s) (intoR p (outR r₀ b))
     (λ ξ ξ′ e z z′ l → subst₂ (λ w w′ → Rᵒ t (owk swp (ψᵒ (tr< r q) (ι q (h ξ (intoU r₀ w))))) (owk swp (ψᵒ r′ (h′ ξ′ (intoU r₀′ w′)))))
                                (sym (trans (out-intoU′ (tr< r₀ q) (outU p (intoU p z))) (out-intoU′ p z))) (sym (out-intoU′ p z′))
                                (rwk (R-ψι r r′ q (f ξ ξ′ e z z′ (intoR r₀ (outR p l))))))
R-ψιΩ {t = t} {φ = φ} {ψ = ψ} r r′ q {r₀ = r₀} {r₀′ = r₀′} {h = h} {h′ = h′} s b f chain =
  rl (λ n → rwk (subst (λ w → Rᵒ t (ψᵒ (tr< r q) (ι q (h (Fl ⊔ φ) (intoU r₀ w)))) (ψᵒ r′ (h′ (Fl ⊔ ψ) (intoU r₀′ _)))) (sym (out-intoU′ (tr< r₀ q) _))
                  (R-ψι r r′ q (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR r₀ (chι q {r₀ = r₀} {r₀′ = r₀′} {h = h} {h′ = h′} s b f n))))))

chι q {r₀ = r₀} s b f zero = rwk (outR r₀ b)
chι {k = k} {φ = φ} {ψ = ψ} q {r₀ = r₀} {r₀′ = r₀′} {h = h} {h′ = h′} s b f (suc n) =
  rwk (subst (λ w → Rᵒ k (ψᵒ (tr< r₀ q) (ι q (h (Fl ⊔ φ) (intoU r₀ w)))) (ψᵒ r₀′ (h′ (Fl ⊔ ψ) (intoU r₀′ _)))) (sym (out-intoU′ (tr< r₀ q) _))
       (R-ψι r₀ r₀′ q (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR r₀ (chι q {r₀ = r₀} {r₀′ = r₀′} {h = h} {h′ = h′} s b f n)))))

Rῑ : ∀ {c d φ ψ} (q : c <ᴸ d) {x : O c φ} {x′ : O c ψ} → Rᵒ c x x′ → ψ̄ (ι q x) ≈ᴿ ψ̄ x′
Rῑ q rz = wkR _ _ r∅
Rῑ q (rs s r) = sucR (Rῑ q r)
Rῑ q (rl h) = limR (λ n → Rῑ q (h n))
Rῑ q (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ (ι q (f x))} {H′ = λ x → ψ̄ (f′ x)} e (λ x y d → Rῑ q (h x y d))
Rῑ q (rŝ e r h) = ŝR e (Rῑ q r) (λ η ee η′ e′ d → Rῑ q (h η ee η′ e′ d))
Rῑ q (rĉ e dz dg r h) = ĉR e dz dg (Rῑ q r) (λ η ee η′ e′ d → Rῑ q (h η ee η′ e′ d))
Rῑ q (rclo {t = t} {t′} {g} {g′} s r h) = cloR {t = ψ̄ (ι q t)} {g = λ η → ψ̄ (ι q (g η))} {t′ = ψ̄ t′} {g′ = λ η → ψ̄ (g′ η)} s (Rῑ q r) (λ η η′ d → Rῑ q (h η η′ d))
Rῑ q (rwkˡ {le = le} r) = wkR le (λ e → e) (Rῑ q r)
Rῑ q (rwkʳ {le′ = le′} r) = wkR (λ e → e) le′ (Rῑ q r)
Rῑ {φ = φ} {ψ = ψ} q (rΩ {k = k} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} refl s b f) =
  limR (λ n → wkR _ _ (subst (λ w → ψ̄ (ι q (h φ (intoU r w))) ≈ᴿ ψ̄ (h′ ψ (intoU r′ _))) (sym (out-intoU′ (tr< r q) _))
                         (Rῑ q (f φ ψ s _ _ (intoR r (chE n))))))
  where
  chE : ∀ n → Rᵒ k (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ (tr< r q) (ι q (h φ (intoU r (outU (tr< r q) (intoU (tr< r q) z))))))) n)
                   (chainᵒ fe′ (λ z → owk (λ v → fe′ v , (v , v)) (ψᵒ r′ (h′ ψ (intoU r′ z)))) n)
  chE zero = rwk (outR r b)
  chE (suc n) = rwk (subst (λ w → Rᵒ k (ψᵒ (tr< r q) (ι q (h φ (intoU r w)))) (ψᵒ r′ (h′ ψ (intoU r′ _)))) (sym (out-intoU′ (tr< r q) _))
                       (R-ψι r r′ q (f φ ψ s _ _ (intoR r (chE n)))))

Tω : Run Fl
Tω = limA 0 (λ n → ψ̄ (Ω̇ n))

monoΩ̇ : ∀ n {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) (G : Goodᴺ (toZ (ψ̄ (Ω̇ n) ev z))) (G′ : Goodᴺ (toZ (ψ̄ (Ω̇ (suc n)) ev z))) → forceᴺ _ G ⊑ forceᴺ _ G′
monoΩ̇ n ev z G (gl Gs st) = ⊑-lim 0 (≅→⊑ (forceᴺ-≅ (toZ-≅ (≅ˢ-sym (Rῑ zero (RΩ̇ n) ev z ev z z≅))) G (Gs 0)))

GᴺTω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tω ev z))
GᴺTω ev z = gl (λ n → GᴺΩ̇ n ev z) (λ n → monoΩ̇ n ev z (GᴺΩ̇ n ev z) (GᴺΩ̇ (suc n) ev z))
```

## §2 闭包定理的一般形式与压力测试

`Z₀ φ`: 地板 $\varphi$ 的项都平凡 (只含 $K=0$). 这时 $\psi$, $\iota$, $\oplus$, 后继都保持 `Gᵀ c 𝓥`. 下面的塔 $x_{n+1}=\psi_\Omega(\iota\,x_n+1)$ 每一格都穿过 $\psi$ 的后继行, 深度任意; 帧路线在第 2 格要 "副本的世界" ([UniformNF3D3V](UniformNF3D3V.lagda.md)), 这里是 `Psi` 的一次调用. 这些点没有验收 (`Uniform4Label` 没有写它们的标签), 只有证书.

```agda
Z₀ : Flr → Set
Z₀ φ = ∀ {K} (q : InF K φ) {X : Ordᴵ} → Dem X q

Z-Fl : Z₀ Fl
Z-Fl (inr ink) = inj₂ z≅

Z-⊔ : ∀ {a b} → Z₀ a → Z₀ b → Z₀ (a ⊔ b)
Z-⊔ za zb (inl q) = za q
Z-⊔ za zb (inr q) = zb q

good-ψ : ∀ {c t φ} (q : t <ᴸ c) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ t 𝓥 (ψᵒ q x)
good-ψ q = Psi q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-ι : ∀ {c d φ} (q : c <ᴸ d) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ d 𝓥 (ι q x)
good-ι q = Iota q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-os : ∀ {c φ} {a : O c φ} → Z₀ φ → Gᵀ c 𝓥 a → Gᵀ c 𝓥 (os a)
good-os z g = gs 𝓥 (λ x → x) g (λ _ f → cxoᵀ f) (λ x _ _ → x) (λ _ G q → z q)

good-⊕ : ∀ {c α φ} {W : O c α} {y : O c φ} → Z₀ α → WFl W → Gᵀ c 𝓥 W → Gᵀ c 𝓥 y → Gᵀ c 𝓥 (W ⊕ y)
good-⊕ {φ = φ} z w gW g = AddT.Add {𝓐 = 𝓥} gW w (λ x _ _ → x) (λ _ f → cxoᵀ f) (λ x → x) (λ _ G q → z q)
                                {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → w , x) g

Flᶠ : ℕ → Flr
Flᶠ zero    = Fl
Flᶠ (suc n) = Fl ⊔ Flᶠ n

tow : ∀ n → O 0 (Flᶠ n)
tow zero    = Ω̇ 0
tow (suc n) = ψᵒ zero (os (ι zero (tow n)))

Z-tow : ∀ n → Z₀ (Flᶠ n)
Z-tow zero    = Z-Fl
Z-tow (suc n) = Z-⊔ Z-Fl (Z-tow n)

gtow : ∀ n → Gᵀ 0 𝓥 (tow n)
gtow zero    = Ω̇G 0
gtow (suc n) = good-ψ zero (good-os (Z-tow n) (good-ι zero (gtow n)))

Gᴺtow : ∀ n {ℓ} (ev : Ev ℓ (Flᶠ n)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (tow n) ev z))
Gᴺtow n = Gᴺof (gtow n)

Ω+1ᵒ : ∀ c → O c (Fl ⊔ fz)
Ω+1ᵒ c = Ω̇ c ⊕ tl fz (cvFlo zero) 𝟏

gone : ∀ {c} → Gᵀ c 𝓥 (tl fz (cvFlo zero) 𝟏)
gone = TL {k = zero} {𝓖 = 𝓥} {𝓧 = isId} refl (λ x → x) (b1 z≅) (s≅ z≅ z≅)

GᴺΩ+1 : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ fz)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω+1ᵒ c) ev z))
GᴺΩ+1 c = Gᴺof (good-⊕ Z-Fl (wfΩ̇ c) (Ω̇G c) gone)
```

## §3 判据: 一个闭包定理

下面的话是判断, 依据是上面编译过的定理.

**帧路线要分开论证的四条轴, 这里都不进证明.**

| 轴 | 帧路线 | 这里 |
|---|---|---|
| 帧数 | `Stage`, `stΩ` | `pa W C` 一个构造子; `Psi`, `Add` 不读 $W$ 的形状 |
| 地板形状 | `LoD`, `dm`, `Fk₁` 的 `Ab` | `gclo` 的 `dt`/`dg`, 两半: $W$ 的由 `hoA`, $y$ 的拉回 |
| 深度 | `FF₁`, `Frm`, `Fr`/`Sp`, 世界 `RF` | `pψ q C` 一个构造子; `Gᴺtow n` 对一切深度 |
| 层号 $c$ | 帧式的塔在 $\psi_{\Omega+1}$ 失败 ([Uniform4Expt](Uniform4Expt.lagda.md)) | `Ω̇G` 对 $c$ 递归只有 `gΩ` 一行, 主定理 `Psi`, `T̄` 对 $c$, $t$ 都没有归纳 |

**没有按阶段的支配论证.** 支配只在两处: `Brᵀ` (对任意上下文, 只写一次) 与 `Bd` (`T̄` 的 `gclo` 行, 由 `dt`/`dg` 读地板).

**"底抬高" 不需要.** `ψᵒ` 的后继行是 $W\oplus X$, $W=\mathrm{rep}(n+1)\sqsupseteq X$, 所以上下文 `pψ q (pa W C)` 压在 `pψ q C` 之上, 这正是 `clk`. [UniformNF3D2U](UniformNF3D2U.lagda.md) §4 担心的 "$F_t\,P\,Q\sqsubseteq F_t\,P\,B$" 不是被证明的, 而是不问的: `Gᵀ` 的类对上下文量化, $B$ 就在上下文里. 这与 [UniformNF3D3V](UniformNF3D3V.lagda.md) §1 的结论一致 (`clk` 直接给出成员, `¬BaseRaise` 说只有 $B\sqsupseteq Q$ 不够), 区别在 D3 要把点带进世界 `RF`, 这里 $W\sqsupseteq X$ 是 `Xfl` 一行.

**$\oplus$ 不结合不是障碍.** $W\oplus(r\oplus y)$ 里 $y$ 的上下文是 `pa r (pa W C)`. 从来不需要 $(W\oplus r)\oplus y$, 所以不要规范化, 也不要互模拟不变的 `Good`.

**先前的纸面估计, 修正两条.** "`oΩ` 需要自己的观测": 不需要. 输入的上下文是 `W ξ C : Cx m ξ`, 还是同一族. "约 2500 行新证明": 代码共约 3000 行, 其中新写约 1800 行, 约 1100 行是 D1 与 Uniform4Rel 的克隆.

**树侧逼出的:** `Cx`/`wkC` (取消 `pw`), `gclo` 的形状, `AboveΩ`, `Ctx` 的 `nzA` (由退化极限层逼出), `at≡`. **看带标签证明定形状的:** `Gᵀ` 的行与 `Ld` 一一对应, `zG` 与 `chainL` 同形, `Psi` 的分情况 (`cmp<`) 照 `Ld-ψ`.

**往 $\psi_0(\Omega_{\Omega\cdot2})$ (判断, 没有编译).** 这里的 `Cx`, `Gᵀ`, `Add`, `Psi` 不读层号语法, 只读 `O` 的构造子. [Uniform5Top](Uniform5Top.lagda.md) 的树是 [Uniform4Two](Uniform4Two.lagda.md) 的 `TΩ·2`, 层号从 ℕ 换成 `Ordᴵ`: `cmp<` 换成 `<ᴵ-dec` 的三歧, 穿透分支多 `tr⁻O`. 克隆时要加: 上下文的 `tr⁻`-构造子或 `trO` 对 `Gᵀ` 的搬运 (值层的 `Bb` 已经是这个形状, Uniform5Tr 说标签版本是 40 行新内容); `Ω̇` 的外层闭包 (链 $\gamma_{n+1}=\psi_0(\Omega_{\Omega+\gamma_n})$) 在值层是 `gc`, 单调性要 $\gamma_n$ 层号上的 `Ω̇` 单调, 对应这里的 `monoΩ̇` 与 `Rῑ`. 没有看到新的数学, 但这是未编译的判断. 再往上 (`Syn`, `oev`) 的跨 $\ell$ 互模拟, Uniform5 自己也记为未写, 我预期那里是第一个真正的问题.
