# 层号参数化的无符号闭包定理 (十二): 证书

> 接 [UniformNF5Omega](UniformNF5Omega.lagda.md), [UniformNF5Eval](UniformNF5Eval.lagda.md). 结论先说:
>
> 1. **`GᴺΩ̇ η`: $\psi_0(\Omega_{\Omega+\eta})$, 对一切 $\eta:$ `Ordᴵ`, 一个定理.** 不限于 `toLevel` 的像, 不限于有穷, 含退化的极限层. ℕ 是实例 (`GᴺΩ̇ (natᴵ n)`), 不是另一份克隆.
> 2. **`GᴺTΩ·2`: $\psi_0(\Omega_{\Omega\cdot2})$, 树是 [Uniform4Two](Uniform4Two.lagda.md) 的 `TΩ·2`, 未改动.** 这是数据树路线上第一个链点喂回下标的闭包: $\gamma_{n+1}=\psi_0(\Omega_{\Omega+\gamma_n})$. 它不要新的吸收者: 外层是一个 `bŝ`, 分支由 `T̄` 对 `Ω̇G η` 给 (任意 $\eta$, 所以链点是什么都行), 单调由 `Vm` (§2), 界由 `readT`, 与树层 `gclo` 的行逐字对应. `GoodTΩ·2`: 对一切目标 $i$ 都是 `Good`, 目标 0 是实例.
> 3. **判据见 §4.** 每阶段输入: `Uniform4Two` 的 `Ω̇` 的子句与一个 `<ᴵ-dec`. 定理本身在 `Ordᴵ` 上写一次. 新的证明义务只有三件, 都是一次性的: 跨层 `Rᵒ`, `ptr`/`ptr⁻` 两行上下文 (`Trᵀ`), $\dot\Omega$ 对层号单调 (`Ωm`, `Vm`).
> 4. **构造不读记号.** 本文件与它的依赖 (`UniformNF5Base/Rules/Strict/Class/ClassF/Good/Tr/Add/Psi/Eval/Tail/Omega`) 只用 `Uniform4Base`、`Uniform4Two`、值层的树与 `Goodᴺ`. 验收在 [UniformNF5Accept](UniformNF5Accept.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; toZ-≅; _≈ᴿ_; ≅ˢ-sym; cloR; wkR)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; Run; InF; inl; inr; ink; Dem; _∼ᶠ_; ∼ᶠ-refl; ⊔∼; flo; cvFlo; limA; wk; cloA; Top; bound; FB; liftEv; Bd; Fc; evF; iF; FM; ubd)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two
open import OCF.Align.UniformNF5Base
open import OCF.Align.UniformNF5Rules
open import OCF.Align.UniformNF5Strict
open import OCF.Align.UniformNF5Class
open import OCF.Align.UniformNF5ClassF
open import OCF.Align.UniformNF5Good
open import OCF.Align.UniformNF5Add
open import OCF.Align.UniformNF5Psi
open import OCF.Align.UniformNF5Eval
open import OCF.Align.UniformNF5Tail
open import OCF.Align.UniformNF5Omega

open EvalM Ω̇G public using (T̄)
open PsiM Ω̇G public using (Psi)

Gᴺof : ∀ {c φ ℓ} {x : O c φ} → Gᵀ c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ x ev z))
Gᴺof g ev z = Good→N refl (T̄ {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺΩ̇ : ∀ η {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ η) ev z))
GᴺΩ̇ η = Gᴺof (Ω̇G η)
```

## §1 ℕ 的实例, 加法与塔

旧的 $c:\mathbb N$ 就是 `natᴵ c`: 没有别的定理. `natᴵ`-层的 `GᴺΩ̇`, `GᴺΩ2`, `Gᴺsq`, `Gᴺtow` 与 [UniformNF4Main](UniformNF4Main.lagda.md) 同形, 它们的证明不看层号的语法. 对角线 $\psi_0(\Omega_{\Omega+\omega})$ 现在只是 `GᴺΩ̇ ωᴵ`, 不再需要单独的 `Rῑ`, `R-ψι`: 单调性落在 `Ω̇G (lim f s)` 的 `gl` 行里.

```agda
Gᴺfin : ∀ n {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ (natᴵ n)) ev z))
Gᴺfin n = GᴺΩ̇ (natᴵ n)

Gᴺω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω̇ ωᴵ) ev z))
Gᴺω = GᴺΩ̇ ωᴵ

wfΩ̇ : ∀ c → WFl (Ω̇ c)
wfΩ̇ c = wfl (RΩ̇ (≅ᴵ-refl c)) (𝟏⊑Ω̇ c)

hoΩ̇ : ∀ c {C} → 𝓥 C → HonT (Ω̇ c) C
hoΩ̇ c x G (inr ink) = inj₂ z≅

Ω·2ᵒ : ∀ c → O c (Fl ⊔ Fl)
Ω·2ᵒ c = Ω̇ c ⊕ Ω̇ c

gΩ2 : ∀ c → Gᵀ c 𝓥 (Ω·2ᵒ c)
gΩ2 c = AddT.Add {𝓐 = 𝓥} (Ω̇G c) (wfΩ̇ c) (λ x o _ → x) (λ _ f → cxoᵀ f) (λ x → x) (hoΩ̇ c)
                 {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → wfΩ̇ c , x) (Ω̇G c)

GᴺΩ2 : ∀ c {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (Ω·2ᵒ c) ev z))
GᴺΩ2 c = Gᴺof (gΩ2 c)

tsqᵒ : O zero (Fl ⊔ Fl)
tsqᵒ = ψᵒ zero (ι zero (Ω̇ zero))

gsq : Gᵀ zero 𝓥 tsqᵒ
gsq = Psi zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Iota zero {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x) (Ω̇G zero))

Gᴺsq : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ Fl)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ tsqᵒ ev z))
Gᴺsq = Gᴺof gsq

Z₀ : Flr → Set
Z₀ φ = ∀ {K} (q : InF K φ) {X : Ordᴵ} → Dem X q

Z-Fl : Z₀ Fl
Z-Fl (inr ink) = inj₂ z≅

Z-⊔ : ∀ {a b} → Z₀ a → Z₀ b → Z₀ (a ⊔ b)
Z-⊔ za zb (inl q) = za q
Z-⊔ za zb (inr q) = zb q

good-ψ : ∀ {c t φ} (q : t <ᴵ c) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ t 𝓥 (ψᵒ q x)
good-ψ q = Psi q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-ι : ∀ {c d φ} (q : c ◃ d) {x : O c φ} → Gᵀ c 𝓥 x → Gᵀ d 𝓥 (ι q x)
good-ι q = Iota q {𝓖 = 𝓥} {𝓧 = 𝓥} (λ x → x) (λ x → x)

good-os : ∀ {c φ} {a : O c φ} → Z₀ φ → Gᵀ c 𝓥 a → Gᵀ c 𝓥 (os a)
good-os z g = gs 𝓥 (λ x → x) g (λ _ f → cxoᵀ f) (λ x _ _ → x) (λ _ G q → z q)

good-⊕ : ∀ {c α φ} {W : O c α} {y : O c φ} → Z₀ α → WFl W → Gᵀ c 𝓥 W → Gᵀ c 𝓥 y → Gᵀ c 𝓥 (W ⊕ y)
good-⊕ {φ = φ} z w gW g = AddT.Add {𝓐 = 𝓥} gW w (λ x _ _ → x) (λ _ f → cxoᵀ f) (λ x → x) (λ _ G q → z q)
                                {𝓐₁ = λ E → 𝓥 E} {𝓧 = 𝓥} (λ {C} x → Ctx-wkC C x) (λ x → w , x) g

Flᶠ : ℕ → Flr
Flᶠ zero    = Fl
Flᶠ (suc n) = Fl ⊔ Flᶠ n

tow : ∀ n → O zero (Flᶠ n)
tow zero    = Ω̇ zero
tow (suc n) = ψᵒ zero (os (ι zero (tow n)))

Z-tow : ∀ n → Z₀ (Flᶠ n)
Z-tow zero    = Z-Fl
Z-tow (suc n) = Z-⊔ Z-Fl (Z-tow n)

gtow : ∀ n → Gᵀ zero 𝓥 (tow n)
gtow zero    = Ω̇G zero
gtow (suc n) = good-ψ zero (good-os (Z-tow n) (good-ι zero (gtow n)))

Gᴺtow : ∀ n {ℓ} (ev : Ev ℓ (Flᶠ n)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ (tow n) ev z))
Gᴺtow n = Gᴺof (gtow n)
```

## §2 值层的单调性

`GoodTΩ·2` 的相邻分支在不同层号上, 没有公共的字面上层可以嵌入, 所以 §3′ 的 `Ωm` 不直接适用: 这里在值层再走一遍. `Vstep`, `Vlim`: 第 0 个链点就是下一层; `Vm`: 对 $a\sqsubseteq^\mathsf I b$ 的证明递归.

```agda
⊑ᵒ-≅ˡ : ∀ {k k′} {x x′ : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x′ → x′ ⊑ᵒ y → x ⊑ᵒ y
⊑ᵒ-≅ˡ e h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ d G (Goodᴺ-tr d G))) (h o (Goodᴺ-tr d G) G′)
  where d = toZ-≅ (run-≅ (≈ᵒ-reflˡ o) e)

module _ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} where
  Vstep : ∀ {k₀ b} {x : Ordˢ k₀} → x ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′ → x ⊑ᴱ ψ̄ (Ω̇ (suc b)) ev′ p′
  Vstep {b = b} h = lim-rᴱ 0 (⊑ᴱ-≅ʳ h (R→≈ (rwkʳ {le′ = proj₁} (R-ιʳ zero (rwkʳ {le′ = λ e → e} (RΩ̇ (≅ᴵ-refl b))))) ev′ p′ (ev′ , ev′) p′ (≅ᴵ-refl i)))

  Vlim : ∀ {k₀ g s} n {x : Ordˢ k₀} → x ⊑ᴱ ψ̄ (Ω̇ (g n)) ev′ p′ → x ⊑ᴱ ψ̄ (Ω̇ (lim g s)) ev′ p′
  Vlim n h = lim-rᴱ n (⊑ᴱ-≅ʳ h (R→≈ (R-ιʳ (self n) (RΩ̇ (≅ᴵ-refl _))) ev′ p′ ev′ p′ (≅ᴵ-refl i)))

Vz : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} b → ψ̄ (Ω̇ zero) ev p ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′
Vz {i} {ev = ev} {ev′} {p} {p′} zero = ≅→⊑ᴱ (R→≈ (RΩ̇ z≅) ev p ev′ p′ (≅ᴵ-refl i))
Vz {i} {ev = ev} {ev′} {p} {p′} (suc b) = Vstep {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} (Vz b)
Vz {i} {ev = ev} {ev′} {p} {p′} (lim g s) = Vlim {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} 0 (Vz (g 0))

Vs : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {a₀ a″ b} → a₀ ≅ᴵ a″ → a″ <ᴵ b → ψ̄ (Ω̇ (suc a₀)) ev p ⊑ᴱ ψ̄ (Ω̇ b) ev′ p′
Vs {i} {ev = ev} {ev′} {p} {p′} e zero = ≅→⊑ᴱ (R→≈ (RΩ̇ (s≅ e)) ev p ev′ p′ (≅ᴵ-refl i))
Vs {ev = ev} {ev′} {p} {p′} e (suc q) = Vstep {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} (Vs e q)
Vs {ev = ev} {ev′} {p} {p′} e (lim n q) = Vlim {ev = ev′} {ev′ = ev′} {p = p′} {p′ = p′} n (Vs e q)

Vm : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {a b} → a ⊑ᴵ b → ψ̄ (Ω̇ a) ev p ⊑ᵒ ψ̄ (Ω̇ b) ev′ p′
Vm {i} {ev = ev} {p = p} {b = b} z⊑ = ⊑ᴱ→ᵒ (R→≈ (RΩ̇ z≅) ev p ev p (≅ᴵ-refl i)) (Vz b)
Vm {i} {ev = ev} {p = p} (s⊑ e q) = ⊑ᴱ→ᵒ (R→≈ (RΩ̇ (≅ᴵ-refl _)) ev p ev p (≅ᴵ-refl i)) (Vs e q)
Vm {i} {ev = ev} {ev′} {p} {p′} (l⊑ k) = lim-l (λ n → ⊑ᵒ-≅ˡ (R→≈ (R-ιˡ (self n) (RΩ̇ (≅ᴵ-refl _))) ev p ev p (≅ᴵ-refl i)) (Vm {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} (k n)))
```

## §3 $\psi_0(\Omega_{\Omega\cdot2})$: 外层闭包定理

`TopClo c F gF rF mF`: 分支族 $F\,\eta:$ `O (c η) Fl`, 层号 $c\,\eta$ 随 $\eta$ 变. 输入只有三件: 每个分支的 `Gᵀ`, 分支在 $\cong^\mathsf I$ 下互模拟, 值层单调. 不要吸收者, 不要守卫 ($\mathcal B$ 平凡): 分支的好性对一切 $\eta$ 成立, 所以链点是什么都行. 第 $n$ 个链点作为层号进入第 $n+1$ 个分支, 是 `Good→N` 的 `Pt₀` 递归做的, 这里什么都不用写. 界由 `readT`; 地板全是 `fk zero`, 所以 `Dem` 平凡. 这一段与树层 `gclo` 在 [UniformNF5Eval](UniformNF5Eval.lagda.md) 的行逐字对应.

`TΩ·2` 是 $c=\mathrm{id}$, $F=\dot\Omega$ 的实例, 单调由 §2 的 `Vm`.

```agda
module TopClo (c : Ordᴵ → Ordᴵ) (F : ∀ η → O (c η) Fl) (gF : ∀ η → Gᵀ (c η) 𝓥 (F η))
              (rF : ∀ {η η′} → η ≅ᴵ η′ → Rᵒ (c η) (c η′) (F η) (F η′))
              (mF : ∀ {i ℓ ℓ′} {ev : Ev ℓ Fl} {ev′ : Ev ℓ′ Fl} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {η η′} → η ⊑ᴵ η′ → ψ̄ (F η) ev p ⊑ᵒ ψ̄ (F η′) ev′ p′) where

  Tᶜ : Run (Fl ⊔ fk zero)
  Tᶜ = cloA 0 {Fl} (wk 0 proj₁ (ψ̄ (F (suc zero)))) (λ η → wk 0 proj₁ (ψ̄ (F η)))

  rT : Tᶜ ≈ᴿ Tᶜ
  rT = cloR {t = wk 0 proj₁ (ψ̄ (F (suc zero)))} {g = λ η → wk 0 proj₁ (ψ̄ (F η))} {t′ = wk 0 proj₁ (ψ̄ (F (suc zero)))} {g′ = λ η → wk 0 proj₁ (ψ̄ (F η))}
            (∼ᶠ-refl Fl) (wkR proj₁ proj₁ (R→≈ (rF (≅ᴵ-refl _)))) (λ η η′ d → wkR proj₁ proj₁ (R→≈ (rF d)))

  module At {i ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (p : i <ᴵ ℓ) where
    B : Top i ℓ (Fl ⊔ fk zero)
    B = bound (Fl ⊔ fk zero) ev p

    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e = Mlev (Fc B) (suc η) (FB B e)

    evη : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) Fl
    evη η e = liftEv Fl (λ q → lim 0 q) (proj₁ (evF B))

    tg : ∀ η (e : Bd B ⊑ᴵ η) → i <ᴵ Lη η e
    tg η e = lim 0 (iF B)

    one⊑η : ∀ η → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
    one⊑η η e = ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)

    bd⊑ : ∀ {O : Obs i} {X : Ordˢ i} (G : Goodᴺ (toZ (run O X))) → suc i ⊑ᴵ lvG G → Bd B ⊑ᴵ lvG G
    bd⊑ G (s⊑ e q) = ubd B (via e q) (λ { (inl (inr ink)) → inj₂ z≅ ; (inr ink) → inj₂ z≅ })

    GoodT : Wit i (VT i) → Good true (VT i) (Tᶜ ev p)
    GoodT w =
      bŝ (λ _ _ → ⊤) (λ _ _ → tt)
         (T̄ {ev = proj₁ ev} {p = p} {𝓖 = 𝓥} {𝓖′ = VT i} (cxT i) (λ x → x) w (gF (suc zero)))
         (λ η e w′ → T̄ {ev = evη η e} {p = tg η e} {𝓖 = 𝓥} {𝓖′ = VT i ∧ (λ _ → ⊤)} (λ (x , _) → cxT i x) proj₁ w′ (gF η))
         (R→≈ (rF (≅ᴵ-refl _)) (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i))
         (λ η e η′ e′ d → R→≈ (rF d) (evη η e) (tg η e) (evη η′ e′) (tg η′ e′) (≅ᴵ-refl i))
         (λ η e → mF (one⊑η η e))
         (λ η e η′ e′ u → mF u)
         (λ c₁ G → bd⊑ G (readT _ c₁ (R→≈ (rF (≅ᴵ-refl _)) (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i)) (F0ᵀ (rF (≅ᴵ-refl _))) G))
         (λ η e c₁ _ G → bd⊑ G (readT _ c₁ (R→≈ (rF (≅ᴵ-refl η)) (evη η e) (tg η e) (evη η e) (tg η e) (≅ᴵ-refl i)) (F0ᵀ (rF (≅ᴵ-refl η))) G))
         (λ _ _ → tt)
         (λ _ _ _ _ _ → tt)

  GᴺT : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᶜ ev z))
  GᴺT ev z = Good→N refl (At.GoodT ev z refl)

open TopClo (λ η → η) Ω̇ Ω̇G (λ e → RΩ̇ e) (λ u → Vm u) public using () renaming (GᴺT to GᴺTΩ·2; rT to RTΩ·2)

GoodTΩ·2 : ∀ {i ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (p : i <ᴵ ℓ) → Wit i (VT i) → Good true (VT i) (TΩ·2 ev p)
GoodTΩ·2 ev p = TopClo.At.GoodT (λ η → η) Ω̇ Ω̇G (λ e → RΩ̇ e) (λ u → Vm u) ev p
```

## §4 判据

下面的话是判断, 依据是上面编译过的定理.

**同一个定理覆盖了反馈.** `GᴺTΩ·2` 没有新的吸收者. 链点喂回下标的那一步, 在帧路线上是阶段输入 (`stΩ`, `Fk₁`), 在这里是一句 `T̄ … (Ω̇G η)`: 定理对一切 $\eta:$ `Ordᴵ` 成立, 而链点的层号 `toLevel (ys m)` 是一个 `Ordᴵ`, 所以 `Good→N` 的 `Pt₀` 递归把它代进去就完了. 这一步能这么短, 原因是 $\psi_0(\Omega_{\Omega\cdot2})$ 的 $\Omega_{\Omega+\gamma_n}$ 由 $\gamma_n$ 的**层号**决定, 不由它的结构决定: 树只看 `Ordᴵ`.

**一次性的新证明义务 (层号结构本身带来的).**

| 义务 | 位置 | 大小 |
|---|---|---|
| `Rᵒ` 跨层, `R-tr*`, `R-ψ` 的 3×3 | [UniformNF5Base](UniformNF5Base.lagda.md) §4–§5 | 取自 Uniform5Rel/RelPsi, 约 100 行 |
| `ptr`, `ptr⁻`: 每个对上下文递归的函数多两行 | Rules, Strict, Class, Good, Omega | 脚本从 `pι` 行生成, 只有 `Ω-rᵀ` 的两行是手写 |
| `FlΩ̇` 带 $x$ 的自相关; `FlΩ̇-tr⁻`, `Fl-back` | [UniformNF5Rules](UniformNF5Rules.lagda.md) §3′ | 约 25 行 |
| `Trᵀ`, `Tr⁻ᵀ`, `Bkᵀ`: `Gᵀ` 沿层号搬运 | [UniformNF5Tr](UniformNF5Tr.lagda.md) | 除 `gΩ` 外由 `Iota` 生成 |
| $\dot\Omega$ 单调: `Ωm` (树层, 极限层的 `gl`), `Vm` (值层, 外层闭包) | Omega §3′, 本文 §2 | 各约 25 行 |

**没有做的简化, 与判断错的地方.** 我原先打算把 `⊑ᵀ`, `≈ᶜ` 也做成跨层的; 看了 `≈ᶜ-trans` 的用处 (`Vis-≈`, `Bc`) 才发现 `pa` 行要 `Rᵒ` 的传递, 而 `rΩ` 没有中间输入, 这条路不通. 留在同层、加 `ptr` 才对: 这是值层 `tro` 的形状, [UniformNF4Main](UniformNF4Main.lagda.md) §3 已经预言. `gΩ` 的 `lΩ` 字段被删掉了: `Ω̇G` 是不依赖 `Psi` 的定理, 而 `lΩ` 在穿透分支要 `Ω̇ m` 到 `Ω̇ m′` 的搬运 (字面不同). [Uniform5Assess](Uniform5Assess.lagda.md) §1 对 `lΩ`/`rΩ` 的判断在无符号一侧也对.

**参数化到什么程度.** ℕ 嵌入 `Ordᴵ` (`natᴵ`), 所以这是一个定理, 不是每阶段一份. 它不是对 "层号结构" 抽象的: `Us`, `LG`, `LRᵒ`, `NZ`, `VisT` 都对 `Ordᴵ` 的三个构造子分情况. 证明实际用到的层号结构只有: `◃` 上的 `out`/`into`, `<◃`, `<ᴵ-dec`, `resO`, `Ω̇` 的三个子句. 我没有把它写成一个接口.

**往 `Syn` (判断, 未编译; 互模拟部分见 [UniformNF5SynRel](UniformNF5SynRel.lagda.md)).** `TΩ·2` 是一个 `Run`, 不在 `O` 里, 所以 $\psi_0(\Omega_{\Omega\cdot2}+1)$ 与 $\psi_0(\Omega_{\Omega\cdot2+1})$ 不是这个定理的实例: 这是下一个停点, 它在树的定义上, 不在证书上. [Uniform5Syn](Uniform5Syn.lagda.md) 的 `Q m α` 给它们树. 证书理论不能原样不动: `Cx` 要加 `pι↓`, `G₊` 要加 `gΩ↓`, `gev` 两行, 每个右引入规则要加 `oΩ↓`, `oev` 两行, `Ω̇G` 要加 `Ω̇ (suc m) zero` 一行 (`gclo`, 分支 `ι↓ (Ω̇ m η)`). 单调性 `Ωm` 要沿 `ι↓` 再走一遍. 这些都是逐构造子的, 我没有看到新的吸收者: `oev` 的比较落在 `ψ≡` 上, 而 `ψ≡` 的两支就是这里的 `PsiPen`, `PsiCh`. 第一个要留意的是 `oev` 的跨 $\ell$ 互模拟, 已写. 把 `Q 0 α` 当作 `O α`, 整个理论写在 `Q` 上, `Ordᴵ` 版就是 $m=0$ 的实例, 也不必克隆. 再往上 ($\psi_1(\Omega_\theta)$, 层号要对树递归) 这个判断不适用: 那里缺的是 `Acc`, 不是行.
