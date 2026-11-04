# 紧界树比值 (七): 换占位也上不去

> [TightVal](TightVal.lagda.md) 的第七篇. [TightValGlobal](TightValGlobal.lagda.md) 说占位 $0$ 让 `TΩ2′ˢ` 没有证书. 自然的反问是: $0$ 只是一个坏选择, 换成单调的占位呢? 本文把占位做成参数 `Ph`, 重证上界.
>
> `ψᵖ Ph`: 与 `ψᵉ′` 逐字, 只有第 $\ge2$ 层的后继写成 `Ph (ψᵖ S z p σ a)`. `Ph` 只能看递归值, 这是紧界设计能拿到的东西: 帧要 `Simᴵ k ℓ′`, 而多态的栈只给 $0<^\mathsf I\ell'$ (`noSim21`).
>
> **`capΩᴾ`: 只要 `Ph` 保持类 `Cᵖ`, 且不把 $\preccurlyeq B$ 的值抬过 $B$, `ψᵖ Ph ∅ˢ` 在一切 $\Omega_\eta$ 处的任何证书计值都 $\preccurlyeq B$.** 实例: `Ph r = r` (`idle`, 空转: $\psi(\eta+1):=\psi(\eta)$) 与 `Ph r = 0`. **`idle-capΩ`, `idle-drop`: 空转的紧界树不超过 $\psi_0(\Omega_\Omega\cdot\Omega_2)$, 所以不 $\succcurlyeq$ `TΩ2-label` 的树.**
>
> 边界: (1) 这两条带证书前提. 空转树有没有 `Goodᴺ` 本文没有证 (判断: 有, 值就是 `TΩ₂ᴸ`; 依据是 $\psi(\Omega_2+x)$ 的叶子都回到 $\psi(\Omega_2)$, 极限单调). (2) 增长型占位 (如 `Ph r = lim (r·m)`) 不满足 `capPh`, 本文不覆盖; 判断它仍到不了 $\psi_0(\psi_\Omega(\Omega_2+1))$, 因为不压帧就没有新的 $\hat\Omega$. (3) 不否定带别的栈或别的层号的紧界设计 (如 `GuardTightTree`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. §5 读标签.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValPh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; coeˢ; toZ; Ωˢ; addˢ; _+ˢ_; tr⁻ˢ; z<suc; z1)
open import OCF.Align.Symbolic using (σ1; Mlev)
open import OCF.Align.UniformS using (_≅ᶻ_; toZ-≅; kd-≅)
open import OCF.Align.Value using (_≼_; z≼; l≼; ≅→≼; ≼-trans; ⊑→≼)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.OmegaExpBase using (Stk; ψˢ; ∅ˢ; _▹Ω̂; σ⊥)
open import OCF.Align.OmegaSqBase using (ψᵉ′; repᴷ; s₀; z3)
open import OCF.Align.UniformS using (two)
open import OCF.Align.OmegaSq using (TΩ2′ˢ; GLΩ₂)
open import OCF.Align.Relative using (_≅ᴬ_; zᴬ; sᴬ; lᴬ; lᵢᴬ; uᴬ; uz; us; ŝᴬ; ĉᴬ; Rᴬ; R→≅ᴬ; ≅→Rᴬ; addˢ-≅ᴬ; tr⁻ˢ-≅ᴬ; ≅ᴬ-tr⁻ˢ; Ωˢ-≅ᴬ; ≅ᴬ→≅ˢ₀; ≅ᴬ-sym)
open import OCF.Align.TightValBase using (Cp; cp-zero; cp-lim; cp-ĉ; s≼-irrefl)
open import OCF.Align.TightValCap using (High; h1; h2; h3)
open import OCF.Align.TightValGlobal using (_≈ᵃ_; ψˢ-≅ᴬ; ▹Ω̂-≈ᵃ; ∅-≈ᵃ)
open import OCF.Align.TightValAccept using (A; h∅; hΩ₀; hΩ₁; hΩ₂; not-below; A≺X; X′)
```

## §1 带参数的紧界折叠

```agda
PhT : Set
PhT = ∀ {i} → Ordˢ i → Ordˢ i

module Fold (Ph : PhT) where
  _▹ᵖ[_]_ : Stk → ∀ {k} → (∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) → Ordˢ k → Stk
  ψᵖ : Stk → ∀ {i k ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
  repᵖ : Stk → ∀ {k} → (∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) → Ordˢ k → ℕ → Stk

  ψᵖ S z p σ Ord₊ˢ.zero = (S ▹Ω̂) z p
  ψᵖ S {k = zero}        z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (λ m → repᵖ S s₀ a m z p)
  ψᵖ S {k = suc zero}    z p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (λ m → repᵖ S σ1 a m z p)
  ψᵖ S {k = suc (suc _)}   z p σ (Ord₊ˢ.suc a) = Ph (ψᵖ S z p σ a)
  ψᵖ S {k = suc (lim _ _)} z p σ (Ord₊ˢ.suc a) = Ph (ψᵖ S z p σ a)
  ψᵖ S {k = lim _ _}       z p σ (Ord₊ˢ.suc a) = Ph (ψᵖ S z p σ a)
  ψᵖ S z p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ m → ψᵖ S z p σ (f m))
  ψᵖ S z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
  ... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → ψᵖ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
  ... | injᵇ _ = Ord₊ˢ.lim (λ m → ψᵖ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵖ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
  ... | injᶜ _ = Ord₊ˢ.lim (λ m → ψᵖ S z p σ (f (intoˢ (<→◃ q) (iter (λ x → ψᵖ S z (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
  ψᵖ S z p σ (Ord₊ˢ.up zero x)     = ψᵖ S z p (λ q → σ (suc q)) x
  ψᵖ S z p σ (Ord₊ˢ.up (self m) x) = ψᵖ S z p (λ q → σ (lim m q)) x
  ψᵖ S {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᵖ S z p σ t₀) (λ η e → ψᵖ S z p σ (g η e))
  ψᵖ S {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵖ S z p σ t₀) (λ η e → ψᵖ S z p σ (g η e))
  ψᵖ S {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = Ord₊ˢ.ŝ c (ψᵖ S z p σ t₀) (λ η e → ψᵖ S z p σ (g η e))
  ψᵖ S z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = Ord₊ˢ.ĉᴸ c t₀ g (ψᵖ S z p σ o₀) (λ η e → ψᵖ S z p σ (o η e))

  (S ▹ᵖ[ s ] a) z p = ψᵖ S z p (s z) a

  repᵖ S s a zero    = S
  repᵖ S s a (suc m) = repᵖ S s a m ▹ᵖ[ s ] a
```

## §2 类 `Cᵖ`

与 [TightValBase](TightValBase.lagda.md) 的 `C` 只差后继: 这里要后继的前驱也在类里, 因为占位读递归值.

```agda
data Cᵖ {i : Ordᴵ} : Ordˢ i → Set where
  cΩ : Cᵖ (Ωˢ i)
  c0 : Cᵖ Ord₊ˢ.zero
  cs : ∀ {a} → Cᵖ a → Cᵖ (Ord₊ˢ.suc a)
  cl : ∀ {f : ℕ → Ordˢ i} → (∀ n → Cᵖ (f n)) → Cᵖ (Ord₊ˢ.lim f)
  ci : ∀ {j} {q : j <ᴵ i} {f : Uˢ j (<→◃ q) → Ordˢ i} → (∀ y → Cᵖ (f y)) → Cᵖ (Ord₊ˢ.limᵢ q f)
  cŝ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ i} → Cᵖ t₀ → (∀ η e → Cᵖ (g η e)) → Cᵖ (Ord₊ˢ.ŝ c t₀ g)
  cĉ : ∀ {c t₀ g o₀} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ i} → Cᵖ o₀ → (∀ η e → Cᵖ (o η e)) → Cᵖ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

cAdd : ∀ {k i} {a : Ordˢ i} (σ : Simᴵ k i) → Cᵖ a → (b : Ordˢ k) → Cᵖ (addˢ a σ b)
cAdd σ h Ord₊ˢ.zero           = h
cAdd σ h (Ord₊ˢ.suc b)        = cs (cAdd σ h b)
cAdd σ h (Ord₊ˢ.lim f)        = cl (λ n → cAdd σ h (f n))
cAdd σ h (Ord₊ˢ.limᵢ q f)     = ci (λ y → cAdd σ h (f (coeˢ (<→◃ (σ q)) (<→◃ q) y)))
cAdd σ h (Ord₊ˢ.up zero x)    = cAdd (λ q → σ (suc q)) h x
cAdd σ h (Ord₊ˢ.up (self n) x) = cAdd (λ q → σ (lim n q)) h x
cAdd {k = zero}    σ h (Ord₊ˢ.ŝ c t₀ g) = cĉ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd {k = suc _}   σ h (Ord₊ˢ.ŝ c t₀ g) = cŝ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd {k = lim _ _} σ h (Ord₊ˢ.ŝ c t₀ g) = cŝ (cAdd σ h t₀) (λ η e → cAdd σ h (g η e))
cAdd σ h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cAdd σ h o₀) (λ η e → cAdd σ h (o η e))

cIter : ∀ {i} {a : Ordˢ i} → Cᵖ a → ∀ m → Cᵖ (iter (a +ˢ_) Ord₊ˢ.zero m)
cIter h zero    = c0
cIter h (suc m) = cAdd (λ q → q) h _

CStk : Stk → Set
CStk S = ∀ {i ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) → Cᵖ (S z p)

cloS : ∀ (S : Stk) → CStk S → ∀ {i k ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (x : Ordˢ k) → Cᵖ (ψˢ S z p σ x)
cloS S hS z p σ Ord₊ˢ.zero    = hS z p
cloS S hS z p σ (Ord₊ˢ.suc a) = cl (cIter (cloS S hS z p σ a))
cloS S hS z p σ (Ord₊ˢ.lim f) = cl (λ m → cloS S hS z p σ (f m))
cloS S hS z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = ci (λ y → cloS S hS z p σ _)
... | injᵇ _ = cl (λ m → cloS S hS z p σ _)
... | injᶜ _ = cl (λ m → cloS S hS z p σ _)
cloS S hS z p σ (Ord₊ˢ.up zero x)     = cloS S hS z p (λ q → σ (suc q)) x
cloS S hS z p σ (Ord₊ˢ.up (self m) x) = cloS S hS z p (λ q → σ (lim m q)) x
cloS S hS {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = cĉ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloS S hS z p σ t₀) (λ η e → cloS S hS z p σ (g η e))
cloS S hS z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cloS S hS z p σ o₀) (λ η e → cloS S hS z p σ (o η e))

cloΩ̂ : ∀ (S : Stk) → CStk S → CStk (S ▹Ω̂)
cloΩ̂ S hS z p = cŝ (cloS S hS _ _ _ _) (λ η e → cloS S hS _ _ _ _)

c∅ : CStk ∅ˢ
c∅ z p = cΩ
```

## §3 封顶

```agda
module Capᴾ (Ph : PhT) (cPh : ∀ {i} {r : Ordˢ i} → Cᵖ r → Cᵖ (Ph r))
            (B : Ordᶜ zero) (capPh : ∀ {r : Ordˢ zero} → Cp B (toZ r) → Cp B (toZ (Ph r)))
  where
  open Fold Ph

  cloE : ∀ (S : Stk) → CStk S → ∀ {i k ℓ} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (x : Ordˢ k) → Cᵖ (ψᵖ S z p σ x)
  cRep : ∀ (S : Stk) → CStk S → ∀ {k} (s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k ℓ) (a : Ordˢ k) m → CStk (repᵖ S s a m)

  cloE S hS z p σ Ord₊ˢ.zero = cloΩ̂ S hS z p
  cloE S hS {k = zero}        z p σ (Ord₊ˢ.suc a) = cl (λ m → cRep S hS _ a m z p)
  cloE S hS {k = suc zero}    z p σ (Ord₊ˢ.suc a) = cl (λ m → cRep S hS _ a m z p)
  cloE S hS {k = suc (suc _)}   z p σ (Ord₊ˢ.suc a) = cPh (cloE S hS z p σ a)
  cloE S hS {k = suc (lim _ _)} z p σ (Ord₊ˢ.suc a) = cPh (cloE S hS z p σ a)
  cloE S hS {k = lim _ _}       z p σ (Ord₊ˢ.suc a) = cPh (cloE S hS z p σ a)
  cloE S hS z p σ (Ord₊ˢ.lim f) = cl (λ m → cloE S hS z p σ (f m))
  cloE S hS z p σ (Ord₊ˢ.limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
  ... | injᵃ (via e r) = ci (λ y → cloE S hS z p σ _)
  ... | injᵇ _ = cl (λ m → cloE S hS z p σ _)
  ... | injᶜ _ = cl (λ m → cloE S hS z p σ _)
  cloE S hS z p σ (Ord₊ˢ.up zero x)     = cloE S hS z p (λ q → σ (suc q)) x
  cloE S hS z p σ (Ord₊ˢ.up (self m) x) = cloE S hS z p (λ q → σ (lim m q)) x
  cloE S hS {k = zero}    z p σ (Ord₊ˢ.ŝ c t₀ g) = cĉ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
  cloE S hS {k = suc _}   z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
  cloE S hS {k = lim _ _} z p σ (Ord₊ˢ.ŝ c t₀ g) = cŝ (cloE S hS z p σ t₀) (λ η e → cloE S hS z p σ (g η e))
  cloE S hS z p σ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = cĉ (cloE S hS z p σ o₀) (λ η e → cloE S hS z p σ (o η e))

  cRep S hS s a zero    z p = hS z p
  cRep S hS s a (suc m) z p = cloE (repᵖ S s a m) (cRep S hS s a m) z p (s z) a

  module Low
    (h∅ᵖ : ∀ {ℓ} (z p : zero <ᴵ ℓ) → Cp B (toZ ((∅ˢ ▹Ω̂) z p)))
    (hΩ₀ᵖ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ zero ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ (Ωˢ zero))))
    (hΩ₁ᵖ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ (Ωˢ (suc zero)))))
    (hΩ₂ᵖ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc (suc zero)) ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ (Ωˢ (suc (suc zero))))))
    where

    capΩᴾ : ∀ (η : Ordᴵ) {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ η ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ (Ωˢ η)))
    cap   : ∀ {k} {x : Ordˢ k} → High k → Cᵖ x → ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ k ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ x))
    stepΩ : ∀ {k} → High k → ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc k) ℓ) → Cp B (toZ (ψᵖ ∅ˢ z p σ (Ωˢ (suc k))))

    capΩᴾ zero                z p σ = hΩ₀ᵖ z p σ
    capΩᴾ (suc zero)          z p σ = hΩ₁ᵖ z p σ
    capΩᴾ (suc (suc zero))    z p σ = hΩ₂ᵖ z p σ
    capΩᴾ (suc (suc (suc a))) z p σ = stepΩ h1 z p σ
    capΩᴾ (suc (suc (lim f s))) z p σ = stepΩ h2 z p σ
    capΩᴾ (suc (lim f s))     z p σ = stepΩ h3 z p σ
    capΩᴾ (lim f s)           z p σ = cp-lim (λ m → capΩᴾ (f m) z p (λ q → σ (lim m q)))

    stepΩ {k} h z p σ with <ᴵ-dec (σ zero) p
    ... | injᵃ (via e ())
    ... | injᵇ _ = cp-lim (λ m → cap h (chain m) z p (λ q → σ (suc q)))
      where
      chain : ∀ m → Cᵖ (iter (λ x → ψᵖ ∅ˢ z (σ zero) (λ q → σ (suc q)) x) (Ωˢ k) m)
      chain zero    = cΩ
      chain (suc m) = cloE ∅ˢ c∅ z (σ zero) (λ q → σ (suc q)) _
    ... | injᶜ _ = cp-lim (λ m → cap h (chain m) z p (λ q → σ (suc q)))
      where
      chain : ∀ m → Cᵖ (iter (λ x → ψᵖ ∅ˢ z (σ zero) (λ q → σ (suc q)) x) (Ωˢ k) m)
      chain zero    = cΩ
      chain (suc m) = cloE ∅ˢ c∅ z (σ zero) (λ q → σ (suc q)) _

    cap {k} h cΩ z p σ = capΩᴾ k z p σ
    cap h c0 z p σ = h∅ᵖ z p
    cap h1 (cs H) z p σ = capPh (cap h1 H z p σ)
    cap h2 (cs H) z p σ = capPh (cap h2 H z p σ)
    cap h3 (cs H) z p σ = capPh (cap h3 H z p σ)
    cap h (cl H) z p σ = cp-lim (λ n → cap h (H n) z p σ)
    cap h (ci {q = q} H) z p σ with <ᴵ-dec (σ q) p
    ... | injᵃ (via e ())
    ... | injᵇ _ = cp-lim (λ m → cap h (H _) z p σ)
    ... | injᶜ _ = cp-lim (λ m → cap h (H _) z p σ)
    cap h1 (cŝ H₀ H) z p σ = cp-ĉ (cap h1 H₀ z p σ) (λ η e → cap h1 (H η e) z p σ)
    cap h2 (cŝ H₀ H) z p σ = cp-ĉ (cap h2 H₀ z p σ) (λ η e → cap h2 (H η e) z p σ)
    cap h3 (cŝ H₀ H) z p σ = cp-ĉ (cap h3 H₀ z p σ) (λ η e → cap h3 (H η e) z p σ)
    cap h (cĉ H₀ H) z p σ = cp-ĉ (cap h H₀ z p σ) (λ η e → cap h (H η e) z p σ)
```

## §4 第 $\le1$ 层上 `ψᵖ` 就是 `ψᵉ′`

占位子句只在第 $\ge2$ 层的后继. 指数在第 $\le1$ 层时, 两个折叠逐项互模拟, 与 `Ph` 无关. `Lo` 的 $k$ 字面只有 $0,1$, 所以 `z≅` 与 `s≅ z≅` 两种.

```agda
module Same (Ph : PhT) where
  open Fold Ph

  liEᵖ : ∀ {S S′ : Stk} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
         {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
         {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
         i ≅ᴵ i′ → j ≅ᴵ j′ →
         (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
            ψᵖ S z p σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
         (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
            ψᵖ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψᵉ′ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
         ψᵖ S z p σ (Ord₊ˢ.limᵢ q f) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
  liEᵖ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
    with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
  ... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
    subst₂ (λ u v → ψᵖ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
           (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
           (rec _ _ (≅→Rᴬ (<→◃ q) (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d)))))
  ... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
  ... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
  ... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
  ... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
  ... | injᵇ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
    where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
  ... | injᵇ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
    where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
  ... | injᶜ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
    where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
  ... | injᶜ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
    where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)

  data Lw : Ordᴵ → Ordᴵ → Set where
    w0 : Lw zero zero
    w1 : Lw (suc zero) (suc zero)

  same : ∀ {S S′ : Stk} → S ≈ᵃ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
         {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
         Lw k₁ k₂ → i ≅ᴵ i′ → a ≅ᴬ b → ψᵖ S z p σ a ≅ᴬ ψᵉ′ S′ z′ p′ σ′ b
  sameRep : ∀ {S S′ : Stk} → S ≈ᵃ S′ → ∀ {k₁ k₂} {s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₁ ℓ} {s′ : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₂ ℓ}
            {a : Ordˢ k₁} {b : Ordˢ k₂} → Lw k₁ k₂ → a ≅ᴬ b → ∀ m → repᵖ S s a m ≈ᵃ repᴷ S′ s′ b m

  same H {z = z} {p = p} {z′ = z′} {p′ = p′} ek ei zᴬ = ▹Ω̂-≈ᵃ H z p z′ p′ ei
  same H {z = z} {p = p} {z′ = z′} {p′ = p′} w0 ei (sᴬ e) = lᴬ (λ m → sameRep H w0 e m z p z′ p′ ei)
  same H {z = z} {p = p} {z′ = z′} {p′ = p′} w1 ei (sᴬ e) = lᴬ (λ m → sameRep H w1 e m z p z′ p′ ei)
  same H ek ei (lᴬ h) = lᴬ (λ n → same H ek ei (h n))
  same H w1 ei (uᴬ uz e) = same H w0 ei e
  same H w0 ei (ŝᴬ k ec et eg) =
    ĉᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (same H w0 ei et) (λ η e η′ e′ eη → same H w0 ei (eg η e η′ e′ eη))
  same H w1 ei (ŝᴬ k ec et eg) =
    ŝᴬ (kd-≅ ei) ec (same H w1 ei et) (λ η e η′ e′ eη → same H w1 ei (eg η e η′ e′ eη))
  same H ek ei (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (same H ek ei eo) (λ η e η′ e′ eη → same H ek ei (eO η e η′ e′ eη))
  same {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ek ei (lᵢᴬ {p = q} {q = q′} {f = f} {g = g} e h) =
    liEᵖ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
         (λ x y d → same H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ek ei (h x y d))
         (λ x y d → same H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} ek e (h x y d))

  sameRep H ek e zero    = H
  sameRep H ek e (suc m) z p z′ p′ ei = same (sameRep H ek e m) ek ei e

  sameΩ₂ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc (suc zero)) ℓ) → ψᵖ ∅ˢ z p σ (Ωˢ (suc (suc zero))) ≅ᴬ ψᵉ′ ∅ˢ z p σ (Ωˢ (suc (suc zero)))
  sameΩ₂ z p σ = liEᵖ {q = zero} {q′ = zero} (≅ᴵ-refl zero) (≅ᴵ-refl (suc zero))
    (λ x y d → same ∅-≈ᵃ w1 (≅ᴵ-refl zero) (R→≅ᴬ zero d))
    (λ x y d → same ∅-≈ᵃ w1 (≅ᴵ-refl (suc zero)) (R→≅ᴬ zero d))
```

## §5 空转占位的实例

`idle r = r`. 第 $\le2$ 层的四个低处值搬自 `ψᵉ′` (§4), 上界取 [TightValAccept](TightValAccept.lagda.md) 的 `A`, 即带标签 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的树.

```agda
idle : PhT
idle r = r

open Fold idle using () renaming (ψᵖ to ψⁱ)
open Same idle using (same; sameΩ₂; w0; w1)
open Capᴾ idle (λ h → h) A (λ h → h) using (module Low)

trCp : ∀ {x y : Ordˢ zero} → x ≅ᴬ y → Cp A (toZ y) → Cp A (toZ x)
trCp e h G = ≼-trans (≅→≼ (forceᴺ-≅ d G (Goodᴺ-tr d G))) (h (Goodᴺ-tr d G))
  where d = toZ-≅ (≅ᴬ→≅ˢ₀ e)

open Low h∅
  (λ z p σ → trCp (same ∅-≈ᵃ {z = z} {p = p} {σ = σ} {z′ = z} {p′ = p} {σ′ = σ} w0 (≅ᴵ-refl zero) (Ωˢ-≅ᴬ (≅ᴵ-refl zero))) (hΩ₀ z p σ))
  (λ z p σ → trCp (same ∅-≈ᵃ {z = z} {p = p} {σ = σ} {z′ = z} {p′ = p} {σ′ = σ} w1 (≅ᴵ-refl zero) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero)))) (hΩ₁ z p σ))
  (λ z p σ → trCp (sameΩ₂ z p σ) (hΩ₂ z p σ))
  renaming (capΩᴾ to idle-capΩ) public

Tⁱ : Ordˢ zero
Tⁱ = Ord₊ˢ.ŝ (suc zero) (ψⁱ ∅ˢ (z<suc z1 z1) zero (σ1 (z<suc z1 z1)) (Ωˢ (suc zero)))
       (λ η e → ψⁱ ∅ˢ {ℓ = Mlev (suc zero) η e} (lim 0 (z<suc z1 z1)) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η))

idle-cap : Cp A (toZ Tⁱ)
idle-cap = cp-ĉ (idle-capΩ (suc zero) (z<suc z1 z1) zero (σ1 (z<suc z1 z1))) (λ η e → idle-capΩ η {ℓ = Mlev (suc zero) η e} (lim 0 (z<suc z1 z1)) (lim 0 zero) (λ q → lim 1 q))

idle-drop : (G : Goodᴺ (toZ Tⁱ)) → ¬ (X′ ≼ forceᴺ _ G)
idle-drop G = not-below A≺X (idle-cap G)

idle-no-value : (G : Goodᴺ (toZ Tⁱ)) → ¬ (X′ ⊑⁰ forceᴺ _ G)
idle-no-value G h = idle-drop G (⊑→≼ X′ h)
```

**一个前提可满足的掉值实例.** 指数 $\Omega_2+1$ 处: 空转树字面就是 $\Omega_2$ 处的树, 所以有证书, 值 $\cong$ `A`. 真值带标签 $\psi_0(\psi_\Omega(\Omega_2+1))$, 严格在上 (`TightValAccept.low-true : suc A ≼ low-Y`). 这里没有空真. `idle-witness-drop` 对一切 $\succ$ `A` 的树陈述; 把 $Y$ 取成 `low-Y` 的那一行编译时堆耗尽 (退出码 251, 上限 10G, 原因没有查), 所以留作参数.

```agda
Eⁱ : Ordˢ zero
Eⁱ = ψⁱ ∅ˢ z3 z3 (λ q → suc q) (Ord₊ˢ.suc (Ωˢ two))

idle-witness : Σ (Goodᴺ (toZ Eⁱ)) λ G → forceᴺ _ G ≅ A
idle-witness = Goodᴺ-tr d (ofL (proj₁ GLΩ₂)) , ≅-trans (≅-sym (forceᴺ-≅ d (ofL (proj₁ GLΩ₂)) (Goodᴺ-tr d (ofL (proj₁ GLΩ₂))))) (ofL-≅ (proj₁ GLΩ₂))
  where d = toZ-≅ (≅ᴬ→≅ˢ₀ (≅ᴬ-sym (sameΩ₂ z3 z3 (λ q → suc q))))

idle-witness-drop : ∀ {Y : Ordᶜ zero} → suc A ≼ Y → ¬ (Y ≼ forceᴺ _ (proj₁ idle-witness))
idle-witness-drop a = not-below a (≅→≼ (proj₂ idle-witness))
```

**读法.** `Tⁱ` 与 `TΩ2′ˢ` 同形, 只换占位. 上界对空转树没有被证明是空真的, 也没有被证明不是: `no-T` 的坏节点在这里消失了 ($\psi(\Omega_2+1)=\psi(\Omega_2)$, 极限单调), 证书的存在性没有写. 判断: 存在, 值就是 `A`.
