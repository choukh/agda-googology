# 脚手架 (三): 站点的节点, 目标 $\tau$ 的 $\psi_\tau(\Omega_\Omega)$

> 不含记号的定义 (`Uniform3Base` 的导入链含 `OCF.Align.EBO`, 用到的只是 `Flr`, `Ev`, `bound`, `cloA`, `limᵢA`). 结论写在 [ScafOmega2](ScafOmega2.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafOmega2Node where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ; intoˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Uniform3Base using
  (Flr; fz; fk; _⊔_; Ev; Run; bound; Bd; Fc; FB; evF; iF; FM; ubd; liftEv; inl; inr; ink; limᵢA; chainA; fold1A; Top; cloA)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two using (O; Ω̇; ψ̄; ψᵒ; tl; oŝ)
open import OCF.Align.NotFree using (Goodᴺ; gc; forceᴺ; forceᴺ-HS)
open import OCF.Align.UniformNF5Base using (Obs; run)
open import OCF.Align.UniformNF5Class using (Good; Good₊; bŝ; lvG; Wit; Cl)
open import OCF.Align.UniformNF5Eval using (VT; cxT; readT)
open import OCF.Align.UniformNF5Omega using (Ω̇G)
open import OCF.Align.UniformNF5Good using (𝓥)
open import OCF.Align.UniformNF5Main using (T̄)
open import OCF.Align.ScafOmega2Family using (G; ω⁺; W)
```

## §1 节点

$\psi_\tau(\Omega_\Omega)$ 在世界 $\ell$ 里求值成字面闭包 `ŝ c t₀ g`. `c` 是 `Bd`: 只由 $\tau$ 与地板算出, 不提链, 不提输出. 分支 $g\,\eta\,e$ 的世界 $\mathrm{Mlev}(\mathrm{Fc},\eta+1)$ 由 $e$ 现造.

```agda
module Node {τ ℓ} (ev : Ev ℓ Fl) (p : τ <ᴵ ℓ) where
  B : Top τ ℓ Fl
  B = bound Fl ev p

  c : Ordᴵ
  c = Bd B

  t₀ : Ordˢ τ
  t₀ = ψ̄ (tl {c = zero} (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) ev p

  Lη : ∀ η → c ⊑ᴵ η → Ordᴵ
  Lη η e = Mlev (Fc B) (suc η) (FB B e)

  evη : ∀ η (e : c ⊑ᴵ η) → Ev (Lη η e) (fz ⊔ fk η)
  evη η e = tt , (λ q → lim 1 q)

  tg : ∀ η (e : c ⊑ᴵ η) → τ <ᴵ Lη η e
  tg η e = lim 0 (iF B)

  gη : ∀ η (e : c ⊑ᴵ η) → Ordˢ τ
  gη η e = ψ̄ (tl {c = zero} (fz ⊔ fk η) (λ e′ q → proj₂ e′ (suc q)) (Ωˢ η)) (evη η e) (tg η e)

  node : ψ̄ (Ω̇ zero) ev p ≡ Ord₊ˢ.ŝ c t₀ gη
  node = refl

  -- c 恰好是 τ+1, 模前序
  τ+1⊑c : suc τ ⊑ᴵ c
  τ+1⊑c with sim (FM B) (iF B)
  ... | via e q = s⊑ e q

  c⊑τ+1 : c ⊑ᴵ suc τ
  c⊑τ+1 = ubd B (via (≅ᴵ-refl τ) zero) (λ { (inl ()) ; (inr ink) → inj₂ z≅ })

  fam→ : ∀ {η} → c ⊑ᴵ η → G τ η
  fam→ e = ⊑ᴵ-trans τ+1⊑c e

  fam← : ∀ {η} → G τ η → c ⊑ᴵ η
  fam← e = ⊑ᴵ-trans c⊑τ+1 e
```

## §2 `ask` 的回答: 第 $a+1$ 枝上升, 不比较

[LvIRReach](LvIRReach.lagda.md) 的 `ask` 问 $a$ 与目标. 这里证据 $e$ 已经回答了: 总是上升, 链在第 $a$ 层, 没有判决参数.

```agda
  ac : ∀ a {L} → Ev L (fz ⊔ fk (suc a)) → a <ᴵ L
  ac a e′ = proj₂ e′ (suc zero)

  H : ∀ a → Ordˢ a → Run (fz ⊔ fk (suc a))
  H a x = ψ̄ (tl {c = zero} (fz ⊔ fk (suc a)) (λ e′ q → proj₂ e′ (suc q)) (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)))

  ij : ∀ {a} → suc τ ⊑ᴵ suc a → (τ ≺ᴵ a) ⊎ (τ ≅ᴵ a)
  ij (s⊑ e zero)    = inj₂ e
  ij (s⊑ e (suc q)) = inj₁ (via e q)

  rise : ∀ a (e : c ⊑ᴵ suc a) →
         gη (suc a) e ≡ Ord₊ˢ.lim (λ m → H a (chainA (ac a) (H a) (evη (suc a) e) m) (evη (suc a) e) (tg (suc a) e))
  rise a e = fold1A {ac = ac a} {H = H a} {ev = evη (suc a) e} {p = tg (suc a) e} (ij (fam→ e))
```

## §3 证书: 对一切 $\tau$, 不要记号, 不要比较

`Ω̇G zero` 经 `T̄` 给 $\psi_\tau(\Omega_\Omega)$ 的 `Good`, 对一切目标 $\tau$, 与 [UniformNF5Main](UniformNF5Main.lagda.md) 的 `GoodTΩ·2` 同形. `Good` 的 `bŝ` 行带两个字段 `d₀`, `dE`: **任何**观测读出的链点, 层号 $\sqsupseteq c$. 字段的前提是输出的证书 `G`: 它不要求输出先有上界, 它从输出读下界. 这是 `self-bound` 没有发生的原因.

```agda
  good : Wit τ (VT τ) → Good true (VT τ) (ψ̄ (Ω̇ zero) ev p)
  good w = T̄ {ev = ev} {p = p} {𝓖 = 𝓥} {𝓖′ = VT τ} (cxT τ) (λ x → x) w (Ω̇G zero)

d₀ : ∀ {ℓ s 𝓖 c} {t : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → Good s 𝓖 (Ord₊ˢ.ŝ c t g) →
     ∀ {C} → 𝓖 C → (G′ : Goodᴺ (toZ (run C t))) → c ⊑ᴵ lvG G′
d₀ (bŝ 𝓑 Bc g0 gg et eg m mm d e ch₀ chS) = d

dE : ∀ {ℓ s 𝓖 c} {t : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} (Gd : Good s 𝓖 (Ord₊ˢ.ŝ c t g)) →
     Σ (Ordᴵ → Cl ℓ) λ 𝓑 → ∀ {C} η e → 𝓖 C → 𝓑 η C → (G′ : Goodᴺ (toZ (run C (g η e)))) → c ⊑ᴵ lvG G′
dE (bŝ 𝓑 Bc g0 gg et eg m mm d e ch₀ chS) = 𝓑 , e

-- 定理: 目标 τ 的第 0 个链点, 在任何观测下, 层号 ⊒ τ+1
first-above : ∀ {τ ℓ} (ev : Ev ℓ Fl) (p : τ <ᴵ ℓ) → Wit τ (VT τ) → ∀ {C} → VT τ C → (G′ : Goodᴺ (toZ (run C (Node.t₀ ev p)))) → suc τ ⊑ᴵ lvG G′
first-above {τ} ev p w v G′ = ⊑ᴵ-trans (Node.τ+1⊑c ev p) (d₀ (Node.good ev p w) v G′)
```

## §4 实例: $\tau=\omega+1$

```agda
ℓ₀ : Ordᴵ
ℓ₀ = suc ω⁺

ev₀ : Ev ℓ₀ Fl
ev₀ = tt , λ { zero → suc (suc (lim 1 zero)) }

good-ω⁺ : Good true (VT ω⁺) (ψ̄ (Ω̇ zero) ev₀ zero)
good-ω⁺ = Node.good ev₀ zero tt

rise-ω⁺ : ∀ a (e : Node.c ev₀ zero ⊑ᴵ suc a) → (ω⁺ ≺ᴵ a) ⊎ (ω⁺ ≅ᴵ a)
rise-ω⁺ a e = Node.ij ev₀ zero (Node.fam→ ev₀ zero e)
```

## §5 $c$ 穿过 $\psi_\Omega$ 与 $\psi_0$ 不变

站点是 $\psi_0(\psi_\Omega(x))$, $x=\psi_{\omega+1}(\Omega_\Omega)$. `tl` 把 $x$ 的 `ŝ c` 变成 `oŝ c`, `ψᵒ` 与 `ψ̄` 都保留 $c$, `toZ` 把它变成 `ĉᴸ c`. 所以站点的第 0 层节点的界**就是** $x$ 的 $c$, 证书 `Goodᴺ` 的 `dy` 就在这个 $c$ 上.

```agda
through : ∀ {α j φ} {t q} {cv : ∀ {L} → Ev L φ → Simᴵ (suc j) L} {c₀ : Ordᴵ} {t₁ : Ordˢ (suc j)} {g₁ : (η : Ordᴵ) → c₀ ⊑ᴵ η → Ordˢ (suc j)}
          {L} (e : Ev L (Fl ⊔ φ)) (z : zero <ᴵ L) →
          Σ Z λ a → Σ ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) λ b → Σ Z λ a′ → Σ ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) λ b′ →
          toZ (ψ̄ (ψᵒ {α} {t} q (tl {c = α} φ cv (Ord₊ˢ.ŝ c₀ t₁ g₁))) e z) ≡ Z.ĉᴸ c₀ a b a′ b′
through e z = _ , _ , _ , _ , refl
```
