# 脚手架 (一): 站点 $\psi_0(\psi_\Omega(\psi_{\omega+1}(\Omega_\Omega)))$ 的标签

> 结论写在 [ScafOmega2](ScafOmega2.lagda.md). 这里用记号: 这是验收节.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafOmega2Site where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)
open import OCF.Align.StandardOmega using (NF₁-fsn; n∷; nψ; Vis₁; vh; vd; vs; vt; Bnd₁)
open import OCF.Align.Uniform5Label using (NF-Ω)
open import OCF.Align.Standard using (c[]; c∷; []≤)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ordˢ; toZ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; cof; cω; c0; c1; sucT; Ωt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅)
open import OCF.Align.StandardOmega using (walk; NF₁; AllLim)
open import OCF.Align.Uniform using (l-inv; ≅-reflˡ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import OCF.Align.GoodLBase using (Goodᴸ; forceᴸ)
open import OCF.Align.Uniform3Base using (Ev; ψ₀ᵗ; Lab₀)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two using (Ω̇; ψ̄)
open import OCF.Align.Uniform4Head using (Ωp)
open import OCF.Align.Uniform4Label using (nfNat)
open import OCF.Align.Uniform5Label using (TΩ-label; Ωs₊)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.UniformNF5Main using (GᴺΩ̇)
open import OCF.Align.UniformNF3Eq using (toZ-≅)
open import OCF.Align.UniformNF5Base using (R→≈; RΩ̇)
```

## §1 记号一侧的路径 (`refl`)

```agda
Ω₁ᵗ ΩΩᵗ ω+1ᵗ ωᵗ : T
Ω₁ᵗ  = Ωp ∷ []
ΩΩᵗ  = Ωt Ω₁ᵗ
ωᵗ   = ψ₀ᵗ (natT 1)
ω+1ᵗ = sucT ωᵗ

ψᵤ : T → T → T
ψᵤ u a = ψᵗ u a ∷ []

-- ψ₀(Ω_{Ω+1})
top₁ : T
top₁ = ψ₀ᵗ (Ωs₊ (natT 1))

-- 站点
site : T
site = ψ₀ᵗ (ψᵤ Ω₁ᵗ (ψᵤ ω+1ᵗ ΩΩᵗ))

path₁ : List ℕ
path₁ = 1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ []

site-walk : walk top₁ path₁ ≡ site
site-walk = refl

-- 更小的站点: 目标 ω, 同样的分支形状. 第一个非自然数目标 + 全部 v 的分支
site₀ : T
site₀ = ψ₀ᵗ (ΩΩᵗ ++ ψᵤ ωᵗ ΩΩᵗ)

Ω2ΩΩ : T
Ω2ΩΩ = ψ₀ᵗ (ΩΩᵗ ++ ΩΩᵗ)

path₀ : List ℕ
path₀ = 1 ∷ 0 ∷ 0 ∷ 2 ∷ []

path₀₁ : List ℕ
path₀₁ = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ []

_ : walk top₁ path₀ ≡ Ω2ΩΩ
_ = refl

site₀-walk : walk Ω2ΩΩ path₀₁ ≡ site₀
site₀-walk = refl
```

## §2 走一条路径, 标签跟着走

`Lab` 是遗传的: 极限项的第 $n$ 项带 `fsn t n` 的标签. 所以 $\psi_0(\Omega_{\Omega+1})$ 的标签 (`TΩ-label`, 无条件) 沿 `path₁` 就是站点的标签.

```agda
walkᶜ : Ordᶜ zero → List ℕ → Ordᶜ zero
walkᶜ X       []       = X
walkᶜ (lim f) (n ∷ ns) = walkᶜ (f n) ns
walkᶜ X       (_ ∷ _)  = X

Lab-walk : ∀ {X t} ns → AllLim t ns → Lab X t → Lab (walkᶜ X ns) (walk t ns)
Lab-walk []       _        l = l
Lab-walk (n ∷ ns) (c , cs) (l0 c′ e) = ⊥-elim (0≠ω (trans (sym c′) c)) where
  0≠ω : c0 ≡ cω → ⊥
  0≠ω ()
Lab-walk (n ∷ ns) (c , cs) (l1 c′ e l) = ⊥-elim (1≠ω (trans (sym c′) c)) where
  1≠ω : c1 ≡ cω → ⊥
  1≠ω ()
Lab-walk {X = lim f} (n ∷ ns) (c , cs) (lω c′ e h) = Lab-walk ns cs (Lab-≅ (l-inv e n) (h n))

all₁ : AllLim top₁ path₁
all₁ = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

all₀ : AllLim top₁ path₀
all₀ = refl , refl , refl , refl , tt

all₀₁ : AllLim (walk top₁ path₀) path₀₁
all₀₁ = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt
```

## §3 通用的走法

下面两条对任意的树 $X$ 陈述, 不展开 $X$. 这样实例的类型检查不必归约证书.

```agda
Lab-site : ∀ {X} → Lab X top₁ → Lab (walkᶜ X path₁) site
Lab-site l = Lab-walk path₁ all₁ l

Lab-site₀ : ∀ {X} → Lab X top₁ → Lab (walkᶜ (walkᶜ X path₀) path₀₁) site₀
Lab-site₀ l = Lab-walk path₀₁ all₀₁ (Lab-walk path₀ all₀ l)
```

## §4 标签

$\theta=1$ 的 `TΩ-label`, 树 `ψ̄ (Ω̇ 1)`, 对任何世界 $\ell$.

```agda
lab₁ : Lab (suc zero) (natT 1)
lab₁ = l1 refl (s≅ z≅) (l0 refl z≅)

top-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω̇ (suc zero)) ev z) top₁
top-label ev z = TΩ-label (suc zero) (hs hz) lab₁ (nfNat 1) (s≅ z≅) ev z

-- 站点的树与它的标签: 无条件, 没有假设
site-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (walkᶜ (forceᴸ _ (proj₁ (top-label ev z))) path₁) site
site-label ev z = Lab-site (proj₂ (top-label ev z))

site₀-label : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (walkᶜ (walkᶜ (forceᴸ _ (proj₁ (top-label ev z))) path₀) path₀₁) site₀
site₀-label ev z = Lab-site₀ (proj₂ (top-label ev z))
```

## §5 同一棵树, 证书不读记号

`GᴺΩ̇ 1` 是 [UniformNF5Main](UniformNF5Main.lagda.md) 的定理, 依赖切片里没有记号. 计值与证书无关 (`forceᴺ-≅`), 所以这棵树带同一个标签. **站点的合法性不依赖标签**: 标签只是验收.

```agda
Xᴺ≅ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) (G : Goodᴸ (toZ (ψ̄ (Ω̇ (suc zero)) ev z))) → forceᴺ _ (GᴺΩ̇ (suc zero) ev z) ≅ forceᴸ _ G
Xᴺ≅ ev z G = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ (RΩ̇ (≅ᴵ-refl (suc zero))) ev z ev z (≅ᴵ-refl zero))) (GᴺΩ̇ (suc zero) ev z) (ofL G)) (ofL-≅ G)

site-labelᴺ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (walkᶜ (forceᴺ _ (GᴺΩ̇ (suc zero) ev z)) path₁) site
site-labelᴺ ev z = Lab-site (Lab-≅ (Xᴺ≅ ev z (proj₁ (top-label ev z))) (proj₂ (top-label ev z)))

site₀-labelᴺ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (walkᶜ (walkᶜ (forceᴺ _ (GᴺΩ̇ (suc zero) ev z)) path₀) path₀₁) site₀
site₀-labelᴺ ev z = Lab-site₀ (Lab-≅ (Xᴺ≅ ev z (proj₁ (top-label ev z))) (proj₂ (top-label ev z)))
```

## §6 记号规定的界: 在输入上, 不在输出上

`NF₁ site`: 由 `NF-Ω` 与 `NF₁-fsn` 沿路径. 它的条件 `Bnd₁ [] a` 说: $a$ 里可见的 $\zeta$ (即 $\psi_0(\zeta)$ 这样的项的参数) 满足 $\zeta<a$. 这是**对输入 $a$ 的**条件, 不要 $\psi_0(a)$ 先存在. 目标 $\omega+1=\psi_0(1)+1$ 的可见参数是 $1$, 所以条件在这里是 $1<a$. 由 $1<a$ 得 $\psi_0(1)<\psi_0(a)$, 第 0 个链点以上都在 $\omega+1$ 之上.

```agda
NF-walk : ∀ {t} ns → AllLim t ns → NF₁ t → NF₁ (walk t ns)
NF-walk []       _        n = n
NF-walk (x ∷ ns) (c , cs) n = NF-walk ns cs (NF₁-fsn n c x)

nf-top : NF₁ top₁
nf-top = NF-Ω (nfNat 1) (c∷ c[])

nf-site : NF₁ site
nf-site = NF-walk path₁ all₁ nf-top

site-arg : T
site-arg = ψᵤ Ω₁ᵗ (ψᵤ ω+1ᵗ ΩΩᵗ)

site-bnd : Bnd₁ [] site-arg
site-bnd with nf-site
... | n∷ (nψ _ _ _ bx) _ _ = bx

-- 第 0, 1 个链点 (refl: 有限检查, 不是全称)
chain₀ : T
chain₀ = ψ₀ᵗ (ψᵤ Ω₁ᵗ (ψᵤ ω+1ᵗ (Ωt (natT 1))))

fs0 : fsn site 0 ≡ chain₀
fs0 = refl

fs1 : fsn site 1 ≡ ψ₀ᵗ (ψᵤ Ω₁ᵗ (ψᵤ ω+1ᵗ (Ωt chain₀)))
fs1 = refl

-- 链点在目标之上; 第 0 个分支的下标 1 在目标之下 (所以它不在族里, 走 t₀)
above₀ : E.cmpᵀ (sucT ω+1ᵗ) chain₀ ≡ E.lt
above₀ = refl

above₁ : E.cmpᵀ (sucT ω+1ᵗ) (fsn site 1) ≡ E.lt
above₁ = refl

below-one : E.cmpᵀ (natT 1) ω+1ᵗ ≡ E.lt
below-one = refl
```

```agda
-- 具体: 目标的参数 1 是可见的, 所以标准形要求 1 < a. 这个条件只提输入
vis-1 : Vis₁ [] (natT 1) site-arg
vis-1 = vd ([]≤ _) (vs ([]≤ _) (vh ([]≤ _)))

one<arg : natT 1 E.<ᵀ site-arg
one<arg = site-bnd vis-1
```

## §7 站点的次序 (`refl`)

$\psi_0(\Omega_{\psi_1(0)})$ 就是 $\psi_0(\Omega_\Omega)$, 已有标签. 其余的目标一个包含一个: 从 $\psi_0(\Omega_{\Omega_2})$ 走到第 5 站, 再到 $\psi_0(\Omega_{\psi_1(\Omega)})$, $\psi_0(\Omega_{\psi_1(1)})$, $\psi_0(\Omega_{\Omega\cdot3})$, $\psi_0(\Omega_{\Omega\cdot2+1})$. 所以 $\psi_0(\Omega_{\Omega\cdot2+1})$ 是必经的第一个, 不存在跳过它的次序. 而 $\psi_0(\Omega_{\Omega+1})$ 在 $\psi_0(\Omega_{\Omega_2})$ 的路径上 (`reach₁`), 站点在它之内.

```agda
ψ₁ᵗ : T → T
ψ₁ᵗ a = ψᵗ (natT 1) a ∷ []

_ : ψ₁ᵗ [] ≡ Ω₁ᵗ
_ = refl

s₄ s₅ s₆ s₇ s₈ : T
s₄ = ψ₀ᵗ (Ωt (Ωt (natT 2)))
s₅ = ψ₀ᵗ (Ωt (ψ₁ᵗ ΩΩᵗ))
s₆ = ψ₀ᵗ (Ωt (ψ₁ᵗ Ω₁ᵗ))
s₇ = ψ₀ᵗ (Ωt (ψ₁ᵗ (natT 1)))
s₈ = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ Ωp ∷ []))

reach₅ : walk s₄ (1 ∷ []) ≡ s₅
reach₅ = refl

reach₆ : walk s₅ (0 ∷ []) ≡ s₆
reach₆ = refl

reach₇ : walk s₆ (0 ∷ []) ≡ s₇
reach₇ = refl

reach₈ : walk s₇ (3 ∷ []) ≡ s₈
reach₈ = refl

reach₉ : walk s₈ (0 ∷ []) ≡ ψ₀ᵗ (Ωt (sucT (Ωp ∷ Ωp ∷ [])))
reach₉ = refl

reach₁ : walk s₄ (1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) ≡ top₁
reach₁ = refl
```
