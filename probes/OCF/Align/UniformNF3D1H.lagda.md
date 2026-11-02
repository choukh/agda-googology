# 深度 1 的观测 (四): 帧 $\Omega_\Omega$ 与深度 1 的严格增长

> 接 [UniformNF3D1G](UniformNF3D1G.lagda.md), [UniformNF3D1C](UniformNF3D1C.lagda.md). 结论先说:
>
> 1. **`ffl-Ω̂ : FFl (Ω̂A 0)` (§1).** 帧的全部地板性质, 从前缀的 `PFl` 算出, 没有阶段, 也没有记号.
> 2. **`growF` (§2): $\psi_0(Q+\psi_\Omega(\Omega_a))\prec\psi_0(Q+\psi_\Omega(\Omega_{a'}))$, 对一切上下文.** 这是 `growQ` 的深度 1 形式, 外层闭包 `Ω̂A 1 E` 的链要的就是它. 证明只有一行: `Ω-strict` 对 `fo1` 头已经成立.
> 3. **`noCross` (§3): 新的 `≅ˢ` 不让跨层的伪树相关.** $1$ 作为第 1 层的树与作为第 0 层的树不再相关; 旧的 `≅ˢ` 相关. 这正是 `≅→⊑ᴱ` 在 `fo1` 下保持为真的代价.
> 4. 深度 1 的折叠定理 `FF₁` 在 [UniformNF3D2H](UniformNF3D2H.lagda.md), 证书在 [UniformNF3D2T](UniformNF3D2T.lagda.md). 本文 §4 记下当时的计划, 那个计划已经按原样实现.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D1H where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (_≅ˢ_; z≅; s≅; Ωˢ-refl; _≈ᴿ_; selfΩ̂0; _≈₁_)
open import OCF.Align.Uniform3Base using (fz; fk; flo; cvFlo; _⊔_; Ev; Run; A; fold; Ω̂A)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ)
open import OCF.Align.UniformNF3D1O using (Obs; fo1; run; _≈ᵒ_)
open import OCF.Align.UniformNF3D1G using (_⊑ᴱ_; Ctx; ctx-refl; PFl; FFl; ffl; 𝟏; σ₀; ⊑ᴱ-trans; ŝ-rᴱ; Ω1ᴱ; suc-fold; fold-congᴱ; pfl-Ω̂; Ω-strict; Ω<ᴱ)
```

## §1 帧 $\Omega_\Omega$

```agda
ffl-Ω̂ : FFl (Ω̂A 0)
ffl-Ω̂ = ffl selfΩ̂0 pfl-Ω̂ s1 st
  where
  Ω₁ = Ωˢ (suc zero)
  s1 : ∀ {fl} {Q : Run fl} → PFl Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ fk zero)) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ Ω̂A 0 Q ev p
  s1 pf ev p = ŝ-rᴱ (PFl.fS pf {φ = fk zero} {cv = λ e → e} ev p Ω₁ (Ωˢ-refl (suc zero)) (Ω1ᴱ (suc zero)))
  st : ∀ {fl} {Q : Run fl} → PFl Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ fk zero)) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Q (proj₁ ev) p) ⊑ᴱ Ω̂A 0 Q ev p
  st {Q = Q} pf ev p = ŝ-rᴱ (⊑ᴱ-trans
    (suc-fold {φ = fz} {P = Q} {cv = λ _ → σ₀} {ev = proj₁ ev , tt} {p = p} {a = Ord₊ˢ.zero} (PFl.rP pf) (PFl.f0 pf) z≅)
    (fold-congᴱ {φ = fz} {φ′ = fk zero} {P = Q} {cv = λ _ → σ₀} {cv′ = λ e → e} {ev = proj₁ ev , tt} {ev′ = ev} {p = p} {p′ = p} {x = 𝟏} {y = Ω₁} (PFl.rP pf) (Ω1ᴱ (suc zero))))
```

## §2 深度 1 的严格增长

```agda
growF : ∀ {flE fl i ℓ ℓ′ j} {O : Obs i} {E : A 1 flE} {Q : Run fl} {ev : Ev ℓ (fl ⊔ (flE ⊔ flo j))} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo (suc j)))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
        Ctx O → FFl E → PFl Q →
        (G′ : Goodᴺ (toZ (run O (fold 1 (flo (suc j)) (cvFlo (suc j)) E (Ωˢ (suc j)) Q ev′ p′)))) →
        Σ (Goodᴺ (toZ (run O (fold 1 (flo j) (cvFlo j) E (Ωˢ j) Q ev p)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
growF {j = j} {O = O} cO fE pf G′ = Ω-strict j (fo1 (ctx-refl O cO) (FFl.rE fE) (PFl.rP pf)) (fE , pf , cO) G′
```

## §3 跨层的伪树

```agda
𝟏₁ : Ordˢ (suc zero)
𝟏₁ = Ord₊ˢ.suc Ord₊ˢ.zero

noCross : 𝟏₁ ≅ˢ 𝟏 → ⊥
noCross (s≅ () _)
```

## §4 当时的计划 (已实现)

`FF₁`: `Good true 𝓖 x` 推出 `Good true 𝓖′ (fold 1 (flo k) (cvFlo k) E x Q ev p)`. 极限行、`limᵢ` 的穿透与折叠、`up`、闭包行都是 `FF` 的克隆 (`fold 1` 在这些行上与 `fold 0` 定义性同形, 规则层已经用同样的克隆编译了). 新内容只在后继行: `lim m. repA Q F m`, 第 $m+1$ 份是以第 $m$ 份为底的 $F$. 类 `𝓚` 的 `clk` 正好给出 `fo1 O E B ∈ 𝓚` ($B$ 压在 $a$ 之上). 卡住的是 `FoldQ` 的形状: 它要底 $B$ 在**一切**目标与一切 `VF` 上下文里好, 而第 $m$ 份只在 `𝓚` 允许的上下文里好. 要把 `VF` 换成抽象的族 (`VisT ∧ 𝓟`, $\mathcal P$ 对 `Above`、`FlOver`、$\approx$ 封闭), 并让底作为函数参数 (不再是模块参数), 使 `FF₁` 能在新的底上递归. 实现见 [UniformNF3D2F](UniformNF3D2F.lagda.md) (抽象类族) 与 [UniformNF3D2C](UniformNF3D2C.lagda.md) (后继行).
