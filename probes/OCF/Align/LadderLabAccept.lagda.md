# 高度上的标签: 验收

> **验收文件, 不在证书的闭包内.** 记号与标签在这里出现. 结论写在 [LadderLab](LadderLab.lagda.md). 证书 `LadderInf*` 只改模块名, 克隆成 `LadderLabZInfW*`; 标签贴在克隆的证书的计值上, 办法与 [LadderInfAccept](LadderInfAccept.lagda.md), [LadderNFAccept](LadderNFAccept.lagda.md) 相同. 克隆与主线的联系是代码逐字相同 (脚本比较) 和 §4 的有限测试, 不是定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.Correspond using (Lab; l0)
import OCF.Align.EBO as E
open E using (T; natT; Ωt; cof; fsT; fsn; cω; cΩ; c1) renaming (_<ᵀ_ to _<ᵗ_; ψ to ψᵗ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; n[]; Ω₁; Ωᵐ; ψ¹; fsn-ψ¹)
open import OCF.Align.LadderLabZGoodLBase using (Lab→Ctbl; lab1; nf1)
open import OCF.Align.LadderLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.LadderLabZUniform3Base using (Ev; ψ₀ᵗ)
open import OCF.Align.LadderLabZUniform4Base using (Fl)
open import OCF.Align.LadderLabZNFWForce
open import OCF.Align.LadderLabNFOmega using (NF-Ωᵐ)
open import OCF.Align.LadderLabNFTop using (NF-ψ)
open import OCF.Align.LadderLabZInfWTop using (HS∞; fin; ∞)
open import OCF.Align.LadderLabZInfWTop2 using (HS₂; top) renaming (fin to fin₂)
open import OCF.Align.LadderLabInst using (Px∞; Px₂)
import OCF.Align.LadderLabTop
import OCF.Align.LadderLabZInfWMain
module L∞ = OCF.Align.LadderLabTop HS∞ Px∞
module L₂ = OCF.Align.LadderLabTop HS₂ Px₂
module I∞ = OCF.Align.LadderLabZInfWMain HS∞
module I₂ = OCF.Align.LadderLabZInfWMain HS₂
```

## §1 $\psi_0(\Omega_{\psi_1(1)+\theta})$

`B∞` $=\psi_0(\Omega_{\psi_1(1)+\Omega})$ 是这一行的上界: $\theta\ge$ `B∞` 时 $\psi_0(\Omega_{\psi_1(1)+\theta})$ 不是标准形 (`Bnd₁` 要 $\theta$ 小于项). 这与 $\theta<\psi_0(\Omega_{\Omega\cdot(m+2)})$ 同形.

```agda
B∞ : T
B∞ = ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ []))

label-∞ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B∞ → ∀ {α} → α ≅ᴵ toLevel Y hY →
          ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ θ)))
label-∞ Y hY lY nθ pm e ev p = L∞.label-cert ∞ Y hY lY nθ (NF-ψ 0 nθ (Lab→Ctbl lY nθ) pm) e ev p

1<B∞ : natT 1 <ᵗ B∞
1<B∞ = E.hd< (E.ar< E.[]<)

-- 不写上界的形式: 只要目标本身是标准形
label-∞ᴺ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψ₀ᵗ (Ωt (ψ¹ ∷ θ))) → ∀ {α} → α ≅ᴵ toLevel Y hY →
           ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ θ)))
label-∞ᴺ Y hY lY nθ nf e ev p = L∞.label-cert ∞ Y hY lY nθ nf e ev p

-- 第一决定性目标: ψ₀(Ω_{ψ₁(1)+1})
label-∞1 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ (suc zero) ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ natT 1)))
label-∞1 = label-∞ one⁰ (hs hz) lab1 nf1 1<B∞ (s≅ z≅)

-- θ = 0: 不再经 anchor, 直接由同一条定理
label-∞0 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ [])))
label-∞0 = label-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

-- 有限部分
label-fin : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ (fin m) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
label-fin m Y hY lY nθ pm e ev p = L∞.label-cert (fin m) Y hY lY nθ (NF-Ωᵐ m nθ (Lab→Ctbl lY nθ) pm) e ev p
```

## §2 $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot n+\theta})$

实例 $\omega+\omega$: 高度 `top n` 的前缀是 $\psi_1(1)+\Omega\cdot n$. 这就是 [LadderInf](LadderInf.lagda.md) 对 `top 1` 的读法, 现在是定理.

```agda
label-top : ∀ n {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top n) α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n θ)))
label-top n Y hY lY nθ pm e ev p = L₂.label-cert (top n) Y hY lY nθ (NF-ψ n nθ (Lab→Ctbl lY nθ) pm) e ev p

-- ψ₀(Ω_{ψ₁(1)+Ω}): 贴到 G₂ψ₁+Ω 的克隆上
label-ψ₁+Ω : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top 1) zero ev p)) B∞
label-ψ₁+Ω = label-top 1 Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

label-ψ₁+Ω·n : ∀ n {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top n) zero ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n [])))
label-ψ₁+Ω·n n = label-top n Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

-- ψ₀(Ω_{ψ₁(1)+Ω+1})
label-ψ₁+Ω+1 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top 1) (suc zero) ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ natT 1)))
label-ψ₁+Ω+1 = label-top 1 one⁰ (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≅ z≅)
```

两个实例的推论, 经 `Lab-uniq`, `Lab-oc`: `top 0` 的树与 ∞ 的树同值, 不用 [LadderInfBridgeTop](LadderInfBridgeTop.lagda.md); 树的序与标签的序一致.

```agda
agree-top0 : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B∞ → ∀ {α β} → α ≅ᴵ toLevel Y hY → β ≅ᴵ toLevel Y hY →
             ∀ {ℓ ℓ′} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
             forceᴺ _ (I∞.GᴺTᵠ ∞ α ev p) ≅ forceᴺ _ (I₂.GᴺTᵠ (top 0) β ev′ p′)
agree-top0 Y hY lY nθ pm e e′ ev p ev′ p′ = Lab-uniq (label-∞ Y hY lY nθ pm e ev p) (label-top 0 Y hY lY nθ pm e′ ev′ p′)

nf-t₁ : NF₁ (ψ₀ᵗ (Ωt (ψ¹ ∷ natT 1)))
nf-t₁ = NF-ψ 0 nf1 (c∷ c[]) 1<B∞

nf-B∞ : NF₁ B∞
nf-B∞ = NF-ψ 1 n[] c[] E.[]<

t₁<B∞ : ψ₀ᵗ (Ωt (ψ¹ ∷ natT 1)) <ᵗ B∞
t₁<B∞ = E.hd< (E.ar< (E.hd< (E.lv< (E.tl< (E.hd< (E.lv< E.[]<))))))

mono-1-Ω : ∀ {ℓ ℓ′} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
           forceᴺ _ (I∞.GᴺTᵠ ∞ (suc zero) ev p) ≺ forceᴺ _ (I₂.GᴺTᵠ (top 1) zero ev′ p′)
mono-1-Ω ev p ev′ p′ = Lab-oc (label-ψ₁+Ω ev′ p′) nf-B∞ (label-∞1 ev p) nf-t₁ t₁<B∞
```

## §3 记号一侧的形状

**`refl`, 有限检查, 只算形状.** 这些说明标签确实是读法说的那个序数: $\Omega_{\psi_1(1)+\Omega}$ 是 $\Omega_1$-共尾, 基本列是 $\Omega_{\psi_1(1)+\theta}$; $\psi_1(1)$ 是 $\omega$-共尾, 基本列是 $\Omega\cdot n$; $\psi_0(\Omega_{\psi_1(1)+1})$ 是 $\omega$-共尾.

```agda
cof-ψ₁ : cof (ψ¹ ∷ []) ≡ cω
cof-ψ₁ = refl

fs-ψ₁ : ∀ n → fsn (ψ¹ ∷ []) n ≡ Ωᵐ n []
fs-ψ₁ = fsn-ψ¹

cof-Ω+ : cof (Ωt (ψ¹ ∷ Ω₁ ∷ [])) ≡ cΩ []
cof-Ω+ = refl

fs-Ω+ : ∀ θ → fsT (Ωt (ψ¹ ∷ Ω₁ ∷ [])) θ ≡ Ωt (ψ¹ ∷ θ)
fs-Ω+ θ = refl

cof-t₁ : cof (ψ₀ᵗ (Ωt (ψ¹ ∷ natT 1))) ≡ cω
cof-t₁ = refl

cof-B∞ : cof B∞ ≡ cω
cof-B∞ = refl
```

## §4 跨世界的有限测试

**有限测试, 不是证明.** 主线的证书与克隆的证书, 计值在第 0 项上 FGH 相等, `refl`. 只比较这几个点.

```agda
import OCF.Align.LadderInfClosed as C

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

fgh-∞0 : C.fgh₀∞ 0 ≡ FGH (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev₀ zero)) 0
fgh-∞0 = refl

fgh-∞1 : C.fgh₁∞ 0 ≡ FGH (forceᴺ _ (I∞.GᴺTᵠ ∞ (suc zero) ev₀ zero)) 0
fgh-∞1 = refl

fgh-Ω : C.fgh₂Ω 0 ≡ FGH (forceᴺ _ (I₂.GᴺTᵠ (top 1) zero ev₀ zero)) 0
fgh-Ω = refl
```
