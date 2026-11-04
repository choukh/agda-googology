> **机械克隆, 验收用.** 由 `LadderMonoMain` 经脚本复制, 只改导入 (规则同 `Survey/scripts/laddernf/mk_w.py`), 把证书搬到标签阶梯的世界. 见 [LadderMonoAccept](LadderMonoAccept.lagda.md).

# 跨高度单调 (三): 主定理

> 结论写在 [LadderMono](LadderMono.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoWMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Align.LadderNFWEq using (toZ-≅; _≅ᶻ_)
open import OCF.Align.LadderNFWFloor using (Flr; Ev; Run; ∼ᶠ-refl; limᵢA)
open import OCF.Align.LadderNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.LadderNFWFT using (Fl)
open import OCF.Align.LadderNFWTree
open import OCF.Align.LadderNFWRel
open import OCF.Align.LadderNFWMain using (GᴺTᵠ; GᴺTωn; GᴺTω-if)
open import OCF.Align.LadderMonoWRel
open import OCF.Align.LadderMonoWDown
```

## §1 从证书取一项

`Goodᴺ` 对闭包要求第一个点好, 对极限要求每一项好, 所以一旦整棵树有证书, 第一个点的第 0 项就有证书, 值不超过整棵树. 这两条不比较任何东西.

```agda
fst-pt : ∀ {c t} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G : Goodᴺ (ĉᴸ c t g t g)) → Σ (Goodᴺ t) λ G₀ → forceᴺ t G₀ ⊑ forceᴺ _ G
fst-pt (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀ , ⊑-lim 0 (λ h → h)

lim-term : ∀ {f : ℕ → Z} (G : Goodᴺ (Z.lim f)) n → Σ (Goodᴺ (f n)) λ G₀ → forceᴺ _ G₀ ⊑ forceᴺ _ G
lim-term (gl G st) n = G n , ⊑-lim n (λ h → h)
```

## §2 $T_{m+1}\sqsubseteq T_{m+2}$

$T_{m+2}=\bar\psi_{m+1}(\dot\Omega_{m+1}\,0)$ 是闭包, 第一个点是 $\bar\psi_{m+1}(\iota_\downarrow(\dot\Omega_m\,1))$. $\dot\Omega_m\,1$ 是 `qΩ` 节点, 所以这个点是链的极限, 链的第 0 项正是 $\dot\Omega_m\,0$, 经 `omk` 的第二格读出来. 所以第 0 项是 $\bar\psi_{m+1}(\iota_\downarrow(\dot\Omega_m\,0))$. 它与 $T_{m+1}=\bar\psi_m(\dot\Omega_m\,0)$ 由 `D-self` 同值.

陈述对**任意**两张证书成立, 所以证明里不展开 `GᴺTᵠ`.

```agda
mono-s : ∀ m {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) (A : Goodᴺ (toZ (Tᵠ m zero ev z))) (B : Goodᴺ (toZ (Tᵠ (suc m) zero ev z))) → forceᴺ _ A ⊑ forceᴺ _ B
mono-s m ev z A B = ⊑-trans (≅→⊑ (forceᴺ-≅ (toZ-≅ (D→≈ᵠ (D-self m) ok₀ _ _ _ ev z _ z (≅ᴵ-refl zero))) A (proj₁ P₀))) (⊑-trans (proj₂ P₀) (proj₂ P₁))
  where
  P₁ = fst-pt B
  P₀ = lim-term (proj₁ P₁) 0
```

## §3 $T_0\sqsubseteq T_1$

同样的形状, 在根层: 第一个点是 $\Omega_1$ 的 `limᵢ`, 目标 $0$ 与节点 $0$ 比较, 走链, 第 0 项是 $\Omega^\mathsf{S}_0 = 1$. 所以 $T_0=\bar\psi_0(1)$ 是第 0 项.

```agda
lim-i : ∀ {φ} (ac : ∀ {ℓ} → Ev ℓ φ → zero <ᴵ ℓ) (H : Ordˢ zero → Run φ) {ℓ} (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) (G : Goodᴺ (toZ (limᵢA 0 ac H ev z))) →
        Σ (Goodᴺ (toZ (H (Ωˢ zero) ev z))) λ G₀ → forceᴺ _ G₀ ⊑ forceᴺ _ G
lim-i ac H ev z G with <ᴵ-dec (ac ev) z
lim-i ac H ev z G | injᵃ (via e ())
lim-i ac H ev z G | injᵇ _ = lim-term G 0
lim-i ac H ev z G | injᶜ _ = lim-term G 0

T₀-self : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → toZ (Tωn 0 ev z) ≅ᶻ toZ (Tωn 0 ev z)
T₀-self ev z = toZ-≅ (R→≈ᵠ (rs (∼ᶠ-refl Fl) (λ i ()) rz) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev z ev z (≅ᴵ-refl zero))

mono-0 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) (A : Goodᴺ (toZ (Tωn 0 ev z))) (B : Goodᴺ (toZ (Tωn 1 ev z))) → forceᴺ _ A ⊑ forceᴺ _ B
mono-0 ev z A B = ⊑-trans (≅→⊑ (forceᴺ-≅ (T₀-self ev z) A (proj₁ P₀))) (⊑-trans (proj₂ P₀) (proj₂ P₁))
  where
  P₁ = fst-pt B
  P₀ = lim-i {φ = Fl} (λ e → proj₂ e zero) (λ x → ψ̄ᵠ {m = 0} {c = zero} {χ = κ Fl} ok₀ (λ i h r → ok₀ i) (tl Fl proj₂ (Ord₊ˢ.up zero (intoˢ {i = zero} {ℓ = suc zero} zero x)))) ev z (proj₁ P₁)
```

## §4 主定理

```agda
Tω-mono : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → forceᴺ _ (GᴺTωn n ev z) ⊑ forceᴺ _ (GᴺTωn (suc n) ev z)
Tω-mono ev z zero    = mono-0 ev z (GᴺTωn 0 ev z) (GᴺTωn 1 ev z)
Tω-mono ev z (suc n) = mono-s n ev z (GᴺTωn (suc n) ev z) (GᴺTωn (suc (suc n)) ev z)

GᴺTω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tω ev z))
GᴺTω ev z = GᴺTω-if ev z (Tω-mono ev z)
```
