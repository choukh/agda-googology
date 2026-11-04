# 主线直接标: 高度 $\omega\cdot 2$, $\omega^2$ 的实例

> **验收文件, 读记号.** 结论写在 [OrdLab](OrdLab.lagda.md), 一般定理在 [OrdLabRead](OrdLabRead.lagda.md). 全部是主线的定理, 没有克隆的证书.
>
> **写法的约束.** 字面位置 (`end`, `low (blk 1 end)`) 上证书能计算, 类型检查一旦比较两个不是字面相同的 `forceᴺ _ (G p …)` 就会展开证书 (20G 堆耗尽, 退出码 251). 所以下面的陈述都逐字写出, 证明走 [OrdLabRead](OrdLabRead.lagda.md) 的 `GenRow`, 不用别名.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabReadTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (_×_)
open import Data.List using (List; _∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; lω; Lab-≅)
import OCF.Align.EBO as E
open E using (T; natT; fsn; cof)
open import OCF.Align.LadderLabZStandardOmega using (n[]; Ωᵐ; ψ¹)
open import OCF.Align.OrdLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabZStage2 using (≺→⊑)
open import OCF.Align.LadderInfTop2 using (top) renaming (fin to fin₂)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂; e²)
open import OCF.Align.LadderOrdAgree using (agree₂; agree²)
import OCF.Align.LadderOrdGrow
open import OCF.Align.OrdLabAccept using (ord-top₂; ord-top²; module G₂; module G²)
open import OCF.Align.OrdLabRead
module Gr₂ = OCF.Align.LadderOrdGrow (HB M₂)
module N₂ = NoChain (HB M₂)
module N² = NoChain (HB ω²ᶜ)
module R₂ = GenRow (HB M₂)
module R² = GenRow (HB ω²ᶜ)

cons≢ : ∀ {A : Set} {x : A} {xs} → x ∷ xs ≡ [] → ⊥
cons≢ ()
```

## §1 带字面标签的树

$t[n]=\psi_0(\Omega_{\psi_1(1)+\Omega\cdot n})$ 就是 `ord-top₂` 的第 $n$ 行. 把这些行取极限得到一棵树, 它的基本列就是 $t$ 的基本列.

```agda
Zf : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → ℕ → Ordᶜ zero
Zf ev z n = forceᴺ _ (G₂.GᴺTᵠ (e₂ (top n)) zero ev z)

Tᴸ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Ordᶜ zero
Tᴸ ev z = lim (Zf ev z)

row-lab : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → Lab (forceᴺ _ (G₂.GᴺTᵠ (e₂ (top n)) zero ev z)) (fsn tω·2 n)
row-lab ev z n = subst (Lab _) (sym (fsn-ω·2 n)) (ord-top₂ n Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅ ev z)

label-Tᴸ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (Tᴸ ev z) tω·2
label-Tᴸ ev z = lω refl (≅-refl⁰ _) (row-lab ev z)
```

## §2 码 `ω·ᶜ 1` 的顶

第 0 行是 $[\omega,\ t[0],\ t[1],\dots]$: 错开一位.

```agda
M₂-row : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → C₂.ChainRow (forceᴺ _ (G₂.GᴺTᵠ end zero ev z)) (λ i → forceᴺ _ (G₂.GᴺTᵠ (e₂ (top i)) zero ev z))
M₂-row ev z = C₂.chain-row {end} {λ i → e₂ (top i)} {λ i → tt} refl ev z

tail-M₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → Lab (C₂.ChainRow.h (M₂-row ev z) (suc n)) (fsn tω·2 n)
tail-M₂ ev z = R₂.tail-gen (M₂-row ev z) (row-lab ev z)

no-lab-M₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (forceᴺ _ (G₂.GᴺTᵠ end zero ev z)) tω·2 → ⊥
no-lab-M₂ ev z L = cons≢ (N₂.chain-needs-zero {end} {λ i → e₂ (top i)} {λ i → tt} refl ev z (ψ¹ ∷ ψ¹ ∷ []) refl L)

same-M₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → (forceᴺ _ (G₂.GᴺTᵠ end zero ev z) ⊑⁰ Tᴸ ev z) × (Tᴸ ev z ⊑⁰ forceᴺ _ (G₂.GᴺTᵠ end zero ev z))
same-M₂ ev z = R₂.same-shift (M₂-row ev z)
```

## §3 码 `ω²ᶜ` 的位置 $\omega\cdot 2$

`low (blk 1 end)`. 第 0 行是 $[\omega,\ t[1],\ t[2],\dots]$: 只差第 0 项.

```agda
pos-row : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → C².ChainRow (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)) (λ i → forceᴺ _ (G².GᴺTᵠ (e² (top (suc i))) zero ev z))
pos-row ev z = C².chain-row {low (blk 1 end)} {λ i → e² (top (suc i))} {λ i → tt} refl ev z

e²≅e₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → forceᴺ _ (G².GᴺTᵠ (e² (top n)) zero ev z) ≅ forceᴺ _ (G₂.GᴺTᵠ (e₂ (top n)) zero ev z)
e²≅e₂ ev z n = ≅-trans (≅-sym (agree² (top n) zero ev z)) (agree₂ (top n) zero ev z)

tail-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → Lab (C².ChainRow.h (pos-row ev z) (suc n)) (fsn tω·2 (suc n))
tail-pos ev z = R².tail-gen (pos-row ev z) (λ n → Lab-≅ (e²≅e₂ ev z (suc n)) (row-lab ev z (suc n)))

no-lab-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)) tω·2 → ⊥
no-lab-pos ev z L = cons≢ (N².chain-needs-zero {low (blk 1 end)} {λ i → e² (top (suc i))} {λ i → tt} refl ev z (ψ¹ ∷ ψ¹ ∷ []) refl L)

fgh-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)) (suc n) ≡ FGH (Tᴸ ev z) (suc n)
fgh-pos ev z = R².fgh-head {Z = Zf ev z} (pos-row ev z) (λ n → e²≅e₂ ev z (suc n))

Zf-grow : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {n m : ℕ} → e₂ (top n) <ᴾ e₂ (top m) → Zf ev z n ⊑⁰ Zf ev z m
Zf-grow ev z {n} {m} r = ≺→⊑ (Gr₂.grow {e₂ (top n)} {e₂ (top m)} r ev z)

step-Tᴸ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Zf ev z 0 ⊑⁰ Zf ev z 1
step-Tᴸ ev z = Zf-grow ev z {0} {1} tt

same-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z) ⊑⁰ Tᴸ ev z) × (Tᴸ ev z ⊑⁰ forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z))
same-pos ev z = R².same-head {Z = Zf ev z} (pos-row ev z) (λ n → e²≅e₂ ev z (suc n)) (step-Tᴸ ev z)
```

## §4 码 `ω²ᶜ` 的顶

$\psi_0(\Omega_{\psi_1(2)})$ 的第 0 项是 $\psi_0(1)$, 过得了链行; 第 1 项是 $\psi_0(\Omega_{\psi_1(1)})$, 也对. 第 2 项是 $\psi_0(\Omega_{\psi_1(1)\cdot2})$, 这就是 §3 的树, 没有字面标签. 所以顶也没有 (`no-lab-ω²`).

```agda
top-row : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → C².ChainRow (forceᴺ _ (G².GᴺTᵠ end zero ev z)) (λ i → forceᴺ _ (G².GᴺTᵠ (low (blk i end)) zero ev z))
top-row ev z = C².chain-row {end} {λ i → low (blk i end)} {λ i → tt} refl ev z

head-ω²0 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (C².ChainRow.h (top-row ev z) 0) (fsn tω² 0)
head-ω²0 ev z = subst (λ X → Lab X (ψ₀ᵗ (natT 1))) (sym (C².ChainRow.first (top-row ev z))) (ω-lab (C².ChainRow.G₀ (top-row ev z)))

at-pos : ∀ {p q : Pos (cs ω²ᶜ)} {t} {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → p ≡ q → Lab (forceᴺ _ (G².GᴺTᵠ p zero ev z)) t → Lab (forceᴺ _ (G².GᴺTᵠ q zero ev z)) t
at-pos ev z refl L = L

head-ω²1 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (C².ChainRow.h (top-row ev z) 1) (fsn tω² 1)
head-ω²1 ev z = Lab-≅ (C².ChainRow.rest (top-row ev z) 0) (at-pos ev z refl (ord-top² 0 Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅ ev z))

tail-ω²2 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → C².ChainRow.h (top-row ev z) 2 ≅ forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)
tail-ω²2 ev z = C².ChainRow.rest (top-row ev z) 1

no-lab-ω² : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab (forceᴺ _ (G².GᴺTᵠ end zero ev z)) tω² → ⊥
no-lab-ω² ev z L = no-lab-pos ev z (Lab-≅ (≅-sym (tail-ω²2 ev z)) (lab-lim L refl (C².ChainRow.eq (top-row ev z)) 2))
```
