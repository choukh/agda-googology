# 值验收 (三): 互相 $\sqsubseteq^0$ 到不了 $\psi_0(\Omega_{\psi_1(1)\cdot2})$ 以上

> **验收文件, 读记号.** 入口 [ValLab](ValLab.lagda.md). 全部是编译过的定理, 无条件.
>
> 规则的值验收是 "树与带字面标签的树互相 $\sqsubseteq^0$". 这里证: 码 `ω·ᶜ 1` 的第 $\alpha\ne0$ 行, 码 `ω²ᶜ` 位置 $\omega\cdot2$ 以上的一切行, 码 `ω·ᶜ 2`, `ω^ωᶜ`, `ε₀ᶜ` 上面的行, **不 $\sqsubseteq^0$ 任何带字面标签的树, 不管读法是什么**.
>
> 原因: $\sqsubseteq^0$ 的叶子是 $\cong$, 所以 $X\sqsubseteq^0Y$ 要求 $X$ 的每个 $\prec$ 子树都 $\cong$ 到 $Y$ 的子树. 带字面标签的树的子树都带字面标签 (`lab-≺`). 而高度 $\omega\cdot2$ 的第 0 行 $[\omega,t[0],t[1],\dots]$ 不带任何字面标签 (`no-any-M₂`, 对一切项 $s$). 它又是上面每一行的 $\prec$ 子树 (`grow`, `V-≺`, 有限测试 `T4`: $X_1[1][0][2][0][2][0][1]$ 是它的后继).
>
> **这否定的是:** 把互相 $\sqsubseteq^0$ 用作这些行的验收. **不否定:** 值前序 $\preccurlyeq$ 下的验收 (它对 `suc` 单调; `ω≈ω⁺`, `⊑-not-suc` 说的就是这个差别); 这些树的强度; 读法本身.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLabNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅)
open import OCF.Align.EBO using (T; fsn; cof; cω)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ω·ᶜ; ω²ᶜ; ω^ωᶜ; ε₀ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂; e²)
open import OCF.Align.LadderInfTop2 using (top)
import OCF.Align.LadderOrdMain
import OCF.Align.ValLabRow
open import OCF.Align.ValLabBase
open import OCF.Align.OrdLabRead using (tω·2)
open import OCF.Align.OrdLabReadTop using (pos-row; tail-pos)
open import OCF.Align.OrdLabRead using (module C²)
module V₂ = OCF.Align.ValLabRow (HB M₂)
module V² = OCF.Align.ValLabRow (HB ω²ᶜ)
module G₂ = OCF.Align.LadderOrdMain (HB M₂)
module G² = OCF.Align.LadderOrdMain (HB ω²ᶜ)
```

## §1 高度 $\omega\cdot2$: 不带任何标签

```agda
no-any-V₂ : ∀ s → Lab (V₂.V end zero) s → ⊥
no-any-V₂ = V₂.no-lab-pat {end} {λ i → low (blk i end)} {λ i → tt} {λ i → low (blk 0 (low (blk i end)))} {λ i → tt} {low (blk 0 end)} {tt} refl refl refl (inj₁ refl)

no-any-M₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) s → Lab (forceᴺ _ (G₂.GᴺTᵠ end zero ev z)) s → ⊥
no-any-M₂ ev z s L = no-any-V₂ s (Lab-≅ (≅-sym (V₂.Vev end zero ev z)) L)
```

## §2 码 `ω·ᶜ 1` 的第 $\alpha$ 行, $\alpha\ne0$

```agda
no-val-M₂ : ∀ {α} → zero <ᴵ α → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (G₂.GᴺTᵠ end α ev z) ⊑⁰ Y → ⊥
no-val-M₂ q = V₂.no-val-row {end} no-any-V₂ q
```

## §3 码 `ω²ᶜ` 的位置 $\omega\cdot2$: 不带任何标签

第 0 行是 $[\omega,t[1],t[2],\dots]$. 这里 $F_0$ 是闭包行, 不是 `no-lab-pat` 的形状; 用 `tail-pos` 的字面标签走第 0 项.

```agda
z⁰ : ℕ → T → T
z⁰ zero t = t
z⁰ (suc k) t = z⁰ k (fsn t 0)

Cofs : ℕ → T → Set
Cofs zero t = ⊤
Cofs (suc k) t = (cof t ≡ cω) × Cofs k (fsn t 0)

Zl : ∀ k t {x} → Lab x t → Cofs k t → Σ (Ordᶜ zero) λ y → Zk k x y × Lab y (z⁰ k t)
Zl zero t l c = _ , z0 (≅-refl⁰ _) , l
Zl (suc k) t (l0 c₀ e) (c , cs′) with trans (sym c₀) c
... | ()
Zl (suc k) t (l1 c₀ e l) (c , cs′) with trans (sym c₀) c
... | ()
Zl (suc k) t {x} (lω {F = F} c₀ e H) (c , cs′) with Zl k (fsn t 0) (H 0) cs′
... | y , zk , ly = y , zs e zk , ly

no-both : ∀ m p q {x} → Lab x p → Lab x q → Cofs m p → Cofs m q → z⁰ m q ≡ ω̂ → (z⁰ m p ≡ ω̂ → ⊥) → ⊥
no-both zero p q lp lq cp cq eq ne = ne (trans (ω-term (subst (Lab _) eq lq) lp) refl)
no-both (suc m) p q (l0 c₀ e) lq (c , cp) cq eq ne with trans (sym c₀) c
... | ()
no-both (suc m) p q (l1 c₀ e l) lq (c , cp) cq eq ne with trans (sym c₀) c
... | ()
no-both (suc m) p q (lω {F = F} c₀ e H) lq (c , cp) (c′ , cq) eq ne =
  no-both m (fsn p 0) (fsn q 0) (H 0) (proj₂ (lim-lab lq e) 0) cp cq eq ne

t[_] : ℕ → T
t[ n ] = fsn tω·2 n

-- 与证书无关: h 都是变量
gen-pos : ∀ {s} {h : ℕ → Ordᶜ zero} → Lab (h 0) ω̂ → Lab (h 1) t[ 1 ] → Lab (h 2) t[ 2 ] → Lab (lim h) s → ⊥
gen-pos {s} {h} l₀ L₁ L₂ L = no-both 2 t[ 1 ] (z⁰ 3 t[ 2 ]) L₁ L₃ (refl , (refl , tt)) (refl , (refl , tt)) refl bad₁
  where
  Y₁ = Zl 3 t[ 1 ] L₁ (refl , (refl , (refl , tt)))
  Y₂ = Zl 3 t[ 2 ] L₂ (refl , (refl , (refl , tt)))
  e-y : proj₁ Y₂ ≅ h 1
  e-y = chain-rule L l₀ (proj₂ (proj₂ Y₁)) (proj₁ (proj₂ Y₁)) (proj₁ (proj₂ Y₂))
  L₃ : Lab (h 1) (z⁰ 3 t[ 2 ])
  L₃ = Lab-≅ (≅-sym e-y) (proj₂ (proj₂ Y₂))
  bad₁ : z⁰ 2 t[ 1 ] ≡ ω̂ → ⊥
  bad₁ ()

no-any-pos′ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) s → Lab (lim (C².ChainRow.h (pos-row ev z))) s → ⊥
no-any-pos′ ev z s L = gen-pos {s} {C².ChainRow.h (pos-row ev z)} (V².ω-of (pos-row ev z)) (tail-pos ev z 0) (tail-pos ev z 1) L

no-any-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) s → Lab (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)) s → ⊥
no-any-pos ev z s L = no-any-pos′ ev z s (Lab-≅ (≅-sym (C².ChainRow.eq (pos-row ev z))) L)
```

## §4 码 `ω²ᶜ`: 位置 $\omega\cdot2$ 以上一切行

```agda
ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

no-any-Vpos : ∀ s → Lab (V².V (low (blk 1 end)) zero) s → ⊥
no-any-Vpos s L = no-any-pos ev₀ zero s (Lab-≅ (V².Vev (low (blk 1 end)) zero ev₀ zero) L)

no-val-ω² : ∀ {q} → low (blk 1 end) <ᴾ q → ∀ α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (G².GᴺTᵠ q α ev z) ⊑⁰ Y → ⊥
no-val-ω² {q} r α = V².no-val-above {low (blk 1 end)} {q} no-any-Vpos r α

-- 特例: 顶, 读法 ψ₀(Ω_{ψ₁(2)})
no-val-ω²-top : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (G².GᴺTᵠ end zero ev z) ⊑⁰ Y → ⊥
no-val-ω²-top ev z = no-val-ω² {end} tt zero ev z

-- 同一位置的第 α 行, α ≠ 0
no-val-pos : ∀ {α} → zero <ᴵ α → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) α ev z) ⊑⁰ Y → ⊥
no-val-pos q = V².no-val-row {low (blk 1 end)} no-any-Vpos q
```

## §5 码 `ω·ᶜ 2`, `ω^ωᶜ`, `ε₀ᶜ`

码 `ω·ᶜ 2` 的位置 $\omega\cdot2$ 是 `no-lab-pat` 的形状 (与码 `ω·ᶜ 1` 的顶同形). `ω^ωᶜ`, `ε₀ᶜ` 里第一个 $F_0$, $F_1$ 都是链行的位置是 `no-lab-pat₂` 的形状. 这些位置以上的行都不能值验收; 顶在其上.

```agda
module V₃ = OCF.Align.ValLabRow (HB (ω·ᶜ 2))
module Vω = OCF.Align.ValLabRow (HB ω^ωᶜ)
module Vε = OCF.Align.ValLabRow (HB ε₀ᶜ)
module G₃ = OCF.Align.LadderOrdMain (HB (ω·ᶜ 2))
module Gω = OCF.Align.LadderOrdMain (HB ω^ωᶜ)
module Gε = OCF.Align.LadderOrdMain (HB ε₀ᶜ)

-- ω·3
no-any-ω·2′ : ∀ s → Lab (V₃.V (low (blk 0 end)) zero) s → ⊥
no-any-ω·2′ = V₃.no-lab-pat {low (blk 0 end)} {λ i → low (blk 0 (low (blk i end)))} {λ i → tt} {λ i → low (blk 0 (low (blk 0 (low (blk i end)))))} {λ i → tt} {low (blk 0 (low (blk 0 end)))} {tt} refl refl refl (inj₁ refl)

no-val-ω·3 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (G₃.GᴺTᵠ end zero ev z) ⊑⁰ Y → ⊥
no-val-ω·3 = V₃.no-val-above {low (blk 0 end)} {end} no-any-ω·2′ tt zero

-- ω^ω
pω : Pos (cs ω^ωᶜ)
pω = low (blk 2 end)

no-any-pω : ∀ s → Lab (Vω.V pω zero) s → ⊥
no-any-pω = Vω.no-lab-pat₂ {pω} {λ i → low (blk 2 (low (blk i end)))} {λ i → tt}
  {λ i → low (blk 2 (low (blk 0 (low (blk i end)))))} {λ i → tt} {λ i → low (blk 2 (low (blk 1 (low (blk i end)))))} {λ i → tt}
  refl refl refl (proj₂ (Vω.V-clos-lim {low (blk 2 (low (blk 0 (low (blk 0 (low end))))))} {low (blk 2 (low (blk 0 (low (blk 0 end)))))} tt refl))

no-val-ω^ω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (Gω.GᴺTᵠ end zero ev z) ⊑⁰ Y → ⊥
no-val-ω^ω = Vω.no-val-above {pω} {end} no-any-pω tt zero

-- ε₀
pε : Pos (cs ε₀ᶜ)
pε = low (blk 1 (low (blk 2 end)))

no-any-pε : ∀ s → Lab (Vε.V pε zero) s → ⊥
no-any-pε = Vε.no-lab-pat₂ {pε} {λ i → low (blk 1 (low (blk 2 (low (blk i end)))))} {λ i → tt}
  {λ i → low (blk 1 (low (blk 2 (low (blk 0 (low (blk i end)))))))} {λ i → tt} {λ i → low (blk 1 (low (blk 2 (low (blk 1 (low (blk i end)))))))} {λ i → tt}
  refl refl refl (proj₂ (Vε.V-clos-lim {low (blk 1 (low (blk 2 (low (blk 0 (low (blk 0 (low end))))))))} {low (blk 1 (low (blk 2 (low (blk 0 (low (blk 0 end)))))))} tt refl))

no-val-ε₀ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (Gε.GᴺTᵠ end zero ev z) ⊑⁰ Y → ⊥
no-val-ε₀ = Vε.no-val-above {pε} {end} no-any-pε tt zero
```
