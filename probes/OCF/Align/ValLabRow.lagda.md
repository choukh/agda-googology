# 值验收 (二): 没有任何字面标签的行, 对一切 `HtB`

> **验收文件, 读记号.** 入口 [ValLab](ValLab.lagda.md). 结构律 `chain-rule` 在 [ValLabBase](ValLabBase.lagda.md), 这里把它用到高度结构的第 0 行.
>
> - `no-lab-pat`: 对一切 `HtB`: 若 $m$ 是链行, $F_0$ 是链行, $F_1$ 是闭包行, 闭包的下面 $n\ge F_0$, 则 **对一切项 $s$**, $V_m0$ 不带 $s$. 这是 `no-PxB` 的前提, 但结论强得多: 不是 "没有 `PxB`", 而是这棵树不是任何字面标签的树. 证明: `chain-rule` 说 $F_1$ 行的第 0 项应 $\cong F_0$ 行, 而它严格更高.
> - `no-⊑`: 带字面标签的树的 $\prec$ 子树都带字面标签. 所以 $c\prec X$, $c$ 没有标签, 则 $X$ 不 $\sqsubseteq^0$ 任何带字面标签的树.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.ValLabRow (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ; forceᴺ-≅; forceᴺ-HS)
open import OCF.Free.Floor using (fz; Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
open import OCF.Free.Eq using (toZ-≅; z≅)
open import OCF.Align.OrdLabZCorrespond using (Lab; Lab-≅)
open import OCF.Align.EBO using (T)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊 using (R→≈ᵠ; RΩ̇)
open import OCF.Align.LadderOrdStrict3 𝕊 using (≺-≅ˡ)
import OCF.Align.LadderOrdGrow
import OCF.Align.OrdLabChain
open import OCF.Align.OrdLabRead using (ω-lab)
open import OCF.Align.ValLabBase
open import OCF.Align.ValLabLadder 𝕊 public using (V; V-G; V-G′; V-≅; V-≺; GV; V-lim; clos-row; ClosRow; first; ys; hy; value; Gf; Fd-≺; D-val; ca₀; ca₁; e₀)
private
  module C = OCF.Align.OrdLabChain 𝕊
  module Gr = OCF.Align.LadderOrdGrow 𝕊
```

## §1 $V$ 上的工具

```agda
≺-tr : ∀ {ℓ} {c : Ordᶜ ℓ} {a b : Ordᶜ zero} → c ≺ a → a ≺ b → c ≺ b
≺-tr h (≺z e) = ≺s (≺-respʳ h e)
≺-tr h (≺s r) = ≺s (≺-tr h r)
≺-tr h (≺l n r) = ≺l n (≺-tr h r)
≺-tr h (≺i {p = ()} x ex r)
≺-tr h (≺u {r = ()} r′)

≺→⊑₀ : ∀ {a b : Ordᶜ zero} → a ≺ b → a ⊑⁰ b
≺→⊑₀ q h = ≺-tr h q

-- 右边换 ≅
≺-≅ʳ : ∀ {c a b : Ordᶜ zero} → c ≺ a → a ≅ b → c ≺ b
≺-≅ʳ = ≺-respʳ

-- V 不自小
V-irr : ∀ m a → V m a ≺ V m a → ⊥
V-irr m a q = ≺ᴵ-irrefl (toLevel-≺ h h q′)
  where
  G = GV m a
  h = forceᴺ-HS _ G
  q′ : forceᴺ _ G ≺ forceᴺ _ G
  q′ = ≺-≅ˡ (V-G m a G) (≺-respʳ q (≅-sym (V-G m a G)))

V-grow : ∀ {n m} (r : n <ᴸ m) → V n zero ≺ V m zero
V-grow {n} {m} r = ≺-≅ˡ (≅-sym (V-G n zero (GV n zero))) (≺-respʳ (Gr.grow r _ zero) (V-G m zero (GV m zero)))

-- 闭包行的第 0 项严格高于下面的第 0 行
first≺ : ∀ {n m} (r : n <ᴸ m) (CR : ClosRow r) → V n zero ≺ ys CR 0
first≺ {n} {m} r CR = ≺-respʳ (≺-≅ˡ (≅-trans (≅-sym (V-G n zero (GV n zero))) (forceᴺ-≅ (toZ-≅ (D-val r ok₀ ca₀ _ zero _ zero z≅)) (GV n zero) (proj₁ K))) (proj₂ K)) (first CR ok₀ ca₁ (Gf CR))
  where
  K = Fd-≺ r zero ok₀ ca₀ ca₁ (Gf CR)
```

## §2 没有标签的行

```agda
-- 链行第 0 项
ω-of : ∀ {X Y} (Rw : C.ChainRow X Y) → Lab (C.ChainRow.h Rw 0) ω̂
ω-of Rw = subst (λ Z → Lab Z ω̂) (sym (C.ChainRow.first Rw)) (ω-lab (C.ChainRow.G₀ Rw))

no-lab-pat : ∀ {m F qf G qg n} {r : n <ᴸ F 1} → view m ≡ chain F qf → view (F 0) ≡ chain G qg → view (F 1) ≡ clos r → (F 0 ≡ n) ⊎ (F 0 <ᴸ n) → ∀ s → Lab (V m zero) s → ⊥
no-lab-pat {m} {F} {qf} {G} {qg} {n} {r} cm c₀ c₁ hi s L = V-irr (F 0) zero (≺-respʳ strict e-y)
  where
  Rm = C.chain-row {m} {F} {qf} cm _ zero
  R₀ = C.chain-row {F 0} {G} {qg} c₀ _ zero
  CR = clos-row r c₁
  h = C.ChainRow.h Rm
  eh1 : h 1 ≅ V (F 0) zero
  eh1 = ≅-trans (C.ChainRow.rest Rm 0) (V-G (F 0) zero (GV (F 0) zero))
  eh2 : h 2 ≅ V (F 1) zero
  eh2 = ≅-trans (C.ChainRow.rest Rm 1) (V-G (F 1) zero (GV (F 1) zero))
  Ll : Lab (lim h) s
  Ll = Lab-≅ (≅-sym (≅-trans (≅-sym (V-G m zero (GV m zero))) (C.ChainRow.eq Rm))) L
  z₁ : Zk 1 (h 1) (C.ChainRow.h R₀ 0)
  z₁ = zs (≅-trans eh1 (≅-trans (≅-sym (V-G (F 0) zero (GV (F 0) zero))) (C.ChainRow.eq R₀))) (z0 (≅-refl⁰ _))
  z₂ : Zk 1 (h 2) (ys CR 0)
  z₂ = zs (≅-trans eh2 (value CR)) (z0 (≅-refl⁰ _))
  e-y : ys CR 0 ≅ V (F 0) zero
  e-y = ≅-trans (chain-rule Ll (ω-of Rm) (ω-of R₀) z₁ z₂) eh1
  strict : V (F 0) zero ≺ ys CR 0
  strict = st hi
    where
    st : (F 0 ≡ n) ⊎ (F 0 <ᴸ n) → V (F 0) zero ≺ ys CR 0
    st (inj₁ e) = subst (λ x → V x zero ≺ ys CR 0) (sym e) (first≺ r CR)
    st (inj₂ l) = ≺-tr (V-grow l) (first≺ r CR)
```

## §3 第二种形状: $F_1$ 也是链行

`no-lab-pat₂`: $F_0$, $F_1$ 都是链行. 这时 `chain-rule` 说 $F_0$ 行 $\cong\omega$, 而 $F_0$ 行的第 1 项是某个第 0 行, 不是后继. 前提写成 $V_{G_0}0$ 是极限, 对具体的码由 `clos-row` 给.

```agda
no-lab-pat₂ : ∀ {m F qf G qg G′ qg′} {g : ℕ → Ordᶜ zero} → view m ≡ chain F qf → view (F 0) ≡ chain G qg → view (F 1) ≡ chain G′ qg′ → V (G 0) zero ≅ lim g → ∀ s → Lab (V m zero) s → ⊥
no-lab-pat₂ {m} {F} {qf} {G} {qg} {G′} {qg′} {g} cm c₀ c₁ lg s L = bad
  where
  Rm = C.chain-row {m} {F} {qf} cm _ zero
  R₀ = C.chain-row {F 0} {G} {qg} c₀ _ zero
  R₁ = C.chain-row {F 1} {G′} {qg′} c₁ _ zero
  h = C.ChainRow.h Rm
  eh1 : h 1 ≅ V (F 0) zero
  eh1 = ≅-trans (C.ChainRow.rest Rm 0) (V-G (F 0) zero (GV (F 0) zero))
  eh2 : h 2 ≅ V (F 1) zero
  eh2 = ≅-trans (C.ChainRow.rest Rm 1) (V-G (F 1) zero (GV (F 1) zero))
  Ll : Lab (lim h) s
  Ll = Lab-≅ (≅-sym (≅-trans (≅-sym (V-G m zero (GV m zero))) (C.ChainRow.eq Rm))) L
  e₀′ : h 1 ≅ lim (C.ChainRow.h R₀)
  e₀′ = ≅-trans eh1 (≅-trans (≅-sym (V-G (F 0) zero (GV (F 0) zero))) (C.ChainRow.eq R₀))
  z₁ : Zk 1 (h 1) (C.ChainRow.h R₀ 0)
  z₁ = zs e₀′ (z0 (≅-refl⁰ _))
  z₂ : Zk 1 (h 2) (C.ChainRow.h R₁ 0)
  z₂ = zs (≅-trans eh2 (≅-trans (≅-sym (V-G (F 1) zero (GV (F 1) zero))) (C.ChainRow.eq R₁))) (z0 (≅-refl⁰ _))
  e-y : C.ChainRow.h R₁ 0 ≅ h 1
  e-y = chain-rule Ll (ω-of Rm) (ω-of R₀) z₁ z₂
  L₁ : Lab (h 1) ω̂
  L₁ = Lab-≅ (≅-sym e-y) (ω-of R₁)
  bad : ⊥
  bad with ω-parts L₁
  ... | f , ef , f0 , b , f1 , b0 with ≅-trans (≅-sym e₀′) ef
  ... | l≅ k with ≅-trans (≅-sym (≅-trans (k 1) f1)) (≅-trans (C.ChainRow.rest R₀ 0) (≅-trans (V-G (G 0) zero (GV (G 0) zero)) lg))
  ... | ()

-- 闭包行的第 0 行是极限
V-clos-lim : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → Σ (ℕ → Ordᶜ zero) λ g → V m zero ≅ lim g
V-clos-lim r c = ys (clos-row r c) , value (clos-row r c)
```

## §4 上面都不能值验收

```agda
no-⊑ : ∀ {c X Y : Ordᶜ zero} {t : T} → c ≺ X → (∀ s → Lab c s → ⊥) → Lab Y t → X ⊑⁰ Y → ⊥
no-⊑ {c} q nl lY le with lab-≺ (le q) lY
... | s , l = nl s l

V-z⊑ : ∀ m b → V m zero ⊑⁰ V m b
V-z⊑ m zero = λ h → h
V-z⊑ m (suc b) = ⊑-trans (V-z⊑ m b) (≺→⊑₀ (V-≺ m b))
V-z⊑ m (lim f s) = ⊑-trans (⊑-lim 0 (V-z⊑ m (f 0))) (≅→⊑ (≅-sym (V-lim m f s)))

-- 任何环境下的计值都是 V
Vev : ∀ m a {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (GᴺTᵠ m a ev z) ≅ V m a
Vev m a ev z = ≅-trans (forceᴺ-≅ (toZ-≅ (R→≈ᵠ (RΩ̇ m (≅ᴵ-refl a)) ok₀ e₀ ok₀ e₀ ev z _ zero z≅)) (GᴺTᵠ m a ev z) (GV m a)) (V-G m a (GV m a))

-- 第 α 行 (α ≠ 0): 第 0 行是它的 ≺ 子树
V-0≺ : ∀ m {b} → zero <ᴵ b → V m zero ≺ V m b
V-0≺ m zero = V-≺ m zero
V-0≺ m (suc q) = ≺-tr (V-0≺ m q) (V-≺ m _)
V-0≺ m (lim {f = f} {s = s} n q) = ≺-respʳ (≺l n (V-0≺ m q)) (≅-sym (V-lim m f s))

-- 一般形式: 一行没有标签, 上面的行与同高度的第 α 行都不能 ⊑⁰ 带标签的树
no-val-above : ∀ {p q} → (∀ s → Lab (V p zero) s → ⊥) → p <ᴸ q → ∀ α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (GᴺTᵠ q α ev z) ⊑⁰ Y → ⊥
no-val-above {p} {q} nl r α ev z lY le = no-⊑ (V-grow r) nl lY (⊑-trans (V-z⊑ q α) (⊑-trans (≅→⊑ (≅-sym (Vev q α ev z))) le))

no-val-row : ∀ {p α} → (∀ s → Lab (V p zero) s → ⊥) → zero <ᴵ α → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) {Y t} → Lab Y t → forceᴺ _ (GᴺTᵠ p α ev z) ⊑⁰ Y → ⊥
no-val-row {p} {α} nl q ev z lY le = no-⊑ (≺-respʳ (V-0≺ p q) (≅-sym (Vev p α ev z))) nl lY le
```
