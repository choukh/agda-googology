# 极限目标上的完全派发: 一个固定的极限目标就要判定极限层号的字面相等

非验收文件. 编译定理, 无前提 (除 `full→wlpo` 带函数外延 `FunextL` 作显式前提). `tw 3` 的第 `suc a₀` 支 (读回域内) 的链第一步折到极限层号 `j₀`; 它的派发若对一切位置完全, 就对每个 `α` 判定字面相等 `T₀ ≡ Tα α` (`full→dec`; 接口形式 `stp-full→decᴾ`).
字面相等推出 `α` 全假 (`eq→false`); 反向要函数外延, 合起来是 WLPO (`full→wlpo`, 条件). `Lam` 的 `stp` 在这里与 N2 的那族支上都不完全 (`lam-not-full₀`, `lam-not-fullα`); N2 的 LPO 对 `Lam` 成立 (`lam-lpo`).
不否定位置带来历或带燃料的派发; 燃料搜索在 [YiLamNFuel](YiLamNFuel.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNLim where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; ⌜_⌝; lev; Way; keep; fold; Ext)
open import OCF.Lean.YiLamFold using (Lw; Lw-tw)
open import OCF.Lean.YiLamIf using (Uniᴾ; Domᴾ; StpFullᴾ)
open import OCF.Lean.YiLamNInst using (Lam; bC; stp)
open import OCF.Lean.YiUniIf using (At; IsKeep; Full)
open import OCF.Lean.YiUniNegBase using (Found; LPO; hit; one; pick; fα; lim-lgl; Tα; found→at)
open import OCF.Lean.YiUniNegCmp using (ηα)
open import OCF.Lean.YiUniNegStep using (step-full→lpo; r₀)
```

## 1 那一支与那一族位置

`a₀ = lim (λ _ → suc (lim (λ _ → 1)))`. 目标 `j₀ = ⌜a₀⌝` 的槽位层号只有 `T₀ = ⌜lim (λ _ → 1)⌝` 与 `zero`; 位置 `rα α` 的层号是 `Tα α`.

```agda
a₀ : R
a₀ = G.lim (λ _ → G.suc (G.lim (λ _ → one)))

l₀ : Lgl zero (G.suc a₀)
l₀ = (λ _ → inj₁ refl) , (λ _ → (λ _ → inj₁ refl) , (λ _ → tt))

j₀ T₀ : LF
j₀ = ⌜ a₀ ⌝
T₀ = ⌜ G.lim (λ _ → one) ⌝

V₀ : Lw (lc j₀ (up j₀))
V₀ = bC (Lw-tw 3) (G.suc a₀) l₀

rα : (ℕ → Bool) → Pre (upT j₀)
rα α = 0 , G.suc (G.em 0 (G.em tt (G.lim (fα α)))) , lim-lgl α , inj₁ tt

rα-lev : ∀ α → lev (upT j₀) (rα α) ≡ Tα α
rα-lev α = refl
```

## 2 完全推出字面相等的判定

```agda
Eqᴸ : (ℕ → Bool) → Set
Eqᴸ α = T₀ ≡ Tα α

Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

slot→eq : ∀ α (s : Pre j₀) → lev j₀ s ≡ Tα α → Eqᴸ α
slot→eq α (n , inj₁ tt) e = e
slot→eq α (n , inj₂ (m , inj₁ tt)) ()
slot→eq α (n , inj₂ (m , inj₂ ())) e

full→dec : (x : Ext j₀ (upT j₀)) → Full j₀ (upT j₀) x → ∀ α → Dec′ (Eqᴸ α)
full→dec x full α = go (x (rα α)) (λ e → full (rα α) ((0 , inj₁ tt) , e))
  where
  go : (w : Way j₀ (Tα α)) → (Eqᴸ α → IsKeep w) → Dec′ (Eqᴸ α)
  go (keep s e) c = inj₁ (slot→eq α s e)
  go fold c = inj₂ c
```

接口形式: 任意 `Uniᴾ` 与读回域, 第 0 个链点上的 `stp`.

```agda
at-topᴾ : (U : Uniᴾ) {k : LF} {g : Raw k → LF} (V : Uniᴾ.Bd U (lc k g)) {η : Raw k} →
  η ≡ G.top → (l : Lgl k η) → StpFullᴾ U V η l → StpFullᴾ U V G.top tt
at-topᴾ U V refl l f = f

stp-full→decᴾ : (U : Uniᴾ) (D : Domᴾ U) →
  StpFullᴾ U {k = j₀} {g = up j₀} (Uniᴾ.bC U (Domᴾ.bd-tw D 3) (G.suc a₀) l₀)
    (Uniᴾ.cpt U {k = j₀} {g = up j₀} (Uniᴾ.bC U (Domᴾ.bd-tw D 3) (G.suc a₀) l₀) 0)
    (Uniᴾ.cpt-lgl U {k = j₀} {g = up j₀} (Uniᴾ.bC U (Domᴾ.bd-tw D 3) (G.suc a₀) l₀) 0) →
  ∀ α → Dec′ (Eqᴸ α)
stp-full→decᴾ U D f = full→dec (Uniᴾ.stp U V G.top tt)
  (at-topᴾ U V (Uniᴾ.cpt-zero U V) (Uniᴾ.cpt-lgl U V 0) f)
  where
  V : Uniᴾ.Bd U (lc j₀ (up j₀))
  V = Uniᴾ.bC U (Domᴾ.bd-tw D 3) (G.suc a₀) l₀
```

## 3 字面相等与 WLPO

```agda
nthL : ℕ → LF → LF
nthL n (lim f) = f n
nthL n _ = zero

up-pick : ∀ b → suc zero ≡ up zero (pick b) → b ≡ false
up-pick false e = refl
up-pick true ()

∨-l : ∀ a b → (a ∨ b) ≡ false → a ≡ false
∨-l false b e = refl
∨-l true b ()

eq→false : ∀ α → Eqᴸ α → ∀ n → α n ≡ false
eq→false α e n = ∨-l (α n) (hit α n) (up-pick (hit α (suc n)) (cong (nthL (suc n)) e))

FunextL : Set
FunextL = ∀ {f g : ℕ → LF} → (∀ n → f n ≡ g n) → f ≡ g

hit-f : ∀ α → (∀ n → α n ≡ false) → ∀ n → hit α n ≡ false
hit-f α af zero = refl
hit-f α af (suc n) with α n | af n
... | .false | refl = hit-f α af n

false→eq : FunextL → ∀ α → (∀ n → α n ≡ false) → Eqᴸ α
false→eq fe α af = cong lim (fe (λ n → cong (λ b → up zero (pick b)) (sym (hit-f α af n))))

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ((∀ n → α n ≡ false) → ⊥)

full→wlpo : FunextL → (x : Ext j₀ (upT j₀)) → Full j₀ (upT j₀) x → WLPO
full→wlpo fe x full α with full→dec x full α
... | inj₁ e = inj₁ (eq→false α e)
... | inj₂ ne = inj₂ (λ af → ne (false→eq fe α af))
```

## 4 `Lam` 的 `stp`

在 `V₀` 上, 层号 `T₀` 的位置有槽位而 `dfin j₀` 折叠; N2 的那族支 (`ηα α`) 上同样. N2 的否定对 `Lam` 的形式.

```agda
r₀′ : Pre (upT j₀)
r₀′ = 0 , G.suc (G.em 0 (G.em tt (G.lim (λ _ → one)))) , ((λ _ → inj₁ refl) , (λ _ → tt)) , inj₁ tt

lam-not-full₀ : StpFullᴾ Lam V₀ G.top tt → ⊥
lam-not-full₀ full = full r₀′ ((0 , inj₁ tt) , refl)

lam-lpo : (∀ α → StpFullᴾ Lam {k = Tα α} {g = up (Tα α)} (bC (Lw-tw 3) (ηα α) (lim-lgl α)) G.top tt) → LPO
lam-lpo full = step-full→lpo (λ α → stp (bC (Lw-tw 3) (ηα α) (lim-lgl α)) G.top tt) full

lam-not-fullα : StpFullᴾ Lam {k = Tα (λ _ → true)} {g = up (Tα (λ _ → true))}
  (bC (Lw-tw 3) (ηα (λ _ → true)) (lim-lgl (λ _ → true))) G.top tt → ⊥
lam-not-fullα full = full (r₀ (λ _ → true)) (found→at (λ _ → true) (0 , refl))
```
