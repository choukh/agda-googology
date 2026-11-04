# 跨段, 下一步 (三): `Ω̇ᵀ cz 0` 的两个证书

> 入口 [CrossNext](CrossNext.lagda.md). **判决: HOLDS (编译过, 无条件, 无参数).** [CrossMTop](CrossMTop.lagda.md) 的 `Ω̇ᵀ cz 0 = tH 𝟏ᵀ stepT`. 下面的分支 `brE e` 就是 `ψ̄ᵀ` 算 `tH` 时对 `stepT e` 算的那一支.
>
> - `G-E e : Goodᴺ (brE e)`, 对一切 `e : cz ⊂ M′`, 由 [CrossNextDn](CrossNextDn.lagda.md) 的 `branch≈` 从已有的 `Gᵖ` 搬来.
> - **修法一 `T̂ᵀ`:** 沿 `T⊤` 自己的累加链取这些分支. `T⊤≅T̂ᵀ : T⊤ ≅ T̂ᵀ`, `fgh⊤≡`: FGH 逐点相等.
> - **修法二 `T̃ᵀ`:** 已有的 `ĉᴸ`, 已有的 `gc`, 分支 $(\hat\eta+1)\oplus$ `brE (⊂+ cz ⌈η⌉)`. 与 `T⊤` 之间 **没有** 定理, 修法三同样.
> - **修法三 `T̄ᵀ`:** 同一个 `ĉᴸ`, 输出是字面的 `oᵀ` (`stepT` 的分支, 没有前缀), 只有链的生成器带前缀 (`T̄-shape`, 对照 `Tᵀ-shape`). 单调性由 `up≺` 给. `T̄≼T̃ᵀ`, `T̃≼T̄ᵀ`: 与修法二的值互相 `≼`.
> - 字面的 `Tᵀ cz 0` (链的生成器不带前缀) **没有** 证书, 未走通, 不是否定.
>
> 全部写字面的 `Gᵖ`, `Gbr 𝒯`: 见 [CrossMInst](CrossMInst.lagda.md) 的说明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNextInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
import Data.Sum
open Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ; Ord₊ˢ; Ordˢ; addˢ; _+ˢ_; Ωˢ)
open import OCF.Free.Eq using (z≅; toZ-≅)
open import OCF.Free.Floor using (Ev; sucRun; wk; ∅ᴿ)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; forceᴺ; forceᴺ-≅; forceᴺ-HS; Goodᴺ-tr)
open import OCF.Free.Class using (lvG)
open import OCF.Free.Prefix using (_≅ᶻ_; zᶻ; sᶻ; lᶻ)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ; ⌈_⌉; _ᶜ+_; _≼_; z≼; ≼-trans; ≼-refl; dom₀)
open import OCF.Align.LadderOrdStr using (≅→≼)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el; ⊂+; ⊂-trans; up; up-mono; up-trans)
open import OCF.Align.CrossMUpTree using (up≺; ≺-≅ˡ)
open import OCF.Align.CrossNextEq
import OCF.Align.CrossMSim
open import OCF.Align.CrossMNode using (Node; Gbr; br; ↑br; yv; C; νT; ≺→⊑; plus-ᶜ+)
open import OCF.Align.CrossMInst using (𝒯; val≼T)
open import OCF.Align.CrossMClosed using (T⊤; fgh⊤)
open import OCF.Align.CrossMTop using (module 𝕎; κ′; module Raise; stepT; ψ̄ᵀ; 𝟏ᵀ; ok₁; Tᵀ; ≤end)
import OCF.Align.CrossNextDn as D
open import OCF.Align.CrossNextSum
```

## §1 分支

```agda
cz⊂ : ∀ M → cz ⊂ M
cz⊂ cz = ⊂r
cz⊂ (cs M) = es (cz⊂ M)
cz⊂ (cl g) = el (cz⊂ (g 0))

brE : ∀ {M′} → cz ⊂ M′ → Z
brE e = toZ (ψ̄ᵀ (Raise.ok′ e (𝕎.ok₀ {cz})) (Raise.riseA e (λ i → 𝕎.ok₀ {cz} i)) (stepT e) ev₀ zero)

dZ : ∀ {M′} (e : cz ⊂ M′) → toZ (Tᵖ M′ end zero ev₀ zero) ≅ᶻ brE e
dZ {M′} e = toZ-≅ (D.branch≈ M′ e (Raise.ok′ e (𝕎.ok₀ {cz})) (Raise.riseA e (λ i → 𝕎.ok₀ {cz} i)) ev₀ zero ev₀ zero z≅)

G-E : ∀ {M′} (e : cz ⊂ M′) → Goodᴺ (brE e)
G-E {M′} e = Goodᴺ-tr (dZ e) (Gᵖ M′ end zero)

-- 分支的值就是 M′ 顶上的第 0 行
E≅ : ∀ {M′} (e : cz ⊂ M′) → forceᴺ _ (Gᵖ M′ end zero) ≅ forceᴺ _ (G-E e)
E≅ e = forceᴺ-≅ (dZ e) _ (G-E e)
```

## §2 修法一

```agda
bᶜ : Code → Z
bᶜ M = brE (cz⊂ M)

Gᶜ : ∀ M → Goodᴺ (bᶜ M)
Gᶜ M = G-E (cz⊂ M)

hᶜ : ∀ M → forceᴺ _ (Gbr 𝒯 M) ≅ forceᴺ _ (Gᶜ M)
hᶜ M = forceᴺ-≅ (dZ (cz⊂ M)) (Gbr 𝒯 M) (Gᶜ M)

uᶜ : ∀ M N → forceᴺ _ (Gᶜ M) ⊑⁰ forceᴺ _ (Gᶜ (M ᶜ+ cs N))
uᶜ M N = ⊑-≅ (≅-sym (hᶜ M)) (≅-sym (hᶜ (M ᶜ+ cs N))) (↑br 𝒯 M N)

module A = Along 𝒯 bᶜ Gᶜ uᶜ hᶜ ωᶜ

T̂ᵀ : Ordᶜ zero
T̂ᵀ = A.T̂

HS-T̂ᵀ : HS T̂ᵀ
HS-T̂ᵀ = A.ĤS

fgĥ : ℕ → ℕ
fgĥ = FGH T̂ᵀ

T⊤≅T̂ᵀ : νT 𝒯 ωᶜ ≅ T̂ᵀ
T⊤≅T̂ᵀ = A.T̂≅

fgh⊤≡ : ∀ n → FGH (νT 𝒯 ωᶜ) n ≡ fgĥ n
fgh⊤≡ = FGH-≅ T⊤≅T̂ᵀ
```

## §3 修法二

`𝟏ᵀ` 的计值是 $\omega$ (`sucRun`), 这是已有的 $\gamma_0$ 这一支.

```agda
natˢ : ℕ → Ordˢ zero
natˢ zero = Ord₊ˢ.zero
natˢ (suc n) = Ord₊ˢ.suc (natˢ n)

natZ : ℕ → Z
natZ zero = Z.zero
natZ (suc n) = Z.suc (natZ n)

natˢ≡ : ∀ n → toZ (natˢ n) ≡ natZ n
natˢ≡ zero = refl
natˢ≡ (suc n) = cong Z.suc (natˢ≡ n)

-- 1 + n = n + 1
one+ : ∀ n → addˢ (Ωˢ zero) (λ q → q) (natˢ n) ≡ natˢ (suc n)
one+ zero = refl
one+ (suc n) = cong Ord₊ˢ.suc (one+ n)

iter≡ : ∀ n → Ord-Ord.iter (Ωˢ zero +ˢ_) Ord₊ˢ.zero n ≡ natˢ n
iter≡ zero = refl
iter≡ (suc n) = trans (cong (Ωˢ zero +ˢ_) (iter≡ n)) (one+ n)

dn : ∀ n → ofZ (natᴵ n) ≅ᶻ toZ (natˢ n)
dn zero = zᶻ
dn (suc n) = sᶻ (dn n)

t₀ᵀ : Z
t₀ᵀ = toZ (ψ̄ᵀ (𝕎.ok₀ {cz}) (λ i → 𝕎.ok₀ {cz} i) (𝟏ᵀ {cz} {zero}) ev₀ zero)

G₀ᵀ : Goodᴺ t₀ᵀ
G₀ᵀ = Goodᴺ-tr (lᶻ (λ n → subst (ofZ (natᴵ n) ≅ᶻ_) (cong toZ (sym (iter≡ n))) (dn n))) (G-ofZ ωᴵ)

-- 字面的 Tᵀ cz 0 就是不加前缀的 ĉᴸ: 分支是 brE, 起点是 t₀ᵀ
Tᵀ-shape : toZ (Tᵀ cz zero ev₀ zero) ≡ Z.ĉᴸ zero t₀ᵀ (λ η _ → brE (⊂+ cz ⌈ η ⌉)) t₀ᵀ (λ η _ → brE (⊂+ cz ⌈ η ⌉))
Tᵀ-shape = refl

module B = Sum (λ η → brE (⊂+ cz ⌈ η ⌉)) (λ η → G-E (⊂+ cz ⌈ η ⌉)) G₀ᵀ

T̃ᵀ : Ordᶜ zero
T̃ᵀ = B.T̃

HS-T̃ᵀ : HS T̃ᵀ
HS-T̃ᵀ = B.H̃S

fgh̃ : ℕ → ℕ
fgh̃ = FGH T̃ᵀ

```

## §4 修法三: 链带前缀, 输出不带

分支带前缀只为了让链记住上一个高度. 输出可以不带: `ĉᴸ` 的链 `S` 与输出 `o` 本来就分开. 这时 $\lceil\eta_k\rceil$ 字面地是 $\lceil\eta_{k+1}\rceil$ 的初始段 (差一个 `≋`), 单调性由 `up≺` 给, 输出的基本列没有前缀.

```agda
module SmE {M M′ : Code} (d : M ≋ M′) where
  open World d using (𝔸; 𝔹; u; ε; rowq)
  open OCF.Align.CrossMSim 𝔸 𝔹 u (λ {n} {m} → ε {n} {m}) <ᴾ-tri-self rowq public using (bridge)

≋-T : ∀ {M M′} (d : M ≋ M′) → forceᴺ _ (Gᵖ M end zero) ≅ forceᴺ _ (Gᵖ M′ end zero)
≋-T {M} {M′} d = forceᴺ-≅ (toZ-≅ (SmE.bridge d end zero zero (≅ᴵ-refl zero) ev₀ zero ev₀ zero z≅)) (Gᵖ M end zero) (Gᵖ M′ end zero)

strict : ∀ {a E} (p : cs a ⊂ E) → up (⊂-trans (es ⊂r) p) end <ᴾ end
strict {a} {E} p = subst (_<ᴾ end) (sym (up-trans (es ⊂r) p end)) (go (≤end (up p end)))
  where
  go : (up p end ≡ end) Data.Sum.⊎ (up p end <ᴾ end) → up p (low end) <ᴾ end
  go (inj₁ d) = subst (up p (low end) <ᴾ_) d (up-mono p {low end} {end} tt)
  go (inj₂ l) = <ᴾ-trans (up p (low end)) (up p end) end (up-mono p {low end} {end} tt) l

oᵀ : Ordᴵ → Z
oᵀ η = brE (⊂+ cz ⌈ η ⌉)

Goᵀ : ∀ η → Goodᴺ (oᵀ η)
Goᵀ η = G-E (⊂+ cz ⌈ η ⌉)

Eᵀ : Ordᴵ → Code
Eᵀ x = ⌈ lvG (B.GS x) ⌉

stepᵀ : ∀ x → forceᴺ _ (Goᵀ x) ⊑⁰ forceᴺ _ (Goᵀ (lvG (B.GS x)))
stepᵀ x = ≺→⊑ (≺-respʳ (≺-≅ˡ p₁ (up≺ (⊂-trans (es ⊂r) (B.path x)) end end (strict (B.path x)))) p₂)
  where
  p₁ : forceᴺ _ (Goᵀ x) ≅ forceᴺ _ (Gᵖ (B.Aˢ x) end zero)
  p₁ = ≅-trans (≅-sym (E≅ (⊂+ cz ⌈ x ⌉))) (≅-trans (≋-T (cz+≋ ⌈ x ⌉)) (≋-T (≋-sym (ofZ-≋ x))))
  p₂ : forceᴺ _ (Gᵖ (Eᵀ x) end zero) ≅ forceᴺ _ (Goᵀ (lvG (B.GS x)))
  p₂ = ≅-trans (≋-T (≋-sym (cz+≋ (Eᵀ x)))) (E≅ (⊂+ cz (Eᵀ x)))

-- 起点: 第 0 项 ω 是下一项的第 0 项
nr : ∀ n → toZ (natˢ n) ≅ᶻ toZ (natˢ n)
nr zero = zᶻ
nr (suc n) = sᶻ (nr n)

d₀ : t₀ᵀ ≅ᶻ t₀ᵀ
d₀ = lᶻ (λ n → subst (λ w → toZ w ≅ᶻ toZ w) (sym (iter≡ n)) (nr n))

mo₀ᵀ : forceᴺ _ G₀ᵀ ⊑⁰ forceᴺ _ (Goᵀ (B.η 0))
mo₀ᵀ h = ≺l 0 (≺-respʳ h (forceᴺ-≅ d₀ G₀ᵀ _))

module O = B.Out oᵀ Goᵀ G₀ᵀ mo₀ᵀ stepᵀ

-- 与字面的 Tᵀ cz 0 (Tᵀ-shape) 只差 ĉᴸ 的第 3 个字段: 链的生成器
T̄-shape : O.ẐO ≡ Z.ĉᴸ zero t₀ᵀ (λ x _ → B.S x) t₀ᵀ (λ x _ → oᵀ x)
T̄-shape = refl

T̄ᵀ : Ordᶜ zero
T̄ᵀ = O.T̄

HS-T̄ᵀ : HS T̄ᵀ
HS-T̄ᵀ = O.H̄S

fgh̄ : ℕ → ℕ
fgh̄ = FGH T̄ᵀ

-- 第 0 行的值不低于高度
domᵀ : ∀ x → x ≼ lvG (Goᵀ x)
domᵀ x = ≼-trans (≼-trans (dom₀ x) (plus-ᶜ+ zero cz ⌈ x ⌉))
  (≼-trans (val≼T (cz ᶜ+ ⌈ x ⌉)) (≅→≼ (toLevel-≅ (forceᴺ-HS _ (Gᵖ (cz ᶜ+ ⌈ x ⌉) end zero)) (forceᴺ-HS _ (Goᵀ x)) (E≅ (⊂+ cz ⌈ x ⌉)))))

-- 修法二与修法三的值互相 ≼
T̄≼T̃ᵀ : lvG O.ĜO ≼ lvG B.ĜS
T̄≼T̃ᵀ = O.T̄≼T̃ (≼-refl _) (λ x → lvG-≼ (gs (G-ofZ x)) (Goᵀ x))

T̃≼T̄ᵀ : lvG B.ĜS ≼ lvG O.ĜO
T̃≼T̄ᵀ = O.T̃≼T̄ domᵀ
```
