> **机械克隆.** 由 `Uniform4Base` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (四): 解开 CPS, $\Omega+c$ 层上的数据树

> 接 [Uniform4Expt](Uniform4Expt.lagda.md) (帧式的塔在 $\psi_{\Omega+1}$ 上失败). 结论先说:
>
> 1. **设计: $\psi_\Omega(t)$ 不再是帧, 是数据树.** `O c φ` 是 $<\Omega_{\Omega+c+1}$ 的项的树, 构造子与 `fold` 的七种行一一对应 (后继、ω-极限、`limᵢ`、`ŝ`、`ĉ`、闭包、弱化), 外加 `oΩ`: 输入在低层 `O k` 的极限 ($k<c$), 共尾度 $\Omega_{\Omega+k+1}$. 这就是 (B) 要的 "输入是符号项", 只是符号项现在是树.
> 2. **折叠是普通的结构递归, 没有帧, 没有深度.** `ψ̄ : O c φ → Run φ` 给 $\psi_i(x)$ ($i$ 可数), 只有 9 行. `ψᵒ q : O c φ → O t (Fl ⊔ φ)` 给 $\psi_{\Omega+t}(x)$, 共尾度 $\Omega_{\Omega+m+1}$ 的情形比较 $m$ 与 $t$ (`cmp<`, ℕ 上的判定, 不碰 `<ᴵ-dec`). $\psi_i$ 与 $\psi_{\Omega+t}$ 的链是同一个 `chainᵒ`. 加法 `_⊕_` 在数据层, 所以 (A) 消失: $W+\psi_{\Omega+1}(\zeta+\Omega_{\Omega+1})$ 的链点含 $W$ 是因为 `oΩ` 的分支就是 $z\mapsto W+\cdots$.
> 3. **对 $c$ 一致.** 没有按 $c$ 的子句: `Ω̇ c`, `ψᵒ`, `ψ̄`, `_⊕_` 都对一切 $c$ 写一次.
> 4. **保守性: 不改 Uniform3 的任何定义, 但 Uniform3 的帧、深度塔 `A (suc d)`、`fold`、`Ω̂A`、`Sym` 在这里都不用.** 复用的只有深度 0 的 `Run`, `limᵢA`, `ŝA`, `ĉA`, `cloA`, `wk`, `sucRun`, 地板 `Flr`/`Ev`. 新树与 Uniform3 的树字面不同, 计值后 $\cong$ ([Uniform4Label](Uniform4Label.lagda.md) §4 的 `agree-O1`, `agree-sq`).
> 5. **不读记号.** 本文件不导入任何记号模块. 定义层依赖切片 (从 `ψ̄`, `ψᵒ`, `Ω̇`, `ι`, `tl` 出发, 经 Agda `--html` 的引用图) 到不了 `EBO`/`Correspond`/`StandardOmega`/`SystemOmega`/`Standard`/`Bachmann`/`Closure` 的任何定义 (0 条命中, 231 个定义).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform4Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; _+ˢ_)
open import OCF.Align.ScafLadderZUniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
```

## §1 数据树

```agda
data _<ᴸ_ : ℕ → ℕ → Set where
  zero : ∀ {m} → m <ᴸ suc m
  suc  : ∀ {m c} → m <ᴸ c → m <ᴸ suc c

Fl : Flr
Fl = fz ⊔ fk zero

module _ (c : ℕ) (U : ∀ {m} → m <ᴸ c → Flr → Set) where
  data O₊ : Flr → Set where
    o0   : ∀ {φ} → O₊ φ
    os   : ∀ {φ} → O₊ φ → O₊ φ
    ol   : ∀ {φ} → (ℕ → O₊ φ) → O₊ φ
    oi   : ∀ {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → O₊ φ) → O₊ φ
    oŝ   : ∀ {φ} (c₀ : Ordᴵ) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oĉ   : ∀ {φ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oclo : ∀ {φ} → O₊ (φ ⊔ fk zero) → ((η : Ordᴵ) → O₊ (φ ⊔ fk η)) → O₊ (φ ⊔ fk zero)
    owk  : ∀ {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → O₊ φ → O₊ ψ
    oΩ   : ∀ {φ m} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : m <ᴸ c) → (∀ ξ → U q ξ → O₊ (ξ ⊔ φ)) → O₊ φ

O  : ℕ → Flr → Set
Us : ∀ c {m} → m <ᴸ c → Flr → Set
O c φ = O₊ c (Us c) φ
Us (suc c) zero    φ = O c φ
Us (suc c) (suc q) φ = Us c q φ

outU : ∀ {c m} (q : m <ᴸ c) {φ} → Us c q φ → O m φ
outU zero    x = x
outU (suc q) x = outU q x

intoU : ∀ {c m} (q : m <ᴸ c) {φ} → O m φ → Us c q φ
intoU zero    x = x
intoU (suc q) x = intoU q x

tr< : ∀ {m c d} → m <ᴸ c → c <ᴸ d → m <ᴸ d
tr< r zero    = suc r
tr< r (suc q) = suc (tr< r q)

data Pen (m t : ℕ) : Set where
  pen   : m <ᴸ t → Pen m t
  chain : Pen m t

z<s : ∀ t → zero <ᴸ suc t
z<s zero    = zero
z<s (suc t) = suc (z<s t)

s<s : ∀ {a b} → a <ᴸ b → suc a <ᴸ suc b
s<s zero    = zero
s<s (suc q) = suc (s<s q)

upP : ∀ {m t} → Pen m t → Pen (suc m) (suc t)
upP (pen s) = pen (s<s s)
upP chain   = chain

cmp< : ∀ m t → Pen m t
cmp< m       zero    = chain
cmp< zero    (suc t) = pen (z<s t)
cmp< (suc m) (suc t) = upP (cmp< m t)
```

## §2 加法、嵌入、尾巴

```agda
asl : ∀ {a b d ℓ} → Ev ℓ (a ⊔ (b ⊔ d)) → Ev ℓ ((a ⊔ b) ⊔ d)
asl (u , (v , w)) = (u , v) , w

asr : ∀ {a b d ℓ} → Ev ℓ ((a ⊔ b) ⊔ d) → Ev ℓ (a ⊔ (b ⊔ d))
asr ((u , v) , w) = u , (v , w)

swp : ∀ {a b d ℓ} → Ev ℓ (a ⊔ (b ⊔ d)) → Ev ℓ (b ⊔ (a ⊔ d))
swp (u , (v , w)) = v , (u , w)

dupr : ∀ {a b ℓ} → Ev ℓ (a ⊔ b) → Ev ℓ (a ⊔ (b ⊔ b))
dupr (u , v) = u , (v , v)

dupr2 : ∀ {a b ℓ} → Ev ℓ (a ⊔ b) → Ev ℓ (a ⊔ ((a ⊔ b) ⊔ b))
dupr2 (u , v) = u , ((u , v) , v)

infixl 6 _⊕_
_⊕_ : ∀ {c φ ψ} → O c φ → O c ψ → O c (φ ⊔ ψ)
W ⊕ o0       = owk proj₁ W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ oclo t g = owk asl
                   (oclo (owk asr (W ⊕ t))
                         (λ η → owk asr (W ⊕ g η)))
W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))

ι : ∀ {c d} (q : c <ᴸ d) {φ} → O c φ → O d φ
ι q o0 = o0
ι q (os a) = os (ι q a)
ι q (ol F) = ol (λ n → ι q (F n))
ι q (oi ac f) = oi ac (λ x → ι q (f x))
ι q (oŝ c₀ t g) = oŝ c₀ (ι q t) (λ η e → ι q (g η e))
ι q (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι q o₀) (λ η e → ι q (o η e))
ι q (oclo t g) = oclo (ι q t) (λ η → ι q (g η))
ι q (owk le t) = owk le (ι q t)
ι q (oΩ fe r h) = oΩ fe (tr< r q) (λ ξ z → ι q (h ξ (intoU r (outU (tr< r q) z))))

tl : ∀ {c k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → O c φ
tl φ cv Ord₊ˢ.zero = o0
tl φ cv (Ord₊ˢ.suc a) = os (tl φ cv a)
tl φ cv (Ord₊ˢ.lim f) = ol (λ n → tl φ cv (f n))
tl φ cv (Ord₊ˢ.limᵢ q f) = oi (λ e → cv e q) (λ x → tl φ cv (f (intoˢ (<→◃ q) x)))
tl {k = suc k′} φ cv (Ord₊ˢ.up zero x) = owk (λ v → toFlo k′ (λ q → cv v (suc q))) (tl (flo k′) (cvFlo k′) x)
tl {k = lim f s} φ cv (Ord₊ˢ.up (self n) x) = owk (λ v → toFlo (f n) (λ q → cv v (lim n q))) (tl (flo (f n)) (cvFlo (f n)) x)
tl {k = zero} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oĉ c₀ (toZ t₀) (λ η e → toZ (g η e)) (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = suc _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = lim _ _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl φ cv (Ord₊ˢ.ĉᴸ c₀ t₀ g o₀ o) = oĉ c₀ t₀ g (tl φ cv o₀) (λ η e → tl φ cv (o η e))

Ω̇ : ∀ c → O c Fl
Ω̇ zero = oclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc c) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (ι zero z))
```

## §3 折叠

`ψᵒ q x` $=\psi_{\Omega+t}(x)$, `ψ̄ x` $=\psi_i(x)$ ($i$ 可数). 链 `γ` 对 `h` 的分支结构递归, 不读任何比较.

```agda
repᵒ : ∀ {c φ} → O c φ → ℕ → O c φ
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

chainᵒ : ∀ {m φ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (O m φ → O m φ) → ℕ → O m φ
chainᵒ {m} fe f zero    = owk fe (Ω̇ m)
chainᵒ fe f (suc n) = f (chainᵒ fe f n)

ψᵒ : ∀ {c t} → t <ᴸ c → ∀ {φ} → O c φ → O t (Fl ⊔ φ)
ψᵒΩ : ∀ {c t m} → t <ᴸ c → ∀ {φ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (r : m <ᴸ c) → (∀ ξ → Us c r ξ → O c (ξ ⊔ φ)) → Pen m t → O t (Fl ⊔ φ)

ψᵒ {t = t} q o0 = owk proj₁ (Ω̇ t)
ψᵒ q (os a) = ol (repᵒ (ψᵒ q a))
ψᵒ q (ol F) = ol (λ n → ψᵒ q (F n))
ψᵒ q (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ q (f x))
ψᵒ q (oŝ c₀ t g) = oŝ c₀ (ψᵒ q t) (λ η e → ψᵒ q (g η e))
ψᵒ q (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ q o₀) (λ η e → ψᵒ q (o η e))
ψᵒ q (oclo t g) = owk asl
                      (oclo (owk asr (ψᵒ q t))
                            (λ η → owk asr (ψᵒ q (g η))))
ψᵒ q (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q x)
ψᵒ {t = t} q (oΩ {m = m} fe r h) = ψᵒΩ q fe r h (cmp< m t)

ψᵒΩ q fe r h (pen s) =
  oΩ proj₁ s (λ ξ z → owk swp (ψᵒ q (h ξ (intoU r (outU s z)))))
ψᵒΩ q {φ} fe r h chain =
  ol (λ n → owk dupr2
                (ψᵒ q (h (Fl ⊔ φ) (intoU r (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU r z)))) n)))))

ψ̄ : ∀ {c φ} → O c φ → Run φ
ψ̄ o0 = wk 0 (λ e → tt) ∅ᴿ
ψ̄ (os a) = sucRun (ψ̄ a)
ψ̄ (ol F) = limA 0 (λ n → ψ̄ (F n))
ψ̄ (oi ac f) = limᵢA 0 ac (λ x → ψ̄ (f x))
ψ̄ (oŝ c₀ t g) = ŝA 0 c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
ψ̄ (oĉ c₀ z zg o₀ o) = ĉA 0 c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
ψ̄ (oclo t g) = cloA 0 (ψ̄ t) (λ η → ψ̄ (g η))
ψ̄ (owk le x) = wk 0 le (ψ̄ x)
ψ̄ {φ = φ} (oΩ fe r h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ (h φ (intoU r (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU r z)))) n)))))
```
