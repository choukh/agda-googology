# 同层上界的代价: 闭包的界被无关的地板抬高 (否定)

> 接 [Uniform5Syn](Uniform5Syn.lagda.md), [NotFree](NotFree.lagda.md). 不含记号. 结论写在 [UniformLv](UniformLv.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLvNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import OCF.Align.Level
import OCF.Align.Level as Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.NotFree using (Goodᴺ; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.UniformNF3Eq using (≅ᴵ→⊑ᴵ; _≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; wkR)
open import OCF.Align.Uniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; Top; Bd; sb; bound; accT; sup₁-up; sup₁-K; sup-K; sup-up; wk; top₀; toFlo)
open import OCF.Align.Uniform4Base using (Fl; _<ᴸ_; zero; suc)
open import OCF.Align.Uniform5Syn
open import OCF.Align.Uniform5SynPsi using (ψ̄)
open import OCF.Align.UniformNF5SynRel using (r∅)
import OCF.Align.UniformLvTree as LT
```

## §1 闭包的第 0 点必须高于界

`Goodᴺ` 的 `gc` 带 `dy m : c ⊑ᴵ toLevel (ys m) …`, 而第 0 个链点就是 `force t₀`. 所以闭包的界 $c$ 不高于第 0 点的层号. 这是 `Goodᴺ` 的定义, 不是额外假设.

```agda
lvG : ∀ {x : Z} → Goodᴺ x → Ordᴵ
lvG G = toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

clo⊑ : ∀ {c t₀ g o₀ o} → Goodᴺ (ĉᴸ c t₀ g o₀ o) → Σ (Goodᴺ t₀) λ G₀ → c ⊑ᴵ lvG G₀
clo⊑ (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  G₀ , ⊑ᴵ-trans (dy 0) (≅ᴵ→⊑ᴵ (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)))
```

## §2 地板进了 `Bd`

`Bd` 是地板各项与目标的逐点上确界, 所以 `flo K` 一进地板, 界就不低于 $K$.

```agda
Bd-K : ∀ K {i ℓ} (e : Ev ℓ ((fz ⊔ flo K) ⊔ fk zero)) (p : i <ᴵ ℓ) → K ⊑ᴵ Bd (bound ((fz ⊔ flo K) ⊔ fk zero) e p)
Bd-K zero      e p = z⊑
Bd-K (suc K)   {i} ((tt , a) , b) p = ⊑ᴵ-trans (sup₁-K (Bd T′) K (sb T′) a) (sup₁-up (Bd A) zero (sb A) b)
  where
  T′ = accT (top₀ p) fz tt
  A  = accT (top₀ p) (fz ⊔ fk K) (tt , a)
Bd-K (lim f s) {i} ((tt , a) , b) p = ⊑ᴵ-trans (sup-K (Bd T′) (lim f s) (sb T′) a) (sup₁-up (Bd A) zero (sb A) b)
  where
  T′ = accT (top₀ p) fz tt
  A  = accT (top₀ p) (fz ⊔ fb (lim f s)) (tt , a)
```

## §3 嵌入带来的地板

`Uniform5Syn` 的 `ι↓` 把 `Q n k` 嵌入 `Q m α`, 输出多一项地板 `flo k`, 这是 `oΩ↓` 的证据 `ac` 的来源. 它在 `oclo` 上照样加这一项. `Clo K r` 是 $\Omega_{\Omega}$ 的闭包经这样的嵌入之后的树: 节点是 $\Omega_\eta$, 与 $K$ 毫无关系, 但界不低于 $K$.

```agda
one : ∀ {m α φ} → Q m α φ → Q m α φ
one x = x

t₁ : ∀ {K} → Q 0 K (fz ⊔ fk zero)
t₁ = tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))

Clo : ∀ K → zero ◃ K → Q 1 zero (Fl ⊔ flo K)
Clo K r = ι↓ zero (ι r (Ω̇ 0 zero))

Fst : ∀ K → zero ◃ K → Q 1 zero ((fz ⊔ fk zero) ⊔ flo K)
Fst K r = ι↓ zero (ι r (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))))
```

**界落在 $K$ 之上 (`refl` 地展开).** 第 0 点是 `Fst`.

```agda
Clo-⊑ : ∀ K r {ℓ} (ev : Ev ℓ (Fl ⊔ flo K)) (z : zero <ᴵ ℓ) (G : Goodᴺ (toZ (ψ̄ (Clo K r) ev z))) →
        Σ (Goodᴺ (toZ (ψ̄ (Fst K r) ev z))) λ G₀ → K ⊑ᴵ lvG G₀
Clo-⊑ K r ev z G with clo⊑ G
... | G₀ , h = G₀ , ⊑ᴵ-trans (Bd-K K (sw₃ ev) z) h
```

## §4 第 0 点与 $K$ 无关

`Fst K r` 的计值只用目标与 `Fl` 的证据. 它不是 `R-ι↓` 的实例 (`rs` 要求地板对齐, 而这里 $K$ 不同), 所以直接在值层走一遍 `tl`.

```agda
leS : ∀ {k′ K} (cv : ∀ {L} → Ev L (flo (suc k′)) → Simᴵ (suc k′) L) {L} → Ev L (flo (suc k′) ⊔ flo K) → Ev L (flo k′ ⊔ flo K)
leS {k′} cv e = toFlo k′ (λ q → cv (proj₁ e) (suc q)) , proj₂ e

leL : ∀ {f s K} n (cv : ∀ {L} → Ev L (flo (lim f s)) → Simᴵ (lim f s) L) {L} → Ev L (flo (lim f s) ⊔ flo K) → Ev L (flo (f n) ⊔ flo K)
leL {f} n cv e = toFlo (f n) (λ q → cv (proj₁ e) (lim n q)) , proj₂ e

B : ∀ {K₁ K₂ c₁ c₂ k₁ k₂} (r₁ : c₁ ◃ K₁) (r₂ : c₂ ◃ K₂) {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L}
    {a : Ordˢ k₁} {b : Ordˢ k₂} → a ≅ˢ b →
    ψ̄ {1} {zero} (ι↓ zero (ι r₁ (tl {0} (flo k₁) cv a))) ≈ᴿ ψ̄ {1} {zero} (ι↓ zero (ι r₂ (tl {0} (flo k₂) cv′ b)))
B r₁ r₂ z≅ = wkR _ _ r∅
B r₁ r₂ (s≅ le e) = sucR (B r₁ r₂ e)
B r₁ r₂ (l≅ h) = limR (λ n → B r₁ r₂ (h n))
B {k₁ = k₁} {k₂ = k₂} r₁ r₂ (lᵢ≅ {p = q} e h) = limᵢR e (λ x y dd → B r₁ r₂ (h x y (≅→Rˢ (<→◃ q) dd)))
B {k₁ = suc k′} r₁ r₂ {cv = cv} (upˡ {r = zero} d) = wkR (leS cv) (λ e → e) (B r₁ r₂ d)
B {k₁ = lim f s} r₁ r₂ {cv = cv} (upˡ {r = self n} d) = wkR (leL n cv) (λ e → e) (B r₁ r₂ d)
B {k₂ = suc k′} r₁ r₂ {cv′ = cv} (upʳ {r = zero} d) = wkR (λ e → e) (leS cv) (B r₁ r₂ d)
B {k₂ = lim f s} r₁ r₂ {cv′ = cv} (upʳ {r = self n} d) = wkR (λ e → e) (leL n cv) (B r₁ r₂ d)
B {k₁ = zero} {k₂ = zero} r₁ r₂ (ŝ≅ k ec et eg) =
  ĉR ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (B r₁ r₂ et) (λ η e η′ e′ eη → B r₁ r₂ (eg η e η′ e′ eη))
B {k₁ = zero} {k₂ = suc _}   r₁ r₂ (ŝ≅ () ec et eg)
B {k₁ = zero} {k₂ = lim _ _} r₁ r₂ (ŝ≅ () ec et eg)
B {k₁ = suc _}   {k₂ = zero} r₁ r₂ (ŝ≅ () ec et eg)
B {k₁ = lim _ _} {k₂ = zero} r₁ r₂ (ŝ≅ () ec et eg)
B {k₁ = suc _} {k₂ = suc _} r₁ r₂ (ŝ≅ k ec et eg) = ŝR ec (B r₁ r₂ et) (λ η e η′ e′ eη → B r₁ r₂ (eg η e η′ e′ eη))
B {k₁ = suc _} {k₂ = lim _ _} r₁ r₂ (ŝ≅ k ec et eg) = ŝR ec (B r₁ r₂ et) (λ η e η′ e′ eη → B r₁ r₂ (eg η e η′ e′ eη))
B {k₁ = lim _ _} {k₂ = suc _} r₁ r₂ (ŝ≅ k ec et eg) = ŝR ec (B r₁ r₂ et) (λ η e η′ e′ eη → B r₁ r₂ (eg η e η′ e′ eη))
B {k₁ = lim _ _} {k₂ = lim _ _} r₁ r₂ (ŝ≅ k ec et eg) = ŝR ec (B r₁ r₂ et) (λ η e η′ e′ eη → B r₁ r₂ (eg η e η′ e′ eη))
B r₁ r₂ (ĉ≅ ec dt dg eo eO) = ĉR ec dt dg (B r₁ r₂ eo) (λ η e η′ e′ eη → B r₁ r₂ (eO η e η′ e′ eη))
```

`Fst` 的计值与 $K$ 无关. 只差最外面的 `oi`.

```agda
F-≈ : ∀ {K₁ K₂} (r₁ : zero ◃ K₁) (r₂ : zero ◃ K₂) → ψ̄ (Fst K₁ r₁) ≈ᴿ ψ̄ (Fst K₂ r₂)
F-≈ r₁ r₂ = limᵢR (≅ᴵ-refl zero) (λ x y d → wkR (λ e → tt , proj₂ e) (λ e → tt , proj₂ e) (B r₁ r₂ {cv = cvFlo zero} {cv′ = cvFlo zero} d))
```

## §5 否定: 不是对一切 $K$ 都有证书

环境 $\ell=K+1$. 对比: [UniformNF5Main](UniformNF5Main.lagda.md) 的 `GᴺΩ̇ η` 对一切 $\eta$ 成立, 那棵树的闭包没有这项地板.

```agda
envK : ∀ K → zero <ᴵ K → Ev (suc K) (Fl ⊔ flo K)
envK K q = (tt , one′) , toFlo K suc
  where
  one′ : Simᴵ (suc zero) (suc K)
  one′ zero = suc q
  one′ (suc ())

noAll : ((K : Ordᴵ) (q : zero <ᴵ K) → Goodᴺ (toZ (ψ̄ (Clo K (<→◃ q)) (envK K q) (suc q)))) → ⊥
noAll all with Clo-⊑ (suc zero) (<→◃ zero) (envK _ zero) (suc zero) (all (suc zero) zero)
... | G₀ , s⊑ Level.z≅ q′ with Clo-⊑ (suc (lvG G₀)) (<→◃ (suc q′)) (envK _ (suc q′)) (suc (suc q′)) (all (suc (lvG G₀)) (suc q′))
...   | G₁ , s⊑ e q = ≺ᴵ-irrefl (≺ᴵ-respʳ (via e q) (toLevel-≅ _ _ (forceᴺ-≅ (toZ-≅ (F-≈ (<→◃ (suc q′)) (<→◃ zero) (envK _ (suc q′)) (suc (suc q′)) (envK _ zero) (suc zero) (≅ᴵ-refl zero))) G₁ G₀)))
```

## §6 修正: 高度不同的地板不进界

[UniformLvTree](UniformLvTree.lagda.md) 的闭包只取 `prj h π`. 所以 $h\ne h'$ 时那一项地板在界里消失 (定义相等), 上面的论证就没有了起点; 高度相同时它还在, 那是真正要比较的情形. 这只说明 `noAll` 的论证不适用, **不是** `Goodᴺ` 成立的证明.

```agda
prj-blind : ∀ K → LT.prj 0 (LT.tk 1 K) ≡ fz
prj-blind K = refl

prj-blind₂ : ∀ K → LT.prj 1 (LT.tk 2 K) ≡ fz
prj-blind₂ K = refl

prj-self : ∀ K → LT.prj 1 (LT.tk 1 K) ≡ fk K
prj-self K = refl
```
