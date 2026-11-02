# Uniform3 上的无符号闭包定理 (四): 上下文类下标的遗传好树

> [UniformPendingGoodClass](UniformPendingGoodClass.lagda.md) 的重编译, 一个字符都没有改 (除模块名). 定义与 `Ωg` 不读折叠的 `up (self n)` 子句.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3Class where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; Restrˢ; resˢ; res⁻ˢ)
open Restrˢ
open import OCF.Align.UniformS using (⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl;
  trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; self-trˢ; self-tr⁻ˢ; ĉ-refl₀; ĉ-reflg; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; backˢ-≅; back⁻ˢ-≅)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3Base using (Obs; idO; fo; addo; tro; tr⁻o; run; _≈ᵒ_; ≈ᵒ-reflˡ; ≈ᵒ-reflʳ; run-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr; _⊑ᵒ_; up-l; up-r; Ω-monoᵒ; tr-cong; tr⁻-cong; fold-cong; add-cong; rule4ᵒ; B1; FlΛ-fold)
open import OCF.Align.UniformNF3NGrow using (_⊑ᴱ_; Ctx; ctx-refl; PFl; AFl; afl; 𝟏; ⊑ᴱ-≅ʳ; ⊑ᴱ-trans; ⊑ᴱ-≅ˡ; ≅→⊑ᴱ; up-rᴱ; limᵢ-rᴱ; lim-rᴱ; add-floorᴱ; add-rᴱ; add-congᴱ; tr-congᴱ; tr⁻-congᴱ; B1ᴱ; Ω1ᴱ; Ω<ᴱ; fold-congᴱ; ŝ-rᴱ; ĉ-rᴱ; suc-fold)
```

## §1 上下文类

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤
```

`CvP C b`: 在上下文 $C$ 下, 尾巴地板 $\sqsupseteq\Omega_b$ 的计值, 对任意证书, 层号 $\sqsupseteq b+1$. 它是条件式的: 不要求低处的证书存在. `Vis K C`: $C$ 是上下文且对一切 $b\prec K$ 有 `CvP`. `isId`: 第 0 层只读 `idO`, 第 0 层的闭包与后面的上下文无关. `VisT i`: 目标 $i$ 的值所需的上下文类. `Above j C′ D`: $C'$ 在节点 $j$ 处压在 $D$ 之上: 任意尾巴在 $C'$ 下的值就是某个 $\sqsupseteq\Omega_j$ 的 $u$ 在 $D$ 下的值. 这是 "外层吸收者" 的语义形式.

```agda
Cl : Ordᴵ → Set₁
Cl ℓ = Obs ℓ → Set

lvG : ∀ {x : Z} → Goodᴺ x → Ordᴵ
lvG G = toLevel (forceᴺ _ G) (forceᴺ-HS _ G)

FlΩ : ∀ {k} → Ordᴵ → Ordˢ k → Set
FlΩ b t = ∀ {k₀} {x : Ordˢ k₀} → x ≅ˢ x → x ⊑ᴱ Ωˢ b → x ⊑ᴱ t

CvP : ∀ {k} → Obs k → Ordᴵ → Set
CvP {k} C b = (t : Ordˢ k) → t ≅ˢ t → FlΩ b t → (G : Goodᴺ (toZ (run C t))) → suc b ⊑ᴵ lvG G

Tw : ∀ {k} → Obs k → Set
Tw {k} C = (s : Ordˢ k) → s ≅ˢ s → (∀ {K} → 𝟏 {K} ⊑ᴱ s) → (G : Goodᴺ (toZ (run C s))) → one⁰ ≺ forceᴺ _ G

record Vis (K : Ordᴵ) {k} (C : Obs k) : Set where
  constructor vis
  field
    cx : Ctx C
    tw : NZ k → Tw C
    cp : ∀ {b} → b ≺ᴵ K → CvP C b
open Vis public

isId : Cl zero
isId O = O ≡ idO

Inp : ∀ j → Cl j → Cl j
Inp zero      𝓓 = isId
Inp (suc j)   𝓓 = 𝓓
Inp (lim f s) 𝓓 = 𝓓

VisT : ∀ i → Cl i
VisT zero      = isId
VisT (suc i)   = Vis (suc (suc i))
VisT (lim f s) = Vis (suc (lim f s))

record Above (j : Ordᴵ) {ℓ} (C′ : Obs ℓ) (D : Obs j) : Set where
  constructor above
  field
    cx′  : Ctx C′
    wrap : ∀ (t : Ordˢ ℓ) → t ≅ˢ t → Σ (Ordˢ j) λ u → (u ≅ˢ u) × (Ωˢ j ⊑ᴱ u) × (run C′ t ≅ˢ run D u)
open Above public

_⟨_⟩ : ∀ {ℓ j} → (Obs ℓ → Obs j) → Cl ℓ → Cl j
_⟨_⟩ W 𝓔 D = Ctx D × (Σ _ λ C → 𝓔 C × (D ≈ᵒ W C))

Dn : ∀ {k ℓ} → k ◃₁ ℓ → Cl ℓ → Cl k
Dn {k = zero}    r 𝓖 = isId
Dn {k = suc _}   r 𝓖 = λ D → Ctx D × (Σ _ λ C → 𝓖 C × (D ≈ᵒ C))
Dn {k = lim _ _} r 𝓖 = λ D → Ctx D × (Σ _ λ C → 𝓖 C × (D ≈ᵒ C))

_∧_ : ∀ {ℓ} → Cl ℓ → Cl ℓ → Cl ℓ
(𝓖 ∧ 𝓑) C = 𝓖 C × 𝓑 C

Wit : ∀ i → Cl i → Set
Wit zero      𝓖 = 𝓖 idO
Wit (suc _)   𝓖 = ⊤
Wit (lim _ _) 𝓖 = ⊤

wit-nz : ∀ i {𝓖 : Cl i} → NZ i → Wit i 𝓖
wit-nz (suc _)   nz = tt
wit-nz (lim _ _) nz = tt

wit-map : ∀ i {𝓖 𝓖′ : Cl i} → (∀ {C} → 𝓖′ C → 𝓖 C) → Wit i 𝓖′ → Wit i 𝓖
wit-map zero      h w = h w
wit-map (suc _)   h w = tt
wit-map (lim _ _) h w = tt

record FlOver {ℓ} (a : Ordˢ ℓ) (O C″ : Obs ℓ) : Set where
  constructor flo-over
  field
    cxo : Ctx C″
    flw : ∀ (t : Ordˢ ℓ) → t ≅ˢ t → (G : Goodᴺ (toZ (run C″ t))) → Σ (Goodᴺ (toZ (run O a))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
open FlOver public
```

## §2 遗传好树

下标 `s`: `true` 是尾巴 (可含 `b1`、`bu`, 即 $\Omega_\eta$ 的形状), `false` 是折叠的输出. `bi` 没有水位: 分支的输入类由 `W` 决定 (输入 $z$ 在上下文 $C$ 下处于 `W C`, `Wf`), 分支对一切子类成立. `St` 说类对 "压上一层" 封闭, 这是吸收的全部内容; `Wv` 给输入的 $\Omega_j$ 与目标 $j$ 的值. 闭包 `bŝ`: 分支只在类有居留时要求好 (`gg`), 带守卫 `𝓑 η`; `ch₀`/`chS` 说守卫沿链封闭. `bs`: 后继, 它的类 `𝓚` 对 "压在 $a$ 之上" 封闭 (`FlOver`), 折叠后的和要用. `bĉ`: 第 0 层闭包被折叠后的形状, 只在链点上要求.

```agda
module _ (ℓ : Ordᴵ) (G< : Bool → (i : Ordᴵ) (r : i ◃ ℓ) → Cl i → Uˢ i r → Set₁) where
  data Good₊ : Bool → Cl ℓ → Ordˢ ℓ → Set₁ where
    bz : ∀ {s 𝓖} → Good₊ s 𝓖 Ord₊ˢ.zero
    b1 : ∀ {𝓖} → Good₊ true 𝓖 (Ord₊ˢ.suc Ord₊ˢ.zero)
    bs : ∀ {s 𝓖} {a : Ordˢ ℓ} (𝓚 : Cl ℓ) → (∀ {C} → 𝓖 C → 𝓚 C) → a ≅ˢ a → Good₊ s 𝓚 a →
         (NZ ℓ → ∀ {O C″} → 𝓚 O → FlOver a O C″ → 𝓚 C″) → (NZ ℓ → ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C) → Good₊ s 𝓖 (Ord₊ˢ.suc a)
    bl : ∀ {s 𝓖} {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ s 𝓖 (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ s 𝓖 (Ord₊ˢ.lim h)
    bi : ∀ {s 𝓖 j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ}
         (𝓖₀ : Cl ℓ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Obs ℓ → Obs j) →
         (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ run C (f (intoˢ (<→◃ p) u))) →
         (∀ (𝓔 : Cl ℓ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z →
            G< true j (<→◃ p) (Inp j (W ⟨ 𝓔 ⟩)) (intoˢ (<→◃ p) z) → Good₊ s 𝓔 (f (intoˢ (<→◃ p) z))) →
         (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
         (∀ {C C′} → 𝓖₀ C → Above j C′ (W C) → 𝓖₀ C′) →
         (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓖₀ C′ → 𝓖₀ C) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
         Good₊ s 𝓖 (Ord₊ˢ.limᵢ p f)
    bu : ∀ {𝓖 k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< true k (◃₁→◃ r) (Dn r 𝓖) x → Good₊ true 𝓖 (Ord₊ˢ.up r x)
    bŝ : ∀ {s 𝓖 c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} (𝓑 : Ordᴵ → Cl ℓ) →
         (∀ {η η′ C} → η ≅ᴵ η′ → 𝓑 η C → 𝓑 η′ C) →
         Good₊ s 𝓖 t₀ → (∀ η e → Wit ℓ (𝓖 ∧ 𝓑 η) → Good₊ s (𝓖 ∧ 𝓑 η) (g η e)) →
         t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
         (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → c ⊑ᴵ lvG G) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → c ⊑ᴵ lvG G) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (run C t₀))) → 𝓑 (lvG G) C) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (run C (g η e)))) → 𝓑 (lvG G) C) →
         Good₊ s 𝓖 (Ord₊ˢ.ŝ c t₀ g)
    bĉ : ∀ {s 𝓖 c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
         (ys : ℕ → Ordᶜ zero) (hy : ∀ m → HS (ys m)) (dy : ∀ m → c ⊑ᴵ toLevel (ys m) (hy m))
         (G₀ : Goodᴺ t₀) (l₀ : forceᴺ t₀ G₀ ≅ ys 0)
         (Gg : ∀ m → Goodᴺ (g (toLevel (ys m) (hy m)) (dy m)))
         (lE : ∀ m → forceᴺ _ (Gg m) ≅ ys (suc m)) →
         Good₊ s 𝓖 o₀ → (∀ k → Good₊ s 𝓖 (o (toLevel (ys k) (hy k)) (dy k))) →
         o₀ ⊑ᵒ o (toLevel (ys 0) (hy 0)) (dy 0) → (∀ k → o (toLevel (ys k) (hy k)) (dy k) ⊑ᵒ o (toLevel (ys (suc k)) (hy (suc k))) (dy (suc k))) →
         Good₊ s 𝓖 (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

Gd : ∀ {ℓ} → Bool → (i : Ordᴵ) (r : i ◃ ℓ) → Cl i → Uˢ i r → Set₁
Gd s i zero         𝓖 x = Good₊ i Gd s 𝓖 x
Gd s i (suc r)      𝓖 x = Gd s i r 𝓖 x
Gd s _ (self {f} n) 𝓖 x = Good₊ (f n) Gd s 𝓖 x
Gd s i (lim n r)    𝓖 x = Gd s i r 𝓖 x

Good : ∀ {ℓ} → Bool → Cl ℓ → Ordˢ ℓ → Set₁
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ s 𝓖} (r : i ◃ ℓ) {x : Ordˢ i} → Gd s i r 𝓖 (intoˢ r x) → Good s 𝓖 x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ s 𝓖} (r : i ◃ ℓ) {x : Ordˢ i} → Good s 𝓖 x → Gd s i r 𝓖 (intoˢ r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g
```

## §3 类单调与第 0 层证书

`Good→N`: 类含 `idO` 的第 0 层好树给出 `Goodᴺ`. 闭包的链在这里生成: `ys 0` 是第 0 点的计值, `ys (m+1)` 是分支在 `ys m` 层号处的计值. 证书只在链点上要, 守卫 `𝓑 η idO` 由 `ch₀`/`chS` 沿链传.

```agda
dn-map : ∀ {k ℓ} (r : k ◃₁ ℓ) {𝓖 𝓖′ : Cl ℓ} → (∀ {C} → 𝓖′ C → 𝓖 C) → ∀ {D} → Dn r 𝓖′ D → Dn r 𝓖 D
dn-map {k = zero}    r h x = x
dn-map {k = suc _}   r h (x , C , c , o) = x , C , h c , o
dn-map {k = lim _ _} r h (x , C , c , o) = x , C , h c , o

Good-mono : ∀ {ℓ s} {𝓖 𝓖′ : Cl ℓ} {x : Ordˢ ℓ} → (∀ {C} → 𝓖′ C → 𝓖 C) → Good s 𝓖 x → Good s 𝓖′ x
Good-mono h bz = bz
Good-mono h b1 = b1
Good-mono h (bs 𝓚 v ea g clk cgk) = bs 𝓚 (λ c → v (h c)) ea g clk cgk
Good-mono h (bl hg st) = bl (λ n → Good-mono h (hg n)) st
Good-mono h (bi 𝓖₀ inc W Wf hb Wv St cg hm) = bi 𝓖₀ (λ c → inc (h c)) W Wf hb Wv St cg hm
Good-mono h (bu {r = zero} g)   = bu {r = zero} (Good-mono (dn-map zero h) g)
Good-mono h (bu {r = self n} g) = bu {r = self n} (Good-mono (dn-map (self n) h) g)
Good-mono h (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) =
  bŝ 𝓑 Bc (Good-mono h g0) (λ η e w → Good-mono (λ { (c , b) → h c , b }) (gg η e (wit-map _ (λ { (c , b) → h c , b }) w)))
     et eg m mm (λ c G → d₀ (h c) G) (λ η e c b G → dE η e (h c) b G) (λ c G → ch₀ (h c) G) (λ η e c b G → chS η e (h c) b G)
Good-mono h (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) = bĉ ys hy dy G₀ l₀ Gg lE (Good-mono h go) (λ k → Good-mono h (gO k)) mo mO

record Pt₀ (c : Ordᴵ) (B : Ordᴵ → Set) : Set where
  constructor pt
  field
    Yp : Ordᶜ zero
    hp : HS Yp
    dp : c ⊑ᴵ toLevel Yp hp
    bp : B (toLevel Yp hp)
open Pt₀ public

Good→N : ∀ {s} {𝓖 : Cl zero} {x : Ordˢ zero} → 𝓖 idO → Good s 𝓖 x → Goodᴺ (toZ x)
Good→N i bz = gz
Good→N i b1 = gs gz
Good→N i (bs 𝓚 v ea g clk cgk) = gs (Good→N (v i) g)
Good→N i (bl hg st) = gl (λ n → Good→N i (hg n)) (λ n → st n idO (Good→N i (hg n)) (Good→N i (hg (suc n))))
Good→N i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm)
Good→N i (bu {r = ()} g)
Good→N {𝓖 = 𝓖} i (bŝ {c = c} {t₀ = t₀} {g = g} 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) =
  gc (λ k → Yp (P k)) (λ k → hp (P k)) (λ k → dp (P k)) G₀ (≅-refl⁰ _) Gk (λ k → ≅-refl⁰ _) G₀ Gk
     (m _ (dp (P 0)) idO G₀ (Gk 0))
     (λ k → mm _ (dp (P k)) _ (dp (P (suc k))) (toLevel-⊑ (hp (P k)) (hp (P (suc k))) (Ymono k)) idO (Gk k) (Gk (suc k)))
  where
  G₀ : Goodᴺ (toZ t₀)
  G₀ = Good→N i g0
  P  : ℕ → Pt₀ c (λ η → 𝓑 η idO)
  Gk : ∀ k → Goodᴺ (toZ (g (toLevel (Yp (P k)) (hp (P k))) (dp (P k))))
  P zero    = pt (forceᴺ _ G₀) (forceᴺ-HS _ G₀) (d₀ i G₀) (ch₀ i G₀)
  P (suc k) = pt (forceᴺ _ (Gk k)) (forceᴺ-HS _ (Gk k)) (dE _ (dp (P k)) i (bp (P k)) (Gk k)) (chS _ (dp (P k)) i (bp (P k)) (Gk k))
  Gk k = Good→N (i , bp (P k)) (gg _ (dp (P k)) (i , bp (P k)))
  Ymono : ∀ k → Yp (P k) ⊑⁰ Yp (P (suc k))
  Ymono zero    = m _ (dp (P 0)) idO G₀ (Gk 0)
  Ymono (suc k) = mm _ (dp (P k)) _ (dp (P (suc k))) (toLevel-⊑ (hp (P k)) (hp (P (suc k))) (Ymono k)) idO (Gk k) (Gk (suc k))
Good→N i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) =
  gc ys hy dy G₀ l₀ Gg lE (Good→N i go) (λ k → Good→N i (gO k))
     (mo idO (Good→N i go) (Good→N i (gO 0))) (λ k → mO k idO (Good→N i (gO k)) (Good→N i (gO (suc k))))
```

## §4 语义引理: 观测的关系、读数、上下文的下移

`pull`: 沿 $\cong$ 读层号下界. `sh r C`: 把上下文下移一层 (`up` 的对偶). `Vis-≈`, `Vis-sh`: `Vis` 对相似与下移封闭.

```agda
≈-sym : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O
≈-sym idO = idO
≈-sym (fo o r) = fo (≈-sym o) r
≈-sym (addo o k e) = addo (≈-sym o) (sym k) (≅ˢ-sym e)
≈-sym (tro o) = tro (≈-sym o)
≈-sym (tr⁻o o) = tr⁻o (≈-sym o)

≈-trans : ∀ {k k′ k″} {O : Obs k} {O′ : Obs k′} {O″ : Obs k″} → O ≈ᵒ O′ → O′ ≈ᵒ O″ → O ≈ᵒ O″
≈-trans idO idO = idO
≈-trans (fo o r) (fo o′ _) = fo (≈-trans o o′) r
≈-trans (addo o k e) (addo o′ k′ e′) = addo (≈-trans o o′) (trans k k′) (≅ˢ-trans e e′)
≈-trans (tro o) (tro o′) = tro (≈-trans o o′)
≈-trans (tr⁻o o) (tr⁻o o′) = tr⁻o (≈-trans o o′)

≺-≅tw : ∀ {X Y : Ordˢ zero} → X ≅ˢ Y → (∀ (H : Goodᴺ (toZ Y)) → one⁰ ≺ forceᴺ _ H) → (G : Goodᴺ (toZ X)) → one⁰ ≺ forceᴺ _ G
≺-≅tw d k G = ≺-respʳ (k (Goodᴺ-tr (toZ-≅ d) G)) (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) G) G)

pull : ∀ {X Y : Ordˢ zero} {c} → X ≅ˢ Y → (∀ (H : Goodᴺ (toZ Y)) → c ⊑ᴵ lvG H) → (G : Goodᴺ (toZ X)) → c ⊑ᴵ lvG G
pull d k G = ⊑ᴵ-≅ʳ (k (Goodᴺ-tr (toZ-≅ d) G)) (toLevel-≅ (forceᴺ-HS _ (Goodᴺ-tr (toZ-≅ d) G)) (forceᴺ-HS _ G) (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) G) G))

τ₁ : ∀ {k ℓ} → k ◃₁ ℓ → Simᴵ k ℓ
τ₁ zero     q = suc q
τ₁ (self n) q = lim n q

sh : ∀ {k ℓ} → k ◃₁ ℓ → Obs ℓ → Obs k
sh r (fo φ O P cv ev p) = fo φ O P (λ e q → cv e (τ₁ r q)) ev p
sh r (addo O a σ) = addo O a (λ q → σ (τ₁ r q))
sh zero (tro O (s≅ e)) = tro (sh zero O) e
sh (self n) (tro O (l≅ f)) = tro (sh (self n) O) (f n)
sh zero (tr⁻o O (s≅ e)) = tr⁻o (sh zero O) e
sh (self n) (tr⁻o O (l≅ f)) = tr⁻o (sh (self n) O) (f n)

sh-≈ : ∀ {k ℓ} (r : k ◃₁ ℓ) (C : Obs ℓ) → Ctx C → sh r C ≈ᵒ C
sh-≈ r (fo φ O P cv ev p) (pf , c) = fo (ctx-refl O c) (PFl.rP pf)
sh-≈ r (addo O a σ) (afl e _ , c) = addo (ctx-refl O c) refl e
sh-≈ zero (tro O (s≅ e)) c = tro (sh-≈ zero O c)
sh-≈ (self n) (tro O (l≅ f)) c = tro (sh-≈ (self n) O c)
sh-≈ zero (tr⁻o O (s≅ e)) c = tr⁻o (sh-≈ zero O c)
sh-≈ (self n) (tr⁻o O (l≅ f)) c = tr⁻o (sh-≈ (self n) O c)

Vis-≈ : ∀ {K k} {C C′ : Obs k} → Ctx C → C ≈ᵒ C′ → Vis K C′ → Vis K C
Vis-≈ c₀ o (vis cx tw′ cp) = vis c₀ (λ nz s es os G → ≺-≅tw (run-≅ o es) (tw′ nz s es os) G) (λ b t et fl G → pull (run-≅ o et) (cp b t et fl) G)

Vis-lift : ∀ {K k ℓ} (r : k ◃₁ ℓ) {D : Obs k} {C : Obs ℓ} → Ctx D → D ≈ᵒ C → Vis K C → Vis K D
Vis-lift zero {D} c₀ o (vis cx tw′ cp) = vis c₀ (λ nz s es os G → ≺-≅tw (run-≅ o (upʳ {r = zero} {y = s} es)) (tw′ tt (Ord₊ˢ.up zero s) (upˡ {r = zero} (upʳ {r = zero} es)) (up-rᴱ {r = zero} {y = s} os)) G) (λ {b} h t et fl G →
  pull (run-≅ o (upʳ {r = zero} {y = t} et)) (cp h (Ord₊ˢ.up zero t) (upˡ {r = zero} (upʳ {r = zero} et)) (λ ex h₀ → up-rᴱ {r = zero} {y = t} (fl ex h₀))) G)
Vis-lift (self n) {D} c₀ o (vis cx tw′ cp) = vis c₀ (λ nz s es os G → ≺-≅tw (run-≅ o (upʳ {r = self n} {y = s} es)) (tw′ tt (Ord₊ˢ.up (self n) s) (upˡ {r = self n} (upʳ {r = self n} es)) (up-rᴱ {r = self n} {y = s} os)) G) (λ {b} h t et fl G →
  pull (run-≅ o (upʳ {r = self n} {y = t} et)) (cp h (Ord₊ˢ.up (self n) t) (upˡ {r = self n} (upʳ {r = self n} et)) (λ ex h₀ → up-rᴱ {r = self n} {y = t} (fl ex h₀))) G)
```

## §5 $\Omega_\eta$ 是好的: 类 `Vis η`

这里是吸收进入定义的地方. `St`: 若 $C'$ 在节点 $c$ 处压在 `sh zero C` 之上, 则 $C'$ 下的一切值是某个 $\sqsupseteq\Omega_c$ 的尾巴在 $C$ 下的值, 所以 $C$ 的 `CvP` 给出 $C'$ 的 `CvP`. 没有水位.

```agda
Ωlt : ∀ {b x K} → b ≅ᴵ x → x <ᴵ K → Ωˢ b ⊑ᴱ Ωˢ K
Ωlt e zero      = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (≅→⊑ᴱ (≅ˢ-trans (Ωˢ-≅ e) (≅ˢ-sym d))))
Ωlt e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ωlt e q) (≅ˢ-sym d)))
Ωlt e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (Ωlt e q))

Ω≺s : ∀ {b j} → b ≺ᴵ suc j → Ωˢ b ⊑ᴱ Ωˢ j
Ω≺s (via e zero)    = ≅→⊑ᴱ (Ωˢ-≅ e)
Ω≺s (via e (suc q)) = Ωlt e q

Ctx-sh : ∀ {k ℓ} (r : k ◃₁ ℓ) (C : Obs ℓ) → Ctx C → Ctx (sh r C)
Ctx-sh r (fo φ O P cv ev p) c = c
Ctx-sh r (addo O a σ) c = c
Ctx-sh zero (tro O (s≅ e)) c = Ctx-sh zero O c
Ctx-sh (self n) (tro O (l≅ f)) c = Ctx-sh (self n) O c
Ctx-sh zero (tr⁻o O (s≅ e)) c = Ctx-sh zero O c
Ctx-sh (self n) (tr⁻o O (l≅ f)) c = Ctx-sh (self n) O c

Vis-mono : ∀ {K K′ k} {C : Obs k} → (∀ {b} → b ≺ᴵ K′ → b ≺ᴵ K) → Vis K C → Vis K′ C
Vis-mono h (vis cx tw′ cp) = vis cx tw′ (λ b → cp (h b))

fl-tr⁻ : ∀ {k₀ a b} (e : a ≅ᴵ b) {x : Ordˢ k₀} {t : Ordˢ b} → x ≅ˢ x → x ⊑ᴱ t → x ⊑ᴱ tr⁻ˢ e t
fl-tr⁻ {k₀} e {x} ex h {O} {O′} o G′ =
  Goodᴺ-tr (toZ-≅ d) (proj₁ L) , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) (proj₁ L)) (proj₁ L))) (proj₂ L)
  where
  L = h {O = tr⁻o O (≅ᴵ-refl k₀)} {O′ = tr⁻o O′ e} (tr⁻o o) G′
  d : run (tr⁻o O (≅ᴵ-refl k₀)) x ≅ˢ run O x
  d = run-≅ (≈ᵒ-reflˡ o) (tr⁻ˢ-≅ (≅ᴵ-refl k₀) ex)

fl-tr : ∀ {k₀ a b} (e : a ≅ᴵ b) {x : Ordˢ k₀} {t : Ordˢ a} → x ≅ˢ x → x ⊑ᴱ t → x ⊑ᴱ trˢ e t
fl-tr {k₀} e {x} ex h {O} {O′} o G′ =
  Goodᴺ-tr (toZ-≅ d) (proj₁ L) , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) (proj₁ L)) (proj₁ L))) (proj₂ L)
  where
  L = h {O = tro O (≅ᴵ-refl k₀)} {O′ = tro O′ e} (tro o) G′
  d : run (tro O (≅ᴵ-refl k₀)) x ≅ˢ run O x
  d = run-≅ (≈ᵒ-reflˡ o) (trˢ-≅ (≅ᴵ-refl k₀) ex)

⊑ᴱ-Ω≅ : ∀ {k₀ a b} {x : Ordˢ k₀} → x ≅ˢ x → a ≅ᴵ b → x ⊑ᴱ Ωˢ a → x ⊑ᴱ Ωˢ b
⊑ᴱ-Ω≅ ex e h = ⊑ᴱ-≅ʳ (fl-tr e ex h) (trˢ-≅ e (Ωˢ-≅ e))

ΩTr : ∀ {k₀ b x K} {y : Ordˢ k₀} → y ≅ˢ y → y ⊑ᴱ Ωˢ b → b ≅ᴵ x → x <ᴵ K → y ⊑ᴱ Ωˢ K
ΩTr ey h e zero      = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (⊑ᴱ-Ω≅ ey e h) (≅ˢ-sym d)))
ΩTr ey h e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (ΩTr ey h e q) (≅ˢ-sym d)))
ΩTr ey h e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (ΩTr ey h e q))

Ωup : ∀ {k₀ b c} {y : Ordˢ k₀} → y ≅ˢ y → y ⊑ᴱ Ωˢ b → b ≺ᴵ suc c → y ⊑ᴱ Ωˢ c
Ωup ey h (via e zero)    = ⊑ᴱ-Ω≅ ey e h
Ωup ey h (via e (suc q)) = ΩTr ey h e q

St-Ω : ∀ {c ℓ₀} {C : Obs (suc c)} {C′ : Obs ℓ₀} → Vis (suc c) C → Above c C′ (sh zero C) → Vis (suc c) C′
St-Ω {c} {C = C} v (above cx′ wrap) = vis cx′ (λ nz t et _ G →
  let u = proj₁ (wrap t et)
      eu = proj₁ (proj₂ (wrap t et))
      fu = proj₁ (proj₂ (proj₂ (wrap t et)))
      d  = proj₂ (proj₂ (proj₂ (wrap t et)))
  in ≺-≅tw (≅ˢ-trans d (run-≅ (sh-≈ zero C (cx v)) (upʳ {r = zero} {y = u} eu)))
          (tw v tt (Ord₊ˢ.up zero u) (upˡ {r = zero} (upʳ {r = zero} eu)) (up-rᴱ {r = zero} {y = u} (⊑ᴱ-trans (Ω1ᴱ c) fu))) G) (λ {b} h t et _ G →
  let u = proj₁ (wrap t et)
      eu = proj₁ (proj₂ (wrap t et))
      fu = proj₁ (proj₂ (proj₂ (wrap t et)))
      d  = proj₂ (proj₂ (proj₂ (wrap t et)))
  in pull (≅ˢ-trans d (run-≅ (sh-≈ zero C (cx v)) (upʳ {r = zero} {y = u} eu)))
          (cp v h (Ord₊ˢ.up zero u) (upˡ {r = zero} (upʳ {r = zero} eu)) (λ ex h₀ → up-rᴱ {r = zero} {y = u} (⊑ᴱ-trans (Ωup ex h₀ h) fu))) G)

dn→inp : ∀ c {𝓔 : Cl (suc c)} → (∀ {C} → 𝓔 C → Vis (suc c) C) → ∀ {D} → Dn zero 𝓔 D → Inp c (sh zero ⟨ 𝓔 ⟩) D
dn→inp zero h x = x
dn→inp (suc c) h {D} (x , C , cc , o) = x , C , cc , ≈-trans o (≈-sym (sh-≈ zero C (cx (h cc))))
dn→inp (lim f s) h {D} (x , C , cc , o) = x , C , cc , ≈-trans o (≈-sym (sh-≈ zero C (cx (h cc))))

dn→vis : ∀ {k ℓ} (r : k ◃₁ ℓ) {D} → Dn r (Vis ℓ) D → Vis k D
dn→vis {k = zero} r {D} refl = vis tt (λ ()) (λ { (via e ()) })
dn→vis {k = suc _} r (x , C , cc , o) = Vis-mono (λ { (via e q) → via e (τ₁ r q) }) (Vis-lift r x o cc)
dn→vis {k = lim _ _} r (x , C , cc , o) = Vis-mono (λ { (via e q) → via e (τ₁ r q) }) (Vis-lift r x o cc)

Ωg : ∀ η → Good true (Vis η) (Ωˢ η)
Ωg zero      = b1
Ωg (suc c)   = bi (Vis (suc c)) (λ v → v) (sh zero)
  (λ {C} v u eu → run-≅ (sh-≈ zero C (cx v)) (upʳ {r = zero} {y = u} eu))
  (λ 𝓔 inc z ez g → bu {r = zero} (Good-mono (dn→inp c inc) g))
  (λ {C} v → Vis-lift zero (Ctx-sh zero C (cx v)) (sh-≈ zero C (cx v)) v)
  St-Ω
  (λ c₀ o v → Vis-≈ c₀ o v)
  (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
Ωg (lim g s) = bl (λ n → bu {r = self n} (Good-mono (dn→vis (self n)) (Ωg (g n))))
                  (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))
```

## §6 第 0 层的搬运

第 0 层只读 `idO`, 搬运经 $\cong$. 对 `trˢ z≅`、`tr⁻ˢ z≅` 各一份, 形状相同.

```agda
lvl≅ : ∀ {X Y : Ordˢ zero} (d : X ≅ˢ Y) (G : Goodᴺ (toZ X)) → lvG (Goodᴺ-tr (toZ-≅ d) G) ≅ᴵ lvG G
lvl≅ d G = toLevel-≅ (forceᴺ-HS _ (Goodᴺ-tr (toZ-≅ d) G)) (forceᴺ-HS _ G) (forceᴺ-≅ (≅ᶻ-sym (toZ-≅ d)) (Goodᴺ-tr (toZ-≅ d) G) G)

Tr₀ : ∀ {s} {𝓧 : Cl zero} {x : Ordˢ zero} → 𝓧 idO → Good s 𝓧 x → x ≅ˢ x → Good s isId (trˢ z≅ x)
Tr₀ i bz ex = bz
Tr₀ i b1 ex = b1
Tr₀ i (bs 𝓚 v ea g clk cgk) ex = bs isId (λ c → c) (self-trˢ z≅ ea) (Tr₀ (v i) g ea) (λ ()) (λ ())
Tr₀ i (bl hg st) ex = bl (λ n → Tr₀ i (hg n) (l-invˢ ex n)) (λ n → tr-cong (st n))
Tr₀ i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm) ex
Tr₀ i (bu {r = ()} g) ex
Tr₀ i (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η _ → 𝓑 η idO) (λ e b → Bc e b) (Tr₀ i g0 et)
     (λ η e w → Good-mono proj₁ (Tr₀ (i , proj₂ w) (gg η e (i , proj₂ w)) (eg η e η e (≅ᴵ-refl η))))
     (self-trˢ z≅ et) (λ η e η′ e′ eη → trˢ-≅ z≅ (≅-trˢ z≅ (eg η e η′ e′ eη)))
     (λ η e → tr-cong (m η e)) (λ η e η′ e′ h → tr-cong (mm η e η′ e′ h))
     (λ { refl G → pull (trˢ-≅ z≅ et) (d₀ i) G })
     (λ { η e refl b G → pull (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) (dE η e i b) G })
     (λ { refl G → Bc (lvl≅ (trˢ-≅ z≅ et) G) (ch₀ i (Goodᴺ-tr (toZ-≅ (trˢ-≅ z≅ et)) G)) })
     (λ { η e refl b G → Bc (lvl≅ (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) G) (chS η e i b (Goodᴺ-tr (toZ-≅ (trˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η)))) G)) })
Tr₀ i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr₀ i go (ĉ-refl₀ ex)) (λ k → Tr₀ i (gO k) (ĉ-reflg ex _ _)) (tr-cong mo) (λ k → tr-cong (mO k))

Tr⁻₀ : ∀ {s} {𝓧 : Cl zero} {x : Ordˢ zero} → 𝓧 idO → Good s 𝓧 x → x ≅ˢ x → Good s isId (tr⁻ˢ z≅ x)
Tr⁻₀ i bz ex = bz
Tr⁻₀ i b1 ex = b1
Tr⁻₀ i (bs 𝓚 v ea g clk cgk) ex = bs isId (λ c → c) (self-tr⁻ˢ z≅ ea) (Tr⁻₀ (v i) g ea) (λ ()) (λ ())
Tr⁻₀ i (bl hg st) ex = bl (λ n → Tr⁻₀ i (hg n) (l-invˢ ex n)) (λ n → tr⁻-cong (st n))
Tr⁻₀ i (bi {p = ()} 𝓖₀ inc W Wf hb Wv St cg hm) ex
Tr⁻₀ i (bu {r = ()} g) ex
Tr⁻₀ i (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η _ → 𝓑 η idO) (λ e b → Bc e b) (Tr⁻₀ i g0 et)
     (λ η e w → Good-mono proj₁ (Tr⁻₀ (i , proj₂ w) (gg η e (i , proj₂ w)) (eg η e η e (≅ᴵ-refl η))))
     (self-tr⁻ˢ z≅ et) (λ η e η′ e′ eη → tr⁻ˢ-≅ z≅ (≅-tr⁻ˢ z≅ (eg η e η′ e′ eη)))
     (λ η e → tr⁻-cong (m η e)) (λ η e η′ e′ h → tr⁻-cong (mm η e η′ e′ h))
     (λ { refl G → pull (tr⁻ˢ-≅ z≅ et) (d₀ i) G })
     (λ { η e refl b G → pull (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) (dE η e i b) G })
     (λ { refl G → Bc (lvl≅ (tr⁻ˢ-≅ z≅ et) G) (ch₀ i (Goodᴺ-tr (toZ-≅ (tr⁻ˢ-≅ z≅ et)) G)) })
     (λ { η e refl b G → Bc (lvl≅ (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η))) G) (chS η e i b (Goodᴺ-tr (toZ-≅ (tr⁻ˢ-≅ z≅ (eg η e η e (≅ᴵ-refl η)))) G)) })
Tr⁻₀ i (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr⁻₀ i go (ĉ-refl₀ ex)) (λ k → Tr⁻₀ i (gO k) (ĉ-reflg ex _ _)) (tr⁻-cong mo) (λ k → tr⁻-cong (mO k))
```

## §7 非零层的搬运

`Tr`/`Tr⁻` 对类的作用: 输出类的上下文前插搬运后落在输入类里 (`M`). 分支经 `backˢ`, 上下文经 `bkO`. 这与 Pending 的 `Good-tr` 同结构, 多的是 `W`/`St`/`Wv` 的搬运.

```agda
NZ-e : ∀ {a b} → a ≅ᴵ b → NZ b → NZ a
NZ-e (s≅ _) nz = tt
NZ-e (l≅ _) nz = tt
NZ-e z≅ ()

NZ-e′ : ∀ {a b} → a ≅ᴵ b → NZ a → NZ b
NZ-e′ (s≅ _) nz = tt
NZ-e′ (l≅ _) nz = tt
NZ-e′ z≅ ()


bkO : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) → Obs j → Obs (repˢ (resˢ q e))
bkO zero      (s≅ e) D = tr⁻o D e
bkO (suc q)   (s≅ e) D = bkO q e D
bkO (lim n q) (l≅ f) D = bkO q (f n) D

rb : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Obs j) (u : Ordˢ (repˢ (resˢ q e))) → run (bkO q e D) u ≡ run D (backˢ (resˢ q e) u)
rb zero      (s≅ e) D u = refl
rb (suc q)   (s≅ e) D u = rb q e D u
rb (lim n q) (l≅ f) D u = rb q (f n) D u

cb : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Obs j) → Ctx D → Ctx (bkO q e D)
cb zero      (s≅ e) D c = c
cb (suc q)   (s≅ e) D c = cb q e D c
cb (lim n q) (l≅ f) D c = cb q (f n) D c

ob : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {D D′ : Obs j} → D ≈ᵒ D′ → bkO q e D ≈ᵒ bkO q e D′
ob zero      (s≅ e) o = tr⁻o o
ob (suc q)   (s≅ e) o = ob q e o
ob (lim n q) (l≅ f) o = ob q (f n) o

fb : ∀ {k₀ j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {x : Ordˢ k₀} {u : Ordˢ (repˢ (resˢ q e))} → x ≅ˢ x → x ⊑ᴱ u → x ⊑ᴱ backˢ (resˢ q e) u
fb zero      (s≅ e) ex h = fl-tr⁻ e ex h
fb (suc q)   (s≅ e) ex h = fb q e ex h
fb (lim n q) (l≅ f) ex h = fb q (f n) ex h

bm : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (resˢ q e))} → u ⊑ᵒ u′ → backˢ (resˢ q e) u ⊑ᵒ backˢ (resˢ q e) u′
bm zero      (s≅ e) h = tr⁻-cong h
bm (suc q)   (s≅ e) h = bm q e h
bm (lim n q) (l≅ f) h = bm q (f n) h

bkO⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) → Obs j → Obs (repˢ (res⁻ˢ q e))
bkO⁻ zero      (s≅ e) D = tro D e
bkO⁻ (suc q)   (s≅ e) D = bkO⁻ q e D
bkO⁻ (lim n q) (l≅ f) D = bkO⁻ q (f n) D

rb⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (D : Obs j) (u : Ordˢ (repˢ (res⁻ˢ q e))) → run (bkO⁻ q e D) u ≡ run D (backˢ (res⁻ˢ q e) u)
rb⁻ zero      (s≅ e) D u = refl
rb⁻ (suc q)   (s≅ e) D u = rb⁻ q e D u
rb⁻ (lim n q) (l≅ f) D u = rb⁻ q (f n) D u

cb⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (D : Obs j) → Ctx D → Ctx (bkO⁻ q e D)
cb⁻ zero      (s≅ e) D c = c
cb⁻ (suc q)   (s≅ e) D c = cb⁻ q e D c
cb⁻ (lim n q) (l≅ f) D c = cb⁻ q (f n) D c

ob⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {D D′ : Obs j} → D ≈ᵒ D′ → bkO⁻ q e D ≈ᵒ bkO⁻ q e D′
ob⁻ zero      (s≅ e) o = tro o
ob⁻ (suc q)   (s≅ e) o = ob⁻ q e o
ob⁻ (lim n q) (l≅ f) o = ob⁻ q (f n) o

fb⁻ : ∀ {k₀ j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {x : Ordˢ k₀} {u : Ordˢ (repˢ (res⁻ˢ q e))} → x ≅ˢ x → x ⊑ᴱ u → x ⊑ᴱ backˢ (res⁻ˢ q e) u
fb⁻ zero      (s≅ e) ex h = fl-tr e ex h
fb⁻ (suc q)   (s≅ e) ex h = fb⁻ q e ex h
fb⁻ (lim n q) (l≅ f) ex h = fb⁻ q (f n) ex h

bm⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (res⁻ˢ q e))} → u ⊑ᵒ u′ → backˢ (res⁻ˢ q e) u ⊑ᵒ backˢ (res⁻ˢ q e) u′
bm⁻ zero      (s≅ e) h = tr-cong h
bm⁻ (suc q)   (s≅ e) h = bm⁻ q e h
bm⁻ (lim n q) (l≅ f) h = bm⁻ q (f n) h

sbk : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → backˢ (resˢ q e) u ≅ˢ backˢ (resˢ q e) u
sbk q e d = ≅ˢ-reflˡ (backˢ-≅ q e d)

sbk⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → backˢ (res⁻ˢ q e) u ≅ˢ backˢ (res⁻ˢ q e) u
sbk⁻ q e d = ≅ˢ-reflˡ (back⁻ˢ-≅ q e d)

≺s-eq : ∀ {b′ j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) → b′ ≺ᴵ suc (repˢ (resˢ q e)) → b′ ≺ᴵ suc j
≺s-eq q e r = ≺ᴵ-respʳ r (s≅ (≅ᴵ-sym (eqˢ (resˢ q e))))

≺s-eq⁻ : ∀ {b′ j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) → b′ ≺ᴵ suc (repˢ (res⁻ˢ q e)) → b′ ≺ᴵ suc j
≺s-eq⁻ q e r = ≺ᴵ-respʳ r (s≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e))))

Tr  : ∀ {s a b} (e : a ≅ᴵ b) → NZ a → {𝓧 : Cl a} {𝓨 : Cl b} {x : Ordˢ a} → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (tro D e)) → Good s 𝓧 x → x ≅ˢ x → Good s 𝓨 (trˢ e x)
Tr⁻ : ∀ {s a b} (e : a ≅ᴵ b) → NZ b → {𝓧 : Cl b} {𝓨 : Cl a} {x : Ordˢ b} → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (tr⁻o D e)) → Good s 𝓧 x → x ≅ˢ x → Good s 𝓨 (tr⁻ˢ e x)
Bk  : ∀ {s j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (𝓕 : Cl j) (𝓕′ : Cl (repˢ (resˢ q e))) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (bkO q e D)) → ∀ {u} → u ≅ˢ u →
      Good s (Inp _ 𝓕′) u → Good s (Inp j 𝓕) (backˢ (resˢ q e) u)
Bk⁻ : ∀ {s j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (𝓕 : Cl j) (𝓕′ : Cl (repˢ (res⁻ˢ q e))) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (bkO⁻ q e D)) → ∀ {u} → u ≅ˢ u →
      Good s (Inp _ 𝓕′) u → Good s (Inp j 𝓕) (backˢ (res⁻ˢ q e) u)
Dtr : ∀ {s k k′ ℓ ℓ′} (r : k ◃₁ ℓ) (r′ : k′ ◃₁ ℓ′) (e : k ≅ᴵ k′) {𝓧 : Cl ℓ} {𝓨 : Cl ℓ′} (E : Obs ℓ′ → Obs ℓ) →
      (∀ {D : Obs k′} {D′ : Obs ℓ′} → D ≈ᵒ D′ → tro D e ≈ᵒ E D′) → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (E D)) →
      ∀ {x : Ordˢ k} → Good s (Dn r 𝓧) x → x ≅ˢ x → Good s (Dn r′ 𝓨) (trˢ e x)
Dtr⁻ : ∀ {s k k′ ℓ ℓ′} (r : k′ ◃₁ ℓ′) (r′ : k ◃₁ ℓ) (e : k ≅ᴵ k′) {𝓧 : Cl ℓ′} {𝓨 : Cl ℓ} (E : Obs ℓ → Obs ℓ′) →
      (∀ {D : Obs k} {D′ : Obs ℓ} → D ≈ᵒ D′ → tr⁻o D e ≈ᵒ E D′) → (∀ {D} → 𝓨 D → Ctx D × 𝓧 (E D)) →
      ∀ {x : Ordˢ k′} → Good s (Dn r 𝓧) x → x ≅ˢ x → Good s (Dn r′ 𝓨) (tr⁻ˢ e x)
Bb : ∀ {s j j′} (e : j ≅ᴵ j′) (𝓕 : Cl j) (𝓕′ : Cl j′) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (tr⁻o D e)) → ∀ {u} → u ≅ˢ u → Good s (Inp j′ 𝓕′) u → Good s (Inp j 𝓕) (tr⁻ˢ e u)
Bb⁻ : ∀ {s j j′} (e : j′ ≅ᴵ j) (𝓕 : Cl j) (𝓕′ : Cl j′) → (∀ {D} → 𝓕 D → Ctx D × 𝓕′ (tro D e)) → ∀ {u} → u ≅ˢ u → Good s (Inp j′ 𝓕′) u → Good s (Inp j 𝓕) (trˢ e u)

Dtr r r′ z≅ E oE M g ex = Tr₀ refl g ex
Dtr r r′ e@(s≅ _) E oE M g ex = Tr e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr r r′ e@(l≅ _) E oE M g ex = Tr e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr⁻ r r′ z≅ E oE M g ex = Tr⁻₀ refl g ex
Dtr⁻ r r′ e@(s≅ _) E oE M g ex = Tr⁻ e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex
Dtr⁻ r r′ e@(l≅ _) E oE M g ex = Tr⁻ e tt (λ { (x , C , c , o) → x , x , E C , proj₂ (M c) , oE o }) g ex

Bb z≅ 𝓕 𝓕′ M eu g = Tr⁻₀ refl g eu
Bb e@(s≅ _) 𝓕 𝓕′ M eu g = Tr⁻ e tt M g eu
Bb e@(l≅ _) 𝓕 𝓕′ M eu g = Tr⁻ e tt M g eu
Bb⁻ z≅ 𝓕 𝓕′ M eu g = Tr₀ refl g eu
Bb⁻ e@(s≅ _) 𝓕 𝓕′ M eu g = Tr e tt M g eu
Bb⁻ e@(l≅ _) 𝓕 𝓕′ M eu g = Tr e tt M g eu

Bk zero      (s≅ e) 𝓕 𝓕′ M eu g = Bb e 𝓕 𝓕′ M eu g
Bk (suc q)   (s≅ e) 𝓕 𝓕′ M eu g = Bk q e 𝓕 𝓕′ M eu g
Bk (lim n q) (l≅ f) 𝓕 𝓕′ M eu g = Bk q (f n) 𝓕 𝓕′ M eu g
Bk⁻ zero      (s≅ e) 𝓕 𝓕′ M eu g = Bb⁻ e 𝓕 𝓕′ M eu g
Bk⁻ (suc q)   (s≅ e) 𝓕 𝓕′ M eu g = Bk⁻ q e 𝓕 𝓕′ M eu g
Bk⁻ (lim n q) (l≅ f) 𝓕 𝓕′ M eu g = Bk⁻ q (f n) 𝓕 𝓕′ M eu g

Tr e nz M bz ex = bz
Tr e nz M b1 ex = b1
Tr e nz M (bs 𝓚 v ea g clk cgk) ex =
  bs (λ D → Ctx D × 𝓚 (tro D e)) (λ c → proj₁ (M c) , v (proj₂ (M c))) (self-trˢ e ea) (Tr e nz (λ c → c) g ea)
     (λ nz₂ (x , c) fo′ → cxo fo′ , clk (NZ-e e nz₂) c (flo-over (cxo fo′) (λ t et G → flw fo′ (trˢ e t) (self-trˢ e et) G)))
     (λ nz₂ c₀ o (x , c) → c₀ , cgk (NZ-e e nz₂) c₀ (tro o) c)
Tr e nz M (bl hg st) ex = bl (λ n → Tr e nz M (hg n) (l-invˢ ex n)) (λ n → tr-cong (st n))
Tr {s = s} e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bi {j = j} {p = q} {f = f} 𝓖₀ inc W Wf hb Wv St cg hm) ex = bi
  (λ D → Ctx D × 𝓖₀ (tro D e))
  (λ c → proj₁ (M c) , inc (proj₂ (M c)))
  (λ D → bkO q e (W (tro D e)))
  (λ {D} (x , c) u eu → subst (λ w → run (bkO q e (W (tro D e))) u ≅ˢ run D (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
       (subst (λ y → y ≅ˢ run D (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))))) (sym (rb q e (W (tro D e)) u)) (Wf c (backˢ (resˢ q e) u) (sbk q e eu))))
  (λ 𝓔′ inc″ z ez g → subst (λ y → Good s 𝓔′ (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) y))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (Tr e nz {𝓧 = λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)} (λ {D} c → proj₁ (inc″ c) , D , c , refl)
          (hb (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)) (λ { (D , c , refl) → proj₂ (inc″ c) })
              (backˢ (resˢ q e) z) (sbk q e ez)
              (Good→Gd (<→◃ q) (Bk q e (W ⟨ (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tro D e)) ⟩) ((λ D → bkO q e (W (tro D e))) ⟨ 𝓔′ ⟩)
                  (λ { (x , D₁ , (D , c , refl) , o) → x , cb q e _ x , D , c , ob q e o }) ez (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))
          (i-respˢ ex (sbk q e ez))))
  (λ {D} (x , c) → vis (cb q e _ (cx (Wv c)))
       (λ nz t et fl G → ≺-≅tw (subst (λ y → y ≅ˢ run (W (tro D e)) (backˢ (resˢ q e) t)) (sym (rb q e (W (tro D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk q e et)))
            (tw (Wv c) (NZ-e (eqˢ (resˢ q e)) nz) (backˢ (resˢ q e) t) (sbk q e et) (fb q e (s≅ z≅) fl)) G)
       (λ {b} h t et fl G →
       pull (subst (λ y → y ≅ˢ run (W (tro D e)) (backˢ (resˢ q e) t)) (sym (rb q e (W (tro D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk q e et)))
            (cp (Wv c) (≺s-eq q e h) (backˢ (resˢ q e) t) (sbk q e et) (λ ex₀ h₀ → fb q e ex₀ (fl ex₀ h₀))) G))
  (λ {D} {C″} (x , c) (above cx′ wrap) → cx′ , St c (above cx′ (λ t et →
       let t′ = trˢ e t
           et′ = self-trˢ e et
           u = proj₁ (wrap t′ et′)
           eu = proj₁ (proj₂ (wrap t′ et′))
           fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
           d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
       in backˢ (resˢ q e) u , sbk q e eu , fb q e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ (eqˢ (resˢ q e)))) fu) ,
          subst (λ y → run C″ t′ ≅ˢ y) (rb q e (W (tro D e)) u) d)))
  (λ c₀ o (x , c) → c₀ , cg c₀ (tro o) c)
  (λ {z} {z′} h → subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
       (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′)) (tr-cong (hm (bm q e h))))
Tr (s≅ e′) nz M (bu {r = zero} g) ex = bu {r = zero} (Dtr zero zero e′ (λ D → tro D (s≅ e′)) (λ o → tro o) M g (u-reflˢ zero ex))
Tr (l≅ f) nz M (bu {r = self n} g) ex = bu {r = self n} (Dtr (self n) (self n) (f n) (λ D → tro D (l≅ f)) (λ o → tro o) M g (u-reflˢ (self n) ex))
Tr e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η D → 𝓑 η (tro D e)) Bc (Tr e nz M g0 et)
     (λ η d w → Tr e nz {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c , b) → proj₁ (M c) , proj₂ (M c) , b)
        (gg η d (wit-nz _ nz)) (eg η d η d (≅ᴵ-refl η)))
     (self-trˢ e et) (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
     (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
     (λ c G → d₀ (proj₂ (M c)) G) (λ η d c b G → dE η d (proj₂ (M c)) b G)
     (λ c G → ch₀ (proj₂ (M c)) G) (λ η d c b G → chS η d (proj₂ (M c)) b G)
Tr e nz M (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr e nz M go (ĉ-refl₀ ex)) (λ k → Tr e nz M (gO k) (ĉ-reflg ex _ _)) (tr-cong mo) (λ k → tr-cong (mO k))

Tr⁻ e nz M bz ex = bz
Tr⁻ e nz M b1 ex = b1
Tr⁻ e nz M (bs 𝓚 v ea g clk cgk) ex =
  bs (λ D → Ctx D × 𝓚 (tr⁻o D e)) (λ c → proj₁ (M c) , v (proj₂ (M c))) (self-tr⁻ˢ e ea) (Tr⁻ e nz (λ c → c) g ea)
     (λ nz₂ (x , c) fo′ → cxo fo′ , clk (NZ-e′ e nz₂) c (flo-over (cxo fo′) (λ t et G → flw fo′ (tr⁻ˢ e t) (self-tr⁻ˢ e et) G)))
     (λ nz₂ c₀ o (x , c) → c₀ , cgk (NZ-e′ e nz₂) c₀ (tr⁻o o) c)
Tr⁻ e nz M (bl hg st) ex = bl (λ n → Tr⁻ e nz M (hg n) (l-invˢ ex n)) (λ n → tr⁻-cong (st n))
Tr⁻ {s = s} e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bi {j = j} {p = q} {f = f} 𝓖₀ inc W Wf hb Wv St cg hm) ex = bi
  (λ D → Ctx D × 𝓖₀ (tr⁻o D e))
  (λ c → proj₁ (M c) , inc (proj₂ (M c)))
  (λ D → bkO⁻ q e (W (tr⁻o D e)))
  (λ {D} (x , c) u eu → subst (λ w → run (bkO⁻ q e (W (tr⁻o D e))) u ≅ˢ run D (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
       (subst (λ y → y ≅ˢ run D (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))))) (sym (rb⁻ q e (W (tr⁻o D e)) u)) (Wf c (backˢ (res⁻ˢ q e) u) (sbk⁻ q e eu))))
  (λ 𝓔′ inc″ z ez g → subst (λ y → Good s 𝓔′ (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) y))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (Tr⁻ e nz {𝓧 = λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)} (λ {D} c → proj₁ (inc″ c) , D , c , refl)
          (hb (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)) (λ { (D , c , refl) → proj₂ (inc″ c) })
              (backˢ (res⁻ˢ q e) z) (sbk⁻ q e ez)
              (Good→Gd (<→◃ q) (Bk⁻ q e (W ⟨ (λ D₁ → Σ _ λ D → 𝓔′ D × (D₁ ≡ tr⁻o D e)) ⟩) ((λ D → bkO⁻ q e (W (tr⁻o D e))) ⟨ 𝓔′ ⟩)
                  (λ { (x , D₁ , (D , c , refl) , o) → x , cb⁻ q e _ x , D , c , ob⁻ q e o }) ez (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))
          (i-respˢ ex (sbk⁻ q e ez))))
  (λ {D} (x , c) → vis (cb⁻ q e _ (cx (Wv c)))
       (λ nz t et fl G → ≺-≅tw (subst (λ y → y ≅ˢ run (W (tr⁻o D e)) (backˢ (res⁻ˢ q e) t)) (sym (rb⁻ q e (W (tr⁻o D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk⁻ q e et)))
            (tw (Wv c) (NZ-e (eqˢ (res⁻ˢ q e)) nz) (backˢ (res⁻ˢ q e) t) (sbk⁻ q e et) (fb⁻ q e (s≅ z≅) fl)) G)
       (λ {b} h t et fl G →
       pull (subst (λ y → y ≅ˢ run (W (tr⁻o D e)) (backˢ (res⁻ˢ q e) t)) (sym (rb⁻ q e (W (tr⁻o D e)) t)) (run-≅ (ctx-refl _ (cx (Wv c))) (sbk⁻ q e et)))
            (cp (Wv c) (≺s-eq⁻ q e h) (backˢ (res⁻ˢ q e) t) (sbk⁻ q e et) (λ ex₀ h₀ → fb⁻ q e ex₀ (fl ex₀ h₀))) G))
  (λ {D} {C″} (x , c) (above cx′ wrap) → cx′ , St c (above cx′ (λ t et →
       let t′ = tr⁻ˢ e t
           et′ = self-tr⁻ˢ e et
           u = proj₁ (wrap t′ et′)
           eu = proj₁ (proj₂ (wrap t′ et′))
           fu = proj₁ (proj₂ (proj₂ (wrap t′ et′)))
           d = proj₂ (proj₂ (proj₂ (wrap t′ et′)))
       in backˢ (res⁻ˢ q e) u , sbk⁻ q e eu , fb⁻ q e (Ωˢ-refl j) (⊑ᴱ-trans (≅→⊑ᴱ (Ωˢ-≅ (eqˢ (res⁻ˢ q e)))) fu) ,
          subst (λ y → run C″ t′ ≅ˢ y) (rb⁻ q e (W (tr⁻o D e)) u) d)))
  (λ c₀ o (x , c) → c₀ , cg c₀ (tr⁻o o) c)
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
       (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)) (tr⁻-cong (hm (bm⁻ q e h))))
Tr⁻ (s≅ e′) nz M (bu {r = zero} g) ex = bu {r = zero} (Dtr⁻ zero zero e′ (λ D → tr⁻o D (s≅ e′)) (λ o → tr⁻o o) M g (u-reflˢ zero ex))
Tr⁻ (l≅ f) nz M (bu {r = self n} g) ex = bu {r = self n} (Dtr⁻ (self n) (self n) (f n) (λ D → tr⁻o D (l≅ f)) (λ o → tr⁻o o) M g (u-reflˢ (self n) ex))
Tr⁻ e nz {𝓧 = 𝓧} {𝓨 = 𝓨} M (bŝ 𝓑 Bc g0 gg et eg m mm d₀ dE ch₀ chS) ex =
  bŝ (λ η D → 𝓑 η (tr⁻o D e)) Bc (Tr⁻ e nz M g0 et)
     (λ η d w → Tr⁻ e nz {𝓧 = 𝓧 ∧ 𝓑 η} (λ (c , b) → proj₁ (M c) , proj₂ (M c) , b)
        (gg η d (wit-nz _ nz)) (eg η d η d (≅ᴵ-refl η)))
     (self-tr⁻ˢ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
     (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
     (λ c G → d₀ (proj₂ (M c)) G) (λ η d c b G → dE η d (proj₂ (M c)) b G)
     (λ c G → ch₀ (proj₂ (M c)) G) (λ η d c b G → chS η d (proj₂ (M c)) b G)
Tr⁻ e nz M (bĉ ys hy dy G₀ l₀ Gg lE go gO mo mO) ex =
  bĉ ys hy dy G₀ l₀ Gg lE (Tr⁻ e nz M go (ĉ-refl₀ ex)) (λ k → Tr⁻ e nz M (gO k) (ĉ-reflg ex _ _)) (tr⁻-cong mo) (λ k → tr⁻-cong (mO k))
```

```agda
≈-id : ∀ {C : Obs zero} → C ≈ᵒ idO → C ≡ idO
≈-id idO = refl
```
