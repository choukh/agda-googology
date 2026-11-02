# Uniform3 上的无符号闭包定理 (一): 观测

> [UniformNFBase](UniformNFBase.lagda.md) 在修正的折叠 [Uniform3Base](Uniform3Base.lagda.md) 上重编译. 结论先说:
>
> 1. **改动只有四行.** `B1`、`Pl-fold∅` 的 `up (self n)` 子句与 `up zero` 同形 (地板换成 `flo (f n)`, 证据 `toFlo`); `toFlo` 改收 `Simᴵ k ℓ`; `suc (Mx B)` 写成 `Bd B`.
> 2. 其余逐字. 深度 0 不读地板的形状.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS; z<suc)
open Restrˢ
open import OCF.Align.UniformS using (kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans; force-≅; Goodᶻ-tr;
  _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; Rˢ; R→≅ˢ; ≅→Rˢ; R-convˢ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-invˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg; ≅ᶻ-refl₀; ≅ᶻ-reflg; ĉ-reflO;
  two; Lv; Lv-refl; Lv-up; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; ink; inl; inr; liftEv; Run; A; wk; limA; limᵢA; ŝA; ĉA;
  Top; top; bound; Bd; sb; nz; ubd; Fc; evF; iF; FM; MF; FB; cloA; flo; cvFlo; toFlo; repA; fold; Ω̂A; ∅ᴿ;
  _≈ᴿ_; fold-≅0; chainA; _∼ᶠ_; ∼ᶠ-refl; cloR; ≺0)
```

## §1 统一折叠上的观测

**观测.** UniformS 的 `ψo₀`/`ψo₁` (两种栈) 换成一个 `fo`: 以前缀 $P:$ `Run fl` 在目标 $i<^\mathsf I\ell$ 处、地板 $\varphi$、证据 `ev` 下折叠. 加法与搬运观测照 UniformS. 相似: `fo` 两侧**同一前缀、同一目标**, 地板/`cv`/证据/环境任意, 并携带 $P$ 的自互模拟 (供 `run-≅`); `addo` 照 UniformS 带种类字段.

**读法 (为什么没有 `fo1`).** 深度 1 的折叠 `fold 1 φ cv E x Q ev p` 也可以作观测, 它的同余是一行. 但 `run-≅` 要相关尾巴 $x\cong^\mathsf s y$ 在同一深度 1 观测下的结果相关, 即 Uniform2Depth1 的 `fold-≅1`, 它要求层对齐 `AlignD φ φ′ d`; 一般的相关对不满足 (Relative `¬AlignΩ₃`), 所以把 `fo1` 加进相似关系就要把 `AlignD` 当相似的字段, 而 `≅→⊑ᵒ`/`⊑ᵒ-≅ʳ` 对一切相关对量化, 得不到. 这与 Relative §6 的结论一致: 深度 $\ge1$ 的一切互模拟论证要换成层对齐互模拟 `≅ᴬ`. 本文停在深度 0.

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  fo   : ∀ {i k ℓ fl} (φ : Flr) → Obs i → (P : Run fl) → (cv : ∀ {L} → Ev L φ → Simᴵ k L) → Ev ℓ (fl ⊔ φ) → i <ᴵ ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
run idO              x = x
run (fo φ O P cv ev p) x = run O (fold 0 φ cv P x ev p)
run (addo O a σ)     x = run O (addˢ a σ x)
run (tro O e)        x = run O (trˢ e x)
run (tr⁻o O e)       x = run O (tr⁻ˢ e x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  fo   : ∀ {i k k′ ℓ ℓ′ fl φ φ′} {O O′ : Obs i} {P : Run fl}
         {cv : ∀ {L} → Ev L φ → Simᴵ k L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L}
         {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
         O ≈ᵒ O′ → P ≈ᴿ P → fo φ O P cv ev p ≈ᵒ fo φ′ O′ P cv′ ev′ p′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → kd ℓ ≡ kd ℓ′ → a ≅ˢ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO          = idO
≈ᵒ-reflˡ (fo o r)     = fo (≈ᵒ-reflˡ o) r
≈ᵒ-reflˡ (addo o k e) = addo (≈ᵒ-reflˡ o) refl (≅ˢ-reflˡ e)
≈ᵒ-reflˡ (tro o)      = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)     = tr⁻o (≈ᵒ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO          = idO
≈ᵒ-reflʳ (fo o r)     = fo (≈ᵒ-reflʳ o) r
≈ᵒ-reflʳ (addo o k e) = addo (≈ᵒ-reflʳ o) refl (≅ˢ-reflʳ e)
≈ᵒ-reflʳ (tro o)      = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)     = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
run-≅ idO          d = d
run-≅ (fo o r)     d = run-≅ o (fold-≅0 r d _ _ _ _ (≅ᴵ-refl _))
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))
```

**观测前序** 照 UniformS §4: 对一切相似观测与一切 Prefix 证书, 计值后 $\sqsubseteq$.

```agda
_⊑ᵒ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ →
  (G : Goodᶻ (toZ (run O x))) (G′ : Goodᶻ (toZ (run O′ y))) → force _ G ⊑ force _ G′

≅→⊑ᵒ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᵒ y
≅→⊑ᵒ e o G G′ = ≅→⊑ (force-≅ (toZ-≅ (run-≅ o e)) G G′)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᵒ y → y ≅ˢ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o G G′ = ⊑-trans (h o G Gm) (≅→⊑ (force-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᶻ-tr (≅ᶻ-sym d) G′
```

## §2 同余与 `up`

`fold-cong` 是观测本身 (要前缀的自互模拟). `up-l`/`up-r`: `fold 0 φ cv P (up zero x) ev p` 定义性地是 `fold 0 (flo k′) (cvFlo k′) P x (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p`, 而 `up (self n)` 只换 `cv`; 相似关系允许两侧地板与证据不同, 所以同一个假设 `h` 在换过的观测下直接可用.

```agda
fold-cong : ∀ {fl φ φ′ k k′ i ℓ ℓ′} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L}
            {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
            P ≈ᴿ P → x ⊑ᵒ y → fold 0 φ cv P x ev p ⊑ᵒ fold 0 φ′ cv′ P y ev′ p′
fold-cong r h o = h (fo o r)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           kd ℓ ≡ kd ℓ′ → a ≅ˢ a′ → x ⊑ᵒ y → addˢ a σ x ⊑ᵒ addˢ a′ σ′ y
add-cong k e h o = h (addo o k e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᵒ y → trˢ e x ⊑ᵒ trˢ e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᵒ y → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᵒ y → Ord₊ˢ.up r x ⊑ᵒ y
up-l {r = zero}   h (fo o rP)     = h (fo o rP)
up-l {r = zero}   h (addo o k e) = h (addo o k e)
up-l {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-l {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-l {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (fo o rP)     = h (fo o rP)
up-l {r = self n} h (addo o k e) = h (addo o k e)
up-l {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-l {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-l {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᵒ outˢ (◃₁→◃ r) y → x ⊑ᵒ Ord₊ˢ.up r y
up-r {r = zero}   h (fo o rP)     = h (fo o rP)
up-r {r = zero}   h (addo o k e) = h (addo o k e)
up-r {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-r {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-r {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (fo o rP)     = h (fo o rP)
up-r {r = self n} h (addo o k e) = h (addo o k e)
up-r {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-r {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-r {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
```

## §3 上界引理与链起点

**上界引理.** `lim-r`/`lim-l`/`suc-r`/`ŝ-r`/`ĉ-r`/`limᵢ-r` 照 UniformS §6, `fo` 情况把折叠推进两侧: 后继子句是 $\lim$ 的重复和 (第 1 项是折叠本身), 极限子句逐项, `ŝ` 在第 0 层尾巴处变成 `ĉᴸ` (转 `ĉ-r`), `limᵢ` 的派发用 `with <ᴵ-dec (cv (proj₂ ev) q) p` (`limᵢA` 的 `with` 抽象在 β-归约后字面出现, 与 Uniform3Base 的 `fold1A` 同). 递归调用写出隐式的树 (UniformS §6 的工程注记).

```agda
lim-r : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᵒ h n → x ⊑ᵒ Ord₊ˢ.lim h
lim-r n p idO G (Goodᶻ.gl G′ st) = ⊑-lim n (p idO G (G′ n))
lim-r {h = h} n p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-r {h = λ m → fold 0 φ′ cv′ P (h m) ev′ p′} n (fold-cong r p) o
lim-r {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-r {h = λ m → addˢ a′ σ′ (h m)} n (add-cong k a p) o
lim-r {h = h} n p (tro {e′ = e′} o)  = lim-r {h = λ m → trˢ e′ (h m)} n (tr-cong p) o
lim-r {h = h} n p (tr⁻o {e′ = e′} o) = lim-r {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordˢ k} {y : Ordˢ k′} → (∀ n → h n ⊑ᵒ y) → Ord₊ˢ.lim h ⊑ᵒ y
lim-l K idO (Goodᶻ.gl G st) G′ = lim-⊑ (λ n → K n idO (G n) G′)
lim-l {h = h} {y = y} K (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  lim-l {h = λ m → fold 0 φ cv P (h m) ev p} {y = fold 0 φ′ cv′ P y ev′ p′} (λ n o′ → K n (fo o′ r)) o
lim-l {h = h} {y = y} K (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) =
  lim-l {h = λ m → addˢ a σ (h m)} {y = addˢ a′ σ′ y} (λ n o′ → K n (addo o′ k ea)) o
lim-l {h = h} {y = y} K (tro {e = e} {e′ = e′} o)  =
  lim-l {h = λ m → trˢ e (h m)} {y = trˢ e′ y} (λ n o′ → K n (tro o′)) o
lim-l {h = h} {y = y} K (tr⁻o {e = e} {e′ = e′} o) =
  lim-l {h = λ m → tr⁻ˢ e (h m)} {y = tr⁻ˢ e′ y} (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᵒ y → x ⊑ᵒ Ord₊ˢ.suc y
suc-r p idO G (Goodᶻ.gs G′) = λ h → ≺s (p idO G G′ h)
suc-r {y = y} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  lim-r {h = iter (fold 0 φ′ cv′ P y ev′ p′ +ˢ_) Ord₊ˢ.zero} 1 (fold-cong r p) o
suc-r {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-r {y = addˢ a′ σ′ y} (add-cong k a p) o
suc-r {y = y} p (tro {e′ = e′} o)  = suc-r {y = trˢ e′ y} (tr-cong p) o
suc-r {y = y} p (tr⁻o {e′ = e′} o) = suc-r {y = tr⁻ˢ e′ y} (tr⁻-cong p) o

ŝ-r : ∀ {k k′ c} {x : Ordˢ k} {t₀ : Ordˢ k′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} → x ⊑ᵒ t₀ → x ⊑ᵒ Ord₊ˢ.ŝ c t₀ g
ĉ-r : ∀ {k k′ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {x : Ordˢ k} {o₀ : Ordˢ k′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} →
      x ⊑ᵒ o₀ → x ⊑ᵒ Ord₊ˢ.ĉᴸ c t₀ g o₀ o
ŝ-r {k′ = zero} p idO G (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′}
      (fold-cong r p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o r) =
  ŝ-r {c = c} {t₀ = fold 0 φ′ cv′ P t₀ ev′ p′} {g = λ η e → fold 0 φ′ cv′ P (g η e) ev′ p′} (fold-cong r p) o
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = addˢ a′ σ′ t₀} {o = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tro {e′ = e′} o)  = ŝ-r {c = c} {t₀ = trˢ e′ t₀} {g = λ η d → trˢ e′ (g η d)} (tr-cong p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tr⁻o {e′ = e′} o) = ŝ-r {c = c} {t₀ = tr⁻ˢ e′ t₀} {g = λ η d → tr⁻ˢ e′ (g η d)} (tr⁻-cong p) o
ĉ-r p idO G (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev′ = ev′} {p′ = p′} o′ r) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = fold 0 φ′ cv′ P o₀ ev′ p′} {o = λ η e → fold 0 φ′ cv′ P (o η e) ev′ p′} (fold-cong r p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (addo {a′ = a′} {σ′ = σ′} o′ k a) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = addˢ a′ σ′ o₀} {o = λ η e → addˢ a′ σ′ (o η e)} (add-cong k a p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tro {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = trˢ e′ o₀} {o = λ η d → trˢ e′ (o η d)} (tr-cong p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tr⁻o {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = tr⁻ˢ e′ o₀} {o = λ η d → tr⁻ˢ e′ (o η d)} (tr⁻-cong p) o′

limᵢ-r : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᵒ g (intoˢ (<→◃ q) z)) → x ⊑ᵒ Ord₊ˢ.limᵢ q g
limᵢ-r {q = ()} H idO
limᵢ-r {j = j} {x = x} {q = q} {g = g} H
       (fo {φ = φ} {φ′ = φ′} {P = P} {cv = cv} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r)
  with <ᴵ-dec (cv′ (proj₂ ev′) q) p′
... | injᵃ (via e s) = limᵢ-r (λ z d →
        subst (λ u → fold 0 φ cv P x ev p ⊑ᵒ fold 0 φ′ cv′ P (g (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (fold-cong r (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (fold-cong r (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-r 0 (fold-cong r (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-r (λ z d →
  subst (λ u → addˢ a σ x ⊑ᵒ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-cong k ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → trˢ e x ⊑ᵒ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-cong (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-cong (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o
```

**链起点 `B1`.** 统一折叠在尾巴 $0$ 处的值是前缀的值: `fold 0 φ cv P zero ev p = P (proj₁ ev) p` (定义性). 所以 UniformS 的两条 `B1₀`/`B1₁` 合成一条: 若 $x\sqsubseteq^\mathsf oP\,\mathtt{ev}\,p$, 则对一切自反尾巴 $y$, $x\sqsubseteq^\mathsf o$ `fold 0 φ cv P y ev p`. 对 $y$ 结构递归; `up zero` 情况换地板与证据, 假设 "$x\sqsubseteq^\mathsf oP\,(\mathtt{proj}_1\,\mathtt{ev})\,p$" 在新证据下字面相同 (`proj₁ (proj₁ ev , _) = proj₁ ev`).

```agda
B1 : ∀ {fl φ k k₀ i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} {x : Ordˢ k₀} →
     P ≈ᴿ P → x ⊑ᵒ P (proj₁ ev) p → (y : Ordˢ k) → y ≅ˢ y → x ⊑ᵒ fold 0 φ cv P y ev p
B1 r h Ord₊ˢ.zero e = h
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.suc a) e = lim-r 1 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h a (s-invˢ e))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.lim f) e = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (f 0) (l-invˢ e 0))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} {x = x} r h (Ord₊ˢ.limᵢ {i = j′} q g) e with <ᴵ-dec (cv (proj₂ ev) q) p
... | injᵃ (via e₁ s) = limᵢ-r (λ z d →
        subst (λ u → x ⊑ᵒ fold 0 φ cv P (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ev p) (sym (out-intoˢ (<→◃ s) z))
              (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (g (intoˢ (<→◃ q) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1 {k = suc k′} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up zero y) e =
  B1 {φ = flo k′} {P = P} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))} {p = p} r h y (u-reflˢ zero e)
B1 {φ = φ} {k = lim f s} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.up (self n) y) e =
  B1 {φ = flo (f n)} {P = P} {cv = cvFlo (f n)} {ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))} {p = p} r h y (u-reflˢ (self n) e)
B1 {φ = φ} {k = zero} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {k = suc _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {k = lim _ _} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h t₀ (ŝ-refl₀ e))
B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r h o₀ (ĉ-refl₀ e))
```

**`add-r`、`zero-l`、$\Omega$ 的单调性** 照 UniformS §7. `zero-l` 的 `fo` 情况: 两侧的观测用同一前缀, `run (fo …) 𝟎 = run O (P (proj₁ ev) p)`, 由 `B1` 以 $P$ 的自互模拟为假设.

```agda
add-r : ∀ {k ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordˢ k) → a ≅ˢ a′ → b ≅ˢ b → a ⊑ᵒ addˢ a′ σ b
add-r Ord₊ˢ.zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (Ord₊ˢ.suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-invˢ eb))
add-r {σ = σ} (Ord₊ˢ.lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-invˢ eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (Ord₊ˢ.limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ addˢ a′ σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (intoˢ (<→◃ q) z)) ea (i-respˢ eb (≅ˢ-reflˡ d))))
add-r {σ = σ} (Ord₊ˢ.up zero x)     ea eb = add-r {σ = λ q → σ (suc q)} x ea (u-reflˢ zero eb)
add-r {σ = σ} (Ord₊ˢ.up (self n) x) ea eb = add-r {σ = λ q → σ (lim n q)} x ea (u-reflˢ (self n) eb)
add-r {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ĉ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) ea eb = ĉ-r (add-r {σ = σ} o₀ ea (ĉ-refl₀ eb))

zero-l : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᵒ y
zero-l ey idO Goodᶻ.gz G′ = λ ()
zero-l {y = y} ey (fo {φ′ = φ′} {P = P} {cv′ = cv′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o r) =
  B1 {φ = φ′} {P = P} {cv = cv′} {ev = ev′} {p = p′} {x = P (proj₁ ev) p} r (≅→⊑ᵒ (r (proj₁ ev) p (proj₁ ev′) p′ (≅ᴵ-refl _))) y ey o
zero-l {y = y} ey (addo {σ′ = σ′} o k ea) = add-r {σ = σ′} y ea ey o
zero-l ey (tro {b = b} {e′ = e′} o)  = zero-l {k = b} (self-trˢ e′ ey) o
zero-l ey (tr⁻o {a = a} {e′ = e′} o) = zero-l {k = a} (self-tr⁻ˢ e′ ey) o

Ω0 : ∀ b → Ωˢ zero ⊑ᵒ Ωˢ b
Ω0 zero      = ≅→⊑ᵒ (Ωˢ-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω0 b) (≅ˢ-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r {r = self 0} (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᵒ Ωˢ b
Ω< e zero      = ≅→⊑ᵒ (Ωˢ-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω< e q) (≅ˢ-sym d)))
Ω< e (lim n q) = lim-r n (up-r {r = self n} (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ωˢ a ⊑ᵒ Ωˢ b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l {r = self n} (Ω-monoᵒ (k n)))

rule4ᵒ : ∀ {ℓ} {c : Ordˢ ℓ} → c ≅ˢ c → ∀ n → iter (c +ˢ_) Ord₊ˢ.zero n ⊑ᵒ iter (c +ˢ_) Ord₊ˢ.zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong refl ec (rule4ᵒ ec n)
```

## §4 地板由前缀再生; 严格性

**前缀的地板 `FlR P`**: 在目标 $i$ 处的值 $\sqsupseteq^\mathsf o\Omega_\varphi$ 对一切 $\varphi\sqsubseteq i$. 它是 TreeNFBase "映射者再生地板" 的统一形: 一个尾巴的折叠的地板不来自尾巴, 而来自前缀 (`FlΛ-fold` 就是 `B1`). 空前缀 `∅ᴿ` 的值是 $\Omega_i$ (`Ω-monoᵒ`); $\Omega_\Omega$ 闭包 `Ω̂A 0 P` 的值是弹栈闭包, 第 0 点是 $P+\Omega_1$ 的折叠 (`ŝ-r`). 加法沿前缀 (`add-floor`).

```agda
FlΛ : Ordᴵ → ∀ {k} → Ordˢ k → Set
FlΛ φ t = Ωˢ φ ⊑ᵒ t

FlR : ∀ {fl} → Run fl → Set
FlR {fl} P = ∀ {φ i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → φ ⊑ᴵ i → FlΛ φ (P ev p)

FlΛ-fold : ∀ {fl φ φ₀ k i ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {p : i <ᴵ ℓ} →
           P ≈ᴿ P → FlR P → φ₀ ⊑ᴵ i → (y : Ordˢ k) → y ≅ˢ y → FlΛ φ₀ (fold 0 φ cv P y ev p)
FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r fP h y ey = B1 {φ = φ} {P = P} {cv = cv} {ev = ev} {p = p} r (fP (proj₁ ev) p h) y ey

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei

FlR-∅ : FlR ∅ᴿ
FlR-∅ ev p h = Ω-monoᵒ h

FlR-Ω̂ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → FlR P → FlR (Ω̂A 0 P)
FlR-Ω̂ {P = P} r fP ev p h = ŝ-r (FlΛ-fold {φ = fk zero} {P = P} {cv = λ e → e} {ev = ev} {p = p} r fP h (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

rΩ̂ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → Ω̂A 0 P ≈ᴿ Ω̂A 0 P
rΩ̂ {fl} {P} r =
  cloR {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       {t′ = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       (∼ᶠ-refl fl)
       (fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = P} {P′ = P} r (Ωˢ-refl (suc zero)))
       (λ η η′ eη → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = λ e q → e (suc q)} {cv′ = λ e q → e (suc q)} {P = P} {P′ = P} r (Ωˢ-≅ eη))

add-floor : ∀ {k ℓ ℓ₀} {x : Ordˢ ℓ₀} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → x ⊑ᵒ a → b ≅ˢ b → x ⊑ᵒ addˢ a σ b
add-floor Ord₊ˢ.zero h eb = h
add-floor {σ = σ} (Ord₊ˢ.suc b) h eb = suc-r (add-floor {σ = σ} b h (s-invˢ eb))
add-floor {σ = σ} (Ord₊ˢ.lim f) h eb = lim-r 0 (add-floor {σ = σ} (f 0) h (l-invˢ eb 0))
add-floor {x = x} {a = a} {σ = σ} (Ord₊ˢ.limᵢ q g) h eb = limᵢ-r (λ z d →
  subst (λ u → x ⊑ᵒ addˢ a σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-floor {σ = σ} (g (intoˢ (<→◃ q) z)) h (i-respˢ eb (≅ˢ-reflˡ d))))
add-floor {σ = σ} (Ord₊ˢ.up zero y) h eb     = add-floor {σ = λ q → σ (suc q)} y h (u-reflˢ zero eb)
add-floor {σ = σ} (Ord₊ˢ.up (self n) y) h eb = add-floor {σ = λ q → σ (lim n q)} y h (u-reflˢ (self n) eb)
add-floor {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ĉ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-r (add-floor {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floor {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) h eb = ĉ-r (add-floor {σ = σ} o₀ h (ĉ-refl₀ eb))

FlΛ-add : ∀ {φ k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → FlΛ φ a → b ≅ˢ b → FlΛ φ (addˢ a σ b)
FlΛ-add b h eb = add-floor b h eb
```

**严格性 `Strict₀`.** 有地板的前缀在目标 $0$ 的一切折叠输出, 对任意自反尾巴与任意证书, 层号 $\sqsupseteq^\mathsf I1$: `FlΛ-fold` 在观测 `idO` 下以 `gs gz` 为 $\Omega_0=1$ 的证书, 再 `toLevel-⊑`. 这是 Stage2Label `Strict₀` 的统一形, 对**任意**带地板前缀 (不只空栈). `Strict₁` 的统一形 ($\Omega_\Omega$ 闭包之上的输出 $\sqsupseteq2$) 要闭包的证书, 在 Depth0 §5.

```agda
Strict₀ : ∀ {fl φ k ℓ} {P : Run fl} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ} →
          P ≈ᴿ P → FlR P → (y : Ordˢ k) → y ≅ˢ y → (G : Goodᶻ (toZ (fold 0 φ cv P y ev z))) →
          suc zero ⊑ᴵ toLevel (force _ G) (force-HS _ G)
Strict₀ {φ = φ} {P = P} {cv = cv} {ev = ev} {z = z} r fP y ey G =
  toLevel-⊑ (hs hz) (force-HS _ G) (FlΛ-fold {φ = φ} {P = P} {cv = cv} {ev = ev} {p = z} r fP z⊑ y ey idO (Goodᶻ.gs Goodᶻ.gz) G)
```

## §5 覆盖、折叠观测与支配定理

**折叠观测 `IsCol P`**: 目标 0 的 $P$-折叠 (任意地板/`cv`/证据/环境), 外套搬运. **被支配 `ColC P c t`**: 对一切折叠观测与一切证书, $c\sqsubseteq^\mathsf I$ 层号. **覆盖 `CovΛ P φ c`**: 链点 $\hat\chi^P_\varphi=$ `fold 0 (flo φ) (cvFlo φ) P (Ωˢ φ) ev z` (某环境、某证据) 有 Prefix 证书且层号 $\sqsupseteq c$; 地板约定取 `flo φ`, 与 Uniform2 的 `tlᵀ (flo k) (cvFlo k)` 一致, 于是 $\varphi=1$ 的链点就是 `pΩ-label` 的树 (环境可取 `suc zero`).

**支配定理 `dom-cov`.** 与 TreeNFBase 同: 对折叠观测 $O$ 造同形的 `canΛ` 作用于 $\Omega_\varphi$, 它在 $\Omega_\varphi$ 上的值与链点 `fold-≅0`-相关 (同一前缀, 不同地板证据), 证书由覆盖经 `Goodᶻ-tr` 搬来; 地板给 $\hat\chi^P_\varphi\sqsubseteq\mathrm{run}\,O\,t$.

```agda
χ̂ : ∀ {fl} (P : Run fl) (φ : Ordᴵ) {ℓ} → Ev ℓ (fl ⊔ flo φ) → zero <ᴵ ℓ → Ordˢ zero
χ̂ P φ ev z = fold 0 (flo φ) (cvFlo φ) P (Ωˢ φ) ev z

CovΛ : ∀ {fl} (P : Run fl) (φ c : Ordᴵ) → Set
CovΛ {fl} P φ c = Σ Ordᴵ λ ℓ → Σ (Ev ℓ (fl ⊔ flo φ)) λ ev → Σ (zero <ᴵ ℓ) λ z →
                  Σ (Goodᶻ (toZ (χ̂ P φ ev z))) λ G → c ⊑ᴵ toLevel (force _ G) (force-HS _ G)

data IsCol {fl} (P : Run fl) : ∀ {k} → Obs k → Set where
  col  : ∀ {k ℓ φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ} → IsCol P (fo φ idO P cv ev z)
  ctr  : ∀ {a b} {O : Obs b} {e : a ≅ᴵ b} → IsCol P O → IsCol P (tro O e)
  ctr⁻ : ∀ {a b} {O : Obs a} {e : a ≅ᴵ b} → IsCol P O → IsCol P (tr⁻o O e)

ColC : ∀ {fl} (P : Run fl) {k} → Ordᴵ → Ordˢ k → Set
ColC P {k} c t = ∀ {O : Obs k} → IsCol P O → (G : Goodᶻ (toZ (run O t))) → c ⊑ᴵ toLevel (force _ G) (force-HS _ G)

ColC-tr : ∀ {fl} {P : Run fl} {c a b} (e : a ≅ᴵ b) {t : Ordˢ a} → ColC P c t → ColC P c (trˢ e t)
ColC-tr e h k G = h (ctr k) G

ColC-tr⁻ : ∀ {fl} {P : Run fl} {c a b} (e : a ≅ᴵ b) {t : Ordˢ b} → ColC P c t → ColC P c (tr⁻ˢ e t)
ColC-tr⁻ e h k G = h (ctr⁻ k) G

canΛ : ∀ {fl} (P : Run fl) (φ : Ordᴵ) {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} → IsCol P O → Obs φ
canΛ P φ ev z col      = fo (flo φ) idO P (cvFlo φ) ev z
canΛ P φ ev z (ctr k)  = tro (canΛ P φ ev z k) (≅ᴵ-refl φ)
canΛ P φ ev z (ctr⁻ k) = tr⁻o (canΛ P φ ev z k) (≅ᴵ-refl φ)

canΛ-≈ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ φ {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} (c : IsCol P O) →
         canΛ P φ ev z c ≈ᵒ O
canΛ-≈ r φ ev z col      = fo idO r
canΛ-≈ r φ ev z (ctr k)  = tro (canΛ-≈ r φ ev z k)
canΛ-≈ r φ ev z (ctr⁻ k) = tr⁻o (canΛ-≈ r φ ev z k)

canΛ-run : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ φ {ℓ} (ev : Ev ℓ (fl ⊔ flo φ)) (z : zero <ᴵ ℓ) {k} {O : Obs k} (c : IsCol P O)
           {x : Ordˢ φ} → x ≅ˢ Ωˢ φ → run (canΛ P φ ev z c) x ≅ˢ χ̂ P φ ev z
canΛ-run r φ ev z col      ex = fold-≅0 r ex ev z ev z (≅ᴵ-refl zero)
canΛ-run r φ ev z (ctr k)  ex = canΛ-run r φ ev z k (trˢ-≅ (≅ᴵ-refl φ) ex)
canΛ-run r φ ev z (ctr⁻ k) ex = canΛ-run r φ ev z k (tr⁻ˢ-≅ (≅ᴵ-refl φ) ex)

dom-cov : ∀ {fl} {P : Run fl} → P ≈ᴿ P → ∀ {φ c k} {t : Ordˢ k} → FlΛ φ t → CovΛ P φ c → ColC P c t
dom-cov {P = P} r {φ} {t = t} fl (ℓ , ev , z , G* , d) {O} k G =
  ⊑ᴵ-trans d (toLevel-⊑ (force-HS _ G*) (force-HS _ G)
                        (⊑-trans (≅→⊑ (force-≅ (toZ-≅ (≅ˢ-sym rr)) G* G₁)) (fl (canΛ-≈ r φ ev z k) G₁ G)))
  where
  rr : run (canΛ P φ ev z k) (Ωˢ φ) ≅ˢ χ̂ P φ ev z
  rr = canΛ-run r φ ev z k (Ωˢ-refl φ)
  G₁ : Goodᶻ (toZ (run (canΛ P φ ev z k) (Ωˢ φ)))
  G₁ = Goodᶻ-tr (toZ-≅ (≅ˢ-sym rr)) G*
```

**出现不变量 `Occ≺ᴳ P c t₀ g`** (非零层闭包 `ŝ c t₀ g` 的, 相对前缀 $P$): 存在覆盖层号 $\varphi$, 且第 0 点与各点被 $c$ 支配. **保持**: 弹栈 (`Occ-pop`: 统一折叠的弹栈闭包 `cloA 0 t g ev p` 的第 0 点是 `t ev p`, 各点是 `g η …`; 只要它们有地板 $\Omega_\varphi$ 且 $\varphi$ 覆盖界 `suc (Mx B)`), 任意前缀 $Q$ 的折叠 (`Occ-fold`: 目标 $i\sqsupseteq\varphi$, $Q$ 有地板; 支配由再生的地板经 `dom-cov` 重算), 加法 (`Occ-add`), 搬运 (`Occ-tr`, 定义性). `Dom-of-Occ`: 闭包被 $P$ 在目标 0 折叠成第 0 层链时, 不变量就是 `gc` 要的支配 (观测取 `col`).

```agda
Occ≺ᴳ : ∀ {fl} (P : Run fl) {k} (c : Ordᴵ) → Ordˢ k → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k) → Set
Occ≺ᴳ P c t₀ g = Σ Ordᴵ λ φ → CovΛ P φ c × ColC P c t₀ × (∀ η e → ColC P c (g η e))

Dom-of-Occ : ∀ {fl} {P : Run fl} {φ k ℓ c} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl ⊔ φ)} {z : zero <ᴵ ℓ}
             {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → Occ≺ᴳ P c t₀ g →
             (∀ G → c ⊑ᴵ toLevel (force (toZ (fold 0 φ cv P t₀ ev z)) G) (force-HS _ G)) ×
             (∀ η e G → c ⊑ᴵ toLevel (force (toZ (fold 0 φ cv P (g η e) ev z)) G) (force-HS _ G))
Dom-of-Occ (φ , cv , c₀ , cg) = (λ G → c₀ col G) , (λ η e G → cg η e col G)

Occ-fold : ∀ {fl fl′ φ k i ℓ c} {P : Run fl} {Q : Run fl′} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fl′ ⊔ φ)} {p : i <ᴵ ℓ}
           {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → P ≈ᴿ P → Q ≈ᴿ Q → FlR Q →
           (o : Occ≺ᴳ P c t₀ g) → proj₁ o ⊑ᴵ i → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
           Occ≺ᴳ P c (fold 0 φ cv Q t₀ ev p) (λ η e → fold 0 φ cv Q (g η e) ev p)
Occ-fold {φ = φ} {Q = Q} {cv = cv} {ev = ev} {p = p} {t₀ = t₀} {g = g} r rQ fQ (ψ , cv₀ , _ , _) h et eg =
  ψ , cv₀ , dom-cov r (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ h t₀ et) cv₀ ,
  λ η e → dom-cov r (FlΛ-fold {φ = φ} {P = Q} {cv = cv} {ev = ev} {p = p} rQ fQ h (g η e) (eg η e)) cv₀

Occ-add : ∀ {fl k ℓ c} {P : Run fl} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → P ≈ᴿ P →
          (o : Occ≺ᴳ P c t₀ g) → FlΛ (proj₁ o) a → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
          Occ≺ᴳ P c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
Occ-add {t₀ = t₀} {g = g} r (ψ , cv₀ , _ , _) fa et eg =
  ψ , cv₀ , dom-cov r (FlΛ-add t₀ fa et) cv₀ , λ η e → dom-cov r (FlΛ-add (g η e) fa (eg η e)) cv₀

Occ-tr : ∀ {fl} {P : Run fl} {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
         Occ≺ᴳ P c t₀ g → Occ≺ᴳ P c (trˢ e t₀) (λ η d → trˢ e (g η d))
Occ-tr e (ψ , cv₀ , c₀ , cg) = ψ , cv₀ , ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

Occ-tr⁻ : ∀ {fl} {P : Run fl} {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
          Occ≺ᴳ P c t₀ g → Occ≺ᴳ P c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
Occ-tr⁻ e (ψ , cv₀ , c₀ , cg) = ψ , cv₀ , ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)
```

**弹栈.** `cloA 0 t g ev p = ŝ (suc (Mx B)) (t ev p) (λ η e → g η … (lim 0 (iF B)))`, $B=$ `bound (φ ⊔ fk zero) ev p`. 它的 `Occ≺ᴳ` 要: 第 0 点 `t ev p` 与各点 `g η …` 有地板 $\Omega_\psi$, $\psi$ 覆盖 `suc (Mx B)`. 对 `Ω̂A 0 Q` 两者都是 $Q$ 的折叠, 地板由 `FlΛ-fold`.

```agda
Occ-pop : ∀ {fl fl′ i ℓ ψ} {P : Run fl} {Q : Run fl′} (ev : Ev ℓ (fl′ ⊔ fk zero)) (p : i <ᴵ ℓ) → P ≈ᴿ P → Q ≈ᴿ Q → FlR Q →
          ψ ⊑ᴵ i → CovΛ P ψ (Bd (bound (fl′ ⊔ fk zero) ev p)) →
          Occ≺ᴳ P (Bd (bound (fl′ ⊔ fk zero) ev p))
                (fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) ev p)
                (λ η e → fold 0 (fk η) (λ e′ q → e′ (suc q)) Q (Ωˢ η)
                   {ℓ = Mlev (Fc (bound (fl′ ⊔ fk zero) ev p)) (suc η) (FB (bound (fl′ ⊔ fk zero) ev p) e)}
                   (liftEv fl′ (λ q → lim 0 q) (proj₁ (evF (bound (fl′ ⊔ fk zero) ev p))) , (λ q → lim 1 q))
                   (lim 0 (iF (bound (fl′ ⊔ fk zero) ev p))))
Occ-pop {fl′ = fl′} {ψ = ψ} {Q = Q} ev p r rQ fQ h cv₀ =
  ψ , cv₀ , dom-cov r (FlΛ-fold {φ = fk zero} {P = Q} {cv = λ e → e} {ev = ev} {p = p} rQ fQ h (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) cv₀ ,
  λ η e → dom-cov r (FlΛ-fold {φ = fk η} {P = Q} {cv = λ e′ q → e′ (suc q)}
                               {ev = liftEv fl′ (λ q → lim 0 q) (proj₁ (evF (bound (fl′ ⊔ fk zero) ev p))) , (λ q → lim 1 q)}
                               {p = lim 0 (iF (bound (fl′ ⊔ fk zero) ev p))}
                               rQ fQ h (Ωˢ η) (Ωˢ-refl η)) cv₀
```

## §6 对照表: 记号侧、Prefix 树侧与统一树侧

| 记号侧 (StandardOmega/SystemOmega) | Prefix 族树侧 (TreeNFBase) | 统一折叠树侧 (本文) |
|---|---|---|
| $G$-条件: $\psi_0(\Omega_\Omega+b)$ 里经下标 $\ge u$ 可见的参数 $<^\mathsf T$ 项 | `Occ≺ᴳ c t₀ g`: 有覆盖 $\varphi$ 与地板 | `Occ≺ᴳ P c t₀ g`: 同, 覆盖与支配相对前缀 $P$ |
| `occ<`: 出现的下标 $<^\mathsf T$ 项 | `ColC c t₀`: $c\sqsubseteq$ 一切单 $\hat\Omega$ 折叠的层号 | `ColC P c t₀`: $c\sqsubseteq$ 一切目标 0 的 $P$-折叠的层号 |
| 谁看见下标 $u$ | 映射者 $\psi_i$ 再生地板 $\Omega_i$ (`FlΛ-ψ0`/`FlΛ-ψ1`) | **前缀**再生地板: `FlR Q` + `B1` (`FlΛ-fold`), 一条引理代替两种栈 |
| `Lab-oc` 所指的值 | 覆盖链点 $\hat\chi_\varphi=\psi^{[\hat\Omega]}_0(\Omega_\varphi)$ 的证书 | 覆盖链点 $\hat\chi^P_\varphi=\psi_0(P+\Omega_\varphi)$, 地板约定 `flo φ` (= Uniform2 的 `tlᵀ` 树) |
| `SELF` | `dom-cov` (`ψ1-cong` + `toLevel-⊑`) | `dom-cov`: 规范观测在 $\Omega_\varphi$ 上的值与链点 `fold-≅0`-相关 |
| 基本列保持 NF₁ | `Occ-pop`/`Occ-ψ1ᴳ`/`Occ-ψ0ᴳ`/`Occ-addᴳ`/`Occ-trᴳ` | `Occ-pop` (`cloA`, 非紧界 `suc (Mx B)`)/`Occ-fold`/`Occ-add`/`Occ-tr` |
| 上下文 | 观测栈 `ψo₀`/`ψo₁`/`addo`/`tro` | 观测栈 `fo`/`addo`/`tro`; `fo` 带前缀与地板证据 |

**读法.** 统一折叠把 Prefix 的 "两种栈" 吸收进前缀 $P$: 空栈是 `∅ᴿ`, 单 $\hat\Omega$ 栈是 `Ω̂A 0 ∅ᴿ`. 于是每条引理只有一个 `fo` 情况, 但以 $P$ 的自互模拟与地板 (`FlR`) 为前提; 这两条对 `∅ᴿ` 与 `Ω̂A 0 _` 都已证 (`r∅`/`rΩ̂`, `FlR-∅`/`FlR-Ω̂`). 非紧界 `suc (Mx B)` 在不变量里只作为被覆盖的界出现 (`Occ-pop`), 本文不需要它字面等于 `suc i`; Depth0 对 `Ω̂A 0 ∅ᴿ` 证 `Mx B ≡ i` (地板平凡).

## §7 无符号谓词 `Pl`

空前缀的折叠定理 (Depth0) 在目标 0 处要求尾巴无闭包 (Stage2Label 的 `Ok`): 空前缀在目标 0 的输出不能支配非零层闭包. Stage2Label 用异族互模拟定义 `Pl`; 这里改用**语法**谓词: 零、后继、极限、`limᵢ` (分支把无符号输入映成无符号输出)、`up`. 它对搬运 (四重互递归, 形同 `Good-tr`)、加法、$\Omega$、以及空前缀的折叠封闭 (`Pl-fold∅`: 折叠的链点无符号由归纳给出, 递归都落在 `pi` 的字段上).

```agda
module _ (ℓ : Ordᴵ) (P< : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
  data Pl₊ : Ordˢ ℓ → Set where
    pz : Pl₊ Ord₊ˢ.zero
    ps : ∀ {a} → Pl₊ a → Pl₊ (Ord₊ˢ.suc a)
    pl : ∀ {f : ℕ → Ordˢ ℓ} → (∀ n → Pl₊ (f n)) → Pl₊ (Ord₊ˢ.lim f)
    pi : ∀ {j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} →
         (∀ (z : Ordˢ j) → P< j (<→◃ q) (intoˢ (<→◃ q) z) → Pl₊ (f (intoˢ (<→◃ q) z))) → Pl₊ (Ord₊ˢ.limᵢ q f)
    pu : ∀ {k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → P< k (◃₁→◃ r) x → Pl₊ (Ord₊ˢ.up r x)

Pd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
Pd i zero         x = Pl₊ i Pd x
Pd i (suc r)      x = Pd i r x
Pd _ (self {f} n) x = Pl₊ (f n) Pd x
Pd i (lim n r)    x = Pd i r x

Pl : ∀ {ℓ} → Ordˢ ℓ → Set
Pl {ℓ} = Pl₊ ℓ Pd

Pd→Pl : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Pd i r (intoˢ r x) → Pl x
Pd→Pl zero      g = g
Pd→Pl (suc r)   g = Pd→Pl r g
Pd→Pl (self n)  g = g
Pd→Pl (lim n r) g = Pd→Pl r g

Pl→Pd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Pl x → Pd i r (intoˢ r x)
Pl→Pd zero      g = g
Pl→Pd (suc r)   g = Pl→Pd r g
Pl→Pd (self n)  g = g
Pl→Pd (lim n r) g = Pl→Pd r g

Pd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Pd i r (intoˢ r x) → Pd i r′ (intoˢ r′ x)
Pd-conv r r′ g = Pl→Pd r′ (Pd→Pl r g)

Pl-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Pl x → Pl (trˢ e x)
Pl-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Pl x → Pl (tr⁻ˢ e x)
Pl-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Pl u → Pl (backˢ (resˢ q e) u)
Pl-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Pl u → Pl (backˢ (res⁻ˢ q e) u)

Pl-tr e pz = pz
Pl-tr e (ps h) = ps (Pl-tr e h)
Pl-tr e (pl h) = pl (λ n → Pl-tr e (h n))
Pl-tr e (pi {q = q} {f = f} h) = pi (λ z g →
  subst (λ w → Pl (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
        (Pl-tr e (h (backˢ (resˢ q e) z) (Pl→Pd (<→◃ q) (Pl-back q e (Pd→Pl (<→◃ (ltˢ (resˢ q e))) g))))))
Pl-tr (s≅ e) (pu {r = zero} h)   = pu (Pl-tr e h)
Pl-tr (l≅ f) (pu {r = self n} h) = pu (Pl-tr (f n) h)

Pl-tr⁻ e pz = pz
Pl-tr⁻ e (ps h) = ps (Pl-tr⁻ e h)
Pl-tr⁻ e (pl h) = pl (λ n → Pl-tr⁻ e (h n))
Pl-tr⁻ e (pi {q = q} {f = f} h) = pi (λ z g →
  subst (λ w → Pl (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
        (Pl-tr⁻ e (h (backˢ (res⁻ˢ q e) z) (Pl→Pd (<→◃ q) (Pl-back⁻ q e (Pd→Pl (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
Pl-tr⁻ (s≅ e) (pu {r = zero} h)   = pu (Pl-tr⁻ e h)
Pl-tr⁻ (l≅ f) (pu {r = self n} h) = pu (Pl-tr⁻ (f n) h)

Pl-back zero      (s≅ e) h = Pl-tr⁻ e h
Pl-back (suc q)   (s≅ e) h = Pl-back q e h
Pl-back (lim n q) (l≅ f) h = Pl-back q (f n) h

Pl-back⁻ zero      (s≅ e) h = Pl-tr e h
Pl-back⁻ (suc q)   (s≅ e) h = Pl-back⁻ q e h
Pl-back⁻ (lim n q) (l≅ f) h = Pl-back⁻ q (f n) h

Pl-Ω : ∀ a → Pl (Ωˢ a)
Pl-Ω zero      = ps pz
Pl-Ω (suc a)   = pi (λ z h → pu h)
Pl-Ω (lim f s) = pl (λ n → pu (Pl-Ω (f n)))

Pl-add : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → Pl a → Pl b → Pl (addˢ a σ b)
Pl-add pa pz = pa
Pl-add pa (ps h) = ps (Pl-add pa h)
Pl-add pa (pl h) = pl (λ n → Pl-add pa (h n))
Pl-add {a = a} {σ = σ} pa (pi {q = q} {f = f} h) = pi (λ z g →
  subst (λ u → Pl (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z)) (Pl-add pa (h z (Pd-conv (<→◃ (σ q)) (<→◃ q) g))))
Pl-add pa (pu {r = zero} h)   = Pl-add pa h
Pl-add pa (pu {r = self n} h) = Pl-add pa h

Pl-iter : ∀ {ℓ} {c : Ordˢ ℓ} → Pl c → ∀ n → Pl (iter (c +ˢ_) Ord₊ˢ.zero n)
Pl-iter pc zero    = pz
Pl-iter pc (suc n) = Pl-add pc (Pl-iter pc n)

Pl-fold∅ : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {ev : Ev ℓ (fz ⊔ φ)} {p : i <ᴵ ℓ} {t : Ordˢ k} →
           Pl t → Pl (fold 0 φ cv ∅ᴿ t ev p)
Pl-fold∅ {i = i} pz = Pl-Ω i
Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (ps h) = pl (Pl-iter (Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} h))
Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (pl h) = pl (λ n → Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (h n))
Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (pi {j = j} {q = q} {f = f} h) with <ᴵ-dec (cv (proj₂ ev) q) p
... | injᵃ (via e s) = pi (λ z g →
        subst (λ u → Pl (fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ev p)) (sym (out-intoˢ (<→◃ s) z))
              (Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (h (tr⁻ˢ e z) (Pl→Pd (<→◃ q) (Pl-tr⁻ e (Pd→Pl (<→◃ s) g))))))
... | injᵇ _ = pl (λ n → Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (h _ (Pl→Pd (<→◃ q) (ch n))))
  where
  ch : ∀ n → Pl (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)
  ch zero    = Pl-Ω j
  ch (suc n) = Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (h _ (Pl→Pd (<→◃ q) (ch n)))
... | injᶜ _ = pl (λ n → Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = p} (h _ (Pl→Pd (<→◃ q) (ch n))))
  where
  ch : ∀ n → Pl (chainA (λ ev′ → cv (proj₂ ev′) q) (λ x → fold 0 φ cv ∅ᴿ (f (intoˢ (<→◃ q) x))) ev n)
  ch zero    = Pl-Ω j
  ch (suc n) = Pl-fold∅ {φ = φ} {cv = cv} {ev = ev} {p = cv (proj₂ ev) q} (h _ (Pl→Pd (<→◃ q) (ch n)))
Pl-fold∅ {k = suc k′} {cv = cv} {ev = ev} {p = p} (pu {r = zero} h) =
  Pl-fold∅ {φ = flo k′} {cv = cvFlo k′} {ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))} {p = p} h
Pl-fold∅ {φ = φ} {k = lim f s} {cv = cv} {ev = ev} {p = p} (pu {r = self n} h) = Pl-fold∅ {φ = flo (f n)} {cv = cvFlo (f n)} {ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))} {p = p} h
```

**读法.** `Pl-fold∅` 的停机: 对 `Pl` 推导递归; 折叠分支的链点 `ch n` 用 `h _ (ch n)` (推导的字段) 再递归, 与 Stage2Label `chain0-good` 同形. 空前缀的值 $\Omega_i$ 无符号 (`Pl-Ω`), 这就是 "空栈不产生闭包" 的树侧形式.

## §8 结论与边界

**已证 (编译).** 统一折叠深度 0 的观测 `Obs`/`run`/`≈ᵒ`/`run-≅`; 观测前序 `⊑ᵒ`、`≅→⊑ᵒ`、`⊑ᵒ-≅ʳ`; 同余 `fold-cong`/`add-cong`/`tr-cong`/`tr⁻-cong`/`up-l`/`up-r`; 上界引理 `lim-r`/`lim-l`/`suc-r`/`ŝ-r`/`ĉ-r`/`limᵢ-r`; 链起点 `B1` (一条代替 `B1₀`/`B1₁`); `add-r`/`zero-l`/`Ω-monoᵒ`/`rule4ᵒ`; 地板 `FlR`/`FlΛ-fold`/`FlR-∅`/`FlR-Ω̂`/`rΩ̂`/`FlΛ-add`; 严格性 `Strict₀`; 覆盖 `CovΛ`、折叠观测 `IsCol`、`ColC`、**支配定理 `dom-cov`**、`Occ≺ᴳ`、`Dom-of-Occ`、保持 `Occ-fold`/`Occ-add`/`Occ-tr`/`Occ-tr⁻`/`Occ-pop`; 无符号 `Pl` 及其对搬运、加法、$\Omega$、空前缀折叠的封闭.

**与 Prefix 折叠的差别 (任务 1 要求报告的).** (1) 深度索引的子句: 观测只用深度 0, `fold 0` 的子句与 `ψᴾ` 同形, 多出的 `up zero` 换地板子句由相似关系允许两侧地板不同而吸收. (2) `repA`: 只在深度 $\ge1$ 的后继子句出现, 深度 0 的后继子句是重复和, 观测前序不碰 `repA`. (3) 非紧界 `suc (Mx B)`: 观测前序对界不敏感 (`ŝ-r` 对任意界), 不变量里界只作为被覆盖的数 (`Occ-pop`); 界的字面值在 Depth0 对平凡地板算出. (4) 链起点: 前缀在尾巴 0 处的值, 不是 $\Omega_j$ 也不是弹栈闭包的特例, 所以 `B1` 一条; `zero-l` 要前缀自互模拟. (5) 没有 `kd`-相关的新前提: `addo` 照 UniformS.

**边界.** 深度 1 的观测未加 (`fold-≅1` 的 `AlignD` 前提, §1 读法); 本文不含闭包定理 (Depth0) 与检验 (UniformNF). 只导入已有模块, 不改任何已有文件.
