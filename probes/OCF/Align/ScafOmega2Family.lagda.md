# 脚手架 (二): 站点上的好输入族是下界族, 不是上界族

> 不含记号. 结论写在 [ScafOmega2](ScafOmega2.lagda.md). 只导入 [Level](Level.lagda.md) 与 [LvIRNeg](LvIRNeg.lagda.md) 的旗标.
>
> **结论.** [LvIRNeg](LvIRNeg.lagda.md) 的 `no-read` 说: 好输入含反例族 `y s` 就是 WLPO. [LvIR](LvIR.lagda.md) 由此判断 "好输入要是一个有公共上界的族". 后半句不对 (`G-unbounded`). 另一个出路是**下界证据** $\tau+1\sqsubseteq^\mathsf I\eta$.
>
> 1. `Ordᴵ` 本身含反例族 (`yᴵ`, `no-read-ᴵ`): 只把分支换成 `Ordᴵ` 不够, 无条件的目标判决仍是 WLPO.
> 2. `G τ η` $:=\tau+1\sqsubseteq^\mathsf I\eta$. 判决不要比较 (`G-rise`, `G-suc`). 全假的 `s` 不在族里 (`G-excl`); 这不是把反例族整个排除: `yᴵ (λ _ → true)` 在族里 (`G-y-in`).
> 3. 这个族没有公共上界 (`G-unbounded`), 向上封闭 (`G-up`), 没有族内三歧 (`¬G-tri`).
> 4. 比较的公共上界逐分支现造 (`cmpW`): $\mathrm{Mlev}(\tau+1,\eta+1)$, 由 $\tau$ 与 $\eta$ 自己算出, 不提折叠的输出. 不同分支从不比较.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.ScafOmega2Family where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; Fs; Fst)
open import OCF.Align.LvIRNeg using (flag; flag-false; flag-true; flag→s; WLPO)
```

## §1 `Ordᴵ` 含反例族

$h_s$ 与 [LvIRNeg](LvIRNeg.lagda.md) 同形, 步进证据是字面的搬运 (`Sim→⊑ᴵ`).

```agda
plusᴵ : Ordᴵ → ℕ → Ordᴵ
plusᴵ a zero    = a
plusᴵ a (suc n) = suc (plusᴵ a n)

ωfᴵ : Ordᴵ → Ordᴵ
ωfᴵ a = lim (plusᴵ a) (λ n → Sim→⊑ᴵ suc)

stepᴵ : Bool → Bool → Ordᴵ → ℕ → Ordᴵ
stepᴵ true  _     p n       = suc p
stepᴵ false true  p n       = ωfᴵ p
stepᴵ false false p zero    = p
stepᴵ false false p (suc n) = suc p

hᴵ : (ℕ → Bool) → ℕ → Ordᴵ
hᴵ s zero    = stepᴵ false (s zero) zero zero
hᴵ s (suc n) = stepᴵ (flag s n) (s (suc n)) (hᴵ s n) (suc n)

step-⊑ : ∀ b c p n → p ⊑ᴵ stepᴵ b c p (suc n)
step-⊑ true  c     p n = Sim→⊑ᴵ suc
step-⊑ false true  p n = Sim→⊑ᴵ (lim 0)
step-⊑ false false p n = Sim→⊑ᴵ suc

yᴵ : (ℕ → Bool) → Ordᴵ
yᴵ s = lim (hᴵ s) (λ n → step-⊑ (flag s n) (s (suc n)) (hᴵ s n) n)

ω⁺ : Ordᴵ
ω⁺ = suc ωᴵ

h-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → hᴵ s n ≅ᴵ natᴵ n
h-false s e zero rewrite e zero = z≅
h-false s e (suc n) rewrite flag-false s e n | e (suc n) = s≅ (h-false s e n)

y-false : ∀ s → (∀ n → s n ≡ false) → yᴵ s ≅ᴵ ωᴵ
y-false s e = l≅ (h-false s e)

h-true : ∀ s n → flag s n ≡ true → hᴵ s n ≅ᴵ natᴵ n → ⊥
h-true s zero p e with s zero
h-true s zero p () | true
h-true s (suc n) p e with flag s n in fe | s (suc n)
h-true s (suc n) p (s≅ e) | true  | c = h-true s n fe e
h-true s (suc n) p ()     | false | true

nat-sub : ∀ m {a} → a <ᴵ natᴵ m → Σ ℕ λ k → a ≡ natᴵ k
nat-sub (suc m) zero    = m , refl
nat-sub (suc m) (suc q) = nat-sub m q

lim≠nat : ∀ k {f t} → lim f t ≡ natᴵ k → ⊥
lim≠nat zero    ()
lim≠nat (suc k) ()

lim≮nat : ∀ m {f t} → lim f t <ᴵ natᴵ m → ⊥
lim≮nat m q with nat-sub m q
... | k , e = lim≠nat k e

ω≇nat : ∀ k → ωᴵ ≅ᴵ natᴵ k → ⊥
ω≇nat zero    ()
ω≇nat (suc k) ()

read-yes : ∀ s → yᴵ s ≺ᴵ ω⁺ → ∀ n → flag s n ≡ false
read-yes s (via (l≅ e) zero) n with flag s n in fe
... | false = refl
... | true  = ⊥-elim (h-true s n fe (e n))
read-yes s (via (l≅ e) (suc (lim m q))) n = ⊥-elim (lim≮nat m q)

≺ω⁺ : ∀ {a} → a ≅ᴵ ωᴵ → a ≺ᴵ ω⁺
≺ω⁺ e = via e zero

-- 无条件的判决在 Ordᴵ 上就是 WLPO
no-read-ᴵ : (∀ a → a ≺ᴵ ω⁺ ⊎ ω⁺ ⊑ᴵ a) → WLPO
no-read-ᴵ d s with d (yᴵ s)
... | inj₁ q = inj₁ (flag→s s (read-yes s q))
... | inj₂ (s⊑ e q) = inj₂ (λ af → ≺ᴵ-irrefl (≺ᴵ-respʳ (via e q) (y-false s af)))
```

## §2 下界族

```agda
G : Ordᴵ → Ordᴵ → Set
G τ η = suc τ ⊑ᴵ η

≅ᴵ→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅ᴵ→⊑ᴵ z≅ = z⊑
≅ᴵ→⊑ᴵ (s≅ e) = s⊑ e zero
≅ᴵ→⊑ᴵ (l≅ {t = t} h) = l⊑ (λ n → ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (h n)) (Sim→⊑ᴵ (lim n)))

≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ (via e q) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ r → <ᴵ-trans r q))

-- 判决: 上升. 不比较, 证据就是答案
G-rise : ∀ {τ η} → G τ η → τ ≺ᴵ η
G-rise (s⊑ e q) = via e q

-- `ask` 的形状: 第 a+1 枝问 a 与 τ
G-suc : ∀ {τ a} → G τ (suc a) → τ ⊑ᴵ a
G-suc (s⊑ e zero)    = ≅ᴵ→⊑ᴵ e
G-suc (s⊑ e (suc q)) = ≺→⊑ (via e q)

G-up : ∀ {τ a b} → G τ a → a ⊑ᴵ b → G τ b
G-up = ⊑ᴵ-trans

-- 全假的 s 不在族里
G-excl : ∀ s → G ω⁺ (yᴵ s) → ¬ (∀ n → s n ≡ false)
G-excl s g af with ≺ᴵ-respʳ (G-rise g) (y-false s af)
... | via e (lim m q) with nat-sub m q
... | zero  , refl with e
... | ()
G-excl s g af | via e (lim m q) | suc k , refl with e
... | s≅ d = ω≇nat k d

-- 但 G 不是把反例族整个排除
plus0≅ : ∀ n → plusᴵ zero n ≅ᴵ natᴵ n
plus0≅ zero    = z≅
plus0≅ (suc n) = s≅ (plus0≅ n)

G-y-in : G ω⁺ (yᴵ (λ _ → true))
G-y-in = s⊑ (s≅ (l≅ (λ n → ≅ᴵ-sym (plus0≅ n)))) (lim 2 zero)

-- 没有公共上界
G-unbounded : ∀ τ b → (∀ a → G τ a → a ≺ᴵ b) → ⊥
G-unbounded τ b H = ≺ᴵ-irrefl (H b (≺→⊑ (H (suc τ) ⊑ᴵ-refl)))
```

## §3 比较: 公共上界逐分支现造

$\mathrm{Mlev}(\tau+1,\eta+1)$ 的第 0 项字面含 $\tau$, 其余项字面含 $\eta$ 的前驱, 步进证据就是 `G`. `<ᴵ-dec` 读的正是这个证据. 上界由 $\tau$, $\eta$ 算出, 不提任何折叠的输出, 这是它躲开 [LvStratNeg](LvStratNeg.lagda.md) 的 `self-bound` 的原因: 那里地板要先框住输出, 这里 $\eta$ 自己就是界的一部分.

```agda
W : ∀ {τ η} → G τ η → Ordᴵ
W {τ} {η} e = Mlev (suc τ) (suc η) (⊑ᴵ-trans e (Sim→⊑ᴵ suc))

τ<W : ∀ {τ η} (e : G τ η) → τ <ᴵ W e
τ<W e = lim 0 zero

a<W : ∀ {τ η a} (e : G τ η) → a <ᴵ suc η → a <ᴵ W e
a<W e q = lim 1 q

-- 分支 η 的字面前驱与目标比较: 对一切 η, 只要 e
cmpW : ∀ {τ η a} (e : G τ η) → a <ᴵ suc η → a ≺ᴵ τ ⊎ τ ≺ᴵ a ⊎ a ≅ᴵ τ
cmpW e q = <ᴵ-dec (a<W e q) (τ<W e)
```

## §4 族内没有三歧

两个在族里的成员互不可比. 所以这不是 `Ordᴰ` 的精确初始段, 也用不上全局三歧 ([Barrier](../Barrier.lagda.md) 的前提不成立; 这句对照是判断). 站点从不比较两个分支: `cmpW` 只比分支与目标.

```agda
τ₂ : Ordᴵ
τ₂ = suc ω⁺

m₁ m₂ : Ordᴵ
m₁ = ωfᴵ τ₂
m₂ = ωfᴵ (suc τ₂)

G-m₁ : G ω⁺ m₁
G-m₁ = s⊑ (≅ᴵ-refl ω⁺) (lim 0 zero)

G-m₂ : G ω⁺ m₂
G-m₂ = s⊑ (≅ᴵ-refl ω⁺) (lim 0 (suc zero))

-- m₂ 的字面前驱里, 极限只有 ω 与它的前驱, 它们的第 0 项是 0
plus-sub : ∀ x n {a} → a <ᴵ plusᴵ x n → (a <ᴵ x) ⊎ (Σ ℕ λ k → a ≡ plusᴵ x k)
plus-sub x zero    q       = inj₁ q
plus-sub x (suc n) zero    = inj₂ (n , refl)
plus-sub x (suc n) (suc q) = plus-sub x n q

lim≠plus : ∀ x k {f t} → lim f t ≡ plusᴵ (suc x) k → ⊥
lim≠plus x zero    ()
lim≠plus x (suc k) ()

lim-low : ∀ {x n f t} → lim f t <ᴵ plusᴵ (suc x) n → (∀ {g r} → lim g r <ᴵ suc x → g 0 ≅ᴵ zero) → f 0 ≅ᴵ zero
lim-low {x} {n} q H with plus-sub (suc x) n q
... | inj₁ r = H r
... | inj₂ (k , e) = ⊥-elim (lim≠plus x k e)

low-ω : ∀ {g r} → lim g r <ᴵ ωᴵ → g 0 ≅ᴵ zero
low-ω (lim m q) = ⊥-elim (lim≮nat m q)

low-ω⁺ : ∀ {g r} → lim g r <ᴵ ω⁺ → g 0 ≅ᴵ zero
low-ω⁺ zero    = z≅
low-ω⁺ (suc q) = low-ω q

low-τ₂ : ∀ {g r} → lim g r <ᴵ τ₂ → g 0 ≅ᴵ zero
low-τ₂ (suc q) = low-ω⁺ q

low-τ₂′ : ∀ {g r} → lim g r <ᴵ suc ω⁺ → g 0 ≅ᴵ zero
low-τ₂′ (suc q) = low-ω⁺ q

low-τ₃ : ∀ {g r} → lim g r <ᴵ suc τ₂ → g 0 ≅ᴵ zero
low-τ₃ (suc q) = low-τ₂ q

¬≺₁₂ : m₁ ≺ᴵ m₂ → ⊥
¬≺₁₂ (via (l≅ h) (lim n q)) with h 0 | lim-low {n = n} q low-τ₃
... | e | z with ≅ᴵ-trans e z
... | ()

¬≺₂₁ : m₂ ≺ᴵ m₁ → ⊥
¬≺₂₁ (via (l≅ h) (lim n q)) with h 0 | lim-low {n = n} q low-τ₂′
... | e | z with ≅ᴵ-trans e z
... | ()

¬≅₁₂ : m₁ ≅ᴵ m₂ → ⊥
¬≅₁₂ (l≅ h) with h 0
... | s≅ (s≅ ())

¬G-tri : (∀ a b → G ω⁺ a → G ω⁺ b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b) → ⊥
¬G-tri t with t m₁ m₂ G-m₁ G-m₂
... | inj₁ q = ¬≺₁₂ q
... | inj₂ (inj₁ q) = ¬≺₂₁ q
... | inj₂ (inj₂ e) = ¬≅₁₂ e
```
