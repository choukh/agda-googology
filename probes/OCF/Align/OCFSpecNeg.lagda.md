# 折叠的外部规格: 规格拒绝什么 (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 本文是编译的否定: (1) 规格的两个朴素写法推出 LPO. (2) 规格拒绝已知错的树: 缺口处的折叠, 分支坏的 $\Omega_1'$, `Good` 但不标准的 $w+\Omega$, 静态的 $\omega$-极限替身. (3) 规格看不见基本列: 同值的树都通过, FGH 可以任意小.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecNeg where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Barrier using (LPO; any; any-witness; true→any; any-up)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
open import OCF.Align.OCFSpecRule
open import OCF.Align.OCFSpecAnchor
import OCF.Align.Uniform as Un
```

## §1 朴素的写法推出 LPO

**"$t$ 以下全在 $C$ 里."** $C_0(a)$ 的成员都能判定是 $\preccurlyeq0$ 还是 $\succcurlyeq1$ (`C-dec`, 对推导归纳). 而 $t_\alpha=\lim_n[\mathsf{any}_\alpha(n)]$ 在 $2$ 以下.

```agda
C-dec : ∀ {k} {a : Ordᶜ k} {m} {x : Ordᶜ m} → C zero a x → (x ≼ 𝟎 {zero}) ⊎ (𝟏 {zero} ≼ x)
C-dec {a = a} = Ind.go (λ x → (x ≼ 𝟎 {zero}) ⊎ (𝟏 {zero} ≼ x))
  (λ { (s≼s q) → inj₁ q })
  (λ { {x = x} {y = y} σ (inj₁ p) (inj₁ q) → inj₁ (≼-trans (add-mono {σ′ = λ r → r} p q) z≼)
     ; {x = x} {y = y} σ (inj₂ p) _        → inj₂ (≼-trans p (add-≽ˡ x σ y))
     ; {x = x} {y = y} σ _        (inj₂ q) → inj₂ (≼-trans q (add-≽ʳ x σ y)) })
  (λ {u} {m} {n} {ξ} {w} q r _ _ → inj₂ (1≼ψ̂ (belowᵛ a ξ q) r))
  (λ { (e , e′) (inj₁ p) → inj₁ (≼-trans e p) ; (e , e′) (inj₂ p) → inj₂ (≼-trans p e′) })

bit : Bool → Ordᶜ zero
bit true  = 𝟏
bit false = zero

tα : (ℕ → Bool) → Ordᶜ zero
tα α = lim (λ n → bit (any α n))

bit≼1 : ∀ b → bit b ≼ 𝟏 {zero}
bit≼1 true  = ≼-refl 𝟏
bit≼1 false = z≼

1≼bit : ∀ b → 𝟏 {zero} ≼ bit b → b ≡ true
1≼bit true  _ = refl
1≼bit false ()

¬s≼z : ∀ {ℓ₁ ℓ₂} {x : Ordᶜ ℓ₁} → ¬ (suc x ≼ 𝟎 {ℓ₂})
¬s≼z ()

decide : ∀ {α : ℕ → Bool} → (tα α ≼ 𝟎 {zero}) ⊎ (𝟏 {zero} ≼ tα α) → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
decide {α} (inj₂ q) with ≼lim⁻ q
... | n , r = inj₁ (any-witness n (1≼bit (any α n) r))
decide {α} (inj₁ p) = inj₂ ff where
  ff : ∀ k → α k ≡ false
  ff k with α k in eq
  ... | false = refl
  ... | true  = ⊥-elim (¬s≼z (≼-trans (≼l k (subst (λ b → 𝟏 {zero} ≼ bit b) (sym (true→any k eq)) (≼-refl (𝟏 {zero})))) p))

naive→LPO : ∀ {k n} {a : Ordᶜ k} {t : Ordᶜ n} → suc (𝟏 {zero}) ≼ t →
            (∀ {m} {y : Ordᶜ m} → y ≺ᵛ t → C zero a y) → LPO
naive→LPO two h α = decide (C-dec (h (≼-trans (s≼s (l≼ (λ n → bit≼1 (any α n)))) two)))
```

**"$C$ 的成员都与 $t$ 可比."** 对 $v=1$. 层 $u_\alpha$ 的第 $n$ 项是 $2$ 或 $1$, 看 $\mathsf{any}_\alpha(n)$. 它是合法的 `Ordᴵ`, 步进证据按位给出. $u_\alpha$ 可数, 所以在 $C_1$ 的基底里, 所以 $\Omega_{u_\alpha}\in C_1(a)$. 它的值是 $\Omega_1$ 或 $\Omega_2$, 与 $(\Omega_1,\Omega_2)$ 里任何 $t$ 比较都判定了 $\alpha$. 这就是壁垒在规格里的样子: 比较只能在陈述里出现, 不能写成成员都可比.

```agda
sel : Bool → Ordᴵ
sel true  = suc (suc zero)
sel false = suc zero

sel-step : ∀ b b′ → (b ≡ true → b′ ≡ true) → sel b ⊑ᴵ sel b′
sel-step true  true  h = ⊑ᴵ-refl
sel-step true  false h with h refl
... | ()
sel-step false true  h = Sim→⊑ᴵ (λ q → suc q)
sel-step false false h = ⊑ᴵ-refl

uα : (ℕ → Bool) → Ordᴵ
uα α = lim (λ n → sel (any α n)) (λ n → sel-step (any α n) (any α (suc n)) (any-up n))

Ω₂ : Ordᶜ (suc (suc zero))
Ω₂ = Ω (suc (suc zero))

gap→LPO : ∀ {k n} {a : Ordᶜ k} {t : Ordᶜ n} → 𝟎 {zero} ≺ᵛ a → Ω₁ ≺ᵛ t → t ≺ᵛ Ω₂ →
          (∀ {m} {x : Ordᶜ m} → C (suc zero) a x → (x ≺ᵛ t) ⊎ (t ≺ᵛ x)) → LPO
gap→LPO {a = a} {t = t} q o1 o2 h α with h memb where
  memb : C (suc zero) a (Ω (uα α))
  memb = col {u = uα α} (base (bnd⁰ (forget (uα α)))) (base (0≺Ω (suc zero))) q (irr≡ (wf (𝟎 {zero})) _ (T0 (uα α)))
... | inj₁ lo = inj₂ ff where
  ff : ∀ k → α k ≡ false
  ff k with α k in eq
  ... | false = refl
  ... | true  = ⊥-elim (≺ᵛ-irrefl t (≼-trans o2 (≼-trans big (≺→≼ lo)))) where
    big : Ω₂ ≼ Ω (uα α)
    big = ≼l k (≼u (subst (λ b → Ω₂ ≼ Ω (sel b)) (sym (true→any k eq)) (≼-refl Ω₂)))
... | inj₂ hi with ≼lim⁻ hi
...   | n , ≼u r with any α n in eq
...     | true  = inj₁ (any-witness n eq)
...     | false = ⊥-elim (≺ᵛ-irrefl t (≼-trans r (≺→≼ o1)))
```

**头部分情况.** $v=1$ 时连 "$x<\Omega_2$ 还是 $x\ge\Omega_2$" 也不能对 $C_1$ 的成员判定. 这是 [OCFSpecTwo](OCFSpecTwo.lagda.md) 的不变量 `D` 的 $v=1$ 版本, 所以那里的托架证明不能照搬到 $\psi_1$ 的 $\Omega_2$-共尾节点上.

```agda
headsplit→LPO : ∀ {k} {a : Ordᶜ k} → 𝟎 {zero} ≺ᵛ a →
                (∀ {m} {x : Ordᶜ m} → C (suc zero) a x → (x ≺ᵛ Ω₂) ⊎ (Ω₂ ≼ x)) → LPO
headsplit→LPO {a = a} q h α with h memb where
  memb : C (suc zero) a (Ω (uα α))
  memb = col {u = uα α} (base (bnd⁰ (forget (uα α)))) (base (0≺Ω (suc zero))) q (irr≡ (wf (𝟎 {zero})) _ (T0 (uα α)))
... | inj₁ lo = inj₂ ff where
  ff : ∀ k → α k ≡ false
  ff k with α k in eq
  ... | false = refl
  ... | true  = ⊥-elim (≺ᵛ-irrefl Ω₂ (≼-trans (s≼s big) lo)) where
    big : Ω₂ ≼ Ω (uα α)
    big = ≼l k (≼u (subst (λ b → Ω₂ ≼ Ω (sel b)) (sym (true→any k eq)) (≼-refl Ω₂)))
... | inj₂ hi with ≼lim⁻ (≼-trans (Ω≺Ω⁺ (suc zero)) hi)
...   | n , ≼u r with any α n in eq
...     | true  = inj₁ (any-witness n eq)
...     | false = ⊥-elim (≺ᵛ-irrefl Ω₁ r)
```

## §2 拒绝: 缺口处的折叠

$\varepsilon_0+1$ 不是标准形. 规格给 $\psi_0(\varepsilon_0+1)=\varepsilon_0$ (`gap`), 折叠给 $\varepsilon_0\cdot\omega$ 以上. 这不是折叠的缺陷: 记号里这种输入也不是标准形. 但它说明规格的正确陈述是 "**标准形输入上**折叠的值满足规格", 这个条件没有文法, 就是 `N`/`Sel`.

```agda
ε≼ψε : ε₀ ≼ ψ⁰ ε₀
ε≼ψε = l≼ (λ i → ≼l i (≼-trans (Fδ≼γ i) (≼-trans (psi-≽ (reg-γ (suc i))) (≅→≼ (ψ⁰-≅ (≅-sym (ψ⁰-≅ (≅-sym (γ≅δ i)))))))))

ε≺ψsε : ε₀ ≺ᵛ ψ⁰ (suc ε₀)
ε≺ψsε = suc≼M (1≼ψ⁰ ε₀) ε₀ ε≼ψε

sε≼Ω : suc ε₀ ≼ Ω₁
sε≼Ω = bnd⁰ ε₀

fold-wrong-at-gap : ¬ IsPsi zero (suc ε₀) (ψ⁰ (suc ε₀))
fold-wrong-at-gap s =
  ≺ᵛ-irrefl ε₀ (≼-trans ε≺ψsε (proj₁ (IsPsi-uniq s (gap (≼-self-suc ε₀) sε≼Ω))))

gap-value : IsPsi zero (suc ε₀) ε₀
gap-value = gap (≼-self-suc ε₀) sε≼Ω
```

## §3 拒绝: 值相同, 分支坏

`ψ⁰-not-cong` 的 $\Omega_1'$ (Value §3) 值是 $\Omega$, 折叠只给 $1$. 规格直接拒绝. 这里不需要 $\psi^0$ 同余: 规格只看值, 所以坏的是**树**, 不是规格.

```agda
g : Ordᶜ zero → Ordᶜ zero
g (suc zero) = zero
g x          = x

Ω₁′ : Ordᶜ (suc zero)
Ω₁′ = limᵢ zero (λ x → up zero (g x))

Ω₁≈Ω₁′ : Ω₁ ≈ᵛ Ω₁′
Ω₁≈Ω₁′ = i≼ (λ x ex → ≼i (suc (suc x)) (≅-refl⁰ _) (u≼ (≼u (≼-suc (≼-suc (≼-refl x))))))
        , i≼ (λ x ex → ≼i (g x) (≅-refl⁰ (g x)) (≼-refl (up zero (g x))))

STEP : Ordᶜ zero → Ordᶜ zero
STEP x = ψ {i = zero} {k = suc zero} {ℓ = suc zero} zero (λ r → r) (up zero (g x))

stall : ∀ n → iter STEP 𝟏 n ≡ 𝟏
stall zero    = refl
stall (suc n) = cong STEP (stall n)

ψΩ₁′≼1 : ψ⁰ Ω₁′ ≼ 𝟏 {zero}
ψΩ₁′≼1 = l≼ (λ n → subst (λ w → ψ⁰ (g w) ≼ 𝟏 {zero}) (sym (stall n)) (≼-refl (𝟏 {zero})))

ψΩ-big : suc (𝟏 {zero}) ≼ ψ⁰ Ω₁
ψΩ-big = ≼l 1 (≼l 2 (≼l 1 (≼l 2 (≼-refl (suc (𝟏 {zero}))))))

bad-branch-rejected : ¬ IsPsi zero Ω₁′ (ψ⁰ Ω₁′)
bad-branch-rejected s =
  ≺ᵛ-irrefl (𝟏 {zero}) (≼-trans ψΩ-big (≼-trans (proj₁ (IsPsi-uniq anchor-Ω (IsPsi-a (proj₂ Ω₁≈Ω₁′ , proj₁ Ω₁≈Ω₁′) s))) ψΩ₁′≼1))
```

## §4 `Good` 不是值同余的片段

Value 留了一个问题: `Good` 是不是 "分支按值单调" 的片段, 折叠在那里尊重值? **不是.** 取 $w=\varepsilon_0+1$, $a'=w+\Omega$. 它的分支 $x\mapsto w+x$ 按值单调 (也按 $\sqsubseteq^\mathsf{o}$ 单调), `Good` (Uniform 的, `a′-good`, 用现成的 `Good-add`). 值上 $a'\approx\Omega$ (`a′≈Ω`). 但 $\psi^0(a')>\varepsilon_0=\psi^0(\Omega)$. 所以**单调不够, 要的是标准形**: 第 0 项 $w+1$ 不标准.

规格拒绝 $\psi^0(a')$ (`good-rejected`). 这是 "规格比 `Good` 强" 的编译证据: `Good` 是证书用的条件 (链走得通, 层号能取), 它不管值对不对.

```agda
w₀ : Ordᶜ zero
w₀ = suc ε₀

a′ : Ordᶜ (suc zero)
a′ = up zero w₀ + Ω₁

a′-good : Un.Good a′
a′-good = Un.Good-add (Un.gu (Un.gs (Un.Good-ψ⁰ (Un.Good-Ω (suc zero)) (Ω-refl (suc zero))))) (upˡ (upʳ (≅-refl⁰ w₀))) (Un.Good-Ω (suc zero))

a′≈Ω : a′ ≈ᵛ Ω₁
a′≈Ω = i≼ (λ x ex → ≼i (w₀ + x) (≅-refl⁰ (w₀ + x)) (≼u (add-mono (u≼ (≼-refl w₀)) (u≼ (≼-refl x)))))
     , add-≽ʳ (up zero w₀) (λ q → q) Ω₁

ε≺ψa′ : ε₀ ≺ᵛ ψ⁰ a′
ε≺ψa′ = ≼-trans ε≺ψsε (≼l 0 (≼l 1 (≼-refl (ψ⁰ w₀))))

Good-not-value-fragment : Un.Good Ω₁ × Un.Good a′ × (a′ ≈ᵛ Ω₁) × ¬ (ψ⁰ a′ ≼ ψ⁰ Ω₁)
Good-not-value-fragment = Un.Good-Ω (suc zero) , a′-good , a′≈Ω , λ e → ≺ᵛ-irrefl ε₀ (≼-trans ε≺ψa′ e)

good-rejected : ¬ IsPsi zero a′ (ψ⁰ a′)
good-rejected s = proj₂ (proj₂ (proj₂ Good-not-value-fragment)) (proj₁ (IsPsi-uniq (IsPsi-a a′≈Ω s) anchor-Ω))
```

## §5 拒绝: 静态替身

$\psi_0(\Omega+\Omega)$ 的正确的树在 $\Omega$-共尾的节点上走上下文计值的链. 静态替身把这个节点换成固定的 $\omega$-极限, 比如 $\Omega+\omega$: 这是 [Value](Value.lagda.md) §8 第 5 行说的 "静态前缀是 $\omega$-共尾的 $\mathbb N$-极限, 值严格更小" 的最小实例. 那里是纸面论证, 这里是编译的: $\psi^0(\Omega+\omega)\in C_0(\Omega+\Omega)$, 所以它不是 $\psi_0(\Omega+\Omega)$ (`static-rejected`). 它自己是 $\psi_0(\Omega+\omega)$ (`anchor-Ω+ω`): 树没有错, 错的是它的位置.

```agda
ΩΩ : Ordᶜ (suc zero)
ΩΩ = Ω₁ + Ω₁

T-static : Ordᶜ zero
T-static = ψ⁰ (Ω+ ωᶜ)

𝟏·≅ : ∀ n → 𝟏 {zero} · n ≅ natᶜ n
𝟏+nat : ∀ n → (𝟏 {zero}) + natᶜ n ≡ natᶜ (suc n)
𝟏+nat zero    = refl
𝟏+nat (suc n) = cong suc (𝟏+nat n)
𝟏·≅ zero    = z≅
𝟏·≅ (suc n) = subst (λ w → 𝟏 {zero} · suc n ≅ w) (𝟏+nat n) (add-≅ (s≅ z≅) (𝟏·≅ n))

ω≈ψ1 : ωᶜ ≈ᵛ ψ⁰ (𝟏 {zero})
ω≈ψ1 = l≼ (λ n → ≼l n (≅→≼ (≅-sym (𝟏·≅ n)))) , l≼ (λ n → ≼l n (≅→≼ (𝟏·≅ n)))

0≺ΩΩ : 𝟎 {zero} ≺ᵛ ΩΩ
0≺ΩΩ = ≼i 𝟏 (s≅ z≅) (s≼s z≼)

1≺ΩΩ : 𝟏 {zero} ≺ᵛ ΩΩ
1≺ΩΩ = ≼i (suc 𝟏) (s≅ (s≅ z≅)) (s≼s (s≼s z≼))

ω∈ : C zero ΩΩ ωᶜ
ω∈ = cg ω≈ψ1 (col (v0 ΩΩ) (one∈ ΩΩ 0≺ΩΩ) 1≺ΩΩ (irr≡ (wf (𝟏 {zero})) _ anchor-1))

ξ≺ΩΩ : Ω+ ωᶜ ≺ᵛ ΩΩ
ξ≺ΩΩ = ≼i (suc ωᶜ) (≅-refl⁰ _) (≼-refl (suc (Ω+ ωᶜ)))

static-in : C zero ΩΩ T-static
static-in = col (v0 ΩΩ) (plus (λ q → suc q) (Ω∈ ΩΩ 0≺ΩΩ) ω∈) ξ≺ΩΩ (irr≡ (wf (Ω+ ωᶜ)) _ (anchor-Ω+ω))

static-rejected : ¬ IsPsi zero ΩΩ T-static
static-rejected s = ¬in s static-in
```

## §6 规格看不见基本列

规格只说值. 同值的树都通过, 而 FGH 不随值走: $\omega$ 与 $\omega^+$ 通过同一个规格 ($\psi_0(1)$), FGH 在 2 处是 $8$ 与 $2048$. 更糟: 对任何 $k$, 有通过规格的树, 它在 $k$ 处的 FGH 只是 $k+1$ (`slow`). 所以**规格判定序数, 不判定大数.** 纲领说大数是树上 FGH 的值, 而规格不管是哪棵树; 它管的是树的序数值.

```agda
ω⁺ : Ordᶜ zero
ω⁺ = lim (natᶜ ∘ suc)

ω≈ω⁺ : ωᶜ ≈ᵛ ω⁺
ω≈ω⁺ = l≼ (λ n → ≼l n (≼-self-suc (natᶜ n))) , l≼ (λ n → ≼l (suc n) (≼-refl (natᶜ (suc n))))

ψ1≈ω : ψ⁰ (𝟏 {zero}) ≈ᵛ ωᶜ
ψ1≈ω = proj₂ ω≈ψ1 , proj₁ ω≈ψ1

spec-ω : IsPsi zero (𝟏 {zero}) ωᶜ
spec-ω = IsPsi-t ψ1≈ω anchor-1

spec-blind : IsPsi zero (𝟏 {zero}) ωᶜ × IsPsi zero (𝟏 {zero}) ω⁺ × FGH ωᶜ 2 ≡ 8 × FGH ω⁺ 2 ≡ 2048
spec-blind = spec-ω , IsPsi-t ω≈ω⁺ spec-ω , refl , refl

le : ℕ → ℕ → Bool
le k       zero    = true
le zero    (suc n) = false
le (suc k) (suc n) = le k n

sa : ℕ → ℕ → Ordᶜ zero
sa k n = if le k n then zero else natᶜ n

slowt : ℕ → Ordᶜ zero
slowt k = lim (sa k)

le-refl : ∀ k → le k k ≡ true
le-refl zero    = refl
le-refl (suc k) = le-refl k

le-big : ∀ k n → le k (suc (k +ᴺ n)) ≡ false
le-big zero    n = refl
le-big (suc k) n = le-big k n

nat-up : ∀ m n → natᶜ n ≼ natᶜ (m +ᴺ n)
nat-up zero    n = ≼-refl (natᶜ n)
nat-up (suc m) n = ≼-suc (nat-up m n)

sa≼ : ∀ k n → sa k n ≼ natᶜ n
sa≼ k n with le k n
... | true  = z≼
... | false = ≼-refl (natᶜ n)

≼sa : ∀ k n → natᶜ n ≼ sa k (suc (k +ᴺ n))
≼sa k n = subst (λ b → natᶜ n ≼ (if b then zero else natᶜ (suc (k +ᴺ n)))) (sym (le-big k n)) (≼-suc (nat-up k n))

slow≈ω : ∀ k → slowt k ≈ᵛ ωᶜ
slow≈ω k = l≼ (λ n → ≼l n (sa≼ k n)) , l≼ (λ n → ≼l (suc (k +ᴺ n)) (≼sa k n))

slow-fgh : ∀ k → FGH (slowt k) k ≡ suc k
slow-fgh k = subst (λ b → FGH (if b then zero else natᶜ k) k ≡ suc k) (sym (le-refl k)) refl

slow : ∀ k → IsPsi zero (𝟏 {zero}) (slowt k) × FGH (slowt k) k ≡ suc k
slow k = IsPsi-t (proj₂ (slow≈ω k) , proj₁ (slow≈ω k)) spec-ω , slow-fgh k
```

## §7 输入是替身时

规格的输入 $a$ 是树, 所以它读的是树的**值**. [Stage2](Stage2.lagda.md) 的 `ts` 是 $\psi^0(\mathrm{suc}\,\Omega_{\ell_0})$, 标签说 $\psi_0(\Omega_\Omega+1)$. 但 $\Omega_{\ell_0}$ 的值是 $\Omega_{\psi_0(\Omega_\Omega)}$, 不是 $\Omega_\Omega$: 这棵树里 $\Omega_{\ell_0}$ 是 $\Omega_\Omega$ 的替身. 下面的定理说: 如果 $\Omega_\ell$ 处在缺口里 (`H`: $C_0(\Omega_\ell+1)$ 的可数成员都 $<\psi^0\Omega_\ell$), 规格就拒绝折叠在 $\Omega_\ell+1$ 的值. 对 $\ell=\ell_0$, `H` 经典地成立 (判断, 这里没有证: $\ell_0\notin C_0(\Omega_{\ell_0}+1)$, 见 [OCFSpec](OCFSpec.lagda.md)). 所以**以 `Ordᶜ` 为输入的规格会拒绝一棵已验收的树**, 不是因为树错了, 而是输入类型不够大: $\Omega_\Omega$ 不是 `Ordᶜ` 的元素.

```agda
rejected-if-gap : ∀ ℓ → (∀ {m} {x : Ordᶜ m} → C zero (suc (Ω ℓ)) x → x ≺ᵛ Ω₁ → x ≺ᵛ ψ⁰ (Ω ℓ)) →
                  ¬ IsPsi zero (suc (Ω ℓ)) (ψ⁰ (suc (Ω ℓ)))
rejected-if-gap ℓ H s =
  let B = ψ⁰ (Ω ℓ)
      w = cof s (suc≼M (1≼ψ⁰ (Ω ℓ)) B (≼-refl B))
  in ≺ᵛ-irrefl B (≼-≺ (dom w) (H (mem w) (≼-≺ (≼-refl _) (bd w))))
```
