# 折叠的外部规格: 低处的锚点 (底座)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). 目标 $v=0$: `Reg a` 是折叠在 $a$ 上走到的每个点都满足标准形条件, `correct : Reg a → IsPsi 0 a (ψ⁰ a)`. `Reg` 在 $+$, $\psi^0$ 下封闭. 由此 $a<\varepsilon_0$ 的区域与 $\psi_0(\Omega)$, $\psi_0(\Omega+1)$, $\psi_0(\Omega+\omega)$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecAnchor where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
open import OCF.Align.OCFSpecRule
```

## §1 `ΩO 0`

第 0 层的树可以原样搬到任何层 (`emb`). 于是 $\Omega_{u+1}$ 不可能 $\preccurlyeq$ 第 0 层的树.

```agda
emb : ∀ {w} → Ordᶜ zero → Ordᶜ w
emb zero        = zero
emb (suc x)     = suc (emb x)
emb (lim f)     = lim (emb ∘ f)
emb (limᵢ () f)
emb (up () x)

emb-≅ : ∀ {w} (x : Ordᶜ zero) → emb {w} x ≅ emb {w} x
emb-≅ zero        = z≅
emb-≅ (suc x)     = s≅ (emb-≅ x)
emb-≅ (lim f)     = l≅ (λ n → emb-≅ (f n))
emb-≅ (limᵢ () f)
emb-≅ (up () x)

≼emb : ∀ {w} (x : Ordᶜ zero) → x ≼ emb {w} x
≼emb zero        = z≼
≼emb (suc x)     = s≼s (≼emb x)
≼emb (lim f)     = l≼ (λ n → ≼l n (≼emb (f n)))
≼emb (limᵢ () f)
≼emb (up () x)

¬Ω⁺≼⁰ : ∀ w (z : Ordᶜ zero) → Ω (suc w) ≼ z → ⊥
¬Ω⁺≼⁰ w z p = ≺ᵛ-irrefl z (≼-trans (≼emb (suc z)) (≼-trans (≼i (emb (suc z)) (emb-≅ (suc z)) (≼u (≼-refl _))) p))

ΩO-0 : ΩO zero
ΩO-0 zero      z ez p = ≼-refl (Ω zero)
ΩO-0 (suc w)   z ez p = ⊥-elim (¬Ω⁺≼⁰ w z p)
ΩO-0 (lim f s) z ez p = l≼ (λ n → u≼ (ΩO-0 (f n) z ez (≼-trans (≼l n (≼u (≼-refl _))) p)))
```

## §2 `C 0` 里的基本成员

```agda
C0 : ∀ {k} (a : Ordᶜ k) {m} → C zero a (𝟎 {m})
C0 a = base (s≼s z≼)

v0 : ∀ {k} (a : Ordᶜ k) → C zero a (forget zero)
v0 a = C0 a

one∈ : ∀ {k m} (a : Ordᶜ k) → 𝟎 {zero} ≺ᵛ a → C zero a (𝟏 {m})
one∈ a q = cg (s≼s z≼ , s≼s z≼) (col (v0 a) (C0 a) q (irr≡ (wf (𝟎 {zero})) _ (T0 zero)))

suc∈ : ∀ {k m} (a : Ordᶜ k) {x : Ordᶜ m} → 𝟎 {zero} ≺ᵛ a → C zero a x → C zero a (suc x)
suc∈ a q c = plus (λ r → r) c (one∈ a q)
```

`Sel`: $a\in C_0(a+1)$, `N`: $a\in C_0(a)$. `N` 是 Buchholz 的标准形条件. `Sel` 弱一些: $\varepsilon_0$ 既不 `N` 也不 `Sel`; 但极限列的每一项要的只是 `Sel`.

```agda
Sel : ∀ {k} → Ordᶜ k → Set
Sel a = C zero (suc a) a

N : ∀ {k} → Ordᶜ k → Set
N a = C zero a a

N→Sel : ∀ {k} {a : Ordᶜ k} → N a → Sel a
N→Sel {a = a} c = C-a (≼-self-suc a) c

Sel-add : ∀ {m k} {x : Ordᶜ m} {y : Ordᶜ k} (σ : Simᴵ k m) → Sel x → Sel y → Sel (add x σ y)
Sel-add {x = x} {y = y} σ cx cy = plus σ (C-a (s≼s (add-≽ˡ x σ y)) cx) (C-a (s≼s (add-≽ʳ x σ y)) cy)

N-add : ∀ {m k} {x : Ordᶜ m} {y : Ordᶜ k} (σ : Simᴵ k m) → N x → N y → N (add x σ y)
N-add {x = x} {y = y} σ cx cy = plus σ (C-a (add-≽ˡ x σ y) cx) (C-a (add-≽ʳ x σ y) cy)
```

## §3 `Reg`: 折叠走到的点都标准

`Reg` 的行对应折叠的行, `Sd` 是已经单独验证过的种子. 三行都是 §5–§6 的规则的前提, 没有别的东西. `correct` 只是把它们串起来. 这是 "折叠对标准形输入正确" 在无 $\Omega$ 节点的范围内的完整陈述.

```agda
data Reg (Sd : ∀ {k} → Ordᶜ k → Set) {k} : Ordᶜ k → Set where
  rσ : ∀ {a} → Sd a → Reg Sd a
  rz : Reg Sd zero
  rs : ∀ {b} → Reg Sd b → Sel b → Reg Sd (suc b)
  rl : ∀ {f : ℕ → Ordᶜ k} → (∀ n → Reg Sd (f n)) → (∀ n → Sel (f n)) → (∀ n → f n ≺ᵛ f (suc n)) → Reg Sd (lim f)

correct : ∀ {Sd : ∀ {k} → Ordᶜ k → Set} → (∀ {k} {a : Ordᶜ k} → Sd a → IsPsi zero a (ψ⁰ a)) →
          ∀ {k} {a : Ordᶜ k} → Reg Sd a → IsPsi zero a (ψ⁰ a)
correct cs (rσ d) = cs d
correct cs rz = IsPsi-a (z≼ , z≼) (T0 zero)
correct cs {a = suc b} (rs r c) = Tsuc ΩO-0 (correct cs r) c (v0 (suc b))
correct cs {a = lim f} (rl r c st) =
  Tlim ΩO-0 (λ n → correct cs (r n)) st (λ n → C-a st′ (c n)) (λ n → v0 (f (suc n)))
  where st′ : ∀ {n} → suc (f n) ≼ f (suc n)
        st′ {n} = st n

data ∅ : ∀ {k} → Ordᶜ k → Set where

Reg₀ : ∀ {k} → Ordᶜ k → Set
Reg₀ = Reg ∅

correct₀ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → IsPsi zero a (ψ⁰ a)
correct₀ = correct (λ ())

1≼ψ⁰ : ∀ {ℓ₀ k} (y : Ordᶜ k) → 𝟏 {ℓ₀} ≼ ψ⁰ y
1≼ψ⁰ zero            = s≼s z≼
1≼ψ⁰ (suc a)         = ≼l 1 (1≼ψ⁰ a)
1≼ψ⁰ (lim f)         = ≼l 0 (1≼ψ⁰ (f 0))
1≼ψ⁰ (limᵢ {i = j} q f) = ≼l 0 (1≼ψ⁰ (f (into (<→◃ q) (Ω j))))
1≼ψ⁰ (up zero x)     = 1≼ψ⁰ x
1≼ψ⁰ (up (self n) x) = 1≼ψ⁰ x
```

`psi-≽`: 无种子时 $a\preccurlyeq\psi^0a$. 种子不行: $\Omega\not\preccurlyeq\psi^0\Omega$, 这就是 $\varepsilon_0$ 上的缺口.

```agda
psi-≽ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → a ≼ ψ⁰ a
psi-≽ (rσ ())
psi-≽ rz = z≼
psi-≽ {a = suc b} (rs r c) = suc≼M (1≼ψ⁰ b) b (psi-≽ r)
psi-≽ {a = lim f} (rl r c st) = l≼ (λ n → ≼l n (psi-≽ (r n)))

sel-ψ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → Sel a → Sel (ψ⁰ a)
sel-ψ {a = a} r c = col (v0 (suc (ψ⁰ a))) (C-a (s≼s (psi-≽ r)) c) (s≼s (psi-≽ r)) (irr≡ (wf a) _ (correct₀ r))

strict-ψ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → N a → a ≺ᵛ Ω (suc zero) → a ≺ᵛ ψ⁰ a
strict-ψ r c b = ub (correct₀ r) c b

n-ψ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → N a → a ≺ᵛ Ω (suc zero) → N (ψ⁰ a)
n-ψ {a = a} r c b = col (v0 (ψ⁰ a)) (C-a (≺→≼ (strict-ψ r c b)) c) (strict-ψ r c b) (irr≡ (wf a) _ (correct₀ r))
```

## §4 `Reg` 对 $+$ 与 $\psi^0$ 封闭 ($a<\varepsilon_0$ 的区域)

右边的加数没有种子. 左边可以有.

```agda
reg-add : ∀ {Sd : ∀ {k} → Ordᶜ k → Set} {m k} {x : Ordᶜ m} (σ : Simᴵ k m) {y : Ordᶜ k} →
          Reg Sd x → Sel x → Reg₀ y → Reg Sd (add x σ y)
reg-add σ rx cx (rσ ())
reg-add σ rx cx rz = rx
reg-add σ rx cx (rs r c) = rs (reg-add σ rx cx r) (Sel-add σ cx c)
reg-add {x = x} σ rx cx (rl r c st) =
  rl (λ n → reg-add σ rx cx (r n)) (λ n → Sel-add σ cx (c n)) (λ n → add-mono (≼-refl x) (st n))

reg-· : ∀ {x : Ordᶜ zero} → Reg₀ x → Sel x → ∀ n → Reg₀ (x · n)
reg-· rx cx zero    = rz
reg-· rx cx (suc n) = reg-add (λ q → q) rx cx (reg-· rx cx n)

sel-· : ∀ {x : Ordᶜ zero} → Sel x → ∀ n → Sel (x · n)
sel-· cx zero    = C0 _
sel-· cx (suc n) = Sel-add (λ q → q) cx (sel-· cx n)

·-strict : ∀ {ℓ} {x : Ordᶜ ℓ} → 𝟏 {ℓ} ≼ x → ∀ n → x · n ≺ᵛ x · suc n
·-strict one zero          = one
·-strict {x = x} one (suc n) = +-mono (≼-refl x) (·-strict one n)

reg-ψ : ∀ {k} {a : Ordᶜ k} → Reg₀ a → Reg₀ (ψ⁰ a)
reg-ψ (rσ ())
reg-ψ rz = rs rz (C0 _)
reg-ψ {a = suc b} (rs r c) =
  rl (reg-· (reg-ψ r) (sel-ψ r c)) (sel-· (sel-ψ r c)) (·-strict (1≼ψ⁰ b))
reg-ψ {a = lim f} (rl r c st) =
  rl (λ n → reg-ψ (r n)) (λ n → sel-ψ (r n) (c n))
     (λ n → step-from (correct₀ (r n)) (correct₀ (r (suc n))) (st n) (C-a (st n) (c n)) (v0 (f (suc n))))
```

## §5 第一批锚点

$\psi_0(0)=1$, $\psi_0(1)=\omega$, $\psi_0(\omega)=\omega^\omega$, 以及折叠的链 $1,\omega,\omega^\omega,\dots$ 上的每一点. 全是 `correct₀` 的实例. 树都是折叠的字面输出.

```agda
reg-nat : ∀ n → Reg₀ (natᶜ n)
n-nat   : ∀ n → N (natᶜ n)
reg-nat zero    = rz
reg-nat (suc n) = rs (reg-nat n) (N→Sel (n-nat n))
n-nat zero    = C0 _
n-nat (suc n) = suc∈ (natᶜ (suc n)) (s≼s z≼) (C-a (≼-self-suc (natᶜ n)) (n-nat n))

reg-ω : Reg₀ ωᶜ
reg-ω = rl reg-nat (λ n → N→Sel (n-nat n)) (λ n → ≼-refl (natᶜ (suc n)))

anchor-0 : IsPsi zero (𝟎 {zero}) (ψ⁰ (𝟎 {zero}))
anchor-0 = correct₀ rz

anchor-1 : IsPsi zero (𝟏 {zero}) (ψ⁰ (𝟏 {zero}))
anchor-1 = correct₀ (reg-nat 1)

anchor-ω : IsPsi zero ωᶜ (ψ⁰ ωᶜ)
anchor-ω = correct₀ reg-ω

γ : ℕ → Ordᶜ zero
γ zero    = 𝟏
γ (suc n) = ψ⁰ (γ n)

reg-γ : ∀ n → Reg₀ (γ n)
reg-γ zero    = reg-nat 1
reg-γ (suc n) = reg-ψ (reg-γ n)

bnd⁰ : (x : Ordᶜ zero) → x ≺ᵛ Ω (suc zero)
bnd⁰ x = ⇒bd x (≅-refl⁰ x) (≼-refl x)

n-γ : ∀ n → N (γ n)
n-γ zero    = n-nat 1
n-γ (suc n) = n-ψ (reg-γ n) (n-γ n) (bnd⁰ (γ n))

γ-step : ∀ n → γ n ≺ᵛ γ (suc n)
γ-step n = strict-ψ (reg-γ n) (n-γ n) (bnd⁰ (γ n))
```

## §6 $\psi_0(\Omega)=\varepsilon_0$

`δ` 是折叠 $\psi^0(\Omega_1)$ 的字面的链, 它与 `γ` 只差 $\psi^0$ 与带证明的 $\psi$ (`ψ⁰≅ψ`). 托架: `ub` 的归纳假设说 $C_0(\Omega)$ 的可数成员 $<\lim F$, 而 $F_i\cong\delta_{i+1}$, 所以托架是平凡的. **这是最后一个平凡的托架.**

```agda
Ω₁ : Ordᶜ (suc zero)
Ω₁ = Ω (suc zero)

δ : ℕ → Ordᶜ zero
δ = iter (λ x → ψ {i = zero} {k = suc zero} {ℓ = suc zero} zero (λ r → r) (up zero x)) (Ω zero)

γ≅δ : ∀ n → γ n ≅ δ n
γ≅δ zero    = s≅ z≅
γ≅δ (suc n) = ψ⁰≅ψ {ℓ = suc zero} {p = zero} {σ = λ q → suc q} (γ≅δ n)

Fδ : ℕ → Ordᶜ zero
Fδ n = ψ⁰ (δ n)

ψ⁰Ω₁≡ : ψ⁰ Ω₁ ≡ lim Fδ
ψ⁰Ω₁≡ = refl

s-δ : ∀ i → IsPsi zero (δ i) (Fδ i)
s-δ i = IsPsi-a (≅→≈ᵛ (γ≅δ i)) (IsPsi-t (≅→≈ᵛ (ψ⁰-≅ (γ≅δ i))) (correct₀ (reg-γ i)))

Fδ≼γ : ∀ i → Fδ i ≼ γ (suc i)
Fδ≼γ i = ≅→≼ (ψ⁰-≅ (≅-sym (γ≅δ i)))

γ≼Fδ : ∀ i → γ (suc i) ≼ Fδ i
γ≼Fδ i = ≅→≼ (ψ⁰-≅ (γ≅δ i))

st-δ : ∀ i → Fδ i ≺ᵛ Fδ (suc i)
st-δ i = ≼-trans (s≼s (Fδ≼γ i)) (≼-trans (γ-step (suc i)) (γ≼Fδ (suc i)))

anchor-Ω : IsPsi zero Ω₁ (ψ⁰ Ω₁)
anchor-Ω = Tsup {f̂ = δ} ΩO-0 (λ i → ≼i (δ i) (≅-refl⁰ (δ i)) (≼u (≼-refl (δ i)))) s-δ st-δ
  (λ h q → case-br (h q))
  where
  case-br : ∀ {m} {ξ : Ordᶜ m} → ξ ≺ᵛ lim Fδ → Σ ℕ λ i → ξ ≼ δ i
  case-br (≼l i r) = suc i , ≼-trans (≺→≼ r) (≼-trans (Fδ≼γ i) (≅→≼ (γ≅δ (suc i))))
```

**缺口 (规格的定理).** $\varepsilon_0\preccurlyeq a\preccurlyeq\Omega$ 的所有 $a$ 上, 规格给同一个值 $\varepsilon_0$. 经典的 $\psi_0$ 就是这样, 而折叠不是: `ψ⁰` 在 $\varepsilon_0+1$ 上给 $\varepsilon_0\cdot\omega$ (`fold-wrong-at-gap`). 这是 "折叠只在标准形上正确" 的来源.

```agda
ε₀ : Ordᶜ zero
ε₀ = lim Fδ

gap : ∀ {k} {a : Ordᶜ k} → ε₀ ≼ a → a ≼ Ω₁ → IsPsi zero a ε₀
gap {a = a} ea ab = sup (lt anchor-Ω)
  (λ c b → ub anchor-Ω (C-a ab c) b)
  (λ { (≼l i r) → let w = cof (s-δ i) r in
       wit (C-a (≼-trans (≼-trans (≺→≼ (γ-step′ i)) (≼l i (≼-refl (Fδ i)))) ea) (mem w)) (bd w) (dom w) })
  where
  γ-step′ : ∀ i → δ i ≺ᵛ Fδ i
  γ-step′ i = ≼-trans (s≼s (≅→≼ (≅-sym (γ≅δ i)))) (≼-trans (γ-step i) (γ≼Fδ i))
```

## §7 $\psi_0(\Omega+y)$, $y<\varepsilon_0$

$\Omega$ 作种子. `Sel` 对 $\Omega$: $\Omega=\psi_1(0)$, 这要 `T0` 对 $v=1$. 右加数限于 `Reg₀` 且每步 `Sel`, 所以 $y<\varepsilon_0$. $y=\varepsilon_0$ 不在这个范围: 那里 $y\notin C_0(y+1)$, 要的是相对于前缀的标准形, 见 [OCFSpec](OCFSpec.lagda.md) 的分析.

```agda
data SdΩ : ∀ {k} → Ordᶜ k → Set where
  sΩ : SdΩ Ω₁

cs-Ω : ∀ {k} {a : Ordᶜ k} → SdΩ a → IsPsi zero a (ψ⁰ a)
cs-Ω sΩ = anchor-Ω

Ω∈ : ∀ {k} (a : Ordᶜ k) → 𝟎 {zero} ≺ᵛ a → C zero a Ω₁
Ω∈ a q = col {u = suc zero} (one∈ a q) (C0 a) q (irr≡ (wf (𝟎 {zero})) _ (T0 (suc zero)))

sel-Ω : Sel Ω₁
sel-Ω = Ω∈ (suc Ω₁) (s≼s z≼)

Ω+ : Ordᶜ zero → Ordᶜ (suc zero)
Ω+ y = add Ω₁ (λ q → suc q) y

reg-Ω+ : ∀ {y} → Reg₀ y → Reg SdΩ (Ω+ y)
reg-Ω+ r = reg-add (λ q → suc q) (rσ sΩ) sel-Ω r

anchor-Ω+ : ∀ {y} → Reg₀ y → IsPsi zero (Ω+ y) (ψ⁰ (Ω+ y))
anchor-Ω+ r = correct cs-Ω (reg-Ω+ r)

anchor-Ω+1 : IsPsi zero (suc Ω₁) (ψ⁰ (suc Ω₁))
anchor-Ω+1 = anchor-Ω+ (reg-nat 1)

anchor-Ω+ω : IsPsi zero (Ω+ ωᶜ) (ψ⁰ (Ω+ ωᶜ))
anchor-Ω+ω = anchor-Ω+ reg-ω
```
