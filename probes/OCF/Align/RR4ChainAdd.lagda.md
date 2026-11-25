# RR4 实验 (二): "链靠加法增长" 在第 1 层的检验

> 第四次路线审查 (`probes/Survey/RR4-Fable52.md`) 的实验文件, 第 4 层, 不进成品. 只导入 [Level](Level.lagda.md), [Value](Value.lagda.md) 与 [RR4MonoFragment](RR4MonoFragment.lagda.md), 不改任何已有文件.
>
> 要检验的设想 (RouteReview3 §5.9.3 第二行, 主审未验证): 规则 6 的链从 $\gamma_{n+1}=\psi_j(f\,\gamma_n)$ 改为 $\gamma_{n+1}=\gamma_n+\psi_j(f\,\gamma_n)$, 增长由构造保证. 本文只在第 1 层的结点上, 对目标层 0 定义这个变体 `F⁺`, 不改 `Level.ψ`. 四条编译过的定理:
>
> 1. **`escape`**: 在 `Value` 的 $\Omega_1'$ (分支 $g$, $g(1)=0$) 上, 加法链不再停滞: $\psi^0(\Omega_1)\preccurlyeq F^+(g)$. 对照: 原链给 $\psi^0(\Omega_1')\preccurlyeq1$ (`Value.ψΩ₁′≼1`).
> 2. **`same-on-Ω₁`**: 在规范的 $\Omega_1$ 上, 加法链不改值: $F^+(\mathrm{id})\approx^{\mathsf v}\psi^0(\Omega_1)$.
> 3. **`additive-not-cong`**: 加法链仍不是值的函数. 分支 $g^{\mathsf N}$ 把字面的有限数送到 0, 其余不动. `node gᴺ` 与 $\Omega_1$ 同值, 加法链 $1,2,3,\dots$ 始终是字面的有限数 (`trap`), 输出 $F^+(g^{\mathsf N})\preccurlyeq1$.
> 4. **`additive-prefix`**: [RR4MonoFragment](RR4MonoFragment.lagda.md) 的前缀结点对加法链同样偏大: $\mathrm{suc}\,(\psi^0\Omega_1)\preccurlyeq F^+(x\mapsto X+x)$, 于是 $F^+(x\mapsto X+x)\not\preccurlyeq F^+(\mathrm{id})$.
>
> **读法 (判断).** 加法链治好了 "种子处分支取 0" 这一种停滞 (第 1 条), 在规范结点上值不变 (第 2 条). 它没有让折叠成为值的函数 (第 3, 4 条): 链只读可数个点, 分支在这些点以外的取值决定结点的值, 却不被折叠看见. $g^{\mathsf N}$ 在 "一切 ℕ-极限的值都无穷" 的输入上对值单调 (`gᴺ-mono`, 条件定理), 它的毛病是在 $\omega$ 处不连续.
>
> **范围.** 只对第 1 层结点、目标层 0. 没有证加法链的输出相邻项是字面第一位置, 没有把变体接进 `Level.ψ` 的其它行, 没有回灌. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR4ChainAdd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Value
  using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc;
         s≼s⁻; s≼0; ≼-+ʳ; +-mono; ψ⁰-mono⁰; 1≼ψ⁰; 𝟏; 𝟐; g; Ω₁; Ω₁′; ψΩ₁′≼1)
open import OCF.Align.RR4MonoFragment
  using (Br; node; STEPʰ; chain; step≼; step≽; ≼-+ˡ; x≼ψ⁰; irr; module Prefix; X)
```

## §1 加法链

```agda
STEP⁺ : Br → Ordᶜ zero → Ordᶜ zero
STEP⁺ h x = x + STEPʰ h x

chain⁺ : Br → ℕ → Ordᶜ zero
chain⁺ h = iter (STEP⁺ h) 𝟏

F⁺ : Br → Ordᶜ zero
F⁺ h = lim (λ n → ψ⁰ (h (chain⁺ h n)))

idᵇ : Br
idᵇ x = x
```

## §2 在 $\Omega_1'$ 上不再停滞

`Value.g` 只在字面的 `suc zero` 处取 0. 加法链的前三项是 $1$, $2$, $2+\psi(2)$; 从第 2 项起都是 `lim`, 那里 $g$ 是恒等 (`g-lim`, `refl`).

```agda
data IsLim : Ordᶜ zero → Set where
  islim : ∀ {f} → IsLim (lim f)

g-lim : ∀ {x} → IsLim x → g x ≡ x
g-lim islim = refl

step-lim : ∀ {x} → IsLim x → IsLim (STEP⁺ g x)
step-lim islim = islim

d-lim : ∀ n → IsLim (chain⁺ g (suc (suc n)))
d-lim zero    = islim
d-lim (suc n) = step-lim (d-lim n)

ψ⁰g : ∀ n → ψ⁰ (chain⁺ g (suc (suc n))) ≼ ψ⁰ (g (chain⁺ g (suc (suc n))))
ψ⁰g n = subst (λ w → ψ⁰ (chain⁺ g (suc (suc n))) ≼ ψ⁰ w)
  (sym (g-lim (d-lim n))) (≼-refl (ψ⁰ (chain⁺ g (suc (suc n)))))

c≼d : ∀ n → chain idᵇ n ≼ chain⁺ g (suc (suc n))
c≼d zero    = ≼-trans (≼-suc (≼-refl 𝟏)) (≼-+ʳ 𝟐 (STEPʰ g 𝟐))
c≼d (suc n) =
  ≼-trans (step≼ idᵇ (chain idᵇ n))
  (≼-trans (ψ⁰-mono⁰ (c≼d n))
  (≼-trans (ψ⁰g n)
  (≼-trans (step≽ g (chain⁺ g (suc (suc n))))
           (≼-+ˡ (chain⁺ g (suc (suc n))) (STEPʰ g (chain⁺ g (suc (suc n))))))))

escape : ψ⁰ Ω₁ ≼ F⁺ g
escape = l≼ (λ n → ≼l (suc (suc n)) (≼-trans (ψ⁰-mono⁰ (c≼d n)) (ψ⁰g n)))

-- 对照: 原链在同一个结点上停滞 (Value)
original-stalls : ψ⁰ Ω₁′ ≼ 𝟏
original-stalls = ψΩ₁′≼1
```

## §3 在规范的 $\Omega_1$ 上值不变

下界: 加法链逐项不低于原链. 上界: 原链严格增长 (`c-strict`), 于是加法链的第 $n$ 项不超过原链的第 $2n$ 项.

```agda
c≼c⁺ : ∀ n → chain idᵇ n ≼ chain⁺ idᵇ n
c≼c⁺ zero    = ≼-refl 𝟏
c≼c⁺ (suc n) =
  ≼-trans (step≼ idᵇ (chain idᵇ n))
  (≼-trans (ψ⁰-mono⁰ (c≼c⁺ n))
  (≼-trans (step≽ idᵇ (chain⁺ idᵇ n))
           (≼-+ˡ (chain⁺ idᵇ n) (STEPʰ idᵇ (chain⁺ idᵇ n)))))

-- suc (ψ⁰ a) ≼ ψ⁰ (suc a): 规则 4 的第 2 项
suc-ψ⁰ : ∀ (a : Ordᶜ zero) → suc (ψ⁰ a) ≼ ψ⁰ (suc a)
suc-ψ⁰ a = ≼l 2 (+-mono (≼-refl (ψ⁰ a)) (1≼ψ⁰ a))

-- a + ψ⁰ a ≼ ψ⁰ (suc a)
dbl-ψ⁰ : ∀ (a : Ordᶜ zero) → a + ψ⁰ a ≼ ψ⁰ (suc a)
dbl-ψ⁰ a = ≼l 2 (+-mono (x≼ψ⁰ a) (≼-refl (ψ⁰ a)))

c-strict : ∀ n → suc (chain idᵇ n) ≼ chain idᵇ (suc n)
c-strict zero    = ≼-trans (≼l 2 (≼-refl 𝟐)) (step≽ idᵇ 𝟏)
c-strict (suc n) =
  ≼-trans (s≼s (step≼ idᵇ (chain idᵇ n)))
  (≼-trans (suc-ψ⁰ (chain idᵇ n))
  (≼-trans (ψ⁰-mono⁰ (c-strict n)) (step≽ idᵇ (chain idᵇ (suc n)))))

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

c⁺≼c : ∀ n → chain⁺ idᵇ n ≼ chain idᵇ (dbl n)
c⁺≼c zero    = ≼-refl 𝟏
c⁺≼c (suc n) =
  ≼-trans (+-mono (c⁺≼c n) (≼-trans (step≼ idᵇ (chain⁺ idᵇ n)) (ψ⁰-mono⁰ (c⁺≼c n))))
  (≼-trans (dbl-ψ⁰ (chain idᵇ (dbl n)))
  (≼-trans (ψ⁰-mono⁰ (c-strict (dbl n))) (step≽ idᵇ (chain idᵇ (suc (dbl n))))))

same-on-Ω₁ : F⁺ idᵇ ≈ᵛ ψ⁰ Ω₁
same-on-Ω₁ =
    l≼ (λ n → ≼l (dbl n) (ψ⁰-mono⁰ (c⁺≼c n)))
  , l≼ (λ n → ≼l n (ψ⁰-mono⁰ (c≼c⁺ n)))
```

## §4 加法链仍不是值的函数: 有限数陷阱

`gᴺ` 在字面的有限数上取 0, 其余不动. 判定 "是不是字面的有限数" 只看构造子, 不比较值.

```agda
isNum : Ordᶜ zero → Bool
isNum zero        = true
isNum (suc x)     = isNum x
isNum (lim f)     = false
isNum (limᵢ () f)
isNum (up () x)

sel : Bool → Ordᶜ zero → Ordᶜ zero
sel true  x = zero
sel false x = x

gᴺ : Br
gᴺ x = sel (isNum x) x

isNum-nat : ∀ k → isNum (natᶜ k) ≡ true
isNum-nat zero    = refl
isNum-nat (suc k) = isNum-nat k

gᴺ-nat : ∀ k → gᴺ (natᶜ k) ≡ zero
gᴺ-nat k = cong (λ b → sel b (natᶜ k)) (isNum-nat k)

trap : ∀ n → chain⁺ gᴺ n ≡ natᶜ (suc n)
trap zero    = refl
trap (suc n) =
  trans (cong (STEP⁺ gᴺ) (trap n))
        (cong (λ z → natᶜ (suc n) + ψ {i = zero} {k = suc zero} {ℓ = suc zero} zero (λ r → r) (up zero z))
              (gᴺ-nat (suc n)))

F⁺gᴺ≼1 : F⁺ gᴺ ≼ 𝟏
F⁺gᴺ≼1 = l≼ (λ n → subst (λ w → ψ⁰ w ≼ 𝟏)
  (sym (trans (cong gᴺ (trap n)) (gᴺ-nat (suc n)))) (≼-refl 𝟏))
```

`node gᴺ` 与 $\Omega_1$ 同值. 上界取的坐标是严格增的极限 $\lim_n(x+n)$, 不是常值极限.

```agda
Ω₁≈nodeᴺ : Ω₁ ≈ᵛ node gᴺ
Ω₁≈nodeᴺ =
    i≼ (λ x ex → ≼i (lim (λ n → x + natᶜ n)) (≅-refl⁰ (lim (λ n → x + natᶜ n)))
                    (u≼ (≼u (≼l 0 (≼-refl x)))))
  , i≼ (λ x ex → ≼i (gᴺ x) (≅-refl⁰ (gᴺ x)) (≼-refl (up zero (gᴺ x))))

two≼F⁺ : 𝟐 ≼ F⁺ idᵇ
two≼F⁺ = ≼l 0 (≼l 2 (≼-refl 𝟐))

additive-not-cong : (Ω₁ ≈ᵛ node gᴺ) × ¬ (F⁺ idᵇ ≼ F⁺ gᴺ)
additive-not-cong = Ω₁≈nodeᴺ , λ e → s≼0 (s≼s⁻ (≼-trans two≼F⁺ (≼-trans e F⁺gᴺ≼1)))
```

**`gᴺ` 在什么输入上对值单调.** 设 $x$ 不是字面的有限数时值无穷 (`Inf x`: 一切有限数都在它之下). 严格增的 ℕ-极限满足这一条; 常值极限 $\lim\,\mathrm{const}\,1$ 不满足. 在这个前提下 $x\preccurlyeq y\Rightarrow g^{\mathsf N}x\preccurlyeq g^{\mathsf N}y$.

```agda
Inf : Ordᶜ zero → Set
Inf x = ∀ k → natᶜ k ≼ x

num→nat : ∀ y → isNum y ≡ true → Σ ℕ (λ k → y ≡ natᶜ k)
num→nat zero        e = zero , refl
num→nat (suc y)     e with num→nat y e
... | k , refl = suc k , refl
num→nat (lim f)     ()
num→nat (limᵢ () f) e
num→nat (up () x)   e

gᴺ-mono : ∀ x y → (isNum x ≡ false → Inf x) → x ≼ y → gᴺ x ≼ gᴺ y
gᴺ-mono x y inf e with isNum x in ex | isNum y in ey
... | true  | _     = z≼
... | false | false = e
... | false | true  with num→nat y ey
...   | k , refl = ⊥-elim (irr (natᶜ k) (≼-trans (inf refl (suc k)) e))

-- 前提的实例: ω 不是字面的有限数, 值无穷
ω-inf : isNum ωᶜ ≡ false → Inf ωᶜ
ω-inf _ k = ≼l k (≼-refl (natᶜ k))
```

## §5 前缀结点对加法链同样偏大

```agda
module PX = Prefix X

additive-prefix : (Ω₁ ≈ᵛ node PX.hA) × ¬ (F⁺ PX.hA ≼ F⁺ idᵇ)
additive-prefix = PX.same-value ,
  λ e → irr X (≼-trans (≼l 0 (≼l 2 (+-mono (x≼ψ⁰ X) (1≼ψ⁰ X))))
                (≼-trans e (proj₁ same-on-Ω₁)))
```

## §6 结论与边界

| 结点 (都与 $\Omega_1$ 同值) | 原链 $\psi^0$ | 加法链 $F^+$ |
|---|---|---|
| $\Omega_1$ (分支恒等) | $X$ | $\approx^{\mathsf v}X$ (`same-on-Ω₁`) |
| $\Omega_1'$ (`Value.g`) | $\preccurlyeq1$ (`Value.ψΩ₁′≼1`) | $\succcurlyeq X$ (`escape`) |
| `node gᴺ` | 本文未证 | $\preccurlyeq1$ (`F⁺gᴺ≼1`) |
| $\Omega_1^X$ (分支 $X+x$) | $\succcurlyeq X+1$ (`RR4MonoFragment.sucX≼`) | $\succcurlyeq X+1$ (`additive-prefix`) |

**已编译:** `escape`, `same-on-Ω₁`, `additive-not-cong`, `additive-prefix`, `gᴺ-mono` (条件, 前提实例 `ω-inf`).

**没有证的.** 加法链输出的相邻项是否字面第一位置 (合法性); 高层结点; 接进完整的 $\psi$ 之后其它行是否仍成立; 序数值在一般结点上与原链的关系. 所以本文对 "链靠加法增长" 的结论只有: 它在第 1 层治好一种停滞, 在规范结点上保值, 但不解决 "折叠不是值的函数".
