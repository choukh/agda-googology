# NegSameV (二): 同一世界放不下同值不同结构的两层; 公共目标下决定不会不一致

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延. 只导入 [CRwBase](CRwBase.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`), [ValCRel](ValCRel.lagda.md), [ValCBase](ValCBase.lagda.md), [ValXRel](ValXRel.lagda.md) 的 `⊲→≤` (不改它们), 不依赖接口.
>
> **问题.** 跨层比较 $\Omega$-结点时, 两边的层 $c_1\approx c_2$ 值相同 (互相 `LeAt hz`) 而结构不同. 本篇问这样的两层能否在同一个世界里相遇, 两边的决定 (留 / 同层 / 在上) 会不会不一致.
>
> **定理.**
>
> 1. **`strict-⊲`.** 第 0 层的值关系沿字面第一位置严格: $a\lhd b$ 且 $b\le a$ ⟹ $a=b$ (字面). `¬s≤`: $x+1\not\le x$; `¬l≤`: $\lim f\le y\le f\,n$ 不可能.
> 2. **`≤→⊲`, `one-spine`.** 合法树 $L$ 的两个第一位置 $a,b$: $a\le b$ ⟹ $a\lhd b$; $a\approx b$ ⟹ $a=b$ (字面). 所以 **`LeAt` 在一棵合法树的第一位置上就是字面的 $\lhd$**.
> 3. **`no-common`.** 所以同值不同结构的两层 $c_1\neq c_2$ 不能都是同一棵合法树 (世界) 的第一位置. `ValXMono.monoX` 的形状 (一个目标 $t$, 两边各带证据 $t\lhd B_i$) 在 "在上" 子句里若取 $t=c_1$, 右边要 $c_1\lhd B_2$, 这与 $c_2\lhd B_2$ 矛盾. 所以 **跨层的归纳不能用一个目标: 目标必须成对** ($t_1\approx t_2$, 输出在不同类型 $H\,t_1$, $H\,t_2$ 里).
> 4. **`dec-agree`, `above-mono`, `keep-mono`.** 目标成对 $t_1\approx t_2$ (含公共目标), 同值的两层给出同一种决定: $c_1+1\lhd t_1\Rightarrow c_2+1\lhd t_2$; $c_1=t_1\Rightarrow c_2=t_2$; $t_1\lhd c_1\Rightarrow t_2\lhd c_2$. 所以 **跨层比较时, 同值的层与同值的目标不会给出不一致的决定**; 非同值时决定按 留 < 同层 < 在上 单调. 这是对 "两边决定不一致" 这个反例来源的否定 (定理).
>
> **前提实例.** 1, 2: 一切树; 例子 `ex-spine` ($B=\omega_1+2$). 3: $c_1=\omega_1$, $c_2=\omega_2$, $B=\omega_2+2$ (`ex-no-common`). 4: $B_2=\omega_2+2$, $t=1$ (`ex-dec`); 成对目标 $t_i=\omega_i$ (`ex-dec₂`).
>
> **只否定什么.** 3 只否定单一目标的归纳形状, 不否定成对目标的归纳. 4 是正面结果 (对构造一路有用), 只说决定的种类一致; 不说输出的值一致, 也不说 "留" 时种类的路径一致. 本篇只讲 `LeAt hz`, 不讲高层关系.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegSameVSpine where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat as N using ()
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁ using (⊲→≤)

infix 4 _≤₀_
_≤₀_ : Cd → Cd → Set
_≤₀_ = LeAt hz

≤₀-tr : ∀ {a b c} → a ≤₀ b → b ≤₀ c → a ≤₀ c
≤₀-tr {a} {b} {c} = L.≤-trans hz {a} {b} {c}

≤₀-rf : ∀ a → a ≤₀ a
≤₀-rf = L.≤-refl hz
```

## §1 严格

```agda
¬s≤ : ∀ x → ¬ (hs x ≤₀ x)
¬s≤ hz ()
¬s≤ (hs x) (Rel.s≤s p) = ¬s≤ x p
¬s≤ (hs x) (Rel.≤s p) = ¬s≤ x (≤₀-tr (Rel.≤s (≤₀-rf (hs x))) p)
¬s≤ (hl f) (Rel.≤l n p) = ¬s≤ (f n) (≤₀-tr (Rel.s≤s (Rel.≤l n (≤₀-rf (f n)))) p)
¬s≤ (hΩ () _) _

¬l≤ : ∀ y {f : ℕ → Cd} n → hl f ≤₀ y → ¬ (y ≤₀ f n)
¬l≤ hz n () q
¬l≤ (hs y) n (Rel.≤s p) q = ¬l≤ y n p (≤₀-tr (Rel.≤s (≤₀-rf y)) q)
¬l≤ (hl g) n (Rel.≤l m p) q = ¬l≤ (g m) n p (≤₀-tr (Rel.≤l m (≤₀-rf (g m))) q)
¬l≤ (hl g) n (Rel.l≤l σ i h) q = ¬l≤ (g (σ n)) (σ n) (≤₀-tr q (h n)) (≤₀-rf (g (σ n)))
¬l≤ (hΩ () _) _ _ _

strict-⊲ : ∀ {a b : Cd} → a ⊲ b → b ≤₀ a → a ≡ b
strict-⊲ hself _ = refl
strict-⊲ {a} {hs b} (hsuc p) q = ⊥-elim (¬s≤ b (≤₀-tr q (⊲→≤ p)))
strict-⊲ {a} {hl f} (hlim n p) q = ⊥-elim (¬l≤ a n q (⊲→≤ p))
strict-⊲ (hLim {κ = ()} _ _) _
```

## §2 一棵合法树的第一位置上, `LeAt` 就是 $\lhd$

```agda
≤→⊲ : ∀ {a b L : Cd} → LgB L → a ⊲ L → b ⊲ L → a ≤₀ b → a ⊲ b
≤→⊲ {a} {b} l p q le with cmpB p q tt l
... | inj₂ r = r
... | inj₁ r = subst (λ z → a ⊲ z) (sym (strict-⊲ r le)) hself

one-spine : ∀ {a b L : Cd} → LgB L → a ⊲ L → b ⊲ L → a ≤₀ b → b ≤₀ a → a ≡ b
one-spine l p q le le′ = sym (strict-⊲ (≤→⊲ l q p le′) le)

no-common : ∀ {a b L : Cd} → ¬ (a ≡ b) → a ≤₀ b → b ≤₀ a → LgB L → a ⊲ L → ¬ (b ⊲ L)
no-common ne le le′ l p q = ne (one-spine l p q le le′)
```

## §3 公共目标下决定一致

`dec-agree`: 层 $c_1, c_2$ (各在自己的世界里, $c_i+1\lhd B_i$), 目标 $t_1\approx t_2$ (可以字面相同; $t_2\lhd B_2$). 三条对应 `pick` 的三种读法 (留: $c+1\lhd t$; 同层: $c=t$; 在上: $t\lhd c$). 证明都在右边的世界里读 $\le$ 成 $\lhd$.

```agda
record DecAgree (c₁ c₂ t₁ t₂ : Cd) : Set where
  field
    keep↑  : hs c₁ ⊲ t₁ → hs c₂ ⊲ t₂
    same↑  : c₁ ≡ t₁ → c₂ ≡ t₂
    above↑ : t₁ ⊲ c₁ → t₂ ⊲ c₂

dec-agree : ∀ {B₂ c₁ c₂ t₁ t₂} → LgB B₂ → hs c₂ ⊲ B₂ → t₂ ⊲ B₂ →
            c₁ ≤₀ c₂ → c₂ ≤₀ c₁ → t₁ ≤₀ t₂ → t₂ ≤₀ t₁ → DecAgree c₁ c₂ t₁ t₂
dec-agree {B₂} {c₁} {c₂} {t₁} {t₂} l pc pt le le′ te te′ = record
  { keep↑ = λ q → ≤→⊲ l pc pt (≤₀-tr (Rel.s≤s le′) (≤₀-tr (⊲→≤ q) te))
  ; same↑ = λ e → one-spine l (⊲ᴮ-tr (hsuc hself) pc) pt
      (≤₀-tr le′ (subst (λ z → z ≤₀ t₂) (sym e) te)) (≤₀-tr te′ (subst (λ z → z ≤₀ c₂) e le))
  ; above↑ = λ q → ≤→⊲ l pt (⊲ᴮ-tr (hsuc hself) pc) (≤₀-tr te′ (≤₀-tr (⊲→≤ q) le)) }
```

**单调方向.** 只有 $c_1\le c_2$, $t_2\le t_1$ 时: 左边 "在上" 则右边 "在上"; 右边 "留" 则左边 "留". 决定在 留 < 同层 < 在上 里单调, 不会反向.

```agda
above-mono : ∀ {B₂ c₁ c₂ t₁ t₂} → LgB B₂ → c₂ ⊲ B₂ → t₂ ⊲ B₂ → c₁ ≤₀ c₂ → t₂ ≤₀ t₁ → t₁ ⊲ c₁ → t₂ ⊲ c₂
above-mono l pc pt le te q = ≤→⊲ l pt pc (≤₀-tr te (≤₀-tr (⊲→≤ q) le))

keep-mono : ∀ {B₁ c₁ c₂ t₁ t₂} → LgB B₁ → hs c₁ ⊲ B₁ → t₁ ⊲ B₁ → c₁ ≤₀ c₂ → t₂ ≤₀ t₁ → hs c₂ ⊲ t₂ → hs c₁ ⊲ t₁
keep-mono l pc pt le te q = ≤→⊲ l pc pt (≤₀-tr (Rel.s≤s le) (≤₀-tr (⊲→≤ q) te))
```

## §4 实例

```agda
nat : ℕ → Cd
nat zero = hz
nat (suc n) = hs (nat n)

ω₁ ω₂ : Cd
ω₁ = hl nat
ω₂ = hl (λ n → nat (suc n))

le₁₂ : ω₁ ≤₀ ω₂
le₁₂ = Rel.l≤l (λ n → n) (L.idInc hz) (λ n → Rel.≤s (≤₀-rf (nat n)))

le₂₁ : ω₂ ≤₀ ω₁
le₂₁ = Rel.l≤l suc (λ n → N.s≤s (L.idInc hz n)) (λ n → ≤₀-rf (nat (suc n)))

ω-ne : ¬ (ω₁ ≡ ω₂)
ω-ne e = lem (cong h e)
  where
  h : Cd → Cd
  h (hl f) = f 0
  h x = x
  lem : ¬ (hz ≡ hs hz)
  lem ()

Lg-nat : ∀ n → LgB (nat n)
Lg-nat zero = tt
Lg-nat (suc n) = Lg-nat n

Lg-ω₂ : LgB ω₂
Lg-ω₂ = (λ n → hsuc hself) , (λ n → Lg-nat (suc n))

Lg-ω₁ : LgB ω₁
Lg-ω₁ = (λ n → hsuc hself) , Lg-nat

ex-spine : LgB (hs (hs ω₁)) × (ω₁ ⊲ hs (hs ω₁))
ex-spine = Lg-ω₁ , hsuc (hsuc hself)

ex-no-common : ¬ (ω₁ ⊲ hs (hs ω₂))
ex-no-common p = no-common (λ e → ω-ne (sym e)) le₂₁ le₁₂ Lg-ω₂ (hsuc (hsuc hself)) p

ex-dec : DecAgree ω₁ ω₂ (hs hz) (hs hz)
ex-dec = dec-agree {hs (hs ω₂)} Lg-ω₂ (hsuc hself) (hsuc (hsuc (hlim 0 hself))) le₁₂ le₂₁ (≤₀-rf _) (≤₀-rf _)

-- 成对目标的实例: 目标本身就是这一对层
ex-dec₂ : DecAgree ω₁ ω₂ ω₁ ω₂
ex-dec₂ = dec-agree {hs (hs ω₂)} Lg-ω₂ (hsuc hself) (hsuc (hsuc hself)) le₁₂ le₂₁ le₁₂ le₂₁
```

## 结论 (按档)

- **[定理, 不用 UIP]** `¬s≤`, `¬l≤`, **`strict-⊲`**, **`≤→⊲`**, **`one-spine`**, **`no-common`**, **`dec-agree`**, `above-mono`, `keep-mono`; 实例 `ex-spine`, `ex-no-common`, `ex-dec`, `ex-dec₂`, `le₁₂`, `le₂₁`, `ω-ne`.
