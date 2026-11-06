# 改 "在上" 的折法, 否定一路 (三): 接口的盲与边界

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 导入接口 [Fold1If](Fold1If.lagda.md) (定稿 2026-11-06 08:07), [CRwBase](CRwBase.lagda.md), [NegFold1Base](NegFold1Base.lagda.md), [NegNoAccPt](NegNoAccPt.lagda.md) (`pt-no-LgB`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 接口 `Fold1If` 约定: 零, 后继, ℕ-极限三个子句是字面等式 (`Φ-z`, `Φ-s`, `Φ-pt`); 值单调 `Φ-≤` 与 `Φ-l11` 只对无 $\Omega$ 的输入 (`OF`); 合法 `Lg` 由构造一路给出, `Φ-lg` 读输入合法. 本篇问: 这些律各说了什么, 不说什么.
>
> 1. **`Clauses.F-≤`, `Clauses.F-l11` (定理, 对一切函数).** 任一满足三个子句等式的函数 $F$ (任意种类结构之间), 在无 $\Omega$ 的输入上值单调, 且 $\lim(1,1,\dots)$ 与 $1$ 折出互相 $\le$. 所以对每个接口实例, **`Φ-≤` 与 `Φ-l11` 是 `Φ-z`, `Φ-s`, `Φ-pt` 的推论** (`Φ-≤-free`, `Φ-l11-free`): 这两条律不约束折叠在 $\Omega$-结点上做什么, 也就不说强度. "折叠是值的函数" 在接口里只在折叠不做事的地方 (无 $\Omega$ 的部分) 成立.
> 2. **`Det.Sm-F`, `Φ-indep` (定理).** 无 $\Omega$ 的输入上, 输出与源层 $m$, 目标层 $t$, 界 $b$, 实例都无关: 两个实例, 任意两组参数, 形状相同的无 $\Omega$ 输入折出形状相同的树 (`Sm`, 逐构造子同形). 接口的折叠是 "直接折" (对照 [NegFold1Sup](NegFold1Sup.lagda.md) 的复合式: 那里 $G_k\,0$ 随 $k$ 变).
> 3. **`Infl.no-val-Ω`, `no-val-ext` (定理, 对一切实例).** `Φ-≤` 不能推广到带 $\Omega$ 的输入: 第 $1$ 层的地板 $\Omega_1=$ `top 1` 在值关系 `≤ᵛ` 下高于一切无 $\Omega$ 的 `up x` (`up≤top`, 规则 `≤Ω` 可取任意坐标), 而折叠在无 $\Omega$ 的输入上膨胀 (`infl`: $x\le\Phi(\mathrm{up}\,x)$), 所以 "$a$ 无 $\Omega$, $c$ 合法, $a\le c\Rightarrow\Phi a\le\Phi c$" 推出 $\Phi(\Omega_1)$ 在值上不低于一切可数树, 与 $x+1\not\le x$ (`¬s≤ᵛ`) 矛盾. 这条只用三个子句等式与 `lg-top`, 与 $\Omega$-结点怎么折无关.
> 4. **`Lg-not-total` (定理, 对一切实例).** 对任何 $0\lhd m$, 第 $m$ 层的合法 `Lg m` 不是全的 (由 `pt-no-LgB`): 证书必须读输入 (同 `NegNoAccPt.pt-no-total`, 这里对接口一般地写出).
>
> **前提实例.** 1, 2: 三个子句等式在每个接口实例上由 `Φ-z`, `Φ-s`, `Φ-pt` 给出; 不依赖实例的版本对一切函数. 3: 层 $1$ 合法 (`tt`), $0\lhd1$ (`hsuc hself`), `lg-top` 由实例给出. 4: $m=1$. 2, 3, 4 的 "对一切实例" 在构造一路给出实例之前是空真的; 构造一路的实例见 [NegFold1X](NegFold1X.lagda.md) (若写出).
>
> **只否定什么.** 只否定: (3) 用**不带界**的值关系 `≤ᵛ` 把值单调推广到 $\Omega$-输入 (哪怕只推广到 "左边无 $\Omega$, 右边是合法的 $\Omega$-输入"); (4) `Lg` 全. **不否定**: 带界的值关系 (Fab5 的 `≤` 的 `≤Ω` 要求坐标在世界的界之下, `Bdᵛ`) 下的值单调; 接口的任何一条律本身 (1, 2 说它们成立且弱, 不说它们错). 1 与 2 不是否定, 是 "盲": 律对 $\Omega$-结点的折法不加约束.
>
> **对纲领与目标.** 纲领 3 的影子 (`EBOHandbook` §3.1): 3 是 "被比较的两个下标要有字面公共上界" 在值关系上的又一例: `≤Ω` 取任意坐标时, $\Omega_1$ 在值上高于一切可数树, 折到可数层就不可能保值序. 目标 "折叠是值的函数": 要在 $\Omega$-输入上有意义, 值关系必须带界 (判断; 定理只到 3 的范围).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1If where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
open import OCF.Lean.NegFold1Base
open import OCF.Lean.NegNoAccPt using (pt-no-LgB)
```

## §1 后继严格 (值关系)

```agda
¬s≤ᵛ : ∀ {S : KS} (x : HB S) → ¬ (hs x ≤ᵛ x)
¬s≤ᵛ hz ()
¬s≤ᵛ (hs x) (s≤s p) = ¬s≤ᵛ x p
¬s≤ᵛ (hs x) (≤s p) = ¬s≤ᵛ x (≤ᵛ-trans (≤s (≤ᵛ-refl (hs x))) p)
¬s≤ᵛ (hl f) (≤l n p) = ¬s≤ᵛ (f n) (≤ᵛ-trans (s≤s (≤l n (≤ᵛ-refl (f n)))) p)
¬s≤ᵛ (hΩ κ g) (≤Ω c p) = ¬s≤ᵛ (g c) (≤ᵛ-trans (s≤s (≤Ω c (≤ᵛ-refl (g c)))) p)
```

## §2 三个子句推出无 $\Omega$ 输入上的值单调

```agda
module Clauses {S S′ : KS} (F : HB S → HB S′) (ez : F hz ≡ hs hz)
  (es : ∀ h → F (hs h) ≡ hl (mul (F h))) (ep : ∀ f → F (hl f) ≡ hl (λ n → F (f n))) where

  one≤F : ∀ h → OF h → hs hz ≤ᵛ F h
  one≤F hz o = subst (λ z → hs hz ≤ᵛ z) (sym ez) (s≤s z≤)
  one≤F (hs h) o = subst (λ z → hs hz ≤ᵛ z) (sym (es h)) (≤l 0 (one≤F h o))
  one≤F (hl f) o = subst (λ z → hs hz ≤ᵛ z) (sym (ep f)) (≤l 0 (one≤F (f 0) (o 0)))
  one≤F (hΩ _ _) ()

  F-≤ : ∀ {a c} → OF a → OF c → a ≤ᵛ c → F a ≤ᵛ F c
  F-≤ oa oc (z≤ {b = c}) = subst (λ z → z ≤ᵛ F c) (sym ez) (one≤F c oc)
  F-≤ oa oc (s≤s {a = a} {b = b} p) =
    subst₂ _≤ᵛ_ (sym (es a)) (sym (es b)) (l≤ (λ n → ≤l n (mul≤ (F-≤ oa oc p) n)))
  F-≤ oa oc (≤s {a = a} {b = b} p) = subst (λ z → F a ≤ᵛ z) (sym (es b)) (≤l 0 (F-≤ oa oc p))
  F-≤ oa oc (l≤ {f = f} {b = b} h) = subst (λ z → z ≤ᵛ F b) (sym (ep f)) (l≤ (λ n → F-≤ (oa n) oc (h n)))
  F-≤ oa oc (≤l {a = a} {f = f} n p) = subst (λ z → F a ≤ᵛ z) (sym (ep f)) (≤l n (F-≤ oa (oc n) p))
  F-≤ oa () (≤Ω c p)
  F-≤ oa () (Ω≤Ω H)

  F-l11 : (F l11 ≤ᵛ F one) × (F one ≤ᵛ F l11)
  F-l11 = F-≤ (λ _ → tt) tt (l≤ (λ _ → ≤ᵛ-refl one)) , F-≤ tt (λ _ → tt) (≤l 0 (≤ᵛ-refl one))
```

## §3 无 $\Omega$ 的输入上, 输出与层, 目标, 界, 实例无关

`Sm a a′`: 两棵无 $\Omega$ 的树 (可在不同的种类结构里) 逐构造子同形.

```agda
data Sm {S S′ : KS} : HB S → HB S′ → Set where
  sz : Sm hz hz
  ss : ∀ {a b} → Sm a b → Sm (hs a) (hs b)
  sl : ∀ {f g} → (∀ n → Sm (f n) (g n)) → Sm (hl f) (hl g)

Sm-⊞ : ∀ {S S′ : KS} {a : HB S} {a′ : HB S′} {b b′} → Sm a a′ → Sm b b′ → Sm (a ⊞ b) (a′ ⊞ b′)
Sm-⊞ p sz = p
Sm-⊞ p (ss q) = ss (Sm-⊞ p q)
Sm-⊞ p (sl q) = sl (λ n → Sm-⊞ p (q n))

Sm-mul : ∀ {S S′ : KS} {x : HB S} {x′ : HB S′} → Sm x x′ → ∀ n → Sm (mul x n) (mul x′ n)
Sm-mul p zero = p
Sm-mul p (suc n) = Sm-⊞ (Sm-mul p n) p

module Det {S₁ S₂ S₁′ S₂′ : KS}
  (F : HB S₁ → HB S₂) (ez : F hz ≡ hs hz)
  (es : ∀ h → F (hs h) ≡ hl (mul (F h))) (ep : ∀ f → F (hl f) ≡ hl (λ n → F (f n)))
  (F′ : HB S₁′ → HB S₂′) (ez′ : F′ hz ≡ hs hz)
  (es′ : ∀ h → F′ (hs h) ≡ hl (mul (F′ h))) (ep′ : ∀ f → F′ (hl f) ≡ hl (λ n → F′ (f n))) where

  Sm-F : ∀ {a a′} → Sm a a′ → Sm (F a) (F′ a′)
  Sm-F sz = subst₂ (λ u v → Sm u v) (sym ez) (sym ez′) (ss sz)
  Sm-F (ss {a = a} {b = a′} p) = subst₂ (λ u v → Sm u v) (sym (es a)) (sym (es′ a′)) (sl (λ n → Sm-mul (Sm-F p) n))
  Sm-F (sl {f = f} {g = g} p) = subst₂ (λ u v → Sm u v) (sym (ep f)) (sym (ep′ g)) (sl (λ n → Sm-F (p n)))
```

## §4 膨胀, 与值单调推广到 $\Omega$-输入的不可能

第 $1$ 层 `Lv 1` 就是 `step S⊥`, 地板 `top 1` 字面是 $\Omega_1=$ `hΩ (inj₂ tt) up`.

```agda
OF-up : ∀ (x : Cd) → OF (up {S⊥} x)
OF-up hz = tt
OF-up (hs x) = OF-up x
OF-up (hl f) = λ n → OF-up (f n)
OF-up (hΩ () _)

up≤top : ∀ (x : Cd) → up x ≤ᵛ top (hs hz)
up≤top x = ≤Ω x (≤ᵛ-refl (up x))

module Infl (F : HB (Lv (hs hz)) → Cd) (ez : F hz ≡ hs hz)
  (es : ∀ h → F (hs h) ≡ hl (mul (F h))) (ep : ∀ f → F (hl f) ≡ hl (λ n → F (f n))) where
  open Clauses F ez es ep

  infl : ∀ (x : Cd) → x ≤ᵛ F (up x)
  infl hz = z≤
  infl (hs x) = subst (λ z → hs x ≤ᵛ z) (sym (es (up x)))
    (≤l 1 (≤ᵛ-trans (s≤s (infl x)) (⊞≤ʳ (F (up x)) (one≤F (up x) (OF-up x)))))
  infl (hl f) = subst (λ z → hl f ≤ᵛ z) (sym (ep (λ n → up (f n)))) (l≤ (λ n → ≤l n (infl (f n))))
  infl (hΩ () _)

  no-val-Ω : ¬ (∀ (x : Cd) → F (up x) ≤ᵛ F (top (hs hz)))
  no-val-Ω h = ¬s≤ᵛ y (≤ᵛ-trans (infl (hs y)) (h (hs y)))
    where y = F (top (hs hz))
```

## §5 对一切接口实例

```agda
module _ (I : Fold1If) where
  open Fold1If I

  Φ-≤-free : ∀ m lm t pt b {a c} → OF a → OF c → a ≤ᵛ c → Φ m lm t pt b a ≤ᵛ Φ m lm t pt b c
  Φ-≤-free m lm t pt b = Clauses.F-≤ (Φ m lm t pt b) (Φ-z m lm t pt b) (Φ-s m lm t pt b) (Φ-pt m lm t pt b)

  Φ-l11-free : ∀ m lm t pt b → (Φ m lm t pt b l11 ≤ᵛ Φ m lm t pt b one) × (Φ m lm t pt b one ≤ᵛ Φ m lm t pt b l11)
  Φ-l11-free m lm t pt b = Clauses.F-l11 (Φ m lm t pt b) (Φ-z m lm t pt b) (Φ-s m lm t pt b) (Φ-pt m lm t pt b)

  no-val-ext : ∀ b → ¬ (∀ {a c} → OF a → Lg (hs hz) c → a ≤ᵛ c →
                        Φ (hs hz) tt hz (hsuc hself) b a ≤ᵛ Φ (hs hz) tt hz (hsuc hself) b c)
  no-val-ext b ext = Infl.no-val-Ω F (Φ-z _ _ _ _ b) (Φ-s _ _ _ _ b) (Φ-pt _ _ _ _ b)
    (λ x → ext (OF-up x) (lg-top (hs hz) tt) (up≤top x))
    where F = Φ (hs hz) tt hz (hsuc hself) b

  Lg-not-total : ∀ m lm (pt : hz ⊲ m) → ¬ (∀ h → Lg m h)
  Lg-not-total m lm pt tot =
    pt-no-LgB tt (Φ m lm hz pt hz) (Φ-pt m lm hz pt hz)
      (λ h → lg₀ _ (Φ-lg m lm hz pt hz (lg-top hz tt) h (tot h)))

-- 两个实例, 两组参数: 无 Ω 的同形输入折出同形的树
Φ-indep : ∀ (I I′ : Fold1If) m lm t pt b m′ lm′ t′ pt′ b′ {a a′} → Sm a a′ →
          Sm (Fold1If.Φ I m lm t pt b a) (Fold1If.Φ I′ m′ lm′ t′ pt′ b′ a′)
Φ-indep I I′ m lm t pt b m′ lm′ t′ pt′ b′ =
  Det.Sm-F (Φ I m lm t pt b) (Φ-z I m lm t pt b) (Φ-s I m lm t pt b) (Φ-pt I m lm t pt b)
           (Φ I′ m′ lm′ t′ pt′ b′) (Φ-z I′ m′ lm′ t′ pt′ b′) (Φ-s I′ m′ lm′ t′ pt′ b′) (Φ-pt I′ m′ lm′ t′ pt′ b′)
  where open Fold1If
```

## 结论 (按档)

- **[定理]** `¬s≤ᵛ`; **`Clauses.F-≤`**, `Clauses.F-l11`, `one≤F` (对一切满足三个子句等式的函数); `Sm`, `Sm-⊞`, `Sm-mul`, **`Det.Sm-F`**; `OF-up`, `up≤top`, `Infl.infl`, **`Infl.no-val-Ω`**; 对一切接口实例: **`Φ-≤-free`**, **`Φ-l11-free`** (两条律是三个子句的推论), **`no-val-ext`** (值单调推广到 $\Omega$-输入不可能, 用不带界的 `≤ᵛ`), **`Lg-not-total`**; **`Φ-indep`**.
- **[判断]** 接口里与 "值的函数" 有关的两条律对 $\Omega$-结点盲; 要让值的律说出折叠在 $\Omega$-结点上的行为, 值关系要带界 (由 3 推出的方向, 不是定理).
