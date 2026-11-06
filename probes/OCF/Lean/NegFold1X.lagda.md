# 改 "在上" 的折法, 否定一路 (五): 对构造一路的实例的检查

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 只读导入构造一路的 [Fold1Base](Fold1Base.lagda.md) (`Wi`, `ℓT`, `Lg*`), [Fold1Fold](Fold1Fold.lagda.md) (折叠 `Φ`), [Fold1](Fold1.lagda.md) (实例 `I`, 闭项 `TΩ1`), 不改它们. 另导入接口 [Fold1If](Fold1If.lagda.md), [CRwBase](CRwBase.lagda.md) 与本路的 [NegFold1Base](NegFold1Base.lagda.md), [NegFold1If](NegFold1If.lagda.md), [NegFold1Blind](NegFold1Blind.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **构造一路的折叠 (读代码, 2026-11-06 08:26 版).** 直接折到目标层; 坍缩 (种类是第 $x+1$ 层的新种类, $t\lhd x$, 含 $x=t$) 时坐标链 $e_0=$ 世界里的界, $e_{n+1}=e_n\boxplus\Phi_{m\to x,W_n}(g\,e_n)$, 输出是 $o_n=\Phi_{m\to t,W_n}(g\,e_n)$ 的**部分和**的 ℕ-极限; ℕ-极限子句逐点; 证书 `Lg*` (读输入合法), 第 $0$ 层推出 `LgB`.
>
> **定理.**
>
> 1. **`col-acc`, `col-not-val` (坍缩子句的累加).** 第 $1$ 层的结点 $A=\Omega_1\{\_\mapsto1\}$ (分支恒为 $1$, 合法 `Lg-A`) 折到第 $0$ 层得 $\lim(\omega,\ \omega\boxplus\omega,\ \dots)$, 而 $1$ 折出 $\omega$; $\Phi A\not\le\Phi\,1$ (`col-acc`). 推论 `col-not-val`: 对任何含自反与**带界的 $\Omega$-左规则** ("界之下的每个分支 $\le b$ 则 $\Omega$-结点 $\le b$", 世界取实例用的地板世界) 的关系 $R$, 实例的折叠不保 $R$ 到 `≤ᵛ`. 所以实例的折叠在 $\Omega$-输入上**不是值的函数** (对这类关系). 根在坍缩输出取部分和: 相邻输出点相等时, 部分和把值抬高.
> 2. **`gl-TΩ1` (闭项上的基本列).** 闭项 `TΩ1` 的第 $1$ 项字面是 $1\boxplus\omega$, 不是 $\omega$ (`gl-TΩ1`, `gl-ne`). 两者值相同 (`gl-val`). 这是部分和在闭项基本列上的痕迹, 值不变, FGH 的值随之变 (未算).
> 3. **对接口定理的实例化** (`X-no-val-ext`, `X-Lg-not-total`, `X-≤-free`): [NegFold1If](NegFold1If.lagda.md) 的 "对一切实例" 对 `Fold1.I` 成立.
> 4. **盲 (`blind-pair`, `X-b-irr`).** 本路的 `Ibl` 与构造一路的 `I` 满足同一个接口, 在 $\Omega_1$ 的地板上折出 $1$ 与 `TΩ1` (字面不同); 接口的参数 $b$ 在 `I` 里不起作用 (`refl`).
>
> **前提实例.** 1: `Lg-A` (定理); `col-not-val` 的关系 $R$ 的实例: 由自反与带界 $\Omega$-左规则生成的关系 `Rfree` (§2). 2, 4: `refl`. 3: `Fold1.I`.
>
> **只否定什么.** 1 只否定: 实例的折叠对含带界 $\Omega$-左规则的值关系单调 (即 "折叠是值的函数" 在 $\Omega$-输入上); 输入是人造的常值分支结点, 闭项的输入里是否出现这种结点, 未查 (判断: 地板与 `up` 的分支不是常值). **不否定**: 证书 (`Φ-lg`, `Φ-mono`, 由构造一路证明, 本路复编通过); 闭项的合法 (`LgB-TΩ`, `LgB-TΩΩ`, 标准 `LgB`); 去掉部分和后的版本 (那时输出的步进要跨世界的单调, 判断). 2 不是否定, 是对 "累加不产生毛刺" 的反例 (只在基本列的字面上, 值相同).
>
> **证书是哪一种; 闭项.** 证书是字面的 `Lg*` (ℕ-极限在一切合法世界里步进), 不是值关系; 闭项 `TΩ m`, `TΩΩ` 的证书经 `lgB⊥` 是标准 `LgB`. 所以 "用值关系作证书时闭项没有标准 `LgB`" (`NegNoAccMo.mo⇏lgB` 的后果) 不出现.
>
> **读法与 `TU2` (判断, 不是定理).** 接口与实例的层号只有可数层号 (`Lv m`, $m$ 是可数树; 每个种类在某个可数层, `NegFold1Sup.kind-layer`). `TΩΩ` 的对角形状同 CRw 的 `TU2`, 但对角的层是可数层号 $y_n+1$, 读法 ψ₀(Ω_Ω) (构造一路的读法), 与 CRw 的 `TX` 同档; CRw 的 `TU2` 的层是 $\Omega_1\oplus m$ (底是 $\Omega_1$ 层 `XS`), 读法 ψ₀(Ω_{Ω·2}). 所以按读法, 本轮闭项**低于** `TU2`. 没有值的定理支撑两边的读法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1X where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If
open import OCF.Lean.NegFold1Base
open import OCF.Lean.NegFold1If using (¬s≤ᵛ; no-val-ext; Lg-not-total; Φ-≤-free)
open import OCF.Lean.NegFold1Blind using (Ibl)
import OCF.Lean.Fold1Base as B1
import OCF.Lean.Fold1Fold as FF
import OCF.Lean.Fold1 as F1
```

## §1 坍缩子句的部分和

```agda
l≤-inv : ∀ {S : KS} {f : ℕ → HB S} {y : HB S} → hl f ≤ᵛ y → ∀ n → f n ≤ᵛ y
l≤-inv (l≤ h) n = h n
l≤-inv (≤s p) n = ≤s (l≤-inv p n)
l≤-inv (≤l k p) n = ≤l k (l≤-inv p n)
l≤-inv (≤Ω c p) n = ≤Ω c (l≤-inv p n)

L1 : Cd
L1 = hs hz

F₁ : HB (Lv L1) → Cd
F₁ = FF.Φ L1 tt hz (hsuc hself) (B1.Wi L1)

ω̂ : Cd
ω̂ = hl (mul (hs hz))

A : HB (Lv L1)
A = hΩ (inj₂ tt) (λ _ → hs hz)

Lg-A : B1.Lg* (B1.ℓT L1) A
Lg-A = (λ lw e e′ p → hself) , (λ c lc → tt)

one≤A : one ≤ᵛ A
one≤A = ≤Ω hz (≤ᵛ-refl one)

F-one : F₁ one ≡ ω̂
F-one = refl

col-acc : ¬ (F₁ A ≤ᵛ F₁ one)
col-acc p = ¬s≤ᵛ ω̂ r
  where
  q : ω̂ ⊞ ω̂ ≤ᵛ ω̂
  q = l≤-inv p 1
  r : hs ω̂ ≤ᵛ ω̂
  r = l≤-inv q 0
```

**推论: 对含带界 $\Omega$-左规则的关系不是值的函数.** 地板世界 `Wi 1` 里, $\Omega_1$ 的界是 `top 0` $=0$, 所以 "界之下的坐标" 就是 $c\lhd0$.

```agda
col-not-val : (R : HB (Lv L1) → HB (Lv L1) → Set) →
  (rr : ∀ x → R x x) →
  (Ωl : ∀ {g : Cd → HB (Lv L1)} {b} → (∀ c → c ⊲ hz → R (g c) b) → R (hΩ (inj₂ tt) g) b) →
  ¬ (∀ {a c} → R a c → F₁ a ≤ᵛ F₁ c)
col-not-val R rr Ωl mono = col-acc (mono (Ωl (λ c _ → rr one)))

-- 前提可满足: 由自反与带界 Ω-左规则生成的关系
data Rfree : HB (Lv L1) → HB (Lv L1) → Set where
  rf : ∀ {x} → Rfree x x
  ωl : ∀ {g : Cd → HB (Lv L1)} {b} → (∀ c → c ⊲ hz → Rfree (g c) b) → Rfree (hΩ (inj₂ tt) g) b

Rfree-not-val : ¬ (∀ {a c} → Rfree a c → F₁ a ≤ᵛ F₁ c)
Rfree-not-val = col-not-val Rfree (λ x → rf) ωl
```

## §2 闭项 `TΩ1` 的基本列

```agda
hd : Cd → ℕ → Cd
hd (hl f) n = f n
hd x n = x

gl-TΩ1 : hd F1.TΩ1 1 ≡ hs hz ⊞ ω̂
gl-TΩ1 = refl

gl-ne : ¬ (hs hz ⊞ ω̂ ≡ ω̂)
gl-ne e with cong (λ h → hd h 0) e
... | ()

gl-val : (hs hz ⊞ ω̂ ≤ᵛ ω̂) × (ω̂ ≤ᵛ hs hz ⊞ ω̂)
gl-val = l≤ (λ n → ≤l (suc n) (lem n)) , ⊞≤ʳ′
  where
  lem : ∀ n → hs hz ⊞ mul (hs hz) n ≤ᵛ mul (hs hz) (suc n)
  lem zero = ≤ᵛ-refl _
  lem (suc n) = s≤s (lem n)
  ⊞≤ʳ′ : ω̂ ≤ᵛ hs hz ⊞ ω̂
  ⊞≤ʳ′ = l≤ (λ n → ≤l n (≤ᵛ-trans (≤ᵛ-refl (mul (hs hz) n)) (b n)))
    where
    b : ∀ n → mul (hs hz) n ≤ᵛ hs hz ⊞ mul (hs hz) n
    b zero = ≤s (≤ᵛ-refl (hs hz))
    b (suc n) = s≤s (b n)
```

## §3 接口定理的实例化; 盲

```agda
X-no-val-ext : ∀ b → ¬ (∀ {a c} → OF a → Fold1If.Lg F1.I (hs hz) c → a ≤ᵛ c →
                   Fold1If.Φ F1.I (hs hz) tt hz (hsuc hself) b a ≤ᵛ Fold1If.Φ F1.I (hs hz) tt hz (hsuc hself) b c)
X-no-val-ext = no-val-ext F1.I

X-Lg-not-total : ∀ m lm (pt : hz ⊲ m) → ¬ (∀ h → Fold1If.Lg F1.I m h)
X-Lg-not-total = Lg-not-total F1.I

X-≤-free : ∀ m lm t pt b {a c} → OF a → OF c → a ≤ᵛ c →
           Fold1If.Φ F1.I m lm t pt b a ≤ᵛ Fold1If.Φ F1.I m lm t pt b c
X-≤-free = Φ-≤-free F1.I

blind-pair : ¬ (Fold1If.Φ Ibl (hs hz) tt hz (hsuc hself) hz (top (hs hz))
              ≡ Fold1If.Φ F1.I (hs hz) tt hz (hsuc hself) hz (top (hs hz)))
blind-pair ()

X-b-irr : ∀ m lm t pt b b′ h → Fold1If.Φ F1.I m lm t pt b h ≡ Fold1If.Φ F1.I m lm t pt b′ h
X-b-irr m lm t pt b b′ h = refl
```

## 结论 (按档)

- **[定理]** `l≤-inv`; `Lg-A`, `one≤A`, `F-one`, **`col-acc`**, **`col-not-val`**, `Rfree`, `Rfree-not-val`; **`gl-TΩ1`** (`refl`), `gl-ne`, `gl-val`; `X-no-val-ext`, `X-Lg-not-total`, `X-≤-free`; **`blind-pair`**, `X-b-irr`.
- **[判断]** 读法: 本轮闭项 (ψ₀(Ω_Ω) 档) 低于 `TU2` (ψ₀(Ω_{Ω·2})); 去掉坍缩输出的部分和要跨世界的单调; 闭项的输入里没有常值分支的结点.
