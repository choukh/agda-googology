# 验收一侧: 按项序封闭并带 ℕ 极限规则的关系 (一般形式)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `M̂ R s x`: 或有见证项 t, s ≤ᵀ t 且 `R t x` (`ĉ`); 或 s 余尾 ω 且基本列各项都有 `M̂` (`l̂`). 对任意基础关系 R 陈述.
> `keep`: 基础关系上 "a 变成 ψ_j(t₀ + a)" 的保持提升到 `M̂` (记号引理 `cof-app`, `fsn-app` 是等式); `weak`; `exit̂`: 第 0 层出口, 条件 `Ex` 对推导递归 (每片叶子上参照与见证项是标准形, 见证项可数), 极限处用 `hω`.
> 不给出什么: `M̂` 对项序向下封闭没有证 (极限情形要记号一侧的共尾引理); `Ex` 在哪些推导上成立见 [YiMHLean](YiMHLean.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMHRel where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; c1; cω; fsn; natT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; Ctbl)
open import OCF.Align.EboLeanTree using (hc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; l≼; ≼-trans)
open import OCF.Lean.YiMENote using (cofψω; fsnψω; cof++ω; fsn++)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiDCRel using (app≤)
```

## 关系

```agda
data M̂ {X : Set} (R : E.T → X → Set) : E.T → X → Set where
  ĉ : ∀ {s t x} → s ≤ᵀ t → R t x → M̂ R s x
  l̂ : ∀ {s x} → cof s ≡ cω → (∀ k → M̂ R (fsn s k) x) → M̂ R s x

cast : ∀ {X} {R : E.T → X → Set} {s s′ x} → s ≡ s′ → M̂ R s′ x → M̂ R s x
cast refl m = m

weak : ∀ {X} {R : E.T → X → Set} {x x′} → (∀ {t} → R t x → R t x′) → ∀ {s} → M̂ R s x → M̂ R s x′
weak w (ĉ le m) = ĉ le (w m)
weak w (l̂ e h)  = l̂ e (λ k → weak w (h k))
```

## 记号引理与保持

a 余尾 ω 时 ψ_j(t₀ + a) 余尾 ω, 基本列第 k 项是 ψ_j(t₀ + a[k]) (等式; `YiMENote` 的四条组合, 与 `YiRBFam.LF` 的 `mL` 情形所用相同).

```agda
cof-app : ∀ j t₀ a → cof a ≡ cω → cof (ψᴺ j (t₀ ++ a)) ≡ cω
cof-app j t₀ a e = cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e)

fsn-app : ∀ j t₀ a k → cof a ≡ cω → fsn (ψᴺ j (t₀ ++ a)) k ≡ ψᴺ j (t₀ ++ fsn a k)
fsn-app j t₀ a k e = trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))

keep : ∀ {X Y} {R : E.T → X → Set} {R′ : E.T → Y → Set} j t₀ {x y}
     → (∀ {a} → R a x → R′ (ψᴺ j (t₀ ++ a)) y) → ∀ {a} → M̂ R a x → M̂ R′ (ψᴺ j (t₀ ++ a)) y
keep j t₀ f (ĉ le m)        = ĉ (app≤ j t₀ le) (f m)
keep j t₀ f (l̂ {s = a} e h) = l̂ (cof-app j t₀ a e) (λ k → cast (fsn-app j t₀ a k e) (keep j t₀ f (h k)))
```

## 叶子上的谓词

`All P m`: 推导 m 的每片叶子 (参照 s, 见证项 t) 满足 P. `all-keep⁻`: `keep` 之后的叶子是 (ψ_j(t₀ + s), ψ_j(t₀ + t)).

```agda
All : ∀ {X} {R : E.T → X → Set} (P : E.T → E.T → Set) {s x} → M̂ R s x → Set
All P (ĉ {s} {t} le m) = P s t
All P (l̂ e h)          = ∀ k → All P (h k)

all-cast : ∀ {X} {R : E.T → X → Set} {P : E.T → E.T → Set} {s s′ x} (q : s ≡ s′) (m : M̂ R s′ x)
         → All P (cast q m) → All P m
all-cast refl m a = a

all-cast⁺ : ∀ {X} {R : E.T → X → Set} {P : E.T → E.T → Set} {s s′ x} (q : s ≡ s′) (m : M̂ R s′ x)
          → All P m → All P (cast q m)
all-cast⁺ refl m a = a

all-keep⁻ : ∀ {X Y} {R : E.T → X → Set} {R′ : E.T → Y → Set} {P : E.T → E.T → Set} j t₀ {x y}
            (f : ∀ {a} → R a x → R′ (ψᴺ j (t₀ ++ a)) y) {a} (m : M̂ R a x)
          → All P (keep {R′ = R′} j t₀ f m) → All (λ s t → P (ψᴺ j (t₀ ++ s)) (ψᴺ j (t₀ ++ t))) m
all-keep⁻ j t₀ f (ĉ le m) p = p
all-keep⁻ {R′ = R′} {P = P} j t₀ f (l̂ {s = a} e h) p k =
  all-keep⁻ {R′ = R′} {P = P} j t₀ f (h k) (all-cast {P = P} (fsn-app j t₀ a k e) (keep j t₀ f (h k)) (p k))

all-keep⁺ : ∀ {X Y} {R : E.T → X → Set} {R′ : E.T → Y → Set} {P : E.T → E.T → Set} j t₀ {x y}
            (f : ∀ {a} → R a x → R′ (ψᴺ j (t₀ ++ a)) y) {a} (m : M̂ R a x)
          → All (λ s t → P (ψᴺ j (t₀ ++ s)) (ψᴺ j (t₀ ++ t))) m → All P (keep {R′ = R′} j t₀ f m)
all-keep⁺ j t₀ f (ĉ le m) p = p
all-keep⁺ {R′ = R′} {P = P} j t₀ f (l̂ {s = a} e h) p k =
  all-cast⁺ {P = P} (fsn-app j t₀ a k e) (keep j t₀ f (h k)) (all-keep⁺ {R′ = R′} {P = P} j t₀ f (h k) (p k))
```

## 第 0 层出口

`low` 是基础关系的出口 (`lower⁰`). 叶子处照 `YiDCExit.exitᴰ`; 极限处参照的推导只能是 `hω` (或 `h0`, 值为零), 逐项用归纳假设.

```agda
Leafᴺ : E.T → E.T → Set
Leafᴺ s t = NF s × NF t × Ctbl t

Ex : ∀ {X} {R : E.T → X → Set} {s x} → M̂ R s x → Set
Ex = All Leafᴺ

private
  c1≢cω : c1 ≡ cω → ⊥
  c1≢cω ()

exit̂ : ∀ {X} {R : E.T → X → Set} (v : X → L.Ordᶜ L.zero)
      → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x)
      → ∀ {s x} (m : M̂ R s x) → Ex m → (h : HC s) → Rt h ≼ v x
exit̂ v low (ĉ le m) (ns , nt , ct) h         = ≼-trans (mono≤ⁿ ns nt ct h (hc nt ct) le) (low m (hc nt ct))
exit̂ v low (l̂ e f)  ex             (h0 _)    = z≼
exit̂ v low (l̂ e f)  ex             (h1 e′ _) = ⊥-elim (c1≢cω (trans (sym e′) e))
exit̂ v low (l̂ e f)  ex             (hω _ hs) = l≼ (λ n → exit̂ v low (f n) (ex n) (hs n))
```
