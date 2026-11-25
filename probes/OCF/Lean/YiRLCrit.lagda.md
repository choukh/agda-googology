# 验收 (换基): 目标第 2 层的判据在 ℕ 极限形状的孩子上

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提: 目标层 ⊕ c 的原型 `gᵗ` 对一切满足 `M⁰ (natT (3+k)) c` 的 c 对着 ψ₂(Ω_{3+k}) (`finᵗ`), 所以对一切满足 `M⁰ ω c` 的 c 对着 ψ₂(Ω_ω) 的基本列第 3 项起的每一项 (`ωfamᵗ`), 第 0, 2 项也成立 (`ω0ᵗ`, `ω2ᵗ`); 兄弟孩子 `gˢ` 同样, 但 c 限在 `Can` 内 (ℕ 极限处经孩子 0 的路径接相邻路径等于字面前缀路径; `ωᶜ`, `ωᵉ` 在内).
> 判据本身 `M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (g c)` 归约到基本列第 1 项 ψ₂(Ω₁) (`ω-of-1ᵗ`, `ω-of-1ˢ`); 该项在 c = `nat 1` 处被 [YiRLNeg](YiRLNeg.lagda.md) 否定, 在 ℕ 极限的 c 处未证也未否定. 按项序封闭后的形式逐项成立 (`ω̃ᵗ`, `ω̃ˢ`), 有限的 η 处对一切 n 成立, 含 n = 1 (`fiñᵗ`, `fiñˢ`). 余尾 ω 的一般 η 一步归约到基本列各项 (`limSL`).
> 来源: 归纳的骨架照 `YiKCStep.ind`, `YiCLPhi.Slim` (候选 A); 有限处的判据引 `YiRBCrit.critC`, `critU`. 不涉及 ω 以上的后继 (那里要 ℕ 极限层号上的关系族), 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRLCrit where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (OKB; pt; module Self)
open import OCF.Lean.YiRBCrit
open import OCF.Lean.YiRLClos
open import OCF.Lean.YiKVRel using (M⁰; mL; mw; _⊴_; ⊴r; ⊴◃; +⊴)
open import OCF.Lean.YiKVInst using (Ωω; fsnΩω)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; fsn; natT; 𝟏)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiMENote using (fsnψ1; cofψω; fsnψω)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn; M; module GM; m⊴N; Mβ)
open import OCF.Lean.YiCLLow using (pth)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1; nat⊴; z⊴; inv-lim)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᵉ; dbl)
open import OCF.Lean.YiDCRel using (Ω≤; app≤)
```

## 两种换基折的层, 证据, 路径

```agda
ℓᵗ ℓˢ : Tr zero → L
ℓᵗ c = two ⊕ ↑ zero c
ℓˢ c = h₁ (nat 2 + c)

oᵗ : (c : Tr zero) → Ok (ℓᵗ c)
oᵗ c = Ok⊕ two (↑ zero c) o2 (OkO↑ two zero tt (z≤ two) c)

oˢ : (c : Tr zero) → Ok (ℓˢ c)
oˢ c = proj₂ (Ok-tw 1) (nat 2 + c)

Sᵗ Sˢ : E.T → Tr zero → Set
Sᵗ t c = SL t (ℓᵗ c) (oᵗ c) (lift two (↑ zero c))
Sˢ t c = SL t (ℓˢ c) (oˢ c) (wˢ c)

atᵗ : ∀ {t} (c : Tr zero) → Sᵗ t c → M 2 t (proj₁ (gᵗ c))
atᵗ c s = m⊴N 2 (s (rb-no _) (B₀ _) (Ωt two) (okB₀ _) hβ₂) (+⊴ _ _)

atˢ : ∀ {t} (c : Tr zero) → Sˢ t c → M 2 t (proj₁ (gˢ c))
atˢ c s = m⊴N 2 (s (rb-no _) (B₀ _) (Ωt two) (okB₀ _) hβ₂) (+⊴ _ _)
```

## 目标层 ⊕ c: 沿第 0 层的 `◃` 向上封闭, 对一切 c

ℕ 极限处路径是 `inu`, 第 n 项用孩子 n 自己的路径.

```agda
closᵗ : ∀ {t x x′} → zero ⊢ x ◃ x′ → Sᵗ t x → Sᵗ t x′
closᵗ {t} (◃s {x = x})           s = sucU {t} (ℓᵗ x) (oᵗ (suc x)) (lift two (↑ zero x)) s
closᵗ {t} (◃l {f = f} {a = a} n) s = limU {t} (λ k → ℓᵗ (f k)) (oᵗ (lim f a)) (λ k → lift two (↑ zero (f k))) n s
closᵗ (◃w {p = ()})
closᵗ (◃u _ () _ _)
closᵗ (◃c _ () _)
closᵗ (◃t d e)                   s = closᵗ e (closᵗ d s)

clos⊴ᵗ : ∀ {t x x′} → x ⊴ x′ → Sᵗ t x → Sᵗ t x′
clos⊴ᵗ ⊴r     s = s
clos⊴ᵗ (⊴◃ d) s = closᵗ d s
```

## 兄弟孩子: 量化域 `Can`

ℕ 极限处路径经孩子 0 (`YiRBSib.pre`), 第 n 项经 `way` 落到孩子 n 的层, 路径是 `wˢ (f 0) ∙ from0`. `PreOk`: 它等于孩子 n 自己的路径.

```agda
PreOk : (f : ℕ → Tr zero) → ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) → Set
PreOk f a = (m : ℕ) → wˢ (f 0) ∙ from0 (λ k → ℓˢ (f k)) (proj₁ (oˢ (lim f a))) m ≡ wˢ (f m)

Can : Tr zero → Set
Can zero          = ⊤
Can (suc x)       = Can x
Can (lim f a)     = PreOk f a × ((n : ℕ) → Can (f n))
Can (Ω () _)
Can (up _ () _ _)

can↓ : ∀ {x x′} → zero ⊢ x ◃ x′ → Can x′ → Can x
can↓ ◃s            c       = c
can↓ (◃l n)        (_ , c) = c n
can↓ (◃w {p = ()})
can↓ (◃u _ () _ _)
can↓ (◃c _ () _)
can↓ (◃t d e)      c       = can↓ d (can↓ e c)

closˢ : ∀ {t x x′} → zero ⊢ x ◃ x′ → Can x′ → Sˢ t x → Sˢ t x′
closˢ {t} (◃s {x = x})           c       s = sucC {t} (ℓˢ x) (oˢ (suc x)) (wˢ x) s
closˢ {t} (◃l {f = f} {a = a} n) (p , _) s =
  limC {t} (λ k → ℓˢ (f k)) (oˢ (lim f a)) (wˢ (f 0)) n (subst (SL t (ℓˢ (f n)) (oˢ (f n))) (sym (p n)) s)
closˢ (◃w {p = ()})
closˢ (◃u _ () _ _)
closˢ (◃c _ () _)
closˢ (◃t d e)                   c       s = closˢ e c (closˢ d (can↓ e c) s)

clos⊴ˢ : ∀ {t x x′} → x ⊴ x′ → Can x′ → Sˢ t x → Sˢ t x′
clos⊴ˢ ⊴r     c s = s
clos⊴ˢ (⊴◃ d) c s = closˢ d c s
```

`ωᶜ` (极限 0, 1, 2, …) 与 `ωᵉ` (极限 0, 2, 4, …) 在 `Can` 内.

```agda
canN : ∀ n → Can (nat n)
canN zero    = tt
canN (suc n) = canN n

preω : PreOk nat (λ n → ◃s)
preω zero    = refl
preω (suc m) = cong (inc {s = sS} {h = λ _ → ℓˢ (nat m)} tt) (preω m)

canω : Can ωᶜ
canω = preω , canN

canD : ∀ n → Can (dbl n)
canD zero    = tt
canD (suc n) = canD n

preᵉ : PreOk dbl (λ n → ◃t ◃s ◃s)
preᵉ zero    = refl
preᵉ (suc m) =
  cong (λ v → inc {s = sS} {h = λ _ → nd sS (λ _ → ℓˢ (dbl m))} tt (inc {s = sS} {h = λ _ → ℓˢ (dbl m)} tt v)) (preᵉ m)

canᵉ : Can ωᵉ
canᵉ = preᵉ , canD
```

## 有限的 η ≥ 3, 对量化域内的一切 c

```agda
baseᵗ : ∀ {t} n → SP t (fn (sh n) , pt (ptk n)) → Sᵗ t (nat n)
baseᵗ {t} n s r B β ok hβ = subst (SP t) (sym (eqᵗ n)) s (oᵗ (nat n)) r B β ok hβ

baseˢ : ∀ {t} n → SP t (fn (sh n) , pth (sbk n)) → Sˢ t (nat n)
baseˢ {t} n s r B β ok hβ = subst (SP t) (sym (eqˢ n)) s (oˢ (nat n)) r B β ok hβ

Sfinᵗ : ∀ k {c} → M⁰ (natT (suc (suc (suc k)))) c → Sᵗ (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) c
Sfinᵗ k l = clos⊴ᵗ (nat⊴ (suc (suc (suc k))) l refl) (baseᵗ (suc (suc (suc k))) (critU k))

Sfinˢ : ∀ k {c} → Can c → M⁰ (natT (suc (suc (suc k)))) c → Sˢ (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) c
Sfinˢ k cc l = clos⊴ˢ (nat⊴ (suc (suc (suc k))) l refl) cc (baseˢ (suc (suc (suc k))) (critC k))

finᵗ : ∀ k {c} → M⁰ (natT (suc (suc (suc k)))) c → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gᵗ c))
finᵗ k {c} l = atᵗ c (Sfinᵗ k l)

finˢ : ∀ k {c} → Can c → M⁰ (natT (suc (suc (suc k)))) c → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gˢ c))
finˢ k {c} cc l = atˢ c (Sfinˢ k cc l)
```

## η = 0 与 η = 2

ψ₂(Ω₀) 的基本列是 Ω₂·n: 第 2 层上是保留结点的第一分支 `next⁺ β`, 后继形状取折叠的第 0 项, ℕ 极限取第 0 项. ψ₂(Ω₂): c = 0 处是第 2 层的自身折叠 (`YiRBFam.Self.PF`), 再向上封闭.

```agda
n1 : (β : Tr⁺ two) → M 2 (Ωᴺ 2) (proj₁ β) → M 2 (ψᴺ 2 (Ωᴺ 0)) (proj₁ (next⁺ β))
n1 β hβ = GM.m-next 1 β refl (λ n → fsnψ1 (natT 2) (𝟏 ∷ []) n refl) hβ

S0ᵗ : (c : Tr zero) → Sᵗ (ψᴺ 2 (Ωᴺ 0)) c
S0ᵗ zero          r B β ok hβ = mw (n1 β hβ) ◃w
S0ᵗ (suc x)       r B β ok hβ = suc0U (ℓᵗ x) (oᵗ (suc x)) (lift two (↑ zero x)) r B β (n1 β hβ)
S0ᵗ (lim f a)                 = limU (λ k → ℓᵗ (f k)) (oᵗ (lim f a)) (λ k → lift two (↑ zero (f k))) 0 (S0ᵗ (f 0))
S0ᵗ (Ω () _)
S0ᵗ (up _ () _ _)

S0ˢ : (c : Tr zero) → Sˢ (ψᴺ 2 (Ωᴺ 0)) c
S0ˢ zero          r B β ok hβ = mw (n1 β hβ) ◃w
S0ˢ (suc x)       r B β ok hβ = suc0C (ℓˢ x) (oˢ (suc x)) (wˢ x) r B β (n1 β hβ)
S0ˢ (lim f a)                 = limC (λ k → ℓˢ (f k)) (oˢ (lim f a)) (wˢ (f 0)) 0 (S0ˢ (f 0))
S0ˢ (Ω () _)
S0ˢ (up _ () _ _)

S2ᵗ : (c : Tr zero) → Sᵗ (ψᴺ 2 (Ωᴺ 2)) c
S2ᵗ c = clos⊴ᵗ (z⊴ c) (λ r B β ok hβ → Self.PF 1 (oᵗ zero) r B β {P₀ = []} hβ (Mβ 1))

S2ˢ : (c : Tr zero) → Can c → Sˢ (ψᴺ 2 (Ωᴺ 2)) c
S2ˢ c cc = clos⊴ˢ (z⊴ c) cc (λ r B β ok hβ → Self.PF 1 (oˢ zero) r B β {P₀ = []} hβ (Mβ 1))
```

## η = ω

参照 ψ₂(Ω_ω) 的基本列第 k 项是 ψ₂(Ω_k) (`fsnω`); 余尾 ω 的一般 η 一步归约 (`limSL`).

```agda
a2-lim : ∀ η (x : Tr two) → cof η ≡ cω → (∀ n → M 2 (ψᴺ 2 (E.Ωt (fsn η n))) x) → M 2 (ψᴺ 2 (E.Ωt η)) x
a2-lim η x e ih = mL (cofψω (natT 2) (E.Ωt η) (Ωω η e))
  (λ n → subst (λ z → M 2 z x) (sym (trans (fsnψω (natT 2) (E.Ωt η) n (Ωω η e)) (cong (ψᴺ 2) (fsnΩω η n e)))) (ih n))

limSL : ∀ η → cof η ≡ cω → ∀ {ℓ o v} → (∀ n → SL (ψᴺ 2 (E.Ωt (fsn η n))) ℓ o v) → SL (ψᴺ 2 (E.Ωt η)) ℓ o v
limSL η e h r B β ok hβ = a2-lim η _ e (λ n → h n r B β ok hβ)

fsnω : ∀ k → fsn (ψᴺ 2 (E.Ωt ωᵀ)) k ≡ ψᴺ 2 (Ωᴺ k)
fsnω k = trans (fsnψω (natT 2) (E.Ωt ωᵀ) k (Ωω ωᵀ refl)) (cong (ψᴺ 2) (trans (fsnΩω ωᵀ k refl) (cong E.Ωt (rep1 k))))

at-nat : ∀ {c} → M⁰ ωᵀ c → ∀ k → M⁰ (natT k) c
at-nat {c} l k = subst (λ t → M⁰ t c) (rep1 k) (inv-lim refl l k)
```

基本列第 3 项起, 第 0 项, 第 2 项: 编译定理.

```agda
ωfamᵗ : ∀ {c} → M⁰ ωᵀ c → ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gᵗ c))
ωfamᵗ l k = finᵗ k (at-nat l (suc (suc (suc k))))

ωfamˢ : ∀ {c} → Can c → M⁰ ωᵀ c → ∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (proj₁ (gˢ c))
ωfamˢ cc l k = finˢ k cc (at-nat l (suc (suc (suc k))))

ω0ᵗ : (c : Tr zero) → M 2 (ψᴺ 2 (Ωᴺ 0)) (proj₁ (gᵗ c))
ω0ᵗ c = atᵗ c (S0ᵗ c)

ω0ˢ : (c : Tr zero) → M 2 (ψᴺ 2 (Ωᴺ 0)) (proj₁ (gˢ c))
ω0ˢ c = atˢ c (S0ˢ c)

ω2ᵗ : (c : Tr zero) → M 2 (ψᴺ 2 (Ωᴺ 2)) (proj₁ (gᵗ c))
ω2ᵗ c = atᵗ c (S2ᵗ c)

ω2ˢ : (c : Tr zero) → Can c → M 2 (ψᴺ 2 (Ωᴺ 2)) (proj₁ (gˢ c))
ω2ˢ c cc = atˢ c (S2ˢ c cc)
```

判据归约到基本列第 1 项 (条件定理; 前提在 c = `nat 1` 处被 `YiRLNeg` 否定, 在这里的 c 处未证也未否定).

```agda
of-fsn : ∀ {x} → M 2 (ψᴺ 2 (Ωᴺ 0)) x → M 2 (ψᴺ 2 (Ωᴺ 1)) x → M 2 (ψᴺ 2 (Ωᴺ 2)) x
       → (∀ k → M 2 (ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) x) → M 2 (ψᴺ 2 (E.Ωt ωᵀ)) x
of-fsn {x} p0 p1 p2 h = mL refl (λ k → subst (λ t → M 2 t x) (sym (fsnω k)) (go k))
  where
  go : ∀ k → M 2 (ψᴺ 2 (Ωᴺ k)) x
  go 0                   = p0
  go 1                   = p1
  go 2                   = p2
  go (suc (suc (suc k))) = h k

ω-of-1ᵗ : ∀ {c} → M⁰ ωᵀ c → M 2 (ψᴺ 2 (Ωᴺ 1)) (proj₁ (gᵗ c)) → M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gᵗ c))
ω-of-1ᵗ {c} l p1 = of-fsn (ω0ᵗ c) p1 (ω2ᵗ c) (ωfamᵗ l)

ω-of-1ˢ : ∀ {c} → Can c → M⁰ ωᵀ c → M 2 (ψᴺ 2 (Ωᴺ 1)) (proj₁ (gˢ c)) → M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ c))
ω-of-1ˢ {c} cc l p1 = of-fsn (ω0ˢ c) p1 (ω2ˢ c cc) (ωfamˢ cc l)
```

按项序封闭后 (`YiDCRel.M̃` 的形状: 有见证项 t, 参照 ≤ᵀ t 且 t 对着树), 基本列逐项成立, 无前提.

```agda
le3 : ∀ k → k ≤ⁿ suc (suc (suc k))
le3 zero    = z≤n
le3 (suc k) = s≤s (le3 k)

fsn≤ : ∀ k → fsn (ψᴺ 2 (E.Ωt ωᵀ)) k ≤ᵀ ψᴺ 2 (Ωᴺ (suc (suc (suc k))))
fsn≤ k = subst (λ t → t ≤ᵀ ψᴺ 2 (Ωᴺ (suc (suc (suc k))))) (sym (fsnω k)) (app≤ 2 [] (Ω≤ (le3 k)))

ω̃ᵗ : ∀ {c} → M⁰ ωᵀ c → ∀ k → Σ E.T λ t → (fsn (ψᴺ 2 (E.Ωt ωᵀ)) k ≤ᵀ t) × M 2 t (proj₁ (gᵗ c))
ω̃ᵗ l k = ψᴺ 2 (Ωᴺ (suc (suc (suc k)))) , fsn≤ k , ωfamᵗ l k

ω̃ˢ : ∀ {c} → Can c → M⁰ ωᵀ c → ∀ k → Σ E.T λ t → (fsn (ψᴺ 2 (E.Ωt ωᵀ)) k ≤ᵀ t) × M 2 t (proj₁ (gˢ c))
ω̃ˢ cc l k = ψᴺ 2 (Ωᴺ (suc (suc (suc k)))) , fsn≤ k , ωfamˢ cc l k
```

有限的 η 处, 封闭后的形式对一切 n 成立, 包括 n = 1 (见证项 ψ₂(Ω₃), 由 `YiRBCrit.shiftU`, `shiftC` 经向上封闭).

```agda
fiñᵗ : ∀ n {c} → M⁰ (natT n) c → Σ E.T λ t → (ψᴺ 2 (Ωᴺ n) ≤ᵀ t) × M 2 t (proj₁ (gᵗ c))
fiñᵗ 0                   {c} l = ψᴺ 2 (Ωᴺ 0) , inj₂ refl , ω0ᵗ c
fiñᵗ 1                   {c} l =
  ψᴺ 2 (Ωᴺ 3) , app≤ 2 [] (Ω≤ {1} {3} (s≤s z≤n)) , atᵗ c (clos⊴ᵗ (nat⊴ 1 l refl) (baseᵗ 1 (shiftU 0)))
fiñᵗ 2                   {c} l = ψᴺ 2 (Ωᴺ 2) , inj₂ refl , ω2ᵗ c
fiñᵗ (suc (suc (suc k))) {c} l = ψᴺ 2 (Ωᴺ (suc (suc (suc k)))) , inj₂ refl , finᵗ k l

fiñˢ : ∀ n {c} → Can c → M⁰ (natT n) c → Σ E.T λ t → (ψᴺ 2 (Ωᴺ n) ≤ᵀ t) × M 2 t (proj₁ (gˢ c))
fiñˢ 0                   {c} cc l = ψᴺ 2 (Ωᴺ 0) , inj₂ refl , ω0ˢ c
fiñˢ 1                   {c} cc l =
  ψᴺ 2 (Ωᴺ 3) , app≤ 2 [] (Ω≤ {1} {3} (s≤s z≤n)) , atˢ c (clos⊴ˢ (nat⊴ 1 l refl) cc (baseˢ 1 (shiftC 0)))
fiñˢ 2                   {c} cc l = ψᴺ 2 (Ωᴺ 2) , inj₂ refl , ω2ˢ c cc
fiñˢ (suc (suc (suc k))) {c} cc l = ψᴺ 2 (Ωᴺ (suc (suc (suc k)))) , inj₂ refl , finˢ k cc l
```
