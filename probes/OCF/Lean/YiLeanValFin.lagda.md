# YiLeanVal 实例：一切有限层、ω、链点自己的层号；BTBO 的两条约化

**验收文件，档位：编译定理 (下界) 与条件定理。** 由 `lower-any`：ψ₀(Ω_n) ≼ 读回的 `F (fin n)` 对一切 n，ψ₀(Ω_ω) 同样；`T₃` 的第 n 项不低于它自己层号上的 ψ₀(Ω_{κₙ}) (`T₃-own`)，`T₃` 不低于 ψ₀(Ω_ω) (`T₃-Ωω`)。
条件定理：`btbo-vm : VMᴸ → D.BTBOᴵ ≼ read T₃`；`btbo-p : ChainP → D.BTBOᴵ ≼ read T₃`，`ChainP` 是参照第 n 项与某个链点的读回落在 `YiVmConExact` 的定义域 `≼ᵖ` 里 (n = 0 是定理)。
都是下界，不是同值；`T₃` 的 ψ₀(Ω_Ω) 仍是读法。主引理在 [YiLeanValFold](YiLeanValFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanValFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; read-plus; plus≽; fin)
open import OCF.Lean.YiLeanValRel using (Corr; cz; cs; cl)
open import OCF.Lean.YiLeanValFold using (lower-any)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiMonoVM using (VMᴸ)
open import OCF.Align.YiVmConExact using (_≼ᵖ_; VMᵖ; ˣ→ᵖ; reflˣ)
open L using (_<ᴵ_; _⊑ᴵ_)
```

## 1 有限层与 ω

```agda
fin-lgl : ∀ n → Lgl zero (fin n)
fin-lgl zero = tt
fin-lgl (suc n) = fin-lgl n

corr-fin : ∀ n → Corr (L.natᴵ n) ⌜ fin n ⌝
corr-fin zero = cz
corr-fin (suc n) = cs (corr-fin n)

lower-fin : ∀ n → L.ψ⁰ (L.Ω (L.natᴵ n)) ≼ read (F (fin n) (fin-lgl n))
lower-fin n = lower-any (fin n) (fin-lgl n) (corr-fin n)

ωR : R
ωR = G.lim fin

ωR-lgl : Lgl zero ωR
ωR-lgl = (λ n → inj₂ (inj₁ refl)) , fin-lgl

lower-ω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read (F ωR ωR-lgl)
lower-ω = lower-any ωR ωR-lgl (cl corr-fin)
```

## 2 合法的第 0 层树读成的层号

`HS-read`, `corr-read`：合法的 `η` 读回有证书，它的 `toLevel` 与折叠用的层号 `⌜ η ⌝` 结构对应。于是 `lower-any` 的前提对一切合法的 `η` 可满足。

```agda
cp⊑ : ∀ a b → Cp zero a b → read a L.⊑ read b
dn⊑ : ∀ a b → Dn zero a b → read a L.⊑ read b
cp⊑ a b (inj₁ refl) h = h
cp⊑ a b (inj₂ p) h = dn⊑ a b p h
dn⊑ a (G.suc b) p h = L.≺s (cp⊑ a b p h)
dn⊑ a (G.lim f) (n , p) h = L.≺l n (cp⊑ a (f n) p h)
dn⊑ a (G.lc () g) p h
dn⊑ a (G.em () d) p h

HS-read : ∀ a → Lgl zero a → L.HS (read a)
HS-read G.zero l = L.hz
HS-read (G.suc a) l = L.hs (HS-read a l)
HS-read (G.lim f) (st , lf) = L.hl (λ n → HS-read (f n) (lf n)) (λ n → cp⊑ (f n) (f (suc n)) (st n))
HS-read (G.lc () g) l
HS-read (G.em () a) l
HS-read G.top l = L.hs L.hz

corr-read : ∀ a (h : L.HS (read a)) → Corr (L.toLevel (read a) h) ⌜ a ⌝
corr-read G.zero h = cz
corr-read (G.suc a) h = cs (corr-read a (L.hs⁻ h))
corr-read (G.lim f) h = cl (λ n → corr-read (f n) (L.hl₁ h n))
corr-read (G.lc () g) h
corr-read (G.em () a) h
corr-read G.top h = cs cz

lower-read : ∀ a (l : Lgl zero a) → L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l))) ≼ read (F a l)
lower-read a l = lower-any a l (corr-read a (HS-read a l))
```

## 3 `T₃`

链是累加的：下一点是这一点加上这一点上的折叠值 (`YiLeanTw3.T₃-feedback`，`refl`)，从 `top` 起，`top` 读成 1。

```agda
top-one : read G.top ≡ L.suc L.zero
top-one = refl

chain-cum : ∀ n → read (co (pts (suc n))) L.≅ (read (co (pts n)) L.+ read (obs (pts n)))
chain-cum n = read-plus (co (pts n)) (obs (pts n))

κ : ℕ → L.Ordᴵ
κ n = L.toLevel (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n)))

T₃-own : ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃
T₃-own n = ≼l n (lower-read (co (pts n)) (lw (pts n)))
```

第 1 个链点是 `top + F top`；`F top` 的第 0 项是 ω 倍 `lim (1, 1+1, …)`，所以 `κ 1` 的第 0 项的第 m 项是层号 m+2 (`SN`)，ω ⊑ᴵ κ₁。

```agda
c : ℕ → R
c = acc (λ _ z → plus zero G.top z) G.top

data SN : R → ℕ → Set where
  sn1 : SN G.top 1
  sns : ∀ {a k} → SN a k → SN (G.suc a) (suc k)

SN-lv : ∀ {a k} → SN a k → ∀ h → L.toLevel (read a) h ≡ L.natᴵ k
SN-lv sn1 h = refl
SN-lv (sns d) h = cong L.suc (SN-lv d (L.hs⁻ h))

SN-plus : ∀ {a k} → SN a k → SN (plus zero G.top a) (suc k)
SN-plus sn1 = sns sn1
SN-plus (sns d) = sns (SN-plus d)

SN-c : ∀ m → SN (c m) (suc m)
SN-c zero = sn1
SN-c (suc m) = SN-plus (SN-c m)

lt-c : ∀ m h → L.natᴵ m <ᴵ L.toLevel (read (plus zero G.top (c m))) h
lt-c m h = subst (L.natᴵ m <ᴵ_) (sym (SN-lv (SN-plus (SN-c m)) h)) (L.suc L.zero)

ω⊑κ₁ : L.ωᴵ ⊑ᴵ κ 1
ω⊑κ₁ = L.l⊑ (λ m → L.Sim→⊑ᴵ (λ q → L.<ᴵ-trans q (L.lim 0 (L.lim m (lt-c m _)))))

T₃-Ωω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read T₃
T₃-Ωω = ≼-trans (⊑→≼ _ (L.Ψ⁰-mono ω⊑κ₁)) (T₃-own 1)
```

## 4 BTBO：两条约化

参照取 `Diagonal Uniform` 的对角线 (同 `YiBtValBT.D`)：`D.γ 0 = 1`，`D.γ (n+1) = ψ⁰(Ω_{toLevel (D.γ n)})`，`D.BTBOᴵ = lim (D.γ ∘ suc)`。
`btbo-vm`：沿链归纳，每步用 `VMᴸ` 换层号，再用 `lower-read`。`btbo-p`：不要单调性的一般形式，只要参照项与某个链点落在 `≼ᵖ` 里，经 `VMᵖ` (无条件)。

```agda
module FromVM (vm : VMᴸ) where
  chainV : ∀ n → D.γ n ≼ read (co (pts n))
  mono : ∀ n → L.ψ⁰ (L.Ω (D.L n)) ≼ read (obs (pts n))
  chainV zero = ≼-refl _
  chainV (suc n) = plus≽ (co (pts n)) (obs (pts n)) (mono n)
  mono n = ≼-trans (vm (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) (chainV n))
    (lower-read (co (pts n)) (lw (pts n)))

btbo-vm : VMᴸ → D.BTBOᴵ ≼ read T₃
btbo-vm vm = l≼ (λ n → ≼l n (FromVM.mono vm n))

ChainP : Set
ChainP = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ read (co (pts m))

btbo-p : ChainP → D.BTBOᴵ ≼ read T₃
btbo-p ch = l≼ (λ n → ≼l (proj₁ (ch n))
  (≼-trans (VMᵖ (D.γ n) (D.cert n) (read (co (pts (proj₁ (ch n))))) (HS-read _ (lw (pts (proj₁ (ch n))))) (proj₂ (ch n)))
    (lower-read (co (pts (proj₁ (ch n)))) (lw (pts (proj₁ (ch n)))))))

chainP₀ : D.γ 0 ≼ᵖ read (co (pts 0))
chainP₀ = ˣ→ᵖ (reflˣ (D.γ 0))
```
