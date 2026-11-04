# 紧的树: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [GuardTight](GuardTight.lagda.md). 比较器与 [LvGuardAccept](LvGuardAccept.lagda.md) 同形. **有限测试, 不是证明; 种类检验不看界.** 界的测试 (§5) 看界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; ωᴵ; suc; zero; lim; _⊑ᴵ_; _<ᴵ_; s⊑; z≅)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (F; Lv₅)
import OCF.Align.EBO as E
open E using (T; fsn; fsT; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Uniform5Wall using (ψ₁)
```

## §1 比较器

`dfL d w t x`: 深度 $d$, 宽度 $w$. 闭包的第 0 个孩子是第一支 $t'$, 对 `fsT t 1`; 第 $k\ge1$ 个孩子是分支 $k+1$.

```agda
data Why : Set where
  kindBad : Why
  headBad : Why

zero<nat : ∀ k → zero <ᴵ natᴵ (suc k)
zero<nat zero    = zero
zero<nat (suc k) = suc (zero<nat k)

one⊑nat : ∀ k → suc zero ⊑ᴵ natᴵ (suc k)
one⊑nat k = s⊑ z≅ (zero<nat k)

dfL : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
dfs : ℕ → ℕ → ℕ → T → (ℕ → LG) → Maybe (Why × List ℕ)
dfb : ℕ → ℕ → ℕ → T → ((k : ℕ) → LG) → Maybe (Why × List ℕ)
dfL zero w t x = nothing
dfL (suc d) w t zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
dfL (suc d) w t (suc x) with cof t
... | c1 = dfL d w (pred t) x
... | _  = just (kindBad , [])
dfL (suc d) w t (lim f) with cof t
... | cω = dfs w d w t f
... | _  = just (kindBad , [])
dfL (suc d) w t (lc c t′ g) with cof t
... | cΩ [] with dfL d w (fsT t (natT 1)) t′
...   | just r = just r
...   | nothing = nothing
dfL (suc d) w t (lc c t′ g) | _ = just (headBad , [])

dfs zero d w t f = nothing
dfs (suc n) d w t f with dfL d w (fsn t n) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfs n d w t f

dfb zero d w t f = nothing
dfb (suc n) d w t f with dfL d w (fsT t (natT (suc n))) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfb n d w t f

-- 分支: 字面自然数 k+1
branches : LG → ℕ → LG
branches (lc (suc zero) t′ g) k = g (natᴵ (suc k)) (one⊑nat k)
branches x k = x

dfB : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
dfB d w t x = dfb w d w t (branches x)

is-ok : Maybe (Why × List ℕ) → Bool
is-ok nothing  = true
is-ok (just _) = false
```

```agda
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightTree using (T₀; O; module Fold; module Emb; Ω̇; rdZ; oŝ; owk; ocv; omk; ol; os; o0; oĉ; oΩ; ocl; trL⁻; _⊕_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightRd
open import OCF.Align.GuardTightCum using (Ω; _+_; add; Ordᶜ; add-≅; Ω-refl; z≅)
open U using (rb₁; rb-≈₁₁; Good-Ω; Good-add; Good→WF₁; good-F; ψ¹-≅; Cf-F; self-F)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform5Wall using (Ω·2)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import Data.List using (_++_)

dfZ  : ℕ → ℕ → T → Z → Maybe (Why × List ℕ)
dfZs : ℕ → ℕ → ℕ → T → (ℕ → Z) → Maybe (Why × List ℕ)
dfZ zero w t x = nothing
dfZ (suc d) w t Z.zero with cof t
... | c0 = nothing
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.suc x) with cof t
... | c1 = dfZ d w (pred t) x
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.lim f) with cof t
... | cω = dfZs w d w t f
... | _  = just (kindBad , [])
dfZ (suc d) w t (Z.ĉᴸ c z zg o₀ o) with cof t
... | cω = dfZ d w (fsn t 0) o₀
... | _  = just (kindBad , [])

dfZs zero d w t f = nothing
dfZs (suc n) d w t f with dfZ d w (fsn t n) (f n)
... | just (g , p) = just (g , n ∷ p)
... | nothing = dfZs n d w t f

tF : ℕ → T
tF n = ψ₁ (Ωt (natT n))

tLv₅ : T
tLv₅ = ψ₁ (Ωt (Ωt (natT 1)))

Ω₁ᶜ : Ordᶜ (suc zero)
Ω₁ᶜ = Ω (suc zero)

xΩ₁ x2 x3 : LG
xΩ₁ = rb₁ Ω₁ᶜ
x2  = rb₁ (Ω₁ᶜ + Ω₁ᶜ)
x3  = rb₁ ((Ω₁ᶜ + Ω₁ᶜ) + Ω₁ᶜ)

e1 : Ω₁ᶜ OCF.Align.GuardTightCum.≅ Ω₁ᶜ
e1 = Ω-refl (suc zero)

Cf-xΩ₁ : Cfˢ xΩ₁
Cf-xΩ₁ = Good→WF₁ (Good-Ω (suc zero)) , rb-≈₁₁ e1

e2 : (Ω₁ᶜ + Ω₁ᶜ) OCF.Align.GuardTightCum.≅ (Ω₁ᶜ + Ω₁ᶜ)
e2 = add-≅ {σ = λ q → q} {σ′ = λ q → q} e1 e1

g2 : U.Good (Ω₁ᶜ + Ω₁ᶜ)
g2 = Good-add {σ = λ q → q} (Good-Ω (suc zero)) e1 (Good-Ω (suc zero))

Cf-x2 : Cfˢ x2
Cf-x2 = Good→WF₁ g2 , rb-≈₁₁ e2

Cf-x3 : Cfˢ x3
Cf-x3 = Good→WF₁ (Good-add {σ = λ q → q} g2 e2 (Good-Ω (suc zero))) , rb-≈₁₁ (add-≅ {σ = λ q → q} {σ′ = λ q → q} e2 e1)

-- 读位置的证据: 紧的
Tc-x1 : Tc xΩ₁
Tc-x1 = RdIter.Tc-c

Tc-x2 : Tc x2
Tc-x2 = RdAdd.Tc-top Ω₁ᶜ (λ q → suc q) Tc-x1

Tc-x3 : Tc x3
Tc-x3 = RdAdd.Tc-top (Ω₁ᶜ + Ω₁ᶜ) (λ q → suc q) Tc-x2

-- ψ₁(1) 与它之上
ψ₁₁ᶜ : Ordᶜ (suc zero)
ψ₁₁ᶜ = U.ψ¹ (Ω zero)

xf0 xf0s xf0Ω : LG
xf0 = F (natᴵ 0)
xf0s = suc xf0
xf0Ω = rb₁ (ψ₁₁ᶜ + Ω₁ᶜ)

Tc-f0 : Tc xf0
Tc-f0 = λ n → RdIter.Tc-iter n

Cf-f0 : Cfˢ xf0
Cf-f0 = Cf-F (natᴵ 0)

eψ : ψ₁₁ᶜ OCF.Align.GuardTightCum.≅ ψ₁₁ᶜ
eψ = ψ¹-≅ (Ω-refl zero)

Cf-f0Ω : Cfˢ xf0Ω
Cf-f0Ω = Good→WF₁ (Good-add {σ = λ q → q} (good-F zero) eψ (Good-Ω (suc zero))) , rb-≈₁₁ (add-≅ {σ = λ q → q} {σ′ = λ q → q} eψ e1)

Tc-f0Ω : Tc xf0Ω
Tc-f0Ω = RdAdd.Tc-top ψ₁₁ᶜ (λ q → suc q) Tc-f0

-- 目标
tΩ1 tΩ11 tΩ2 tΩ21 tΩ3 tψ1 tψ1s tψ1Ω tψΩ tψ5 : T
tΩ1 = ψ₀ᵗ (Ωt (natT 0 ++ Ωᵗ))
tΩ11 = ψ₀ᵗ (Ωt (sucT Ωᵗ))
tΩ2 = ψ₀ᵗ (Ωt Ω·2)
tΩ21 = ψ₀ᵗ (Ωt (sucT Ω·2))
tΩ3 = ψ₀ᵗ (Ωt (Ω·2 ++ Ωᵗ))
tψ1 = ψ₀ᵗ (Ωt (tF 0))
tψ1s = ψ₀ᵗ (Ωt (sucT (tF 0)))
tψ1Ω = ψ₀ᵗ (Ωt (tF 0 ++ Ωᵗ))
tψΩ = ψ₀ᵗ (Ωt (tF 1))
tψ5 = ψ₀ᵗ (Ωt tLv₅)

t1 t11 t2 t21 t3 tf0 tf0s tf0Ω tf1 tf5 : Z
t1 = T₀ xΩ₁ Cf-xΩ₁ Tc-x1
t11 = T₀ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) Tc-x1
t2 = T₀ x2 Cf-x2 Tc-x2
t21 = T₀ (suc x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2)) Tc-x2
t3 = T₀ x3 Cf-x3 Tc-x3
tf0 = T₀ xf0 Cf-f0 Tc-f0
tf0s = T₀ xf0s (proj₁ Cf-f0 , s≈ (proj₂ Cf-f0)) Tc-f0
tf0Ω = T₀ xf0Ω Cf-f0Ω Tc-f0Ω
tf1 = T₀ (F (natᴵ 1)) (U.Cf-F (natᴵ 1)) (Tc-id (F (natᴵ 1)))
tf5 = T₀ Lv₅ U.Cf-Lv₅ (Tc-id Lv₅)

c-t1 : dfZ 10 2 tΩ1 t1 ≡ nothing
c-t1 = refl
c-t11 : dfZ 12 2 tΩ11 t11 ≡ nothing
c-t11 = refl
c-t2 : dfZ 12 2 tΩ2 t2 ≡ nothing
c-t2 = refl
c-t21 : dfZ 12 2 tΩ21 t21 ≡ nothing
c-t21 = refl
c-t3 : dfZ 12 2 tΩ3 t3 ≡ nothing
c-t3 = refl
-- 对照
ctl₄ : is-ok (dfZ 12 2 tΩ2 t21) ≡ false
ctl₄ = refl
-- 过 Ω·3: ψ₁(1), ψ₁(1)+1, ψ₁(1)+Ω (过 noTimes)
c-tf0 : dfZ 10 2 tψ1 tf0 ≡ nothing
c-tf0 = refl
c-tf0s : dfZ 10 2 tψ1s tf0s ≡ nothing
c-tf0s = refl
c-tf0Ω : dfZ 10 2 tψ1Ω tf0Ω ≡ nothing
c-tf0Ω = refl
-- ψ₀(Ω_{ψ₁(Ω)}), 第 5 站: 恒等读法
c-tf1 : dfZ 10 2 tψΩ tf1 ≡ nothing
c-tf1 = refl
c-tf5 : dfZ 10 2 tψ5 tf5 ≡ nothing
c-tf5 = refl
ctl₅ : is-ok (dfZ 12 2 tψ1 tf1) ≡ false
ctl₅ = refl
ctl₆ : is-ok (dfZ 10 2 tψΩ tf5) ≡ false
ctl₆ = refl
ctl₇ : is-ok (dfZ 10 2 tψ1 tf0Ω) ≡ false
ctl₇ = refl
```

## §5 界: 对照 [LvGuardAccept](LvGuardAccept.lagda.md) 的 `c-bra*`

**有限测试, 看界.** `Tgt`: 顶层 $D+1$ ($D=\\Omega\\cdot2$), 目标 $\\Omega$, 闭包 $W=\\dot\\Omega_D$. 目标的路径穿过分支 $\\tau$ 时: `Y` 用恒等读法 (旧树的界), `Y′` 用紧的读法. **期待: `Y` 的界是 $\\tau+1$, `Y′` 的界不随 $\\tau$ 变.**

```agda
iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = suc (iterᴵ c k)

iterS : LG → ℕ → LG
iterS x zero = x
iterS x (suc n) = suc (iterS x n)

pthS : ∀ n x → x < iterS x (suc n)
pthS zero x = zero
pthS (suc n) x = suc (pthS n x)

adm-pthS : ∀ n x E → Adm E (pthS n x)
adm-pthS zero x E = tt
adm-pthS (suc n) x E = adm-pthS n x E

toN : Ordᴵ → ℕ
toN zero = 0
toN (suc a) = suc (toN a)
toN (lim f s) = toN (f 1)

cO : ∀ {t ρ} → O t ρ → ℕ
cO (oŝ c _ _) = toN c
cO (owk _ x) = cO x
cO (ocv _ x) = cO x
cO (omk _ _ _ _ x) = cO x
cO (ol f) = 100
cO (os f) = 101
cO o0 = 102
cO (oĉ c _ _ _ _) = 103
cO (oΩ _ _ _) = 104
cO (ocl _ _ _ _ _) = 105

module Tgt {c₁ t₁ g₁} (cf : Cfˢ (lc c₁ t₁ g₁)) (tc : Tc (lc c₁ t₁ g₁)) (τ : Ordᴵ) (eτ : c₁ ⊑ᴵ τ) (b : LG) (r : b < g₁ τ eτ) (ar : ∀ E → Adm E r) (B : Ordᴵ) (τ<B : pr τ <ᴵ B) where
  c₀ : LG
  c₀ = suc (lc c₁ t₁ g₁)
  E : Ents
  E = ∅ B
  q : b < c₀
  q = suc (bra τ eτ r)
  aq : Adm (tab E) q
  aq = (B , refl , τ<B) , ar (tab E)
  -- 读位置 tc₀, 目标规范化之后
  module At (tc₀ : Tc c₀) where
    open Fold c₀ (proj₁ cf) (s≈ (proj₂ cf)) tc₀
    nq = nfT c₀ tc₀ q
    Y : O (repT nq) tz
    Y = ψ E (tp (pathT nq) (tabT nq E aq)) (λ ()) (ι′ (Ω̇ (lc c₁ t₁ g₁) tc))
      where
      ι′ : O (lc c₁ t₁ g₁) tz → O c₀ tz
      ι′ z = owk (λ { (ml ()) ; (mr ()) }) (Emb.ι c₀ tc₀ (lc c₁ t₁ g₁) (suc self) (inj₂ refl) z)
  Yid Ytight : ℕ
  Yid = cO (At.Y (Tc-id c₀))
  Ytight = cO (At.Y tc)

τₙ : ℕ → Ordᴵ
τₙ n = natᴵ (suc n)

-- 旧的界: τ+1
c-bra2 : Tgt.Yid {_} {_} {_} Cf-x2 Tc-x2 (τₙ 1) (one⊑nat 1) xΩ₁ (pthS 1 xΩ₁) (adm-pthS 1 xΩ₁) (suc (τₙ 1)) (suc zero) ≡ 2
c-bra2 = refl
c-bra3 : Tgt.Yid {_} {_} {_} Cf-x2 Tc-x2 (τₙ 2) (one⊑nat 2) xΩ₁ (pthS 2 xΩ₁) (adm-pthS 2 xΩ₁) (suc (τₙ 2)) (suc zero) ≡ 3
c-bra3 = refl
c-bra5 : Tgt.Yid {_} {_} {_} Cf-x2 Tc-x2 (τₙ 4) (one⊑nat 4) xΩ₁ (pthS 4 xΩ₁) (adm-pthS 4 xΩ₁) (suc (τₙ 4)) (suc zero) ≡ 5
c-bra5 = refl
-- 紧的界
t-bra2 : Tgt.Ytight {_} {_} {_} Cf-x2 Tc-x2 (τₙ 1) (one⊑nat 1) xΩ₁ (pthS 1 xΩ₁) (adm-pthS 1 xΩ₁) (suc (τₙ 1)) (suc zero) ≡ 1
t-bra2 = refl
t-bra3 : Tgt.Ytight {_} {_} {_} Cf-x2 Tc-x2 (τₙ 2) (one⊑nat 2) xΩ₁ (pthS 2 xΩ₁) (adm-pthS 2 xΩ₁) (suc (τₙ 2)) (suc zero) ≡ 1
t-bra3 = refl
t-bra5 : Tgt.Ytight {_} {_} {_} Cf-x2 Tc-x2 (τₙ 4) (one⊑nat 4) xΩ₁ (pthS 4 xΩ₁) (adm-pthS 4 xΩ₁) (suc (τₙ 4)) (suc zero) ≡ 1
t-bra5 = refl
-- 过 noTimes: ψ₁(1)+Ω 的闭包, 目标 ψ₁(1), 穿过分支 3, 5
t-brω2 : Tgt.Ytight {_} {_} {_} Cf-f0Ω Tc-f0Ω (τₙ 2) (one⊑nat 2) xf0 (pthS 2 xf0) (adm-pthS 2 xf0) (suc (τₙ 2)) (suc zero) ≡ 1
t-brω2 = refl
t-brω4 : Tgt.Ytight {_} {_} {_} Cf-f0Ω Tc-f0Ω (τₙ 4) (one⊑nat 4) xf0 (pthS 4 xf0) (adm-pthS 4 xf0) (suc (τₙ 4)) (suc zero) ≡ 1
t-brω4 = refl
c-brω4 : Tgt.Yid {_} {_} {_} Cf-f0Ω Tc-f0Ω (τₙ 4) (one⊑nat 4) xf0 (pthS 4 xf0) (adm-pthS 4 xf0) (suc (τₙ 4)) (suc zero) ≡ 5
c-brω4 = refl
```

## §6 $W$

`Xw`: $W$ 的树, 直接由折叠写出, 与 [UniformLvAccept](UniformLvAccept.lagda.md) 同一个位置. 目标 $\\Omega+1$ 的路径是分支 2 的第一个前驱. **有限测试.** 看种类, 再看 $W$ 里右边那份闭包的界 (`c-W-bound`): 它读到左边的 $\\Omega_{\\Omega\\cdot2}$, 与分支 2 的帧.

```agda
open import OCF.Align.Uniform5Wall using (W)

module WT where
  L₂ c₁ : LG
  L₂ = x2
  c₁ = suc x2

  w₂ : WFˢ L₂
  w₂ = proj₁ Cf-x2
  s₂ : L₂ ≈ L₂
  s₂ = proj₂ Cf-x2

  two : Ordᴵ
  two = natᴵ 2
  e₂ : suc zero ⊑ᴵ two
  e₂ = one⊑nat 1

  module F₂ = Fold L₂ w₂ s₂ Tc-x2
  module F₁ = Fold c₁ w₂ (s≈ s₂) Tc-x2

  G₁ : LG
  G₁ = suc xΩ₁

  tgt₁ : G₁ < L₂
  tgt₁ = bra two e₂ zero

  E₃ : Ents
  E₃ = ∅ (natᴵ 3)

  in₁ : O G₁ tz
  in₁ = F₂.ψ E₃ (F₂.tp tgt₁ ((natᴵ 3 , refl , suc zero) , tt)) (λ ()) (Ω̇ L₂ Tc-x2)

  f₂ : Frm
  f₂ = frm (suc zero) (suc xΩ₁) (λ η e → RdAdd.Gₐ Ω₁ᶜ (λ q → suc q) Tc-x1 η) two e₂

  left : O c₁ (tz ∪ tz)
  left = Emb.ι c₁ Tc-x2 L₂ (suc self) (inj₂ refl) (Ω̇ L₂ Tc-x2)

  right : O c₁ (tz ∪ (tk f₂ ∪ tz))
  right = Emb.ι c₁ Tc-x2 G₁ (suc (bra two e₂ (suc self))) (inj₂ refl) in₁

  W̃ : O L₂ (tk f₂)
  W̃ = F₁.ψ E₃ (F₁.tp zero tt)
        (λ { (ml (ml ())) ; (ml (mr ())) ; (mr (ml ())) ; (mr (mr (ml hr))) → F₁.fs nothing (just (F₁.ab hr (inj₂ refl))) ; (mr (mr (mr ()))) })
        (left ⊕ right)

  Xw : Z
  Xw = rdZ (F₂.ψ {ρ = tz} E₃ F₂.t0 (λ { hr → F₂.fs (just (F₂.evd self tt s₂ (natᴵ 3 , refl , suc zero))) nothing }) W̃)

c-W : dfZ 24 1 W WT.Xw ≡ nothing
c-W = refl
c-W₂ : dfZ 12 2 W WT.Xw ≡ nothing
c-W₂ = refl
```

## §7 对照阶梯的树: 看界

**有限测试, 看界.** `agree d w x y`: $x$ 是这棵树, $y$ 是 [ScafLadderQ](ScafLadderQ.lagda.md) 的塔, 两边都是第 0 层的树. 逐层比种类, **闭包比界** (`toN`), 分支走 $\\eta=c_0+k$, $k<w$. 两边的界一致, 就是塔的 `Ψ`, `flo` 与这里的 `nfT`, `omk` 算的是同一个数. 这个比较看得见 `c-bra*`, 比种类强. **有限测试, 不是证明.**

```agda
import OCF.Align.LadderNFTree as Q
import OCF.Free.Prefix as ZP
open import OCF.Free.Prefix using () renaming (Z to Zq)
open import OCF.Align.GuardTightCum using (⊑ᴵ-refl; ⊑ᴵ-trans; Sim→⊑ᴵ)

_==_ : ℕ → ℕ → Bool
zero == zero = true
suc a == suc b = a == b
_ == _ = false

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → suc q))

agree : ℕ → ℕ → Z → Zq → Bool
agreeB : ℕ → ℕ → ℕ → ∀ {c : Ordᴵ} {c′ : Ordᴵ} → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Zq) → Bool
agreeL : ℕ → ℕ → ℕ → (ℕ → Z) → (ℕ → Zq) → Bool
agree zero w _ _ = true
agree (suc d) w Z.zero Zq.zero = true
agree (suc d) w (Z.suc x) (Zq.suc y) = agree d w x y
agree (suc d) w (Z.lim f) (Zq.lim g) = agreeL w d w f g
agree (suc d) w (Z.ĉᴸ c z zg o₀ o) (Zq.ĉᴸ c′ z′ zg′ o₀′ o′) =
  (toN c == toN c′) && (agree d w o₀ o₀′ && agreeB w d w o o′)
agree (suc d) w _ _ = false

agreeL zero d w f g = true
agreeL (suc n) d w f g = agree d w (f n) (g n) && agreeL n d w f g

agreeB zero d w o o′ = true
agreeB (suc k) d w {c} {c′} o o′ = agree d w (o (iterᴵ c k) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k)) && agreeB k d w o o′

w₀ : ℕ → Ordᴵ
w₀ _ = suc zero

tq : (m : ℕ) (α : Ordᴵ) → Zq
tq m α = ZP.toZ (Q.Tᵠ m α {zero} {suc zero} (tt , (λ q → q)) zero)

qa-1 : agree 9 2 t1 (tq 0 zero) ≡ true
qa-1 = refl
qa-11 : agree 9 2 t11 (tq 0 (suc zero)) ≡ true
qa-11 = refl
qa-2 : agree 12 2 t2 (tq 1 zero) ≡ true
qa-2 = refl
qa-21 : agree 10 2 t21 (tq 1 (suc zero)) ≡ true
qa-21 = refl
qa-3 : agree 9 2 t3 (tq 2 zero) ≡ true
qa-3 = refl
tqω : Zq
tqω = ZP.toZ (Q.Tω {zero} {suc zero} (tt , (λ q → q)) zero)
qa-ω : agree 9 2 tf0 tqω ≡ true
qa-ω = refl
-- 对照
qa-ctl : agree 8 2 t21 (tq 1 zero) ≡ false
qa-ctl = refl
qa-ctl₂ : agree 8 2 t2 (tq 2 zero) ≡ false
qa-ctl₂ = refl
```

## §8 更高的定义域: 读回与条件的对角线

**有限测试.** `c-uF²`: `F⁺` 读回对 $\\psi_1(\\Omega_{\\psi_1(\\Omega)})$. `c-Ω₂-n`: $\\psi_0(\\Omega_{\\Omega_2})$ 的前 $n$ 项. **证书是变量 (模块参数), 没有被问到的深度才算数**: 这里的 `refl` 只说种类, 只说到这个深度, 不说明 `GoodFeed` 可证.

```agda
open import OCF.Align.GuardTightUp using (F⁺; GL; gl; lvl; cfG; tcG; entG; pthG; admG; feedL; u₀; GoodFeed; module Diag)

tF²1 : T
tF²1 = ψ₁ (Ωt (tF 1))

ctlU : is-ok (dfL 6 2 tF²1 (F (natᴵ 2))) ≡ false
ctlU = refl

q₁ : suc zero < F (natᴵ 1)
q₁ = fst (lim 1 (bra (natᴵ 2) (one⊑nat 1) zero))

aq₁ : Adm (tab (∅ (natᴵ 2))) q₁
aq₁ = (natᴵ 2 , refl , zero) , tt

F²1 : LG
F²1 = F⁺ (F (natᴵ 1)) (U.Cf-F (natᴵ 1)) (Tc-id _) (∅ (natᴵ 2)) q₁ aq₁

c-uF² : dfL 6 2 tF²1 F²1 ≡ nothing
c-uF² = refl

tΩ₂Ω : T
tΩ₂Ω = ψ₀ᵗ (Ωt (Ωt (natT 2)))

module DiagT (cfv : ∀ u → Cfˢ (feedL u)) (ent : GL → Ents) (pthv : ∀ u → suc zero < feedL u) (admv : ∀ u → Adm (tab (ent u)) (pthv u)) where
  G : GoodFeed
  G = record { cfF = cfv ; tcF = λ u → Tc-id (feedL u) ; entF = ent ; pthF = pthv ; admF = admv }
  open Diag G using (TΩ₂)
  c-Ω₂ : dfZ 6 2 tΩ₂Ω TΩ₂ ≡ nothing
  c-Ω₂ = refl

ctlΩ₂ : is-ok (dfZ 6 2 tΩ₂Ω t2) ≡ false
ctlΩ₂ = refl

-- u₂ = ψ₁(Ω_{ψ₁(Ω_Ω)}): 第 3 项. 输入 u₁ = Lv₅ 的证书是真的, 输出的证书是变量.
u₂ : LG
u₂ = F⁺ Lv₅ U.Cf-Lv₅ (Tc-id Lv₅) (∅ (natᴵ 2)) (fst q₁) aq₁

c-u₂ : dfL 6 2 (ψ₁ (Ωt tLv₅)) u₂ ≡ nothing
c-u₂ = refl

ctl-u₂ : is-ok (dfL 6 2 (ψ₁ (Ωt tLv₅)) F²1) ≡ false
ctl-u₂ = refl

module U₂ (cfv : Cfˢ u₂) where
  c-a2 : dfZ 6 2 (fsn tΩ₂Ω 2) (T₀ u₂ cfv (Tc-id u₂)) ≡ nothing
  c-a2 = refl
```
