# 统一读法: 验收

> **验收节.** 记号与塔只在本文件. 结论写在 [GuardRead](GuardRead.lagda.md). **全部是有限测试, `refl`, 不是证明, 不是证书.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; suc; zero; lim; _⊑ᴵ_; _<ᴵ_; s⊑; z≅; Ω; _+_; Ordᶜ; Ω-refl; add-≅; ωᴵ)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module Un = Uni Dom₀
open Un using (F; Lv₅; rb₁; ψ¹; Cf-F; Cf-Lv₅; good-F; Good-Ω; Good-add; ψ¹-≅)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.GuardTightAccept
open import OCF.Align.GuardReadRs
open import OCF.Align.GuardReadRd
```

## §1 字面的闭包: 统一读法与塔

`Tc-of` 给 $\Omega$, $\Omega\cdot2$, $\Omega\cdot3$, $\psi_1(1)$ 的读法, 换掉 `RdΩ₁`, `RdAdd`, `RdIter`. **对照塔** ([LadderNFTree](LadderNFTree.lagda.md)) 逐闭包比界.

```agda
gΩ₁ : Un.Good Ω₁ᶜ
gΩ₁ = Good-Ω (suc zero)

rΩ₁ : Rs Ω₁ᶜ
rΩ₁ = Rs-Ω (suc zero)

U-x1 : Tc xΩ₁
U-x1 = Tc-of rΩ₁ gΩ₁

r2 : Rs (Ω₁ᶜ + Ω₁ᶜ)
r2 = Rs-add rΩ₁ e1 rΩ₁ e1

U-x2 : Tc x2
U-x2 = Tc-of r2 g2

U-x3 : Tc x3
U-x3 = Tc-of (Rs-add r2 e2 rΩ₁ e1) (Good-add {σ = λ q → q} g2 e2 gΩ₁)

U-f0 : Tc xf0
U-f0 = Tc-F zero

rψ₁₁ : Rs ψ₁₁ᶜ
rψ₁₁ = Rs-ψ¹ (Rs-Ω zero) (Ω-refl zero)

U-f0Ω : Tc xf0Ω
U-f0Ω = Tc-of (Rs-add rψ₁₁ eψ rΩ₁ e1) (Good-add {σ = λ q → q} (good-F zero) eψ gΩ₁)

u1 u11 u2 u21 u3 uf0 uf0s uf0Ω uf1 uf5 : _
u1 = T₀ xΩ₁ Cf-xΩ₁ U-x1
u11 = T₀ (suc xΩ₁) (proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)) U-x1
u2 = T₀ x2 Cf-x2 U-x2
u21 = T₀ (suc x2) (proj₁ Cf-x2 , s≈ (proj₂ Cf-x2)) U-x2
u3 = T₀ x3 Cf-x3 U-x3
uf0 = T₀ xf0 Cf-f0 U-f0
uf0s = T₀ xf0s (proj₁ Cf-f0 , s≈ (proj₂ Cf-f0)) U-f0
uf0Ω = T₀ xf0Ω Cf-f0Ω U-f0Ω
uf1 = T₀ (F (natᴵ 1)) (Cf-F (natᴵ 1)) (Tc-F (natᴵ 1))
uf5 = T₀ Lv₅ Cf-Lv₅ Tc-Lv₅

ua-1 : agree 9 2 u1 (tq 0 zero) ≡ true
ua-1 = refl
ua-11 : agree 9 2 u11 (tq 0 (suc zero)) ≡ true
ua-11 = refl
ua-2 : agree 12 2 u2 (tq 1 zero) ≡ true
ua-2 = refl
ua-21 : agree 10 2 u21 (tq 1 (suc zero)) ≡ true
ua-21 = refl
ua-3 : agree 9 2 u3 (tq 2 zero) ≡ true
ua-3 = refl
ua-ω : agree 9 2 uf0 tqω ≡ true
ua-ω = refl
ua-ctl : agree 8 2 u21 (tq 1 zero) ≡ false
ua-ctl = refl
```

## §2 对记号: 种类

比较器只看种类 (`dfZ`), 不看界. $\psi_0(\Omega_{\psi_1(\Omega)})$, 第 5 站, 现在用紧的读法.

```agda
d-1 : dfZ 10 2 tΩ1 u1 ≡ nothing
d-1 = refl
d-11 : dfZ 12 2 tΩ11 u11 ≡ nothing
d-11 = refl
d-2 : dfZ 12 2 tΩ2 u2 ≡ nothing
d-2 = refl
d-21 : dfZ 12 2 tΩ21 u21 ≡ nothing
d-21 = refl
d-3 : dfZ 12 2 tΩ3 u3 ≡ nothing
d-3 = refl
d-f0 : dfZ 10 2 tψ1 uf0 ≡ nothing
d-f0 = refl
d-f0Ω : dfZ 10 2 tψ1Ω uf0Ω ≡ nothing
d-f0Ω = refl
d-f1 : dfZ 10 2 tψΩ uf1 ≡ nothing
d-f1 = refl
d-f5 : dfZ 10 2 tψ5 uf5 ≡ nothing
d-f5 = refl
-- 对照
d-ctl₁ : is-ok (dfZ 10 2 tψΩ uf5) ≡ false
d-ctl₁ = refl
d-ctl₂ : is-ok (dfZ 12 2 tψ1 uf1) ≡ false
d-ctl₂ = refl
```

## §3 界: 目标穿过分支 $\tau$

**有限测试, 看界.** `Tgt` 与 [GuardTightAccept](GuardTightAccept.lagda.md) 的 `t-bra*` 同一个装置: 顶层 $L+1$, 目标 $k$ 的路径穿过分支 $\tau$. `nav`: 沿第一路径走到目标; `sameL`: 目标确实是 $G\,b$ (结构比较到有限深度, 极限比前 3 项, 闭包只比第一支). **期待: 恒等读法 $\tau$, 紧的读法 $b+1$, 不随 $\tau$ 变.**

```agda
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Product using (Σ)

nav : List ℕ → (x : LG) → Maybe (Σ LG (λ k → k ≪ x))
nav ds zero = nothing
nav [] (suc y) = just (y , zero)
nav (d ∷ ds) (suc y) with nav (d ∷ ds) y
... | just (k , r) = just (k , suc r)
... | nothing = nothing
nav [] (lim f) = nothing
nav (d ∷ ds) (lim f) with nav ds (f d)
... | just (k , r) = just (k , lim d r)
... | nothing = nothing
nav ds (lc c t g) with nav ds t
... | just (k , r) = just (k , fst r)
... | nothing = nothing

admF : ∀ {k x} (r : k ≪ x) E → Adm E (≪→< r)
admF zero E = tt
admF (suc r) E = admF r E
admF (lim n r) E = admF r E
admF (fst r) E = admF r E

sameL : ℕ → LG → LG → Bool
sameB : ℕ → ℕ → (ℕ → LG) → (ℕ → LG) → Bool
sameL zero _ _ = true
sameL (suc d) zero zero = true
sameL (suc d) (suc a) (suc b) = sameL d a b
sameL (suc d) (lim f) (lim g) = sameB 3 d f g
sameL (suc d) (lc c t g) (lc c′ t′ g′) = sameL d t t′
sameL (suc d) _ _ = false
sameB zero d f g = true
sameB (suc n) d f g = sameL d (f n) (g n) && sameB n d f g

data Rd? : Set where
  bad : Rd?
  res : ℕ → ℕ → Rd?

module Bra {c₁ t₁ g₁} (cf : Cfˢ (lc c₁ t₁ g₁)) (tc : Tc (lc c₁ t₁ g₁)) where
  go : (τ : Ordᴵ) (eτ : c₁ ⊑ᴵ τ) (B : Ordᴵ) → pr τ <ᴵ B → List ℕ → Rd?
  go τ eτ B lt ds with nav ds (g₁ τ eτ)
  ... | nothing = bad
  ... | just (k , r) = res (Tgt.Yid cf tc τ eτ k (≪→< r) (λ E → admF r E) B lt) (Tgt.Ytight cf tc τ eτ k (≪→< r) (λ E → admF r E) B lt)

  tgt : (τ : Ordᴵ) (eτ : c₁ ⊑ᴵ τ) → List ℕ → LG
  tgt τ eτ ds with nav ds (g₁ τ eτ)
  ... | nothing = zero
  ... | just (k , r) = k

ltN : ∀ n → pr (τₙ n) <ᴵ suc (τₙ n)
ltN n = suc zero
```

### 第 5 站

$L=\mathrm{Lv}_5$, 分支 $F\,\tau$. 目标 $k=F\,2$: 在 $F\,3$ 里新出现 (`ds₃`), 在 $F(\tau+1)$ 里沿 `lim 0` 还在. **有限测试. 没有塔对照: [LadderNFTree](LadderNFTree.lagda.md) 只到 $\psi_1(1)$ 附近; 这里只比 "不随 $\tau$ 变" 与 "$k$ 确实是 $F\,2$".**

```agda
module L5 = Bra {suc zero} Cf-Lv₅ Tc-Lv₅

ds₃ : List ℕ
ds₃ = 1 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 0 ∷ 1 ∷ []

pfx : ℕ → List ℕ
pfx n = replicate n 0

k₃ : LG
k₃ = L5.tgt (τₙ 2) (one⊑nat 2) ds₃

t5-k : sameL 12 k₃ (F (natᴵ 2)) ≡ true
t5-k = refl
-- 对照: 不是 F 1, 不是 F 3
t5-k₁ : sameL 12 k₃ (F (natᴵ 1)) ≡ false
t5-k₁ = refl

t5-3 : L5.go (τₙ 2) (one⊑nat 2) (suc (τₙ 2)) (ltN 2) ds₃ ≡ res 3 3
t5-3 = refl
```

```agda
t5-4 : L5.go (τₙ 3) (one⊑nat 3) (suc (τₙ 3)) (ltN 3) (pfx 1 ++ ds₃) ≡ res 4 3
t5-4 = refl
t5-5 : L5.go (τₙ 4) (one⊑nat 4) (suc (τₙ 4)) (ltN 4) (pfx 2 ++ ds₃) ≡ res 5 3
t5-5 = refl
t5-7 : L5.go (τₙ 6) (one⊑nat 6) (suc (τₙ 6)) (ltN 6) (pfx 4 ++ ds₃) ≡ res 7 3
t5-7 = refl

-- 目标 F 1: 在 F 2 里新出现
ds₂ : List ℕ
ds₂ = 1 ∷ 2 ∷ 2 ∷ 1 ∷ []

k₂ : LG
k₂ = L5.tgt (τₙ 1) (one⊑nat 1) ds₂

t5-k₂ : sameL 12 k₂ (F (natᴵ 1)) ≡ true
t5-k₂ = refl

t5-2 : L5.go (τₙ 1) (one⊑nat 1) (suc (τₙ 1)) (ltN 1) ds₂ ≡ res 2 2
t5-2 = refl
t5-2′ : L5.go (τₙ 3) (one⊑nat 3) (suc (τₙ 3)) (ltN 3) (pfx 2 ++ ds₂) ≡ res 4 2
t5-2′ = refl

-- 极限分支: τ = ω. F ω 的第 n 项是 F n. 恒等读法的界是极限 (toN 只看第 1 项), 所以只比紧的读法
ωe : suc zero ⊑ᴵ ωᴵ
ωe = s⊑ z≅ (lim 1 zero)

ωlt : pr ωᴵ <ᴵ suc ωᴵ
ωlt = zero

tight : Rd? → ℕ
tight bad = 999
tight (res _ t) = t

t5-ω : tight (L5.go ωᴵ ωe (suc ωᴵ) ωlt (3 ∷ ds₃)) ≡ 3
t5-ω = refl
t5-ω′ : tight (L5.go ωᴵ ωe (suc ωᴵ) ωlt (5 ∷ pfx 2 ++ ds₃)) ≡ 3
t5-ω′ = refl
```

### $\psi_1(\Omega)$

$L=F\,1$, 分支 $H\,\tau=\psi_1(\tau)$, $H(\tau+1)=\lim_n(H\,\tau)\cdot n$. 目标 $k=H\,2$ (`dsH`). 上一个分支 $H\,\tau$ 沿 `lim 1` 还在. **有限测试, 没有塔对照.**

```agda
module LF1 = Bra {suc zero} (Cf-F (natᴵ 1)) (Tc-F (natᴵ 1))

H : Ordᴵ → LG
H τ = rb₁ (ψ¹ (Un.em τ))

dsH pf1 : ℕ → List ℕ
dsH n = pf1 n ++ (2 ∷ 1 ∷ 1 ∷ [])
pf1 n = replicate n 1

kH : LG
kH = LF1.tgt (τₙ 2) (one⊑nat 2) (dsH 0)

tH-k : sameL 12 kH (H (natᴵ 2)) ≡ true
tH-k = refl

tH-3 : LF1.go (τₙ 2) (one⊑nat 2) (suc (τₙ 2)) (ltN 2) (dsH 0) ≡ res 3 3
tH-3 = refl
tH-4 : LF1.go (τₙ 3) (one⊑nat 3) (suc (τₙ 3)) (ltN 3) (dsH 1) ≡ res 4 3
tH-4 = refl
tH-6 : LF1.go (τₙ 5) (one⊑nat 5) (suc (τₙ 5)) (ltN 5) (dsH 3) ≡ res 6 3
tH-6 = refl
-- 第一支: 目标 Ω₁ (下一节点在 H 1 里). 紧的读法落到第一支, 界是 c₂ = 1
tH-f : LF1.go (τₙ 4) (one⊑nat 4) (suc (τₙ 4)) (ltN 4) (replicate 4 1 ++ (2 ∷ [])) ≡ res 5 1
tH-f = refl
```

### 第二层的闭包: $\psi_1(\psi_1(\Omega))$ 的闭包

$F\,2$ 的第 1 项是闭包 $C$, 分支 $\psi_1(\psi_1(\tau))$, 不是任何字面的形状. **有限测试, 没有塔对照.** 目标的路径由 `nav` 走, 只看 "不随 $\tau$ 变".

```agda
xC : LG
xC = rb₁ (ψ¹ (Un.chain {suc zero} {suc (suc zero)} zero (OCF.Align.GuardTightCum.up zero) 1))

cfC : Cfˢ xC
cfC = proj₂ (proj₁ (Cf-F (natᴵ 2))) 1 , inv (proj₂ (Cf-F (natᴵ 2)))
  where
  inv : ∀ {f} → lim f ≈ lim f → f 1 ≈ f 1
  inv (l≈ h) = h 1

tcC : Tc xC
tcC = Tc-F (natᴵ 2) 1

module LC = Bra {suc zero} cfC tcC

GC : Ordᴵ → LG
GC τ = rb₁ (ψ¹ (OCF.Align.GuardTightCum.ψ {suc zero} {zero} {suc (suc zero)} zero (λ q → suc (suc q)) (Un.em τ)))

dsC : ℕ → List ℕ
dsC n = replicate n 1 ++ (2 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ [])

kC : LG
kC = LC.tgt (τₙ 2) (one⊑nat 2) (dsC 0)

tC-k : sameL 12 kC (GC (natᴵ 2)) ≡ true
tC-k = refl

tC-3 : LC.go (τₙ 2) (one⊑nat 2) (suc (τₙ 2)) (ltN 2) (dsC 0) ≡ res 3 3
tC-3 = refl
tC-4 : LC.go (τₙ 3) (one⊑nat 3) (suc (τₙ 3)) (ltN 3) (dsC 1) ≡ res 4 3
tC-4 = refl
tC-6 : LC.go (τₙ 5) (one⊑nat 5) (suc (τₙ 5)) (ltN 5) (dsC 3) ≡ res 6 3
tC-6 = refl
```

### 极限节点的位置

$H\,3$ 的位置 `lim 1 self` 是极限节点 $H\,2$. 读到分支 2, 不是 3 (`s-cg`). 位置 `self`: $H\,3$ 自己, 分支 3. **有限测试.**

```agda
open import OCF.Align.GuardTightCum using (natᴵ)

braOf : ∀ {c t g η e k} {P : Cp k (g η e)} → RdO c t g η e P → ℕ
braOf (rdF _ _ _) = 0
braOf (rdB a _ _ _ _ _) = toN a

rdF1 : Rdr _ _ _
rdF1 = proj₁ (Tc-F (natᴵ 1))

pos-H2 : braOf (rdF1 (natᴵ 3) (one⊑nat 2) (lim 1 self)) ≡ 2
pos-H2 = refl
pos-H3 : braOf (rdF1 (natᴵ 3) (one⊑nat 2) self) ≡ 3
pos-H3 = refl
pos-H2′ : braOf (rdF1 (natᴵ 5) (one⊑nat 4) (lim 1 (lim 1 (lim 1 self)))) ≡ 2
pos-H2′ = refl
```

### 字面的闭包, 统一读法

与 `t-bra*` 同一个目标. 目标 $\Omega$: 第一支, 界 1. 目标 $\Omega+1$: 分支 2, 界 2. 穿过 $\tau=3,5,7$. 对照恒等读法.

```agda
b-1 : Tgt.Ytight {_} {_} {_} Cf-x2 U-x2 (τₙ 4) (one⊑nat 4) xΩ₁ (pthS 4 xΩ₁) (adm-pthS 4 xΩ₁) (suc (τₙ 4)) (suc zero) ≡ 1
b-1 = refl
b-2 : Tgt.Ytight {_} {_} {_} Cf-x2 U-x2 (τₙ 2) (one⊑nat 2) (suc xΩ₁) (pthS 1 (suc xΩ₁)) (adm-pthS 1 (suc xΩ₁)) (suc (τₙ 2)) (suc zero) ≡ 2
b-2 = refl
b-2′ : Tgt.Ytight {_} {_} {_} Cf-x2 U-x2 (τₙ 6) (one⊑nat 6) (suc xΩ₁) (pthS 5 (suc xΩ₁)) (adm-pthS 5 (suc xΩ₁)) (suc (τₙ 6)) (suc zero) ≡ 2
b-2′ = refl
b-id : Tgt.Yid {_} {_} {_} Cf-x2 U-x2 (τₙ 6) (one⊑nat 6) (suc xΩ₁) (pthS 5 (suc xΩ₁)) (adm-pthS 5 (suc xΩ₁)) (suc (τₙ 6)) (suc zero) ≡ 7
b-id = refl
-- 过 noTimes: ψ₁(1)+Ω
b-ω : Tgt.Ytight {_} {_} {_} Cf-f0Ω U-f0Ω (τₙ 4) (one⊑nat 4) xf0 (pthS 4 xf0) (adm-pthS 4 xf0) (suc (τₙ 4)) (suc zero) ≡ 1
b-ω = refl
```

## §4 $W$ 与更深的种类

$W$ 是 `noW` 的那棵树. 与 [GuardTightAccept](GuardTightAccept.lagda.md) §6 同一个构造, 换成统一读法. **有限测试. 第一个孩子走得到的地方不多.**

```agda
open import OCF.Align.GuardTightTree using (O; module Fold; module Emb; Ω̇; rdZ; _⊕_)
open import OCF.Align.Uniform5Wall using (W)

module WU where
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

  module F₂ = Fold L₂ w₂ s₂ U-x2
  module F₁ = Fold c₁ w₂ (s≈ s₂) U-x2

  G₁ : LG
  G₁ = suc xΩ₁

  tgt₁ : G₁ < L₂
  tgt₁ = bra two e₂ zero

  E₃ : Ents
  E₃ = ∅ (natᴵ 3)

  in₁ : O G₁ tz
  in₁ = F₂.ψ E₃ (F₂.tp tgt₁ ((natᴵ 3 , refl , suc zero) , tt)) (λ ()) (Ω̇ L₂ U-x2)

  f₂ : Frm
  f₂ = frm (suc zero) (suc xΩ₁) (λ η e → rb₁ (OCF.Align.GuardTightCum.add Ω₁ᶜ (λ q → suc q) (Un.em η))) two e₂

  left : O c₁ (tz ∪ tz)
  left = Emb.ι c₁ U-x2 L₂ (suc self) (inj₂ refl) (Ω̇ L₂ U-x2)

  right : O c₁ (tz ∪ (tk f₂ ∪ tz))
  right = Emb.ι c₁ U-x2 G₁ (suc (bra two e₂ (suc self))) (inj₂ refl) in₁

  W̃ : O L₂ (tk f₂)
  W̃ = F₁.ψ E₃ (F₁.tp zero tt)
        (λ { (ml (ml ())) ; (ml (mr ())) ; (mr (ml ())) ; (mr (mr (ml hr))) → F₁.fs nothing (just (F₁.ab hr (inj₂ refl))) ; (mr (mr (mr ()))) })
        (left ⊕ right)

  Xw : _
  Xw = rdZ (F₂.ψ {ρ = tz} E₃ F₂.t0 (λ { hr → F₂.fs (just (F₂.evd self tt s₂ (natᴵ 3 , refl , suc zero))) nothing }) W̃)

u-W : dfZ 24 1 W WU.Xw ≡ nothing
u-W = refl
u-W₂ : dfZ 12 2 W WU.Xw ≡ nothing
u-W₂ = refl
```
