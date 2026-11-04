# 验收: 一致的折叠与 EBO 比较

> **验收节.** 记号只在本文件. 结论写在 [DomFold](DomFold.lagda.md). **全部是有限测试, 不是证明; 种类检验不看界.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.GuardTightCum using (Ordᴵ; natᴵ; suc; zero; lim; _⊑ᴵ_; _<ᴵ_; s⊑; z≅; Ω; _+_; add; Ordᶜ; Ω-refl; add-≅)
open import OCF.Align.GuardTightLv
import OCF.Align.GuardTightUni as Uni
import OCF.Align.DomFoldAdd as AddM
import OCF.Align.DomFoldDiag as DDiag
open import OCF.Align.DomFoldDom
open import OCF.Align.DomFoldNext
import OCF.Align.DomFoldBase as DBase
import OCF.Align.DomFoldTree as DTree
open import OCF.Align.DomFoldRead using (convTc)
import OCF.Align.EBO as E
open E using (T; fsn; fsT; cof; c0; c1; cω; cΩ; pred; Ωt; natT; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
import OCF.Align.GuardTightTree as Old
import OCF.Align.GuardTightBase as OldB
open import OCF.Align.GuardTightRd using (module RdIter; module RdAdd)
open import OCF.Free.Prefix using (Z)
```

## §1 比较器, 对任何 `DomX`

`dfO`: 第 0 层的树对 $\omega$-项. `dfL`: 读回的层号. 闭包若对应 `cω` 的项, 是链语义, 比第一支与 `fsn t 0`; 若对应 `cΩ` 的项, 比第一支与 $t[\gamma_0]$.

```agda
data Why : Set where
  kindBad : Why
  headBad : Why

γ₀ : ℕ → T
γ₀ zero = natT 1
γ₀ (suc n) = Ωt (natT (suc n))

is-ok : Maybe (Why × List ℕ) → Bool
is-ok nothing  = true
is-ok (just _) = false

module CmpO (X : DomX) (brs : (c : Dom.D (DomX.𝔻 X)) → ℕ → Maybe (Σ (Dom.D (DomX.𝔻 X)) λ η → (Dom._⊑ᴰ_ (DomX.𝔻 X) c η) × T)) where
  open DomX X
  open Lv 𝔻
  open DTree X

  dfO : ℕ → ℕ → T → ∀ {π} → O zero π → Maybe (Why × List ℕ)
  dfOs : ℕ → ℕ → ℕ → T → ∀ {π} → (ℕ → O zero π) → Maybe (Why × List ℕ)
  dfO zero w t x = nothing
  dfO (suc d) w t o0 with cof t
  ... | c0 = nothing
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (os x) with cof t
  ... | c1 = dfO d w (pred t) x
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (ol f) with cof t
  ... | cω = dfOs w d w t f
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (oŝ c t′ g) with cof t
  ... | cω = dfO d w (fsn t 0) t′
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (oĉ c z zg o₀ o) with cof t
  ... | cω = dfO d w (fsn t 0) o₀
  ... | _  = just (kindBad , [])
  dfO (suc d) w t (owk _ x) = dfO (suc d) w t x
  dfO (suc d) w t (ocv _ x) = dfO (suc d) w t x
  dfO (suc d) w t (omk () _ _ _ _)
  dfO (suc d) w t (oΩ () _ _)
  dfO (suc d) w t (ocl () _ _ _ _)

  dfOs zero d w t f = nothing
  dfOs (suc n) d w t f with dfO d w (fsn t n) (f n)
  ... | just (g , p) = just (g , n ∷ p)
  ... | nothing = dfOs n d w t f

  dfL : ℕ → ℕ → T → LG → Maybe (Why × List ℕ)
  dfLs : ℕ → ℕ → ℕ → T → (ℕ → LG) → Maybe (Why × List ℕ)
  dfLb : ℕ → ℕ → ℕ → T → (c : D) → ((η : D) → c ⊑ᴰ η → LG) → Maybe (Why × List ℕ)
  dfL zero w t x = nothing
  dfL (suc d) w t zero with cof t
  ... | c0 = nothing
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (suc x) with cof t
  ... | c1 = dfL d w (pred t) x
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (lim f) with cof t
  ... | cω = dfLs w d w t f
  ... | _  = just (kindBad , [])
  dfL (suc d) w t (lc c t′ g) with cof t
  dfL (suc d) w t (lc c t′ g) | cω = dfL d w (fsn t 0) t′
  dfL (suc d) w t (lc c t′ g) | cΩ μ with E.cmpᵀ μ (natT (ix c))
  ...   | E.eq with dfL d w (fsT t (γ₀ (ix c))) t′
  ...     | just r = just r
  ...     | nothing = dfLb w d w t c g
  dfL (suc d) w t (lc c t′ g) | cΩ μ | E.lt = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | cΩ μ | E.gt = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | c0 = just (headBad , [])
  dfL (suc d) w t (lc c t′ g) | c1 = just (headBad , [])

  dfLs zero d w t f = nothing
  dfLs (suc n) d w t f with dfL d w (fsn t n) (f n)
  ... | just (g , p) = just (g , n ∷ p)
  ... | nothing = dfLs n d w t f

  -- 闭包的分支: c + k, 记号一侧是 fsT t (c + k). brs 认不出的下界不走.
  dfLb zero d w t c g = nothing
  dfLb (suc k) d w t c g with brs c k
  ... | nothing = dfLb k d w t c g
  ... | just (η , e , τ) with dfL d w (fsT t τ) (g η e)
  ...   | just (w′ , p) = just (w′ , (100 ∷ p))
  ...   | nothing = dfLb k d w t c g
```

## §2 回归: `X₀` 上的折叠与 [GuardTightTree](GuardTightTree.lagda.md) 一致

逐层比种类, **闭包比界**. 有限测试.

```agda
private
  module U₀ = Uni Dom₀
open Lv Dom₀ using (LG; Cfˢ; s≈)
open U₀ using (rb₁; rb-≈₁₁; Good-Ω; Good-add; Good→WF₁; F; Lv₅; Cf-F; Cf-Lv₅; good-F; ψ¹-≅)
private
  module T₀ = DTree X₀
  module B₀ = DBase X₀

toN : Ordᴵ → ℕ
toN zero = 0
toN (suc a) = suc (toN a)
toN (lim f s) = toN (f 1)

_==_ : ℕ → ℕ → Bool
zero == zero = true
suc a == suc b = a == b
_ == _ = false

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = suc (iterᴵ c k)

open import OCF.Align.GuardTightCum using (⊑ᴵ-refl; ⊑ᴵ-trans; Sim→⊑ᴵ)
up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → suc q))

-- 第 0 层下标的分支: 下界是字面的自然数才走
natI : Ordᴵ → Maybe ℕ
natI zero = just 0
natI (suc a) with natI a
... | just n = just (suc n)
... | nothing = nothing
natI (lim _ _) = nothing

_+ᴺ_ : ℕ → ℕ → ℕ
zero +ᴺ b = b
suc a +ᴺ b = suc (a +ᴺ b)

addT : T → ℕ → T
addT τ zero = τ
addT τ (suc k) = sucT (addT τ k)

brs₀ : (c : Ordᴵ) → ℕ → Maybe (Σ Ordᴵ λ η → (c ⊑ᴵ η) × T)
brs₀ c k with natI c
... | just n = just (iterᴵ c k , up⊑ k , natT (k +ᴺ n))
... | nothing = nothing

module C₀ = CmpO X₀ brs₀

agree : ℕ → ℕ → ∀ {π} → T₀.O (T₀.natL 0) π → Z → Bool
agreeB : ℕ → ℕ → ℕ → ∀ {π} {c c′ : Ordᴵ} → ((η : Ordᴵ) → c ⊑ᴵ η → T₀.O (T₀.natL 0) π) → ((η : Ordᴵ) → c′ ⊑ᴵ η → Z) → Bool
agreeL : ℕ → ℕ → ℕ → ∀ {π} → (ℕ → T₀.O (T₀.natL 0) π) → (ℕ → Z) → Bool
agree zero w _ _ = true
agree (suc d) w T₀.o0 Z.zero = true
agree (suc d) w (T₀.os x) (Z.suc y) = agree d w x y
agree (suc d) w (T₀.ol f) (Z.lim g) = agreeL w d w f g
agree (suc d) w (T₀.oŝ c o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) =
  (toN c == toN c′) && (agree d w o₀ o₀′ && agreeB w d w o o′)
agree (suc d) w (T₀.oĉ c z zg o₀ o) (Z.ĉᴸ c′ z′ zg′ o₀′ o′) =
  (toN c == toN c′) && (agree d w o₀ o₀′ && agreeB w d w o o′)
agree (suc d) w (T₀.owk _ x) y = agree (suc d) w x y
agree (suc d) w (T₀.ocv _ x) y = agree (suc d) w x y
agree (suc d) w _ _ = false

agreeL zero d w f g = true
agreeL (suc n) d w f g = agree d w (f n) (g n) && agreeL n d w f g

agreeB zero d w o o′ = true
agreeB (suc k) d w {c = c} {c′ = c′} o o′ = agree d w (o (iterᴵ c k) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k)) && agreeB k d w o o′

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

g2 : U₀.Good (Ω₁ᶜ + Ω₁ᶜ)
g2 = Good-add {σ = λ q → q} (Good-Ω (suc zero)) e1 (Good-Ω (suc zero))

Cf-x2 : Cfˢ x2
Cf-x2 = Good→WF₁ g2 , rb-≈₁₁ e2

Cf-x3 : Cfˢ x3
Cf-x3 = Good→WF₁ (Good-add {σ = λ q → q} g2 e2 (Good-Ω (suc zero))) , rb-≈₁₁ (add-≅ {σ = λ q → q} {σ′ = λ q → q} e2 e1)

Tc-x1 : OldB.Tc xΩ₁
Tc-x1 = RdIter.Tc-c

Tc-x2 : OldB.Tc x2
Tc-x2 = RdAdd.Tc-top Ω₁ᶜ (λ q → suc q) Tc-x1

Tc-x3 : OldB.Tc x3
Tc-x3 = RdAdd.Tc-top (Ω₁ᶜ + Ω₁ᶜ) (λ q → suc q) Tc-x2

new old : (L : LG) → Cfˢ L → OldB.Tc L → _
new L cf tc = T₀.Tn L cf (convTc L tc) 0
old L cf tc = Old.T₀ L cf tc

r-1 : agree 9 2 (new xΩ₁ Cf-xΩ₁ Tc-x1) (old xΩ₁ Cf-xΩ₁ Tc-x1) ≡ true
r-1 = refl
r-2 : agree 10 2 (new x2 Cf-x2 Tc-x2) (old x2 Cf-x2 Tc-x2) ≡ true
r-2 = refl
r-3 : agree 9 2 (new x3 Cf-x3 Tc-x3) (old x3 Cf-x3 Tc-x3) ≡ true
r-3 = refl
r-5 : agree 8 2 (new Lv₅ Cf-Lv₅ (OldB.Tc-id Lv₅)) (old Lv₅ Cf-Lv₅ (OldB.Tc-id Lv₅)) ≡ true
r-5 = refl
r-ctl : agree 9 2 (new x2 Cf-x2 Tc-x2) (old x3 Cf-x3 Tc-x3) ≡ false
r-ctl = refl
```

## §3 第 1 层定义域: $\Omega_2$ 进入

**有限测试.** `X₁`: 第一路径守卫的第 1 层. $\Omega_2$ 就是 `Ωᶠ`, 证书是定理 (`Cf-Ωᶠ`), 不是变量. 读位置用恒等 (`Tc-id`). 比较器看种类, 看闭包的共尾层, 并走分支 $c+k$; 不看界.

```agda
X₁ : DomX
X₁ = Next.X′ X₀
module N₀ = Next X₀
module T₁ = DTree X₁
module B₁ = DBase X₁

-- 第 1 层下标的分支: 下界认得出记号 (Ω₁ + j) 才走, 走 c + k
toT₀ : Lv.LG Dom₀ → Maybe T
toT₀ Lv.zero = just (natT 0)
toT₀ (Lv.suc x) with toT₀ x
... | just τ = just (sucT τ)
... | nothing = nothing
toT₀ (Lv.lim _) = nothing
toT₀ (Lv.lc (suc zero) (Lv.suc Lv.zero) g) = just (Ωt (natT 1))
toT₀ (Lv.lc _ _ _) = nothing

sucsᴳ : ∀ {𝔻′ : Dom} → Lv.LG 𝔻′ → ℕ → Lv.LG 𝔻′
sucsᴳ x zero = x
sucsᴳ x (suc k) = Lv.suc (sucsᴳ x k)

module Up₁ (X : DomX) where
  open DomX X
  module LL = Lv 𝔻
  open FgOf 𝔻
  sucsG : Σ LL.LG LL.Cfˢ → ℕ → Σ LL.LG LL.Cfˢ
  sucsG (x , w , sf) zero = x , w , sf
  sucsG x (suc k) with sucsG x k
  ... | (y , w , sf) = LL.suc y , w , LL.s≈ sf
  fgUp : (x : Σ LL.LG LL.Cfˢ) (k : ℕ) → Fg (proj₁ x) (proj₁ (sucsG x k))
  fgUp (x , w , sf) zero = inj₁ sf
  fgUp x (suc k) with sucsG x k | fgUp x k
  ... | (y , w , sf) | f = fg-tr f (inj₂ (LL.preᶠ sf LL.zero))

module UU₀ = Up₁ X₀

brs₁ : (c : N₀.D′) → ℕ → Maybe (Σ N₀.D′ λ η → (N₀._⊑′_ c η) × T)
brs₁ (inj₁ c) k with brs₀ c k
... | just (η , e , τ) = just (inj₁ η , e , τ)
... | nothing = nothing
brs₁ (inj₂ x) k with toT₀ (proj₁ x)
... | just τ = just (inj₂ (UU₀.sucsG x k) , UU₀.fgUp x k , addT τ k)
... | nothing = nothing

module C₁ = CmpO X₁ brs₁
module C₁ᶠ = CmpO X₁ (λ _ _ → nothing)

Ω₂ᴸ : N₀.L₁.LG
Ω₂ᴸ = N₀.Ωᶠ

tcΩ₂ : B₁.Tc Ω₂ᴸ
tcΩ₂ = B₁.Tc-id Ω₂ᴸ

tΩ₂ tψ₀Ω₂ tψ₁Ω₂ tψ₂Ω₂ : T
tΩ₂ = Ωt (natT 2)
tψ₀Ω₂ = ψ₀ᵗ (Ωt tΩ₂)
tψ₁Ω₂ = ψᵗ (natT 1) (Ωt tΩ₂) ∷ []
tψ₂Ω₂ = ψᵗ (natT 2) (Ωt tΩ₂) ∷ []

ψ₀Ω₂ : T₁.O (T₁.natL 0) N₀.L₁.tz
ψ₀Ω₂ = T₁.Tn Ω₂ᴸ N₀.Cf-Ωᶠ tcΩ₂ 0

ψ₁Ω₂ ψ₂Ω₂ : N₀.L₁.LG
ψ₁Ω₂ = T₁.rb (T₁.Tn Ω₂ᴸ N₀.Cf-Ωᶠ tcΩ₂ 1)
ψ₂Ω₂ = T₁.rb (T₁.Tn Ω₂ᴸ N₀.Cf-Ωᶠ tcΩ₂ 2)

a-ψ₀ : C₁.dfO 12 2 tψ₀Ω₂ ψ₀Ω₂ ≡ nothing
a-ψ₀ = refl
a-ψ₁ : C₁.dfL 10 2 tψ₁Ω₂ ψ₁Ω₂ ≡ nothing
a-ψ₁ = refl
a-ψ₂ : C₁.dfL 10 2 tψ₂Ω₂ ψ₂Ω₂ ≡ nothing
a-ψ₂ = refl
-- 对照
a-ctl₁ : is-ok (C₁.dfL 10 2 tψ₂Ω₂ ψ₁Ω₂) ≡ false
a-ctl₁ = refl
```

## §4 分支: 第 1 层的闭包在好层号 $x$ 处

**有限测试.** $x$ 是真的好层号, 证书是定理. 守卫的证据是字面的第一路径. `br`: 闭包的分支. `rawO`, `brO`: 第 0 层的闭包的链与值.

```agda
GLv₁ : Set
GLv₁ = N₀.GLv

Ωᵍ Lv₅ᵍ sΩᵍ : GLv₁
Ωᵍ = xΩ₁ , Cf-xΩ₁
Lv₅ᵍ = Lv₅ , Cf-Lv₅
sΩᵍ = Lv.suc xΩ₁ , proj₁ Cf-xΩ₁ , s≈ (proj₂ Cf-xΩ₁)

CG : N₀.L₁.LG → GLv₁ → Set
CG (N₀.L₁.lc (inj₂ c) t g) x = N₀.Fg (proj₁ c) (proj₁ x)
CG _ x = ⊤

br : (y : N₀.L₁.LG) (x : GLv₁) → CG y x → N₀.L₁.LG
br (N₀.L₁.lc (inj₂ c) t g) x e = g (inj₂ x) e
br y x e = y

Ω≺Lv₅ : N₀.Fg xΩ₁ Lv₅
Ω≺Lv₅ = inj₂ (Lv.preᶠ (proj₂ Cf-xΩ₁) (Lv.fst (Lv.fst (Lv.lim 2 (Lv.fst Lv.zero)))))

Ω⊑Ω : N₀.Fg xΩ₁ xΩ₁
Ω⊑Ω = inj₁ (proj₂ Cf-xΩ₁)

Ω≺sΩ : N₀.Fg xΩ₁ (Lv.suc xΩ₁)
Ω≺sΩ = inj₂ (Lv.preᶠ (proj₂ Cf-xΩ₁) Lv.zero)

tLv₅ : T
tLv₅ = ψᵗ (natT 1) (Ωt (Ωt (natT 1))) ∷ []

ψt : ℕ → T → T
ψt n b = ψᵗ (natT n) b ∷ []

-- ψ₂(Ω_x), ψ₁(Ω_x) 在 x = Ω₁, Ω₁+1, ψ₁(Ω_Ω): 与下一层的值同形
b-2Ω : C₁.dfL 10 2 (ψt 2 (Ωt (Ωt (natT 1)))) (br ψ₂Ω₂ Ωᵍ Ω⊑Ω) ≡ nothing
b-2Ω = refl
b-2s : C₁.dfL 10 2 (ψt 2 (Ωt (sucT (Ωt (natT 1))))) (br ψ₂Ω₂ sΩᵍ Ω≺sΩ) ≡ nothing
b-2s = refl
b-25 : C₁.dfL 10 2 (ψt 2 (Ωt tLv₅)) (br ψ₂Ω₂ Lv₅ᵍ Ω≺Lv₅) ≡ nothing
b-25 = refl
b-15 : C₁.dfL 10 2 (fsn tψ₁Ω₂ 1) (br ψ₁Ω₂ Lv₅ᵍ Ω≺Lv₅) ≡ nothing
b-15 = refl
b-ctl : is-ok (C₁.dfL 10 2 (ψt 2 (Ωt tLv₅)) (br ψ₂Ω₂ Ωᵍ Ω⊑Ω)) ≡ false
b-ctl = refl
```

## §5 第 0 层的链

**有限测试.** $\psi_0(\Omega_{\Omega_2})$ 的闭包带第 1 层的链: $o_0=\psi_0(\Omega_{\Omega_1})$, $z=\psi_1(\Omega_{\Omega_1})=\gamma_1$, $zg\,x=\psi_1(\Omega_x)$, $o\,x=\psi_0(\Omega_x)$. 链读回成分支要证书, 所以这里只把 $x$ 取成 $\gamma_1$ 的读回版本 `Lv₅`, 它的证书是定理.

```agda
rawZ : ∀ {π} → T₁.O (T₁.natL 0) π → N₀.L₁.LG
rawZ (T₁.oĉ c z zg o₀ o) = z
rawZ (T₁.owk _ x) = rawZ x
rawZ (T₁.ocv _ x) = rawZ x
rawZ _ = N₀.L₁.zero

CGO : T₁.O (T₁.natL 0) N₀.L₁.tz → GLv₁ → Set
CGO (T₁.oĉ (inj₂ c) z zg o₀ o) x = N₀.Fg (proj₁ c) (proj₁ x)
CGO _ x = ⊤

brO : (y : T₁.O (T₁.natL 0) N₀.L₁.tz) (x : GLv₁) → CGO y x → T₁.O (T₁.natL 0) N₀.L₁.tz
brO (T₁.oĉ (inj₂ c) z zg o₀ o) x e = o (inj₂ x) e
brO y x e = y

brZ : (y : T₁.O (T₁.natL 0) N₀.L₁.tz) (x : GLv₁) → CGO y x → N₀.L₁.LG
brZ (T₁.oĉ (inj₂ c) z zg o₀ o) x e = zg (inj₂ x) e
brZ y x e = N₀.L₁.zero

γ₁ᵀ γ₂ᵀ : T
γ₁ᵀ = E.γT tΩ₂′ (natT 1) 1
  where tΩ₂′ = Ωt tΩ₂
γ₂ᵀ = E.γT tΩ₂′ (natT 1) 2
  where tΩ₂′ = Ωt tΩ₂

z-1 : C₁.dfL 10 2 γ₁ᵀ (rawZ ψ₀Ω₂) ≡ nothing
z-1 = refl
z-ctl : is-ok (C₁.dfL 10 2 γ₂ᵀ (rawZ ψ₀Ω₂)) ≡ false
z-ctl = refl
-- 链的下一步: zg 在 γ₁ 的读回版本 Lv₅ 上是 γ₂; o 在 Lv₅ 上是基本列第 1 项
z-2 : C₁.dfL 10 2 γ₂ᵀ (brZ ψ₀Ω₂ Lv₅ᵍ Ω≺Lv₅) ≡ nothing
z-2 = refl
o-1 : C₁.dfO 12 2 (fsn tψ₀Ω₂ 1) (brO ψ₀Ω₂ Lv₅ᵍ Ω≺Lv₅) ≡ nothing
o-1 = refl
o-ctl : is-ok (C₁.dfO 12 2 (fsn tψ₀Ω₂ 0) (brO ψ₀Ω₂ Lv₅ᵍ Ω≺Lv₅)) ≡ false
o-ctl = refl
```

## §6 $\psi_0(\Omega_{\Omega_3})$

**有限测试.** 两条路: 在 `X₁` 上逐点 ($u_0=\Omega_2$, $u_1=\psi_2(\Omega_{\Omega_2})$, $u_2$ 的证书是变量, 只说这个深度没问到它), 与在 `X₂` 上一次写出 (`Ωᶠ` 的证书是定理).

```agda
tΩ₃ tψ₀Ω₃ : T
tΩ₃ = Ωt (natT 3)
tψ₀Ω₃ = ψ₀ᵗ (Ωt tΩ₃)

-- u₀ = Ω₂: 第 0 项
u-0 : C₁.dfO 12 2 (fsn tψ₀Ω₃ 0) ψ₀Ω₂ ≡ nothing
u-0 = refl

u₁ : N₀.L₁.LG
u₁ = ψ₂Ω₂

-- u₁ 的读回对 γ₁
u-1 : C₁.dfL 10 2 (E.γT (Ωt tΩ₃) (natT 2) 1) u₁ ≡ nothing
u-1 = refl

module U₂ (cfv : N₀.L₁.Cfˢ u₁) where
  u₂ : N₀.L₁.LG
  u₂ = T₁.rb (T₁.Tn u₁ cfv (B₁.Tc-id u₁) 2)
  u-2 : C₁ᶠ.dfL 7 2 (E.γT (Ωt tΩ₃) (natT 2) 2) u₂ ≡ nothing
  u-2 = refl
  -- 第 1 项: ψ₀(Ω_{u₁})
  ψ₀u₁ : T₁.O (T₁.natL 0) N₀.L₁.tz
  ψ₀u₁ = T₁.Tn u₁ cfv (B₁.Tc-id u₁) 0
  u-a1 : C₁ᶠ.dfO 7 2 (fsn tψ₀Ω₃ 1) ψ₀u₁ ≡ nothing
  u-a1 = refl

X₂ : DomX
X₂ = Next.X′ X₁
module N₁ = Next X₁
module T₂ = DTree X₂
module B₂ = DBase X₂

toT₁ : N₀.L₁.LG → Maybe T
toT₁ N₀.L₁.zero = just (natT 0)
toT₁ (N₀.L₁.suc x) with toT₁ x
... | just τ = just (sucT τ)
... | nothing = nothing
toT₁ (N₀.L₁.lim _) = nothing
toT₁ (N₀.L₁.lc (inj₁ (suc zero)) (N₀.L₁.suc N₀.L₁.zero) g) = just (Ωt (natT 1))
toT₁ (N₀.L₁.lc (inj₂ _) t g) with toT₁ t
... | just _ = just (Ωt (natT 2))
... | nothing = nothing
toT₁ (N₀.L₁.lc _ _ _) = nothing

module UU₁ = Up₁ X₁

brs₂ : (c : N₁.D′) → ℕ → Maybe (Σ N₁.D′ λ η → (N₁._⊑′_ c η) × T)
brs₂ (inj₁ c) k with brs₁ c k
... | just (η , e , τ) = just (inj₁ η , e , τ)
... | nothing = nothing
brs₂ (inj₂ x) k with toT₁ (proj₁ x)
... | just τ = just (inj₂ (UU₁.sucsG x k) , UU₁.fgUp x k , addT τ k)
... | nothing = nothing

module C₂ = CmpO X₂ brs₂

Ω₃ᴸ : N₁.L₁.LG
Ω₃ᴸ = N₁.Ωᶠ

tcΩ₃ : B₂.Tc Ω₃ᴸ
tcΩ₃ = B₂.Tc-id Ω₃ᴸ

ψ₀Ω₃ : T₂.O (T₂.natL 0) N₁.L₁.tz
ψ₀Ω₃ = T₂.Tn Ω₃ᴸ N₁.Cf-Ωᶠ tcΩ₃ 0

ψ₂Ω₃ ψ₃Ω₃ : N₁.L₁.LG
ψ₂Ω₃ = T₂.rb (T₂.Tn Ω₃ᴸ N₁.Cf-Ωᶠ tcΩ₃ 2)
ψ₃Ω₃ = T₂.rb (T₂.Tn Ω₃ᴸ N₁.Cf-Ωᶠ tcΩ₃ 3)

v-0 : C₂.dfO 12 2 tψ₀Ω₃ ψ₀Ω₃ ≡ nothing
v-0 = refl
v-2 : C₂.dfL 10 2 (ψt 2 (Ωt tΩ₃)) ψ₂Ω₃ ≡ nothing
v-2 = refl
v-3 : C₂.dfL 10 2 (ψt 3 (Ωt tΩ₃)) ψ₃Ω₃ ≡ nothing
v-3 = refl
v-ctl : is-ok (C₂.dfL 10 2 (ψt 3 (Ωt tΩ₃)) ψ₂Ω₃) ≡ false
v-ctl = refl
```

## §7 层号 $\Omega_2+1$: 节点的链穿过 $\Omega_2$ 的闭包

**有限测试.** 目标是路径 `zero`, 闭包保留 (`ka`). 这里的路径比较第一次在第 1 层的定义域上跑过 `oΩ` 的 `riseΩ`.

```agda
sΩ₂ : N₀.L₁.LG
sΩ₂ = N₀.L₁.suc Ω₂ᴸ

cf-sΩ₂ : N₀.L₁.Cfˢ sΩ₂
cf-sΩ₂ = N₀.WF-Ωᶠ , N₀.L₁.s≈ N₀.self-Ωᶠ

tsΩ₂ : T
tsΩ₂ = sucT tΩ₂

s-0 : C₁.dfO 12 2 (ψ₀ᵗ (Ωt tsΩ₂)) (T₁.Tn sΩ₂ cf-sΩ₂ (B₁.Tc-id sΩ₂) 0) ≡ nothing
s-0 = refl
s-1 : C₁.dfL 10 2 (ψt 1 (Ωt tsΩ₂)) (T₁.rb (T₁.Tn sΩ₂ cf-sΩ₂ (B₁.Tc-id sΩ₂) 1)) ≡ nothing
s-1 = refl
s-2 : C₁.dfL 10 2 (ψt 2 (Ωt tsΩ₂)) (T₁.rb (T₁.Tn sΩ₂ cf-sΩ₂ (B₁.Tc-id sΩ₂) 2)) ≡ nothing
s-2 = refl
s-ctl : is-ok (C₁.dfO 12 2 (ψ₀ᵗ (Ωt tΩ₂)) (T₁.Tn sΩ₂ cf-sΩ₂ (B₁.Tc-id sΩ₂) 0)) ≡ false
s-ctl = refl
```

## §8 层号 $\Omega_2\cdot2$, $\Omega_2\cdot2+1$: 证书是定理

**有限测试.** `cf2` 由 `WFˢ-ad` 给出. 这里的闭包有分支 $\Omega_2+x$.

```agda
module A₁ = AddM (N₀.NextDom)
module AΩ = A₁.Ad Ω₂ᴸ

Ω₂2 s2 : N₀.L₁.LG
Ω₂2 = AΩ.ad Ω₂ᴸ
s2 = N₀.L₁.suc Ω₂2

cf2 : N₀.L₁.Cfˢ Ω₂2
cf2 = AΩ.WFˢ-ad N₀.WF-Ωᶠ N₀.self-Ωᶠ Ω₂ᴸ N₀.WF-Ωᶠ N₀.self-Ωᶠ , AΩ.ad≈ N₀.self-Ωᶠ N₀.self-Ωᶠ

cfs2 : N₀.L₁.Cfˢ s2
cfs2 = proj₁ cf2 , N₀.L₁.s≈ (proj₂ cf2)

tc2 : B₁.Tc Ω₂2
tc2 = B₁.Tc-id Ω₂2

tcs2 : B₁.Tc s2
tcs2 = B₁.Tc-id s2

tΩ₂2 : T
tΩ₂2 = tΩ₂ ++ tΩ₂

m-0 : C₁.dfO 12 2 (ψ₀ᵗ (Ωt tΩ₂2)) (T₁.Tn Ω₂2 cf2 tc2 0) ≡ nothing
m-0 = refl
m-1 : C₁.dfL 8 2 (ψt 1 (Ωt tΩ₂2)) (T₁.rb (T₁.Tn Ω₂2 cf2 tc2 1)) ≡ nothing
m-1 = refl
m-2 : C₁.dfL 10 2 (ψt 2 (Ωt tΩ₂2)) (T₁.rb (T₁.Tn Ω₂2 cf2 tc2 2)) ≡ nothing
m-2 = refl
ms-0 : C₁.dfO 12 2 (ψ₀ᵗ (Ωt (sucT tΩ₂2))) (T₁.Tn s2 cfs2 tcs2 0) ≡ nothing
ms-0 = refl
ms-1 : C₁.dfL 8 2 (ψt 1 (Ωt (sucT tΩ₂2))) (T₁.rb (T₁.Tn s2 cfs2 tcs2 1)) ≡ nothing
ms-1 = refl
ms-2 : C₁.dfL 8 2 (ψt 2 (Ωt (sucT tΩ₂2))) (T₁.rb (T₁.Tn s2 cfs2 tcs2 2)) ≡ nothing
ms-2 = refl
m-ctl : is-ok (C₁.dfO 12 2 (ψ₀ᵗ (Ωt tΩ₂2)) (T₁.Tn s2 cfs2 tcs2 0)) ≡ false
m-ctl = refl
```

## §9 同键的帧: $W$ 的第 1 层类比

**有限测试.** 与 [GuardTightAccept](GuardTightAccept.lagda.md) 的 `WT` 同一个位置, 高一层: $\psi_0(\psi_{\Omega_2\cdot2}(\Omega_{\Omega_2\cdot2}+\psi_{\Omega_2+1}(\Omega_{\Omega_2\cdot2})))$. 右边的闭包读到分支 $x=\Omega_1$ 的帧, 所以这里 `bound′` 走 `maxF`, 第 1 层的比较 (`bd′`, `cmpFF`) 真的被读. 目标穿过分支 $\Omega_1$ 与内层的分支 2.

```agda
module WT₁ where
  open N₀.L₁ using (Cp; self; bra; _∪_; tz; tk; ml; mr; hr; Ents; ∅; _▸_,_; Bel′) renaming (zero to lz; suc to ls)
  open T₁ using (O; module Emb; module Fold; Ω̇; _⊕_)

  two : suc zero ⊑ᴵ natᴵ 2
  two = s⊑ z≅ (suc zero)

  Ls L₁ G₁ κ₂ : N₀.L₁.LG
  Ls = Ω₂2
  L₁ = ls Ls
  G₁ = ls Ω₂ᴸ
  κ₂ = AΩ.ad (N₀.emb xΩ₁)

  tcL : B₁.Tc Ls
  tcL = B₁.Tc-id Ls
  tcC : B₁.Tc L₁
  tcC = B₁.Tc-id L₁

  selfκ : κ₂ N₀.L₁.≈ κ₂
  selfκ = AΩ.ad≈ N₀.self-Ωᶠ (N₀.emb≈ (proj₂ Cf-xΩ₁))

  E₃ : Ents
  E₃ = (∅ (inj₂ sΩᵍ)) ▸ κ₂ , inj₁ (natᴵ 3)

  bl₁ : Bel′ E₃ Ls (inj₂ Ωᵍ)
  bl₁ = inj₂ sΩᵍ , inj₂ ((λ { (N₀.L₁.o≈ () _ _) }) , refl) , N₀.L₀.preᶠ (proj₂ Cf-xΩ₁) N₀.L₀.zero

  bl₂ : Bel′ E₃ κ₂ (inj₁ (natᴵ 2))
  bl₂ = inj₁ (natᴵ 3) , inj₁ (selfκ , refl) , suc zero

  tgt₁ : G₁ N₀.L₁.< Ls
  tgt₁ = bra (inj₂ Ωᵍ) Ω⊑Ω (bra (inj₁ (natᴵ 2)) two lz)

  P : Cp G₁ L₁
  P = N₀.L₁.suc (bra (inj₂ Ωᵍ) Ω⊑Ω (bra (inj₁ (natᴵ 2)) two (N₀.L₁.suc self)))

  module F₂ = Fold Ls (proj₁ cf2) (proj₂ cf2) tcL
  module F₁ = Fold L₁ (proj₁ cf2) (N₀.L₁.s≈ (proj₂ cf2)) tcC

  in₁ : O G₁ tz
  in₁ = F₂.ψ E₃ (F₂.tp tgt₁ (bl₁ , bl₂ , tt)) (λ ()) (Ω̇ Ls tcL)

  left : O L₁ (tz ∪ B₁.pF {c = L₁} (N₀.L₁.suc self))
  left = Emb.ι L₁ tcC Ls (N₀.L₁.suc self) (inj₂ refl) (Ω̇ Ls tcL)

  right : O L₁ (tz ∪ B₁.pF P)
  right = Emb.ι L₁ tcC G₁ P (inj₂ refl) in₁

  W̃ : O Ls (B₁.pF P)
  W̃ = F₁.ψ E₃ (F₁.tp lz tt)
        (λ { (ml (ml ())) ; (ml (mr ())) ; (mr (ml ())) ; (mr (mr (ml hr))) → F₁.fs nothing (just (F₁.ab (ml hr) (inj₂ refl))) ; (mr (mr (mr (ml hr)))) → F₁.fs nothing (just (F₁.ab (mr (ml hr)) (inj₂ refl))) ; (mr (mr (mr (mr ())))) })
        (left ⊕ right)

  Xw : O (T₁.natL 0) tz
  Xw = F₂.ψ E₃ (F₂.tn 0)
        (λ { (ml hr) → F₂.fs (just (F₂.evd self tt (proj₂ cf2) bl₁)) nothing
           ; (mr (ml hr)) → F₂.fs (just (F₂.evd (bra (inj₂ Ωᵍ) Ω⊑Ω self) (bl₁ , tt) selfκ bl₂)) nothing
           ; (mr (mr ())) }) W̃

  ΩΩ : E.PT
  ΩΩ = ψᵗ tΩ₂2 []

  Wt : T
  Wt = ψ₀ᵗ (ψᵗ tΩ₂2 (ΩΩ ∷ ψᵗ (sucT tΩ₂) (ΩΩ ∷ []) ∷ []) ∷ [])

  c-W₁ : C₁.dfO 20 1 Wt Xw ≡ nothing
  c-W₁ = refl
  c-W₂ : C₁.dfO 12 2 Wt Xw ≡ nothing
  c-W₂ = refl
  c-Wctl : is-ok (C₁.dfO 20 1 (ψ₀ᵗ (Ωt tΩ₂2)) Xw) ≡ false
  c-Wctl = refl
```

## §10 分支上的折叠就是下一层的折叠, 含界

**有限测试, 看界.** $\psi_0(\Omega_{\Omega_2})$ 的分支 $x$ 对 `X₀` 上的 $\psi_0(\Omega_x)$, 都用恒等读法. 逐层比种类与闭包的界.

```agda
agreeE : ℕ → ℕ → ∀ {π π′} → T₁.O (T₁.natL 0) π → T₀.O (T₀.natL 0) π′ → Bool
agreeEB : ℕ → ℕ → ℕ → ∀ {π π′} {c c′ : Ordᴵ} → ((η : N₀.D′) → N₀._⊑′_ (inj₁ c) η → T₁.O (T₁.natL 0) π) → ((η : Ordᴵ) → c′ ⊑ᴵ η → T₀.O (T₀.natL 0) π′) → Bool
agreeEL : ℕ → ℕ → ℕ → ∀ {π π′} → (ℕ → T₁.O (T₁.natL 0) π) → (ℕ → T₀.O (T₀.natL 0) π′) → Bool
agreeE zero w _ _ = true
agreeE (suc d) w (T₁.owk _ x) y = agreeE (suc d) w x y
agreeE (suc d) w (T₁.ocv _ x) y = agreeE (suc d) w x y
agreeE (suc d) w x@T₁.o0 (T₀.owk _ y) = agreeE (suc d) w x y
agreeE (suc d) w x@T₁.o0 (T₀.ocv _ y) = agreeE (suc d) w x y
agreeE (suc d) w T₁.o0 T₀.o0 = true
agreeE (suc d) w (T₁.os x) (T₀.os y) = agreeE d w x y
agreeE (suc d) w (T₁.os x) (T₀.owk _ y) = agreeE (suc d) w (T₁.os x) y
agreeE (suc d) w (T₁.os x) (T₀.ocv _ y) = agreeE (suc d) w (T₁.os x) y
agreeE (suc d) w (T₁.ol f) (T₀.ol g) = agreeEL w d w f g
agreeE (suc d) w (T₁.ol f) (T₀.owk _ y) = agreeE (suc d) w (T₁.ol f) y
agreeE (suc d) w (T₁.ol f) (T₀.ocv _ y) = agreeE (suc d) w (T₁.ol f) y
agreeE (suc d) w (T₁.oŝ (inj₁ c) o₀ o) (T₀.oŝ c′ o₀′ o′) = (toN c == toN c′) && (agreeE d w o₀ o₀′ && agreeEB w d w o o′)
agreeE (suc d) w (T₁.oŝ (inj₁ c) o₀ o) (T₀.oĉ c′ _ _ o₀′ o′) = (toN c == toN c′) && (agreeE d w o₀ o₀′ && agreeEB w d w o o′)
agreeE (suc d) w (T₁.oĉ (inj₁ c) _ _ o₀ o) (T₀.oŝ c′ o₀′ o′) = (toN c == toN c′) && (agreeE d w o₀ o₀′ && agreeEB w d w o o′)
agreeE (suc d) w (T₁.oĉ (inj₁ c) _ _ o₀ o) (T₀.oĉ c′ _ _ o₀′ o′) = (toN c == toN c′) && (agreeE d w o₀ o₀′ && agreeEB w d w o o′)
agreeE (suc d) w x (T₀.owk _ y) = agreeE (suc d) w x y
agreeE (suc d) w x (T₀.ocv _ y) = agreeE (suc d) w x y
agreeE (suc d) w _ _ = false

agreeEL zero d w f g = true
agreeEL (suc n) d w f g = agreeE d w (f n) (g n) && agreeEL n d w f g

agreeEB zero d w o o′ = true
agreeEB (suc k) d w {c = c} {c′ = c′} o o′ = agreeE d w (o (inj₁ (iterᴵ c k)) (up⊑ k)) (o′ (iterᴵ c′ k) (up⊑ k)) && agreeEB k d w o o′

low : (x : LG) → Cfˢ x → T₀.T⁰ 0
low x cf = T₀.Tn x cf (B₀.Tc-id x) 0

e-1 : agreeE 9 2 (brO ψ₀Ω₂ Ωᵍ Ω⊑Ω) (low xΩ₁ Cf-xΩ₁) ≡ true
e-1 = refl
e-5 : agreeE 9 2 (brO ψ₀Ω₂ Lv₅ᵍ Ω≺Lv₅) (low Lv₅ Cf-Lv₅) ≡ true
e-5 = refl
e-ctl : agreeE 9 2 (brO ψ₀Ω₂ Lv₅ᵍ Ω≺Lv₅) (low xΩ₁ Cf-xΩ₁) ≡ false
e-ctl = refl
```

## §11 对 $n$ 一致的定义

**有限测试.** `Tψ₀ₙ`, `Diag` 是 [DomFoldDiag](DomFoldDiag.lagda.md) 的那一个定义, 这里取 $n=0,1,2$. `Diag` 的 `GoodFeed` 是变量: 证书是变量, 只说这个深度没问到它.

```agda
n-0 : CmpO.dfO (Xₙ 1) brs₁ 12 2 tψ₀Ω₂ (DDiag.Tψ₀ₙ 0) ≡ nothing
n-0 = refl
n-1 : CmpO.dfO (Xₙ 2) brs₂ 12 2 tψ₀Ω₃ (DDiag.Tψ₀ₙ 1) ≡ nothing
n-1 = refl
n-2 : CmpO.dfO (Xₙ 3) (λ _ _ → nothing) 12 2 (ψ₀ᵗ (Ωt (Ωt (natT 4)))) (DDiag.Tψ₀ₙ 2) ≡ nothing
n-2 = refl
n-ctl : is-ok (CmpO.dfO (Xₙ 2) brs₂ 12 2 tψ₀Ω₂ (DDiag.Tψ₀ₙ 1)) ≡ false
n-ctl = refl

module D₀ = DDiag.DiagOf X₀
module D₁ = DDiag.DiagOf X₁

module DiagT₀ (G : D₀.GoodFeed) where
  open D₀.Diag G using (Tdiag)
  c-Ω₂ : C₀.dfO 7 2 tψ₀Ω₂ Tdiag ≡ nothing
  c-Ω₂ = refl

module DiagT₁ (G : D₁.GoodFeed) where
  open D₁.Diag G using (Tdiag)
  c-Ω₃ : C₁ᶠ.dfO 7 2 tψ₀Ω₃ Tdiag ≡ nothing
  c-Ω₃ = refl
```
