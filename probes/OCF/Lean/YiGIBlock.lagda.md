# 精简主线的抽象块、折叠与行

> 编译实例：层号取 `YiRWBlock.L`；底携带 `Ok`、比较表与原底，主线取 `rbᶻ`。
> 不改树、折叠或合法性；实例写法参照 `YiAbsGFin`，槽位逆换型按精简块递归。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGIBlock where
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as T
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsGIface
open B

chLᵍ : (ℓ : L) → CH ℓ → L
chLᵍ (nd s h) c = h c

ChTᵍ : (ℓ : L) → CH ℓ → Set
ChTᵍ ℓ c = Σ (ChT ℓ c) (RCh ℓ c (chZ ℓ c))

chTᵍ : (ℓ : L) (c : CH ℓ) → ChTᵍ ℓ c → Tr (chLᵍ ℓ c)
chTᵍ (nd s h) c (y , _) = y

incᵍ : ∀ {j} (ℓ : L) (c : CH ℓ) → j P.≤ chLᵍ ℓ c → j P.≤ ℓ
incᵍ (nd s h) c w = P.inc c w

incUᵍ : ∀ {j} (ℓ : L) → CH ℓ → ((c : CH ℓ) → j P.≤ chLᵍ ℓ c) → j P.≤ ℓ
incUᵍ (nd s h) _ ws = P.inu ws

upᵍ : ∀ {ℓ} → Tr ℓ → (c : CH ℓ) → ChTᵍ ℓ c → Tr ℓ
upᵍ x c (y , e) = up x c y e

hdᵍ : ∀ {ℓ} → Tr ℓ → Bool
hdᵍ (Ω _ _) = true
hdᵍ _ = false

blkᵍ : Block
blkᵍ = record
  { Lv = L ; Tr = Tr ; Ch = CH ; chL = chLᵍ ; ChT = ChTᵍ ; chT = chTᵍ
  ; _⊑_ = P._≤_ ; self = P.self ; inc = incᵍ ; incU = incUᵍ
  ; up = upᵍ ; hd = hdᵍ ; _◃_ = λ {ℓ} → Lt (Sig ℓ) ; Leg = λ _ → ⊤ }

Bsᵍ : L → Set
Bsᵍ ℓ = P.Ok ℓ × T.Rb ℓ × F.Base ℓ

ψᵍ : (ℓ : L) → Bsᵍ ℓ → (j : L) → j P.≤ ℓ → O.Tr⁺ j → Tr ℓ → O.Tr⁺ j
ψᵍ ℓ (o , r , b) j w β x = T.ψ ℓ o r b j w β x

dnᵍ : (ℓ : L) → Bsᵍ ℓ → (c : CH ℓ) → Tr ℓ → Bsᵍ (chLᵍ ℓ c)
dnᵍ (nd s h) (o , r , b) c x = proj₂ o c , proj₂ r c , λ j w → T.ψ (nd s h) o r b j (P.inc c w) (b j (P.inc c w)) x

foldᵍ : Fold blkᵍ
foldᵍ = record
  { Bs = Bsᵍ ; LegB = λ _ _ → ⊤ ; Bt = O.Tr⁺ ; LegT = λ _ _ → ⊤
  ; ψ = λ ℓ b j w β x → proj₁ (ψᵍ ℓ b j w β x) ; ψβ = ψᵍ ; dn = dnᵍ }

mutual
  slTᵍ : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Tr (at ℓ p)
  slTᵍ (nd s h) (inj₂ (c , t)) z = slT⁼ᵍ (h c) t z
  slTᵍ (nd (sΩ k) h) (inj₁ t) z = slT⁼ᵍ k t z

  slT⁼ᵍ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Tr (proj₁ (sl⁼ a t))
  slT⁼ᵍ a (inj₁ _) z = z
  slT⁼ᵍ a (inj₂ p) z = slTᵍ a p z

rowsᵍ : Rows blkᵍ foldᵍ
rowsᵍ = record
  { sc = suc ; Sl = Pos ; slL = at ; SlT = Br ; slT = slTᵍ ; nd = Ω
  ; Ωt = λ ℓ → proj₁ (O.Ωt ℓ) ; Dn = O.Dn ; upf = λ {ℓ} {j} d β y → proj₁ (O.Up j d β y)
  ; sucL = λ ℓ → nd sS (λ _ → ℓ) ; ΩL = λ k h → nd (sΩ k) h ; lift = ↑ }
```
