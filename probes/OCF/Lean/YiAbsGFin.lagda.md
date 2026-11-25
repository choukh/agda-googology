# 抽象理论 (十四): 有限层号的记号直连关系族是分级接口的部分实例

> 验收文件 (读记号, 读具体块). 判决: 编译定理, 无前提. 合法块 (`YiLegBlock`) 限制到有限层号 (层号取 ℕ, 第 n 层的树是 `Tr (fin n)`) 填进 `Block`, `Fold`, `Rows`; 参照取 `refᴱ`, 关系取 `YiANFam.M`.
> 成立的律 (十条加两项): `Zero`, `Succ`, `Lim`, `Weak`, `Node`, `Emb`, `UpKeep`, `Leaf` (层号 n 读作 `natT n`), `SelfKeep` (底的量化域取后继层号), 第 0 层的 `Base`, 每层的 `Gen`. 结点与 Ω 余尾在这里非空.
> 没有填的: `LowKeep` (`Bd` 取空; `YiANLv` 的结论是带上下文的遗传形式, 没有化成本接口的形状), `Lift` 与读法的四条 (`Rd` 只取字面的 `natT n`). 所以这不是 `GSim` 的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGFin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (Up; Ωt; Ωt-nz)
open import OCF.Lean.YiLegPath using (_≤_; self; ins)
open import OCF.Lean.YiLegFold using (ψs; nzs)
open import OCF.Lean.YiAbsLeg using (hdΩ; ChT⁺; Bsᴸ; Btᴸ; dnᴸ)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanView using (cof0; ne)
open import OCF.Lean.YiMEBase using (Mᴰ; mz; m1; mL; mΩ; mU; mw; read; r1⁰; rω⁰; strict⁰; weak⁰; _⊴_; pos⁰)
open import OCF.Lean.YiANFam using (fin; slot; M; Lw; Nw; mwN; mzN; mLN; Mβ; FD; dn; Pu; ψᴺ; module Self)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiAbsGEbo using (refᴱ)
```

## 块, 折叠, 行

```agda
chLᶠ : (n : ℕ) → Ch (fin n) → ℕ
chLᶠ (suc n) _ = n

chTᶠ : (n : ℕ) (c : Ch (fin n)) → ChT⁺ (fin n) c → Tr (fin (chLᶠ n c))
chTᶠ (suc n) _ (y , _) = y

incᶠ : ∀ {j} (n : ℕ) (c : Ch (fin n)) → fin j ≤ fin (chLᶠ n c) → fin j ≤ fin n
incᶠ (suc n) _ w = ins w

incUᶠ : ∀ {j} (n : ℕ) → Ch (fin n) → ((c : Ch (fin n)) → fin j ≤ fin (chLᶠ n c)) → fin j ≤ fin n
incUᶠ (suc n) _ ws = ins (ws tt)

blkᶠ : Block
blkᶠ = record
  { Lv = ℕ ; Tr = λ n → Tr (fin n) ; Ch = λ n → Ch (fin n) ; chL = chLᶠ ; ChT = λ n → ChT⁺ (fin n) ; chT = chTᶠ
  ; _⊑_ = λ j n → fin j ≤ fin n ; self = self ; inc = incᶠ ; incU = incUᶠ
  ; up = λ x c ye → up x c (proj₁ ye) (proj₂ ye) ; hd = hdΩ
  ; _◃_ = λ {n} x y → fin n ⊢ x ◃ y ; Leg = λ _ → ⊤ }

dnᶠ : (n : ℕ) → Bsᴸ (fin n) → (c : Ch (fin n)) → Tr (fin n) → Bsᴸ (fin (chLᶠ n c))
dnᶠ (suc n) b c x = dnᴸ (suc (fin n)) b c x

foldᶠ : Fold blkᶠ
foldᶠ = record
  { Bs = λ n → Bsᴸ (fin n) ; LegB = λ _ _ → ⊤ ; Bt = λ j → Btᴸ (fin j) ; LegT = λ _ _ → ⊤
  ; ψ  = λ n b j w β x → ψs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin j) w (proj₁ β) (proj₂ β) x
  ; ψβ = λ n b j w β x → ψs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin j) w (proj₁ β) (proj₂ β) x
                       , nzs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin j) w (proj₁ β) (proj₂ β) x
  ; dn = dnᶠ }

slLᶠ : (n : ℕ) → Pos (fin n) → ℕ
slLᶠ (suc n) p = slot n p

slT′ : (n : ℕ) (p : Pos (fin (suc n))) → Br (fin (suc n)) p → Tr (fin (slot n p))
slT′ n       (inj₁ _)  c = c
slT′ (suc n) (inj₂ p)  c = slT′ n p c
slT′ zero    (inj₂ ())

slTᶠ : (n : ℕ) (p : Pos (fin n)) → Br (fin n) p → Tr (fin (slLᶠ n p))
slTᶠ (suc n) p = slT′ n p

Dnᶠ : ℕ → ℕ → Set
Dnᶠ zero    j = ⊥
Dnᶠ (suc N) j = FD (suc N) j

upfᶠ : ∀ {n j} → Dnᶠ n j → Btᴸ (fin n) → Tr (fin j) → Tr (fin n)
upfᶠ {n = suc N} {j = j} d β y = Up (fin j) (dn d) (proj₁ β) (proj₂ β) y

rowsᶠ : Rows blkᶠ foldᶠ
rowsᶠ = record
  { sc = suc ; Sl = λ n → Pos (fin n) ; slL = slLᶠ ; SlT = λ n → Br (fin n) ; slT = slTᶠ ; nd = Ω
  ; Ωt = λ n → Ωt (fin n) ; Dn = Dnᶠ ; upf = upfᶠ
  ; sucL = suc ; ΩL = λ k _ → k ; lift = λ k _ → k }
```

## 关系与量化域

`cl n t` 是 ψ_n(t). `Bd` 取空: 折到低层的律不在这里填.

```agda
Nuᶠ : (n : ℕ) → Pos (fin n) → E.T → Set
Nuᶠ (suc n) p κ = Nw n p κ

gradedᶠ : Graded blkᶠ foldᶠ rowsᶠ refᴱ 𝕍
gradedᶠ = record
  { ℓ₀ = 0 ; v = read ; R = M ; Rd = λ n ν → ν ≡ E.natT n ; Nu = Nuᶠ ; bt = proj₁
  ; cl = ψᴺ ; Cx = λ _ _ → ⊤ ; app = λ _ a → a ; Bd = λ _ _ _ _ → ⊥ }

domsᶠ : Doms blkᶠ foldᶠ
domsᶠ = record { Gx = λ _ _ → ⊤ ; Gb = λ n _ → Σ ℕ λ N → n ≡ suc N ; Wl = λ _ → ⊥ ; Gl = λ _ _ → ⊥ }

open Laws gradedᶠ domsᶠ using (Zero; Succ; Lim; Weak; Node; Emb; SelfKeep; UpKeep; Leaf; Base)
open Row gradedᶠ domsᶠ using (Gen; Rules)
```

## 律

```agda
lw→ : ∀ n p {η c} → Lw n p η c → M (slot n p) η (slT′ n p c)
lw→ n       (inj₁ _)  l = l
lw→ (suc n) (inj₂ p)  l = lw→ n p l
lw→ zero    (inj₂ ())

→lw : ∀ n p {η c} → M (slot n p) η (slT′ n p c) → Lw n p η c
→lw n       (inj₁ _)  l = l
→lw (suc n) (inj₂ p)  l = →lw n p l
→lw zero    (inj₂ ())

zeroᶠ : Zero
zeroᶠ {ℓ = n} {t = []}    e = mzN n
zeroᶠ {ℓ = n} {t = _ ∷ _} e = ⊥-elim (cof0 _ ne e)

succᶠ : Succ
succᶠ {ℓ = zero}  = m1
succᶠ {ℓ = suc n} = m1

limᶠ : Lim
limᶠ {ℓ = n} = mLN n

weakᶠ : Weak
weakᶠ {ℓ = n} = mwN n

nodeᶠ : Node
nodeᶠ {ℓ = suc n} p g e nu h = mΩ e nu (λ η c l → h η c (lw→ n p l))

embᶠ : Emb
embᶠ {ℓ = suc n} c (y , e) m ch = mU m ch

selfᶠ : SelfKeep
selfᶠ (ε , ρ , B) (β , nβ) (N , refl) hP m = Self.PF N ε ρ B β nβ hP m

upᶠ : UpKeep
upᶠ {ℓ = suc N} {j = j} d (b , nb) mb m = Pu j d b nb mb m

leafᶠ : Leaf
leafᶠ {ℓ = zero}  refl = pos⁰ (Ωt zero) (Ωt-nz zero)
leafᶠ {ℓ = suc n} refl = Mβ n

baseᶠ : Base
baseᶠ = record
  { G₀ = λ _ → ⊤ ; _⇝ˢ_ = λ x y → suc x ⊴ y ; _⇝_ = λ x y → x ⊴ y
  ; strict = strict⁰ ; weak = weak⁰
  ; inv1 = λ m _ w → r1⁰ m w ; invω = λ m _ w n → rω⁰ m w n }
```

## 生成

`Mᴰ` 的归纳原理写成六条规则的形式, 第 0 层没有槽位与孩子.

```agda
module Ind {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
           {Nu : P S → E.T → Set} (Q : E.T → T S → Set)
    (qz : ∀ {x} → Q [] x)
    (q1 : ∀ {t x} → E.cof t ≡ E.c1 → Mᴰ S Low Chd Nu (E.pred t) x → Q (E.pred t) x → Q t (suc x))
    (qL : ∀ {t x} → E.cof t ≡ E.cω → (∀ n → Mᴰ S Low Chd Nu (E.fsn t n) x) → (∀ n → Q (E.fsn t n) x) → Q t x)
    (qΩ : ∀ {t ν} (p : P S) (g : B S p → T S) → E.cof t ≡ E.cΩ ν → Nu p ν
        → (∀ η c → Low p η c → Mᴰ S Low Chd Nu (E.fsT t η) (g c))
        → (∀ η c → Low p η c → Q (E.fsT t η) (g c)) → Q t (Ω p g))
    (qU : ∀ {t s x} (c : C S) (y : D S c) (e : R S c (z₀ S c) y) → Mᴰ S Low Chd Nu t x → Q t x → Chd c s y
        → Q (t ++ s) (up x c y e))
    (qw : ∀ {t x x′} → Mᴰ S Low Chd Nu t x → Q t x → Lt S x x′ → Q t x′) where

  ind : ∀ {t x} → Mᴰ S Low Chd Nu t x → Q t x
  ind mz                         = qz
  ind (m1 e r)                   = q1 e r (ind r)
  ind (mL e h)                   = qL e h (λ n → ind (h n))
  ind (mΩ {p = p} {g = g} e nu h) = qΩ p g e nu h (λ η c l → ind (h η c l))
  ind (mU {c = c} {y = y} {e = e} m ch) = qU c y e m (ind m) ch
  ind (mw m d)                   = qw m (ind m) d

genᶠ : ∀ n → Gen n
genᶠ zero    Q rs = Ind.ind Q (qz refl) q1 qL (λ ()) (λ ()) qw
  where open Rules rs
genᶠ (suc n) Q rs = Ind.ind Q (qz refl) q1 qL
  (λ p g e nu hR hQ → qΩ p g e nu (λ η c l → hR η c (→lw n p l)) (λ η c l → hQ η c (→lw n p l)))
  (λ c y e m q ch → qU c (y , e) m q ch) qw
  where open Rules rs
```
