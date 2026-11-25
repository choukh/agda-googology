# 验收一侧 (比较表折叠): `Lift₁` 的实例 (孩子的值不低于 ω), 与归约到后继一步

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 表任意. 编译定理, 无前提: `Dir.lift-ω` (c = `ωᶜ`, η = ω, 经 `YiLTLim` 的 `LFu` 与 `YiHCOmega` 的 `leafω`); `up◃` (第 0 层的树 x ◃ c 时, 层 `h₁ x` 的 Ω 树朝第 0 层的折叠对着的项, 层 `h₁ c` 的也对着); `Qinf≤` (η ≤ ω 时, 第 0 层的树 c 要么是字面的 `nat n`, 要么层 `h₁ c` 的 Ω 树的折叠对着 ψ₀(Ω_η)); `lift-lim` (一切 ℕ 极限形状的 c 与 η = ω); `val-ω≥` (塔第 1 项 Ω 树的第 c 支对着 ψ₀(Ω_ω)).
> 条件定理 `lift-red : StepS → Lift₁`: `M⁰ η c` 的推导的 `mz`, `mL`, `mw`, `mc` 四行无前提, 只有 `m1` (c 是后继) 一行归到前提 `StepS`. `StepS` 未证; 它的结论在 (natT (n+1), nat n) 上成立 (`step-fin`).
> 不给出什么: 后继一步 (c = `suc x`, x 不是字面自然数; 最小的是 `suc ωᶜ` 对 η = ω+1); 带松弛的有限对 (`M⁰ η (nat n)` 而 η 小于 n); 不涉及上界. 这几处没有编译的否定.
> 来源: `upS` 照 `YiHCFold.liftU` (层号从 `fn m` 换成任意, 目标取第 0 层); `liftN`, `lift-fin` 照 `YiKPInst.Sem`; 其余新写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLTLift where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiRBFam using (OKB; Pt; can; pu; pt; tu)
open import OCF.Lean.YiRBCrit using (h₁; blk)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃; ⊴-◃)
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (mz; m1; mL; mΩ; mU; mw; mc; M⁰; module G⁰)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; pred; fsn; fsn0; cofψ0; natT; hd<; lv<)
open import OCF.Lean.YiMENote using (cofψω; fsnψω)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiCLLow using (s0; ss)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiHCFam using (ΩJ)
open import OCF.Lean.YiHCOmega using (module Tω)
open import OCF.Lean.YiKPInst using (zq; zpt; pz-eq; pk-eq)
open import OCF.Lean.YiLTFold using (Qu; sΩ-LF)
open import OCF.Lean.YiLTLim using (module LimT; module LimU)
open import OCF.Lean.YiLTKid
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
```

## 第一条路: c = `ωᶜ`, 沿一致路径的保持

`h₁ ωᶜ` 是 `nd sL fn` (`lvlω`), 相邻路径是 `inc tt self`. 接口的两条路径都是 `inu ws`, 各分量逐点等于 `zpt n` (`pz-eq`, `pk-eq`; 整条路径的相等要函数外延, 所以 `LFu` 的前提是逐点的).

```agda
module Wω = LimT fn (λ n → n) (λ _ → refl) (λ n → inc tt self) (λ n → ss s0 , refl)
module Uω = LimU fn (λ n → n) (λ _ → refl) (λ n → inc tt self) (λ n → ss s0 , refl)
module Hω = Tω fn (λ n → n) (λ _ → refl) (λ n → inc tt self) (λ n → ss s0 , refl)

lvlω : h₁ ωᶜ ≡ Wω.Lω
lvlω = refl

module Dir (r : Rb ℓ¹) where
  open Sem r

  gbOK : (B : Base Wω.Lω) → OKB B → Wω.GBω B []
  gbOK B ok = Wω.mkGBω (λ m {i} si u _ → ok (fn i) (inc m u))
                       (λ m {i} si u _ → ΩJ i (B (fn i) (inc m u)) (ok (fn i) (inc m u)))

  lift-ω : Kdˢ ωᶜ (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ ωᶜ)))
  lift-ω _ (inj₁ refl) B ok β hβ =
    Uω.FoldU.LFu (proj₂ (proj₂ o¹ ωᶜ)) (proj₂ r ωᶜ) B [] (gbOK B ok) (λ n → z≤ (fn n)) zq pz-eq β hβ
      (Hω.leafω (λ k → ≤-refl))
  lift-ω _ (inj₂ refl) B ok β hβ =
    Uω.FoldU.LFu (proj₂ (proj₂ o¹ ωᶜ)) (proj₂ r ωᶜ) B [] (gbOK B ok) (λ n → self ∙ proj₂ (proj₁ o¹) (nat n)) zq pk-eq β hβ
      (Hω.leafω (λ k → ≤-refl))
```

## 第二条路: Ω 树朝第 0 层的折叠对着的项

`ZP ℓ v`: v 是朝第 0 层的一致路径 (每层都是 `inu`). `SΩ t ℓ o r`: 层 ℓ 的 Ω 树沿任一这样的路径, 以任一 `OKB` 的底与对着 ψ₀(0) 的起点, 折到第 0 层后对着 t. `Q t ℓ` 是它对一切证据与表.

```agda
data ZP : (ℓ : L) → zero ≤ ℓ → Set where
  zs : ZP zero self
  zu : ∀ {s h} {ws : (c : Ch s) → zero ≤ h c} → (∀ c → ZP (h c) (ws c)) → ZP (nd s h) (inu ws)

zp-z : ∀ ℓ → ZP ℓ (z≤ ℓ)
zp-z zero     = zs
zp-z (nd s h) = zu (λ c → zp-z (h c))

zp-l : ∀ b → ZP (zero ⊕ b) (self ∙ lift zero b)
zp-l zero     = zs
zp-l (nd s h) = zu (λ c → zp-l (h c))

zp-pt : ∀ n {v} → ZP (fn n) v → v ≡ zpt n
zp-pt zero    zs      = refl
zp-pt (suc n) (zu zw) = cong (λ p → inu (λ _ → p)) (zp-pt n (zw tt))

SΩ : E.T → (ℓ : L) → Ok ℓ → Rb ℓ → Set
SΩ t ℓ o r = (v : zero ≤ ℓ) → ZP ℓ v → (B : Base ℓ) → OKB B → (β : Tr⁺ zero) → M⁰ (Ωᴺ 0) (proj₁ β)
           → M⁰ t (proj₁ (ψ ℓ o r B zero v β (proj₁ (Ωt ℓ))))

Q : E.T → L → Set
Q t ℓ = (o : Ok ℓ) (r : Rb ℓ) → SΩ t ℓ o r

Qc : ∀ {s t ℓ} → s ≤ᵀ t → Q t ℓ → Q s ℓ
Qc le q o r v zv B ok β hβ = mc le (q o r v zv B ok β hβ)

QL : ∀ {t ℓ} → cof t ≡ cω → (∀ k → Q (fsn t k) ℓ) → Q t ℓ
QL e h o r v zv B ok β hβ = mL e (λ k → h k o r v zv B ok β hβ)
```

沿层号上行. 后继形状: Ω 树是结点, 朝第 0 层取回灌链, 链的第 1 项在孩子层的 Ω 树之上. ℕ 极限形状: Ω 树的第 n 个部分和的末项是孩子 n 的 Ω 树的嵌入, 一致路径上它的折叠就是孩子 n 上的折叠 (底换成左项的折叠, 仍是 `OKB`).

```agda
upS : ∀ {t} {h : ⊤ → L} → Q t (h tt) → Q t (nd sS h)
upS {t} {h} q o r (inu ws) (zu zw) B ok β hβ =
    (G⁰.m-cum
      (λ k → next⁺ (ψ (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) zero (ws tt) β
                      (iter (λ z → proj₁ (next⁺ (ψ (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) (h tt) self
                                                    (B (h tt) (inc tt self)) z))) zero k)))
      1
      (mw (mw (q (proj₂ o tt) (proj₂ r tt) (ws tt) (zw tt) (λ i u → B i (inc tt u)) (λ i u → ok i (inc tt u)) β hβ)
              (mono (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) zero (ws tt) β
                (⊴-◃ (ok (h tt) (inc tt self)) (◃l zero))))
          (◃l zero)))

module _ {t : E.T} {g : ℕ → L} (n : ℕ) (q : Q t (g n)) (o : Ok (nd sL g)) (r : Rb (nd sL g))
         (ws : (k : ℕ) → zero ≤ g k) (zw : ∀ k → ZP (g k) (ws k)) (B : Base (nd sL g)) (ok : OKB B)
         (β : Tr⁺ zero) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) where
  private
    stepL : (x : Tr (nd sL g))
          → M⁰ t (proj₁ (ψ (nd sL g) o r B zero (inu ws) β (up x n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n))))))
    stepL x =
      q (proj₂ o n) (proj₂ r n) (ws n) (zw n) (λ i u → ψ (nd sL g) o r B i (inc n u) (B i (inc n u)) x)
        (λ i u → ⊴-trans (ok i (inc n u)) (ψ-⊵ (nd sL g) o r B i (inc n u) (B i (inc n u)) x))
        (ψ (nd sL g) o r B zero (inu ws) β x)
        (G⁰.m-zl (λ y → proj₁ (ψ (nd sL g) o r B zero (inu ws) β y)) (mono (nd sL g) o r B zero (inu ws) β) hβ x)

  upL′ : (m : ℕ) → m ≡ n → M⁰ t (proj₁ (ψ (nd sL g) o r B zero (inu ws) β (proj₁ (Ωt (nd sL g)))))
  upL′ zero    refl = mw (stepL zero) (◃l zero)
  upL′ (suc m) refl = mw (stepL (cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) m)) (◃l (suc m))

upL : ∀ {t} {g : ℕ → L} (n : ℕ) → Q t (g n) → Q t (nd sL g)
upL n q o r (inu ws) (zu zw) B ok β hβ = upL′ n q o r ws zw B ok β hβ n refl

up◃ : ∀ {t} {x c : Tr zero} → zero ⊢ x ◃ c → Q t (h₁ x) → Q t (h₁ c)
up◃ ◃s          q = upS q
up◃ (◃l n)      q = upL n q
up◃ (◃w {p = ()})
up◃ (◃u _ () _ _)
up◃ (◃c _ () _)
up◃ (◃t d e)    q = up◃ e (up◃ d q)
```

有限层 (照 `YiKPInst.Sem.liftN`) 与任意层对着 ψ₀(Ω₀).

```agda
liftN : ∀ n (o : Ok (fn n)) (r : Rb (fn n)) (B : Base (fn n)) → OKB B → (β : Tr⁺ zero) → M⁰ (Ωᴺ 0) (proj₁ β)
      → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ (fn n) o r B zero (zpt n) β (proj₁ (Ωt (fn n)))))
liftN zero    o r B ok β hβ = Qu o r B self β hβ (m1 refl mz)
liftN (suc n) o r B ok β hβ = sΩ-LF o r (tu (zq n)) B β ok hβ

Qfin : ∀ n → Q (ψᴺ 0 (Ωᴺ n)) (fn n)
Qfin n o r v zv B ok β hβ =
  subst (λ v → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ (fn n) o r B zero v β (proj₁ (Ωt (fn n)))))) (sym (zp-pt n zv)) (liftN n o r B ok β hβ)

Qz : ∀ c → Q (ψᴺ 0 (Ωᴺ 0)) (h₁ c)
Qz c with zl c
... | inj₁ refl = Qfin 0
... | inj₂ d    = up◃ d (Qfin 0)
```

## 归约: `Lift₁` 只缺后继一步

记号一侧: η 的余尾是 ω 时 Ω_η 的余尾是 ω, 基本列是 Ω_{η[k]}; Ω 对下标单调.

```agda
cofΩω : ∀ η → cof η ≡ cω → cof (E.Ωt η) ≡ cω
cofΩω []       ()
cofΩω (w ∷ ws) e = cong (cofψ0 (w ∷ ws)) e

fsnΩω : ∀ η k → cof η ≡ cω → fsn (E.Ωt η) k ≡ E.Ωt (fsn η k)
fsnΩω []       k ()
fsnΩω (w ∷ ws) k e = cong (λ c → fsn0 (w ∷ ws) c k) e

Ωt≤ : ∀ {s t} → s ≤ᵀ t → E.Ωt s ≤ᵀ E.Ωt t
Ωt≤ (inj₁ p)    = inj₁ (hd< (lv< p))
Ωt≤ (inj₂ refl) = inj₂ refl

StepS : Set
StepS = ∀ {η x} → cof η ≡ c1 → M⁰ (pred η) x → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x) → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))

liftQ : StepS → ∀ {η c} → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)
liftQ st (mz {x = c})             = Qz c
liftQ st (m1 e m)                 = st e m (liftQ st m)
liftQ st {c = c} (mL {t = η} e h) =
  QL (cofψω (natT 0) (E.Ωt η) (cofΩω η e))
     (λ k → subst (λ z → Q z (h₁ c))
              (sym (trans (fsnψω (natT 0) (E.Ωt η) k (cofΩω η e)) (cong (ψᴺ 0) (fsnΩω η k e))))
              (liftQ st (h k)))
liftQ st (mΩ {p = ()} _ _ _)
liftQ st (mU {c = ()} _ _)
liftQ st (mw m d)                 = up◃ d (liftQ st m)
liftQ st (mc le m)                = Qc (app≤ 0 [] (Ωt≤ le)) (liftQ st m)

module Red (r : Rb ℓ¹) where
  open Sem r

  zpc : ∀ c {v} → Pcˢ c v → ZP (h₁ c) v
  zpc c (inj₁ refl) = zp-z (h₁ c)
  zpc c (inj₂ refl) = zp-l (↑ zero c)

  Q→Kd : ∀ {t c} → Q (ψᴺ 0 t) (h₁ c) → Kdˢ c t (proj₁ (Ωt (h₁ c)))
  Q→Kd {c = c} q v pc B ok β hβ = q (proj₂ o¹ c) (proj₂ r c) v (zpc c pc) B ok β hβ

  lift-red : StepS → Lift₁
  lift-red st l = Q→Kd (liftQ st l)

  k1-red : StepS → M⁰ (E.EBOψ 2) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (proj₁ (Ωt ℓ¹))))
  k1-red st = k1ˢ (lift-red st)

k1-redᶻ : StepS → M⁰ (E.EBOψ 2) (twᶻ 1)
k1-redᶻ = Red.k1-red (rbᶻ ℓ¹)
```

`StepS` 的结论在 (natT (n+1), nat n) 上成立 (不用它的归纳前提).

```agda
step-fin : ∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (nat n)))
step-fin n = Qfin (suc n)
```

## 无前提的实例: 值不低于 ω 的孩子, η = ω

c 在每个 `nat k` 之上时, 层 `h₁ c` 的 Ω 树的折叠对着 ψ₀(Ω_ω): 每个 ψ₀(Ω_k) 由 `Qfin k` 沿 `up◃` 上行得到. 第 0 层的每棵 ℕ 极限形状的树都在每个 `nat k` 之上 (`nat⊴f`, 用相邻步进), 所以第 0 层的树要么是字面的 `nat n`, 要么它的层对着 ψ₀(Ω_ω) (`Qinf`).

```agda
Qω : ∀ c → (∀ k → zero ⊢ nat k ◃ c) → Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ c)
Qω c lt = QL refl (λ k → subst (λ z → Q (ψᴺ 0 (E.Ωt z)) (h₁ c)) (sym (rep1 k)) (up◃ (lt k) (Qfin k)))

suc⊴ : ∀ {x y : Tr zero} → zero ⊢ x ◃ y → suc x ⊴ y
suc⊴ ◃s             = ⊴r
suc⊴ (◃l {a = a} n) = ⊴◃ (⊴-◃ (suc⊴ (a n)) (◃l (suc n)))
suc⊴ (◃w {p = ()})
suc⊴ (◃u _ () _ _)
suc⊴ (◃c _ () _)
suc⊴ (◃t d e)       = ⊴◃ (⊴-◃ (suc⊴ d) e)

nat⊴f : (f : ℕ → Tr zero) (a : ∀ n → zero ⊢ f n ◃ f (suc n)) → ∀ k → nat k ⊴ f k
nat⊴f f a zero with zl (f zero)
... | inj₁ e = subst (λ z → zero ⊴ z) e ⊴r
... | inj₂ d = ⊴◃ d
nat⊴f f a (suc k) = suc⊴ (⊴-◃ (nat⊴f f a k) (a k))

Qlim : ∀ f a → Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ (lim f a))
Qlim f a = Qω (lim f a) (λ k → ⊴-◃ (nat⊴f f a k) (◃l k))

Qinf : ∀ c → (Σ ℕ λ n → c ≡ nat n) ⊎ Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ c)
Qinf zero      = inj₁ (0 , refl)
Qinf (suc c) with Qinf c
... | inj₁ (n , e) = inj₁ (suc n , cong suc e)
... | inj₂ q       = inj₂ (upS q)
Qinf (lim f a) = inj₂ (Qlim f a)
Qinf (Ω () _)
Qinf (up _ () _ _)

Qinf≤ : ∀ {η} → η ≤ᵀ ωᵀ → ∀ c → (Σ ℕ λ n → c ≡ nat n) ⊎ Q (ψᴺ 0 (E.Ωt η)) (h₁ c)
Qinf≤ le c with Qinf c
... | inj₁ fin = inj₁ fin
... | inj₂ q   = inj₂ (Qc (app≤ 0 [] (Ωt≤ le)) q)

module Inst (r : Rb ℓ¹) where
  open Sem r
  open Red r

  lift-fin : ∀ n → Kdˢ (nat n) (E.Ωt (natT n)) (proj₁ (Ωt (h₁ (nat n))))
  lift-fin n = Q→Kd (Qfin n)

  lift-ω≥ : ∀ c → (∀ k → zero ⊢ nat k ◃ c) → Kdˢ c (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ c)))
  lift-ω≥ c lt = Q→Kd (Qω c lt)

  lift-lim : ∀ f a → Kdˢ (lim f a) (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ (lim f a))))
  lift-lim f a = Q→Kd (Qlim f a)

  lift-mono : ∀ {t x c} → zero ⊢ x ◃ c → Q (ψᴺ 0 t) (h₁ x) → Kdˢ c t (proj₁ (Ωt (h₁ c)))
  lift-mono d q = Q→Kd (up◃ d q)
```

检验: 塔第 1 项的 Ω 树的第 c 支 (`blk c`) 朝第 0 层的标准折叠对着 ψ₀(Ω_ω), c 同上; 对着 ψ₀(Ω_n), c = `nat n`.

```agda
  val-ω≥ : ∀ c → (∀ k → zero ⊢ nat k ◃ c) → M⁰ (ψᴺ 0 (E.Ωt ωᵀ)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (blk c)))
  val-ω≥ c lt = Fold.LF¹ (B₀ ℓ¹) gb₀ˢ wu (Ωt zero) (m1 refl mz) {x = blk c} (mU mz (lift-ω≥ c lt)) tt

  val-fin : ∀ n → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (blk (nat n))))
  val-fin n = Fold.LF¹ (B₀ ℓ¹) gb₀ˢ wu (Ωt zero) (m1 refl mz) {x = blk (nat n)} (mU mz (lift-fin n)) tt
```
