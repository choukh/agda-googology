# 新旧块的逐层关系: 折叠保持关系

> 编译定理 (验收用, 无前提, 对一切相关的输入): 保留判定相关 (`kp-R`, 精简块的 `Maybe` 对 F2 的续延与它的归纳原理); 折叠保持关系, 值, 非零与单调各一条: 目标第 0 层且路径是 `z≤` 时对 F2 的 `ψ⊥` (`A`, `Am`), 一般目标与相关路径时对 `ψs` (`S`, `Sm`).
> 量化域: 一切相关的层号证据 (`RelE`), 底 (`RelBase`), 路径 (`RelW`), 底树与树; 不限于塔与 Λ. 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem
open import OCF.Lean.YiBROps
```

## 路径到层号, 默认底, 链

```agda
W→L : ∀ {j ℓ j′ ℓ′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelL ℓ ℓ′ → RelW w w′ → RelL j j′
W→L rl         wself         = rl
W→L (lS r)     (wincS rv)    = W→L r rv
W→L (lS r)     (winuS rv)    = W→L r rv
W→L (lL r)     (wincL n rv)  = W→L (r n) rv
W→L (lL r)     (winuL rvs)   = W→L (r zero) (rvs zero)
W→L (lΩ rk rh) (wincΩ rc rv) = W→L (rh _ _ rc) rv
W→L (lΩ rk rh) (winuΩ rvs)   = W→L (rh zero F.zero iz) (rvs zero F.zero iz)
W→L (lΩ rk rh) (wink rv)     = W→L rk rv

B₀-R : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → RelBase ℓ ℓ′ (B₀ ℓ) (F.B₀ ℓ′)
B₀-R rl j j′ w w′ rw = Ωt-R (W→L rl rw) , Ωn-R (W→L rl rw)

iterR : {X X′ : Set} (R : X → X′ → Set) {s : X → X} {s′ : X′ → X′} {x₀ : X} {x₀′ : X′}
      → R x₀ x₀′ → ((z : X) (z′ : X′) → R z z′ → R (s z) (s′ z′)) → (n : ℕ) → R (iter s x₀ n) (F.iter s′ x₀′ n)
iterR R r₀ rs zero    = r₀
iterR R r₀ rs (suc n) = rs _ _ (iterR R r₀ rs n)

node0 : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X)
        {T′ : F.Tr F.zero} {N′ : F._⊢_◃_ F.zero F.zero T′}
      → RelT zero F.zero (proj₁ (limc⁺ (λ n → G (iter s x₀ n)))) T′ × RelD zero F.zero (proj₂ (limc⁺ (λ n → G (iter s x₀ n)))) N′
      → RelT zero F.zero (proj₁ (node⁺ m G s)) T′ × RelD zero F.zero (proj₂ (node⁺ m G s)) N′
node0 nothing          G s r = r
node0 (just (() , _)) G s r

nodeLe0 : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X)
          {x′ y′ : F.Tr F.zero} {d′ : F._⊢_◃_ F.zero x′ y′} → DL zero d′ → RelD zero F.zero (nodeLe m G s) d′
nodeLe0 nothing          G s r = r
nodeLe0 (just (() , _)) G s r
```

## 保留判定

精简块的 `kp` 交出 `Maybe`, F2 的 `kp` 是续延, `kp-ind` 是它的归纳原理; 这里一并陈述: 对任意谓词 Φ, 保留时两边的槽位与换型相关则 Φ 成立, 不保留时 Φ 对默认值成立, 则 Φ 对两边的结果成立. 推进时 Φ, K, hk 照 F2 的写法改写.

```agda
mutual
  kp-R : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′
       → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
       → {Z : Set} (Q : Z → Set) (K : (q : F.Pos j′) → (F.Br j′ q → F.Br ℓ′ p′) → Z) (d : Z)
         (hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br ℓ′ p′) → F.Good ℓ′ p′ j′ q cv → Q (K q cv)) (hd : Q d)
       → (Φ : Keep j (Br ℓ p) (fromBr ℓ p zero) → (z : Z) → Q z → Set)
       → ((q : Pos j) (q′ : F.Pos j′) → RelP j j′ q q′ → (cv : Br j q → Br ℓ p) (cv′ : F.Br j′ q′ → F.Br ℓ′ p′)
          (g : cv (fromBr j q zero) ≡ fromBr ℓ p zero) (gd : F.Good ℓ′ p′ j′ q′ cv′)
          → ((z : Br j q) (z′ : F.Br j′ q′) → RelB j j′ q q′ z z′ → RelB ℓ ℓ′ p p′ (cv z) (cv′ z′))
          → Φ (just (q , cv , g)) (K q′ cv′) (hk q′ cv′ gd))
       → Φ nothing d hd
       → Φ (kp ℓ o p w) (F.kp ℓ′ ε ρ p′ w′ K d) (F.kp-ind ℓ′ ε ρ p′ w′ Q {K} {d} hk hd)
  kp-R re p p′ rp wself Q K d hk hd Φ hK hD = hK p p′ rp (λ z → z) (λ z → z) refl refl (λ z z′ r → r)
  kp-R (eS re) (inj₂ (c , t)) t′ rp (wincS rv) Q K d hk hd Φ hK hD = kp⁼-R re t t′ rp rv Q K d hk hd Φ hK hD
  kp-R (eS re) (inj₂ (c , t)) t′ rp (winuS rv) Q K d hk hd Φ hK hD = kp⁼-R re t t′ rp rv Q K d hk hd Φ hK hD
  kp-R (eL rr re) (inj₂ (m , t)) .(m , _) (iσₙ rp) (winuL rvs) Q K d hk hd Φ hK hD =
    kp⁼-R (re m) t _ rp (rvs m) Q K d hk hd Φ hK hD
  kp-R {o = o} {ρ = ρ} (eL {g = g} {g′ = g′} rr re) (inj₂ (m , t)) .(m , t′) (iσₙ {b = t′} rp) (wincL n rv) Q K d hk hd Φ hK hD
    with way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | inj₁ u | F.fwd u′ | rfwd ru =
    kp⁼-R (re n) (psh u t) (F.psh u′ t′) (psh-R ru t t′ rp) rv Q
      (λ q cv → K q (λ z → F.pshBr u′ t′ (cv z))) d
      (λ q cv gd → hk q (λ z → F.pshBr u′ t′ (cv z)) (trans (cong (F.pshBr u′ t′) gd) (F.pshFirst u′ t′))) hd
      (λ m₀ z qz → Φ (mapK (pshBr u t) (pshFirst u t) m₀) z qz)
      (λ q q′ rq cv cv′ g₀ gd rcv → hK q q′ rq (λ z → pshBr u t (cv z)) (λ z → F.pshBr u′ t′ (cv′ z))
         (trans (cong (pshBr u t) g₀) (pshFirst u t)) (trans (cong (F.pshBr u′ t′) gd) (F.pshFirst u′ t′))
         (λ z z′ r → pshBr-R ru t t′ (rcv z z′ r)))
      hD
  ... | inj₂ u | F.bwd u′ | rbwd ru = kp⁼-R (re m) t t′ rp (∙-R rv ru) Q K d hk hd Φ hK hD
  kp-R (eΩ rk rwc rc) (inj₁ t) .(inj₁ _) (i₁ rp) (wink rv) Q K d hk hd Φ hK hD = kp⁼-R rk t _ rp rv Q K d hk hd Φ hK hD
  kp-R {o = o} {ε = ε} (eΩ rk rwc rc) (inj₁ t) .(inj₁ t′) (i₁ {a = t′} rp) (wincΩ {c = c} {c′ = c′} rcc rv) Q K d hk hd Φ hK hD =
    kp⁼-R ((rc c c′ rcc)) (psh (proj₂ (proj₁ o) c) t) (F.psh (proj₁ (proj₂ ε c′)) t′) (psh-R ((rwc c c′ rcc)) t t′ rp) rv Q
      (λ q cv → K q (λ z → F.pshBr (proj₁ (proj₂ ε c′)) t′ (cv z))) d
      (λ q cv gd → hk q (λ z → F.pshBr (proj₁ (proj₂ ε c′)) t′ (cv z))
         (trans (cong (F.pshBr (proj₁ (proj₂ ε c′)) t′) gd) (F.pshFirst (proj₁ (proj₂ ε c′)) t′))) hd
      (λ m₀ z qz → Φ (mapK (pshBr (proj₂ (proj₁ o) c) t) (pshFirst (proj₂ (proj₁ o) c) t) m₀) z qz)
      (λ q q′ rq cv cv′ g₀ gd rcv → hK q q′ rq (λ z → pshBr (proj₂ (proj₁ o) c) t (cv z)) (λ z → F.pshBr (proj₁ (proj₂ ε c′)) t′ (cv′ z))
         (trans (cong (pshBr (proj₂ (proj₁ o) c) t) g₀) (pshFirst (proj₂ (proj₁ o) c) t))
         (trans (cong (F.pshBr (proj₁ (proj₂ ε c′)) t′) gd) (F.pshFirst (proj₁ (proj₂ ε c′)) t′))
         (λ z z′ r → pshBr-R ((rwc c c′ rcc)) t t′ (rcv z z′ r)))
      hD
  kp-R {o = o} {ε = ε} (eΩ rk rwc rc) (inj₁ t) .(inj₁ t′) (i₁ {a = t′} rp) (winuΩ rvs) Q K d hk hd Φ hK hD =
    kp⁼-R ((rc zero F.zero iz)) (psh (proj₂ (proj₁ o) zero) t) (F.psh (proj₁ (proj₂ ε F.zero)) t′)
      (psh-R ((rwc zero F.zero iz)) t t′ rp) (rvs zero F.zero iz) Q
      (λ q cv → K q (λ z → F.pshBr (proj₁ (proj₂ ε F.zero)) t′ (cv z))) d
      (λ q cv gd → hk q (λ z → F.pshBr (proj₁ (proj₂ ε F.zero)) t′ (cv z))
         (trans (cong (F.pshBr (proj₁ (proj₂ ε F.zero)) t′) gd) (F.pshFirst (proj₁ (proj₂ ε F.zero)) t′))) hd
      (λ m₀ z qz → Φ (mapK (pshBr (proj₂ (proj₁ o) zero) t) (pshFirst (proj₂ (proj₁ o) zero) t) m₀) z qz)
      (λ q q′ rq cv cv′ g₀ gd rcv → hK q q′ rq (λ z → pshBr (proj₂ (proj₁ o) zero) t (cv z)) (λ z → F.pshBr (proj₁ (proj₂ ε F.zero)) t′ (cv′ z))
         (trans (cong (pshBr (proj₂ (proj₁ o) zero) t) g₀) (pshFirst (proj₂ (proj₁ o) zero) t))
         (trans (cong (F.pshBr (proj₁ (proj₂ ε F.zero)) t′) gd) (F.pshFirst (proj₁ (proj₂ ε F.zero)) t′))
         (λ z z′ r → pshBr-R ((rwc zero F.zero iz)) t t′ (rcv z z′ r)))
      hD
  kp-R (eΩ rk rwc rc) (inj₂ (c , t)) .(inj₂ (c′ , t′)) (i₂ (iσ {a = c′} {b = t′} (rcc , rp))) (wink rv) Q K d hk hd Φ hK hD =
    kp⁼-R ((rc c c′ rcc)) t t′ rp (∙-R rv ((rwc c c′ rcc))) Q K d hk hd Φ hK hD
  kp-R (eΩ rk rwc rc) (inj₂ (c , t)) .(inj₂ (c′ , t′)) (i₂ (iσ {a = c′} {b = t′} (rcc , rp))) (winuΩ rvs) Q K d hk hd Φ hK hD =
    kp⁼-R ((rc c c′ rcc)) t t′ rp (rvs c c′ rcc) Q K d hk hd Φ hK hD
  kp-R (eΩ rk rwc rc) (inj₂ (c , t)) .(inj₂ (c′ , t′)) (i₂ (iσ {a = c′} {b = t′} (rcc , rp))) (wincΩ _ _) Q K d hk hd Φ hK hD = hD

  kp⁼-R : ∀ {a a′ o ε ρ} → RelE a a′ o ε ρ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′
        → ∀ {j j′} {w : j ≤ a} {w′ : F._≤_ j′ a′} → RelW w w′
        → {Z : Set} (Q : Z → Set) (K : (q : F.Pos j′) → (F.Br j′ q → F.Br⁼ a′ t′) → Z) (d : Z)
          (hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br⁼ a′ t′) → F.Good⁼ a′ t′ j′ q cv → Q (K q cv)) (hd : Q d)
        → (Φ : Keep j (Br⁼ a t) (bz⁼ a t) → (z : Z) → Q z → Set)
        → ((q : Pos j) (q′ : F.Pos j′) → RelP j j′ q q′ → (cv : Br j q → Br⁼ a t) (cv′ : F.Br j′ q′ → F.Br⁼ a′ t′)
           (g : cv (fromBr j q zero) ≡ bz⁼ a t) (gd : F.Good⁼ a′ t′ j′ q′ cv′)
           → ((z : Br j q) (z′ : F.Br j′ q′) → RelB j j′ q q′ z z′ → RelB⁼ a a′ t t′ (cv z) (cv′ z′))
           → Φ (just (q , cv , g)) (K q′ cv′) (hk q′ cv′ gd))
        → Φ nothing d hd
        → Φ (kp⁼ a o t w) (F.kp⁼ a′ ε ρ t′ w′ K d) (F.kp⁼-ind a′ ε ρ t′ w′ Q {K} {d} hk hd)
  kp⁼-R re (inj₁ _) .(inj₁ _) (i₁ _)  rw Q K d hk hd Φ hK hD = hD
  kp⁼-R re (inj₂ p) .(inj₂ _) (i₂ rp) rw Q K d hk hd Φ hK hD = kp-R re p _ rp rw Q K d hk hd Φ hK hD
```

## 折叠, 非零, 单调

`A`, `Am`: 目标第 0 层, 路径 `z≤ ℓ`, 对 F2 的 `ψ⊥`, `nz⊥`, `mono⊥`; `S`, `Sm`: 一般的目标与相关路径, 对 `ψs`, `nzs`, `monos`. `cS`, `cL`, `cΩ`: 孩子的底相关 (精简块的孩子底是父层沿 `inc c` 的折叠, F2 的是 `chB`).

```agda
mutual
  A : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
    → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
    → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
    → RelT zero F.zero (proj₁ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′)
    × RelD zero F.zero (proj₂ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)
  A re B B′ rB β rβ rn {x = zero} iz = rβ , rn
  A {ℓ} {o = o} re B B′ rB β rβ rn {x = suc x} (is r) =
    let u = A re B B′ rB β rβ rn r in next-R (ψ ℓ o B zero (z≤ ℓ) β x) (proj₁ u) (proj₂ u)
  A re B B′ rB β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (A re B B′ rB β rβ rn (rf n))) , (λ n → Am re B B′ rB β rβ rn (ra n)))
    , dt (proj₂ (A re B B′ rB β rβ rn (rf zero)) , dl)
  A {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB β rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    node0 (kp ℓ o p (z≤ ℓ)) (λ z → ψ ℓ o B zero (z≤ ℓ) β (g z)) sR
      (limc-R (λ n → ψ ℓ o B zero (z≤ ℓ) β (g (iter sR (fromBr ℓ p zero) n)))
         (λ n → proj₁ (A re B B′ rB β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (A re B B′ rB β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (A re B B′ rB β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→L re
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
    s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
    s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
    rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
    ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
    ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
           (λ z z′ rz → fromBr-R rl p p′ rp
              (proj₁ (S re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  A {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) ry
  A {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {x = up x n y e} {x′ = F.up x′ n′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) ry
  A {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in A ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) ry

  Am : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
     → RelD zero F.zero (mono ℓ o B zero (z≤ ℓ) β d) (F.mono⊥ ℓ′ ε ρ B′ d′)
  Am re B B′ rB β rβ rn {d = ◃s} ds = dl
  Am re B B′ rB β rβ rn {d = ◃l n} dl = dl
  Am {ℓ} {o = o} re B B′ rB β rβ rn {d = ◃w {p = p}} (dw _) = nodeLe0 (kp ℓ o p (z≤ ℓ)) _ _ dl
  Am {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {d = ◃u x n y e} {d′ = F.◃u x′ n′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) rye
  Am {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rr
  Am {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB β rβ rn {d = ◃c x n r} {d′ = F.◃c x′ n′ r′} (dc (rx , (refl , rr))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cL re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rr
  Am {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = A re₀ B B′ rB β rβ rn rx
    in Am ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (ψ (nd (sΩ k) h) o B zero (z≤ (nd (sΩ k) h)) β x) (proj₁ u) (proj₂ u) rr
  Am re B B′ rB β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Am re B B′ rB β rβ rn r₁ , Am re B B′ rB β rβ rn r₂)

  S : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
    → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
    → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
    → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
    → RelT j j′ (proj₁ (ψ ℓ o B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
    × RelD j j′ (proj₂ (ψ ℓ o B j w β x)) (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
  S re B B′ rB rw β rβ rn {x = zero} iz = rβ , rn
  S {ℓ} {o = o} re B B′ rB {j} {w = w} rw β rβ rn {x = suc x} (is r) =
    let u = S re B B′ rB rw β rβ rn r in next-R (ψ ℓ o B j w β x) (proj₁ u) (proj₂ u)
  S re B B′ rB rw β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (S re B B′ rB rw β rβ rn (rf n))) , (λ n → Sm re B B′ rB rw β rβ rn (ra n)))
    , dt (proj₂ (S re B B′ rB rw β rβ rn (rf zero)) , dl)
  S {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    kp-R re p p′ rp rw (λ Z → F._⊢_◃_ j′ F.zero Z) K d hk hd
      (λ m z qz → RelT j j′ (proj₁ (node⁺ m G sR)) z × RelD j j′ (proj₂ (node⁺ m G sR)) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         iw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))
         , dt (proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (rcv _ _ (br0-R (W→L rl rw) q q′ rq))))
              , dw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))))
      (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
         (λ n → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (S re B B′ rB rw β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→L re
    G : Br ℓ p → Tr⁺ j
    G z = ψ ℓ o B j w β (g z)
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
    s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
    s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
    K : (q : F.Pos j′) → (F.Br j′ q → F.Br ℓ′ p′) → F.Tr j′
    K q cv = F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z)))
    d : F.Tr j′
    d = F.limc (λ n → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
               (λ n → F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
    hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br ℓ′ p′) → F.Good ℓ′ p′ j′ q cv → F._⊢_◃_ j′ F.zero (K q cv)
    hk q cv gd = F.◃t (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv (F.br0 j′ q)))) F.◃w
    hd : F._⊢_◃_ j′ F.zero d
    hd = F.◃t (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.br0 ℓ′ p′))) (F.◃l zero)
    rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
    ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
    ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
           (λ z z′ rz → fromBr-R rl p p′ rp
              (proj₁ (S re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  -- 自身行
  S {o = o} re₀@(eS {h = h} {a = a} re) B B′ rB wself β rβ rn {x = up x c y e} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) ry
  S {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {x = up x n y e} (iu (rx , (refl , ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) ry
  S {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Up-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) ry
  -- 一致路径, 下标层侧, 后继形状进孩子 c
  S {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in S re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in S re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in S (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in S ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  S {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , _))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in S ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) ry
  -- ℕ 极限形状: 比较孩子编号
  S {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    S (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₁ (emb-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    S (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) ry
  -- Ω 形状经指定孩子: 回退
  S {o = o} {ε} {ρ} re₀@(eΩ rk rwc rc) B B′ rB {j} (wincΩ rc₁ rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (rcc , ry , rye))) =
    let r₀ = S re₀ B B′ rB (wincΩ rc₁ rv) β rβ rn rx
        re₀ = (rc c c′ rcc)
        a₀ = A re₀ (B₀ _) (F.B₀ _) (B₀-R (E→L re₀)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) ry
    in +-R (proj₁ r₀) (ι-R (proj₁ a₀)) , dt (proj₂ r₀ , +m-R (proj₁ r₀) (ιm-R (proj₂ a₀)))

  Sm : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
     → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
     → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
     → RelD j j′ (mono ℓ o B j w β d) (F.monos ℓ′ ε ρ B′ j′ w′ β′ nβ d′)
  Sm re B B′ rB rw β rβ rn {d = ◃s} ds = dl
  Sm re B B′ rB rw β rβ rn {d = ◃l n} dl = dl
  Sm {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {d = ◃w {p = p} {g = g}} {d′ = F.◃w {p = p′} {g = g′}} (dw (rp , rg)) =
    kp-R re p p′ rp rw Q K d hk hd (λ m z qz → RelD j j′ (nodeLe m G sR) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         RelD-substˡ (λ t → proj₁ (G t)) (λ _ → Ω q (λ z → proj₁ (G (cv z)))) g₀
           (RelD-substʳ (λ t → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (λ _ → F.Ω q′ (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv′ z)))) gd
             (dw (rq , λ z z′ rz → proj₁ (S re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz)))))))
      dl
    where
    G : Br ℓ p → Tr⁺ j
    G z = ψ ℓ o B j w β (g z)
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
    s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
    s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
    K : (q : F.Pos j′) → (F.Br j′ q → F.Br ℓ′ p′) → F.Tr j′
    K q cv = F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z)))
    d : F.Tr j′
    d = F.limc (λ n → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
               (λ n → F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.iter s′R (F.br0 ℓ′ p′) n)))
    Q : F.Tr j′ → Set
    Q Z = F._⊢_◃_ j′ (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (F.br0 ℓ′ p′))) Z
    hk : (q : F.Pos j′) (cv : F.Br j′ q → F.Br ℓ′ p′) → F.Good ℓ′ p′ j′ q cv → Q (K q cv)
    hk q cv gd = subst (λ t → F._⊢_◃_ j′ (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (F.Ω q (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv z))))) gd F.◃w
    hd : Q d
    hd = F.◃l zero
  -- 自身行
  Sm {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃u x c y e} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {d = ◃u x n y e} (du (rx , (refl , ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃c x c r} (dc (rx , rr)) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→L re)) (E→L re) (ddown (lS (E→L re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} re₀@(eL {g = g} rr₀ re) B B′ rB wself β rβ rn {d = ◃c x n r} (dc (rx , (refl , rr))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→L (re i))) (E→L (re n)) (ddown (lL (λ i → E→L (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} re₀@(eΩ {k = k} {h = h} rk rwc rc) B B′ rB wself β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB wself β rβ rn rx
    in Upm-R (E→L re₀) (E→L ((rc c c′ rcc))) (ddown (E→L re₀) dstop rcc)
         (ψ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (proj₁ u) (proj₂ u) rr
  -- 进孩子的各行 (◃u)
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in Sm re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in Sm re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in Sm (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) rye
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    Sm (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₂ (emb-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    Sm (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rye
  Sm {o = o} {ε} {ρ} re₀@(eΩ rk rwc rc) B B′ rB {j} (wincΩ rc₁ rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (rcc , ry , rye))) =
    let r₀ = S re₀ B B′ rB (wincΩ rc₁ rv) β rβ rn rx
        re₀ = (rc c c′ rcc)
        a₀ = A re₀ (B₀ _) (F.B₀ _) (B₀-R (E→L re₀)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) ry
    in +m-R (proj₁ r₀) (ιm-R (proj₂ a₀))
  -- 进孩子的各行 (◃c)
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = S re₀ B B′ rB (winuS rw) β rβ rn rx
    in Sm re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = S re₀ B B′ rB (wincS rv) β rβ rn rx
    in Sm re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cS re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr))) =
    let u = S re₀ B B′ rB (winuL rws) β rβ rn rx
    in Sm (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cL re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (winuΩ {vs = ws} rws) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB (winuΩ rws) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (rws c c′ rcc) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ {k = k} {h = h} {k′ = k′} {h′ = h′} rk rwc rc) B B′ rB {j} (wink {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let u = S re₀ B B′ rB (wink rv) β rβ rn rx
    in Sm ((rc c c′ rcc)) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
         (cΩ re₀ B B′ rB rx c c′ rcc) (∙-R rv ((rwc c c′ rcc))) (ψ (nd (sΩ k) h) o B j (ink v) β x) (proj₁ u) (proj₂ u) rr
  Sm {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr)))
    with S re₀ B B′ rB rw₀ β rβ rn rx | cL re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr₀ m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    Sm (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (emb-mono-R (re n) ru rr)
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    Sm (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rr
  Sm {o = o} {ε} {ρ} re₀@(eΩ rk rwc rc) B B′ rB {j} (wincΩ rc₁ rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , (rcc , rr))) =
    let r₀ = S re₀ B B′ rB (wincΩ rc₁ rv) β rβ rn rx
        re₀ = (rc c c′ rcc)
    in +m-R (proj₁ r₀) (ιm-R (Am re₀ (B₀ _) (F.B₀ _) (B₀-R (E→L re₀)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) rr))
  Sm re B B′ rB rw β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (Sm re B B′ rB rw β rβ rn r₁ , Sm re B B′ rB rw β rβ rn r₂)

  cS : ∀ {h a o ε ρ} → (re : RelE (nd sS h) (F.suc a) o ε ρ) → (B : Base (nd sS h)) (B′ : F.Base (F.suc a))
     → RelBase (nd sS h) (F.suc a) B B′ → {x : Tr (nd sS h)} {x′ : F.Tr (F.suc a)} → RelT (nd sS h) (F.suc a) x x′ → (c : ⊤)
     → RelBase (h c) a (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′)
  cS re B B′ rB rx c i i′ w w′ rw =
    let rb = rB i i′ (inc c w) (F.ins w′) (wincS rw) in S re B B′ rB (wincS rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx

  cL : ∀ {g g′ o ε ρ} → (re : RelE (nd sL g) (F.lim g′) o ε ρ) → (B : Base (nd sL g)) (B′ : F.Base (F.lim g′))
     → RelBase (nd sL g) (F.lim g′) B B′ → {x : Tr (nd sL g)} {x′ : F.Tr (F.lim g′)} → RelT (nd sL g) (F.lim g′) x x′ → (n : ℕ)
     → RelBase (g n) (g′ n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′)
  cL re B B′ rB rx n i i′ w w′ rw =
    let rb = rB i i′ (inc n w) (F.inl n w′) (wincL n rw) in S re B B′ rB (wincL n rw) (B i (inc n w)) (proj₁ rb) (proj₂ rb) rx

  cΩ : ∀ {k h k′ h′ o ε ρ} → (re : RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ) → (B : Base (nd (sΩ k) h)) (B′ : F.Base (F.Ωₗ k′ h′))
     → RelBase (nd (sΩ k) h) (F.Ωₗ k′ h′) B B′ → {x : Tr (nd (sΩ k) h)} {x′ : F.Tr (F.Ωₗ k′ h′)} → RelT (nd (sΩ k) h) (F.Ωₗ k′ h′) x x′
     → (c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′
     → RelBase (h c) (h′ c′) (λ i w → ψ (nd (sΩ k) h) o B i (inc c w) (B i (inc c w)) x) (F.dW k′ h′ ε ρ B′ c′ x′)
  cΩ re B B′ rB rx c c′ rcc i i′ w w′ rw =
    let rb = rB i i′ (inc c w) (F.inb c′ w′) (wincΩ rcc rw) in S re B B′ rB (wincΩ rcc rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx
```
