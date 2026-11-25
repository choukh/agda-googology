# 龙骨原型对 F2: 不含 Ω 形状的层号上的逐层关系

> 验收文件 (工具). `YiKARel` 换成原型折叠 (`YiKDPath`, `YiKDFold`) 后逐行照旧编译: 原型在不含 Ω 形状的层号上各行与候选 A 同式. 编译定理, 无前提: `RelEK`, `AK`, `AmK`, `SK`, `SmK`, `h₁-EK`.
> 不涉及 Ω 形状的层号, 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiKDFold
open import OCF.Lean.YiCertFold using (Base; B₀; Keep; mapK; node⁺; nodeLe)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBRLem hiding (E→L; E-at; E-at⁼)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRFold using (W→L; iterR)
open import OCF.Lean.YiBRTw using (◃→⊑-V; wk-V; ⊕⊑-V; RelEO; oz; oS; oL)
```

## 证据

```agda
data RelEK : (ℓ : L) (ℓ′ : F.L) → Ok ℓ → F.Ev ℓ′ → F.Rt ℓ′ → Set where
  ez : ∀ {o ε ρ} → RelEK zero F.zero o ε ρ
  eS : ∀ {h a} {o : Ok (nd sS h)} {ε : F.Ev a} {ρ : F.Rt a}
     → RelEK (h tt) a (proj₂ o tt) ε ρ → RelEK (nd sS h) (F.suc a) o ε ρ
  eL : ∀ {g g′} {o : Ok (nd sL g)} {ε : F.Ev (F.lim g′)} {ρ : F.Rt (F.lim g′)}
     → ((n : ℕ) → RelW (proj₁ o n) (proj₂ ρ n)) → ((n : ℕ) → RelEK (g n) (g′ n) (proj₂ o n) (ε n) (proj₁ ρ n))
     → RelEK (nd sL g) (F.lim g′) o ε ρ

E→LK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → RelL ℓ ℓ′
E→LK ez        = lz
E→LK (eS re)   = lS (E→LK re)
E→LK (eL _ re) = lL (λ n → E→LK (re n))

B₀-RK : ∀ {ℓ ℓ′} → RelL ℓ ℓ′ → RelBase ℓ ℓ′ (B₀ ℓ) (F.B₀ ℓ′)
B₀-RK rl j j′ w w′ rw = Ωt-R (W→L rl rw) , Ωn-R (W→L rl rw)
```

## 读出层号的证据

```agda
data RelEOK (a : L) (a′ : F.L) : (b : L) (b′ : F.L) → OkO a b → F.EvO a′ b′ → F.RtP b′ → Set where
  oz : ∀ {e eo rp} → RelEOK a a′ zero F.zero e eo rp
  oS : ∀ {h b′} {e : OkO a (nd sS h)} {eo : F.EvO a′ b′} {rp : F.RtP b′}
     → RelEOK a a′ (h tt) b′ (proj₂ e tt) eo rp → RelEOK a a′ (nd sS h) (F.suc b′) e eo rp
  oL : ∀ {g g′} {e : OkO a (nd sL g)} {eo : F.EvO a′ (F.lim g′)} {rp : F.RtP (F.lim g′)}
     → ((n : ℕ) → RelV (proj₁ e n) (proj₂ rp n)) → ((n : ℕ) → RelEOK a a′ (g n) (g′ n) (proj₂ e n) (eo n) (proj₁ rp n))
     → RelEOK a a′ (nd sL g) (F.lim g′) e eo rp

⊕-EK : ∀ {a a′ oa ea ra b b′ e eo rp} → RelEK a a′ oa ea ra → RelEOK a a′ b b′ e eo rp
     → RelEK (a ⊕ b) (a′ F.⊕ b′) (Ok⊕ a b oa e) (F.Ev⊕ a′ b′ ea eo) (F.Rt⊕ a′ b′ ra rp)
⊕-EK re oz        = re
⊕-EK re (oS r)    = eS (⊕-EK re r)
⊕-EK re (oL rv r) = eL (λ n → wk-V (⊕⊑-V (rv n))) (λ n → ⊕-EK re (r n))

↑-EOK₀ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′
       → RelEOK zero F.zero (↑ zero x) (F.↑ F.zero x′) (OkO↑ zero zero tt self x) (F.EvO↑ F.zero F.zero tt F.self x′) (F.RtP↑ F.zero tt x′)
↑-EOK₀ {x = zero}    iz             = oz
↑-EOK₀ {x = suc x}   (is r)         = oS (↑-EOK₀ r)
↑-EOK₀ {x = lim f a} (il (rf , ra)) = oL (λ n → ◃→⊑-V lz (ra n)) (λ n → ↑-EOK₀ (rf n))

h₁-EK : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′
      → RelEK (zero ⊕ ↑ zero x) (F.zero F.⊕ F.↑ F.zero x′)
          (Ok⊕ zero (↑ zero x) tt (OkO↑ zero zero tt self x))
          (F.Ev⊕ F.zero (F.↑ F.zero x′) tt (F.EvO↑ F.zero F.zero tt F.self x′))
          (F.Rt⊕ F.zero (F.↑ F.zero x′) tt (F.RtP↑ F.zero tt x′))
h₁-EK r = ⊕-EK ez (↑-EOK₀ r)
```

## 结点, 保留判定

```agda
node0K : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X)
         {T′ : F.Tr F.zero} {N′ : F._⊢_◃_ F.zero F.zero T′}
       → RelT zero F.zero (proj₁ (limc⁺ (λ n → G (iter s x₀ n)))) T′ × RelD zero F.zero (proj₂ (limc⁺ (λ n → G (iter s x₀ n)))) N′
       → RelT zero F.zero (proj₁ (node⁺ m G s)) T′ × RelD zero F.zero (proj₂ (node⁺ m G s)) N′
node0K nothing          G s r = r
node0K (just (() , _)) G s r

nodeLe0K : {X : Set} {x₀ : X} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X)
           {x′ y′ : F.Tr F.zero} {d′ : F._⊢_◃_ F.zero x′ y′} → DL zero d′ → RelD zero F.zero (nodeLe m G s) d′
nodeLe0K nothing          G s r = r
nodeLe0K (just (() , _)) G s r

mutual
  kp-RK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → (p : Pos ℓ) (p′ : F.Pos ℓ′) → RelP ℓ ℓ′ p p′
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
  kp-RK re p p′ rp wself Q K d hk hd Φ hK hD = hK p p′ rp (λ z → z) (λ z → z) refl refl (λ z z′ r → r)
  kp-RK (eS re) (inj₂ (c , t)) t′ rp (wincS rv) Q K d hk hd Φ hK hD = kp⁼-RK re t t′ rp rv Q K d hk hd Φ hK hD
  kp-RK (eS re) (inj₂ (c , t)) t′ rp (winuS rv) Q K d hk hd Φ hK hD = kp⁼-RK re t t′ rp rv Q K d hk hd Φ hK hD
  kp-RK (eL rr re) (inj₂ (m , t)) .(m , _) (iσₙ rp) (winuL rvs) Q K d hk hd Φ hK hD =
    kp⁼-RK (re m) t _ rp (rvs m) Q K d hk hd Φ hK hD
  kp-RK {o = o} {ρ = ρ} (eL {g = g} {g′ = g′} rr re) (inj₂ (m , t)) .(m , t′) (iσₙ {b = t′} rp) (wincL n rv) Q K d hk hd Φ hK hD
    with way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | inj₁ u | F.fwd u′ | rfwd ru =
    kp⁼-RK (re n) (psh u t) (F.psh u′ t′) (psh-R ru t t′ rp) rv Q
      (λ q cv → K q (λ z → F.pshBr u′ t′ (cv z))) d
      (λ q cv gd → hk q (λ z → F.pshBr u′ t′ (cv z)) (trans (cong (F.pshBr u′ t′) gd) (F.pshFirst u′ t′))) hd
      (λ m₀ z qz → Φ (mapK (pshBr u t) (pshFirst u t) m₀) z qz)
      (λ q q′ rq cv cv′ g₀ gd rcv → hK q q′ rq (λ z → pshBr u t (cv z)) (λ z → F.pshBr u′ t′ (cv′ z))
         (trans (cong (pshBr u t) g₀) (pshFirst u t)) (trans (cong (F.pshBr u′ t′) gd) (F.pshFirst u′ t′))
         (λ z z′ r → pshBr-R ru t t′ (rcv z z′ r)))
      hD
  ... | inj₂ u | F.bwd u′ | rbwd ru = kp⁼-RK (re m) t t′ rp (∙-R rv ru) Q K d hk hd Φ hK hD

  kp⁼-RK : ∀ {a a′ o ε ρ} → RelEK a a′ o ε ρ → (t : Pos⁼ a) (t′ : F.Pos⁼ a′) → RelP⁼ a a′ t t′
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
  kp⁼-RK re (inj₁ _) .(inj₁ _) (i₁ _)  rw Q K d hk hd Φ hK hD = hD
  kp⁼-RK re (inj₂ p) .(inj₂ _) (i₂ rp) rw Q K d hk hd Φ hK hD = kp-RK re p _ rp rw Q K d hk hd Φ hK hD
```

## 嵌入

```agda
embK-R : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → ∀ {k k′} {v : k ≤ ℓ} {v′ : F._≤_ k′ ℓ′} → RelW v v′
       → (y : Tr⁺ k) {y′ : F.Tr k′} {nz : F._⊢_◃_ k′ F.zero y′} → RelT k k′ (proj₁ y) y′ → RelD k k′ (proj₂ y) nz
       → RelT ℓ ℓ′ (proj₁ (emb ℓ o v y)) (F.emb ℓ′ ε v′ y′ nz) × RelD ℓ ℓ′ (proj₂ (emb ℓ o v y)) (F.emb-nz ℓ′ ε v′ y′ nz)
embK-R re wself y ry rn = ry , rn
embK-R (eS re) (wincS rv) y ry rn = let r = embK-R re rv y ry rn in iu (iz , r) , du (iz , r)
embK-R (eS re) (winuS rv) y ry rn = let r = embK-R re rv y ry rn in iu (iz , r) , du (iz , r)
embK-R (eL rr re) (wincL n rv) y ry rn = let r = embK-R (re n) rv y ry rn in iu (iz , (refl , r)) , du (iz , (refl , r))
embK-R (eL rr re) (winuL rvs) y ry rn =
  let r = embK-R (re zero) (rvs zero) y ry rn in iu (iz , (refl , r)) , du (iz , (refl , r))

embK-mono-R : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → ∀ {k k′} {v : k ≤ ℓ} {v′ : F._≤_ k′ ℓ′} → RelW v v′
  → {y₁ y₂ : Tr⁺ k} {y₁′ y₂′ : F.Tr k′} {n₁ : F._⊢_◃_ k′ F.zero y₁′} {n₂ : F._⊢_◃_ k′ F.zero y₂′}
  → {d : k ⊢ proj₁ y₁ ◃ proj₁ y₂} {d′ : F._⊢_◃_ k′ y₁′ y₂′} → RelD k k′ d d′
  → RelD ℓ ℓ′ (emb-mono ℓ o v {y₁} {y₂} d) (F.emb-mono ℓ′ ε v′ {n′ = n₁} {n = n₂} d′)
embK-mono-R re wself rd = rd
embK-mono-R (eS re) (wincS rv) rd = dc (iz , embK-mono-R re rv rd)
embK-mono-R (eS re) (winuS rv) rd = dc (iz , embK-mono-R re rv rd)
embK-mono-R (eL rr re) (wincL n rv) rd = dc (iz , (refl , embK-mono-R (re n) rv rd))
embK-mono-R (eL rr re) (winuL rvs) rd = dc (iz , (refl , embK-mono-R (re zero) (rvs zero) rd))
```

## 折叠, 非零, 单调

```agda
mutual
  AK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
     → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
     → RelT zero F.zero (proj₁ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′)
     × RelD zero F.zero (proj₂ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)
  AK re B B′ rB β rβ rn {x = zero} iz = rβ , rn
  AK {ℓ} {o = o} re B B′ rB β rβ rn {x = suc x} (is r) =
    let u = AK re B B′ rB β rβ rn r in next-R (ψ ℓ o B zero (z≤ ℓ) β x) (proj₁ u) (proj₂ u)
  AK re B B′ rB β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (AK re B B′ rB β rβ rn (rf n))) , (λ n → AmK re B B′ rB β rβ rn (ra n)))
    , dt (proj₂ (AK re B B′ rB β rβ rn (rf zero)) , dl)
  AK {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB β rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    node0K (kp ℓ o p (z≤ ℓ)) (λ z → ψ ℓ o B zero (z≤ ℓ) β (g z)) sR
      (limc-R (λ n → ψ ℓ o B zero (z≤ ℓ) β (g (iter sR (fromBr ℓ p zero) n)))
         (λ n → proj₁ (AK re B B′ rB β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (AK re B B′ rB β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (AK re B B′ rB β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→LK re
    sR : Br ℓ p → Br ℓ p
    sR z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))
    s′R : F.Br ℓ′ p′ → F.Br ℓ′ p′
    s′R z′ = F.fromBr ℓ′ p′ (F.ψs ℓ′ ε ρ B′ (F.at ℓ′ p′) (F.posW ℓ′ p′) (F.bs B′ (F.at ℓ′ p′) (F.posW ℓ′ p′))
                (F.ns B′ (F.at ℓ′ p′) (F.posW ℓ′ p′)) (g′ z′))
    rb = rB (at ℓ p) (F.at ℓ′ p′) (posW ℓ p) (F.posW ℓ′ p′) (posW-R rl p p′ rp)
    ch : (n : ℕ) → RelB ℓ ℓ′ p p′ (iter sR (fromBr ℓ p zero) n) (F.iter s′R (F.br0 ℓ′ p′) n)
    ch = iterR (RelB ℓ ℓ′ p p′) (br0-R rl p p′ rp)
           (λ z z′ rz → fromBr-R rl p p′ rp
              (proj₁ (SK re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  AK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) ry
  AK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {x = up x n y e} {x′ = F.up x′ n′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cLK re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) ry

  AmK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
      → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
      → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
      → RelD zero F.zero (mono ℓ o B zero (z≤ ℓ) β d) (F.mono⊥ ℓ′ ε ρ B′ d′)
  AmK re B B′ rB β rβ rn {d = ◃s} ds = dl
  AmK re B B′ rB β rβ rn {d = ◃l n} dl = dl
  AmK {ℓ} {o = o} re B B′ rB β rβ rn {d = ◃w {p = p}} (dw _) = nodeLe0K (kp ℓ o p (z≤ ℓ)) _ _ dl
  AmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rye
  AmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB β rβ rn {d = ◃u x n y e} {d′ = F.◃u x′ n′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AmK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cLK re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rye
  AmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         (ψ (nd sS h) o B zero (z≤ (nd sS h)) β x) (proj₁ u) (proj₂ u) rr
  AmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB β rβ rn {d = ◃c x n r} {d′ = F.◃c x′ n′ r′} (dc (rx , (refl , rr))) =
    let u = AK re₀ B B′ rB β rβ rn rx
    in AmK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cLK re₀ B B′ rB rx n)
         (ψ (nd sL g) o B zero (z≤ (nd sL g)) β x) (proj₁ u) (proj₂ u) rr
  AmK re B B′ rB β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (AmK re B B′ rB β rβ rn r₁ , AmK re B B′ rB β rβ rn r₂)

  SK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
     → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
     → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
     → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
     → RelT j j′ (proj₁ (ψ ℓ o B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
     × RelD j j′ (proj₂ (ψ ℓ o B j w β x)) (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
  SK re B B′ rB rw β rβ rn {x = zero} iz = rβ , rn
  SK {ℓ} {o = o} re B B′ rB {j} {w = w} rw β rβ rn {x = suc x} (is r) =
    let u = SK re B B′ rB rw β rβ rn r in next-R (ψ ℓ o B j w β x) (proj₁ u) (proj₂ u)
  SK re B B′ rB rw β rβ rn {x = lim f a} (il (rf , ra)) =
    il ((λ n → proj₁ (SK re B B′ rB rw β rβ rn (rf n))) , (λ n → SmK re B B′ rB rw β rβ rn (ra n)))
    , dt (proj₂ (SK re B B′ rB rw β rβ rn (rf zero)) , dl)
  SK {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {x = Ω p g} {x′ = F.Ω p′ g′} (iw (rp , rg)) =
    kp-RK re p p′ rp rw (λ Z → F._⊢_◃_ j′ F.zero Z) K d hk hd
      (λ m z qz → RelT j j′ (proj₁ (node⁺ m G sR)) z × RelD j j′ (proj₂ (node⁺ m G sR)) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         iw (rq , λ z z′ rz → proj₁ (SK re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))
         , dt (proj₂ (SK re B B′ rB rw β rβ rn (rg _ _ (rcv _ _ (br0-R (W→L rl rw) q q′ rq))))
              , dw (rq , λ z z′ rz → proj₁ (SK re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz))))))
      (limc-R (λ n → G (iter sR (fromBr ℓ p zero) n))
         (λ n → proj₁ (SK re B B′ rB rw β rβ rn (rg _ _ (ch n)))) (λ n → proj₂ (SK re B B′ rB rw β rβ rn (rg _ _ (ch n))))
       , dt (proj₂ (SK re B B′ rB rw β rβ rn (rg _ _ (ch zero))) , dl))
    where
    rl : RelL ℓ ℓ′
    rl = E→LK re
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
              (proj₁ (SK re B B′ rB (posW-R rl p p′ rp) (B (at ℓ p) (posW ℓ p)) (proj₁ rb) (proj₂ rb) (rg z z′ rz))))
  -- 自身行
  SK {o = o} re₀@(eS {h = h} {a = a} re) B B′ rB wself β rβ rn {x = up x c y e} (iu (rx , (ry , _))) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Up-R (lS (E→LK re)) (E→LK re) (ddown (lS (E→LK re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) ry
  SK {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {x = up x n y e} (iu (rx , (refl , ry , _))) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Up-R (lL (λ i → E→LK (re i))) (E→LK (re n)) (ddown (lL (λ i → E→LK (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) ry
  -- 一致路径, 后继形状进孩子
  SK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = SK re₀ B B′ rB (winuS rw) β rβ rn rx
    in SK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  SK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {x = up x c y e} {x′ = F.up x′ c′ y′ e′} (iu (rx , (ry , _))) =
    let u = SK re₀ B B′ rB (wincS rv) β rβ rn rx
    in SK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) ry
  SK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , _))) =
    let u = SK re₀ B B′ rB (winuL rws) β rβ rn rx
    in SK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cLK re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) ry
  -- ℕ 极限形状: 比较孩子编号
  SK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {x = up x m y e} {x′ = F.up x′ m′ y′ e′} (iu (rx , (refl , ry , rye)))
    with SK re₀ B B′ rB rw₀ β rβ rn rx | cLK re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    SK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₁ (embK-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    SK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) ry

  SmK : ∀ {ℓ ℓ′ o ε ρ} → RelEK ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
      → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
      → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
      → {x y : Tr ℓ} {x′ y′ : F.Tr ℓ′} {d : ℓ ⊢ x ◃ y} {d′ : F._⊢_◃_ ℓ′ x′ y′} → RelD ℓ ℓ′ d d′
      → RelD j j′ (mono ℓ o B j w β d) (F.monos ℓ′ ε ρ B′ j′ w′ β′ nβ d′)
  SmK re B B′ rB rw β rβ rn {d = ◃s} ds = dl
  SmK re B B′ rB rw β rβ rn {d = ◃l n} dl = dl
  SmK {ℓ} {ℓ′} {o} {ε} {ρ} re B B′ rB {j} {j′} {w} {w′} rw β {β′} {nβ} rβ rn {d = ◃w {p = p} {g = g}} {d′ = F.◃w {p = p′} {g = g′}} (dw (rp , rg)) =
    kp-RK re p p′ rp rw Q K d hk hd (λ m z qz → RelD j j′ (nodeLe m G sR) qz)
      (λ q q′ rq cv cv′ g₀ gd rcv →
         RelD-substˡ (λ t → proj₁ (G t)) (λ _ → Ω q (λ z → proj₁ (G (cv z)))) g₀
           (RelD-substʳ (λ t → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ t)) (λ _ → F.Ω q′ (λ z → F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ (g′ (cv′ z)))) gd
             (dw (rq , λ z z′ rz → proj₁ (SK re B B′ rB rw β rβ rn (rg _ _ (rcv z z′ rz)))))))
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
  SmK {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃u x c y e} (du (rx , (ry , rye))) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→LK re)) (E→LK re) (ddown (lS (E→LK re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rye
  SmK {o = o} re₀@(eL {g = g} rr re) B B′ rB wself β rβ rn {d = ◃u x n y e} (du (rx , (refl , ry , rye))) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→LK (re i))) (E→LK (re n)) (ddown (lL (λ i → E→LK (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rye
  SmK {o = o} re₀@(eS {h = h} re) B B′ rB wself β rβ rn {d = ◃c x c r} (dc (rx , rr)) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lS (E→LK re)) (E→LK re) (ddown (lS (E→LK re)) dstop tt) (ψ (nd sS h) o B (nd sS h) self β x) (proj₁ u) (proj₂ u) rr
  SmK {o = o} re₀@(eL {g = g} rr₀ re) B B′ rB wself β rβ rn {d = ◃c x n r} (dc (rx , (refl , rr))) =
    let u = SK re₀ B B′ rB wself β rβ rn rx
    in Upm-R (lL (λ i → E→LK (re i))) (E→LK (re n)) (ddown (lL (λ i → E→LK (re i))) dstop refl)
         (ψ (nd sL g) o B (nd sL g) self β x) (proj₁ u) (proj₂ u) rr
  -- 进孩子的各行 (◃u)
  SmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = SK re₀ B B′ rB (winuS rw) β rβ rn rx
    in SmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  SmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃u x c y e} {d′ = F.◃u x′ c′ y′ e′} (du (rx , (ry , rye))) =
    let u = SK re₀ B B′ rB (wincS rv) β rβ rn rx
    in SmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rye
  SmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye))) =
    let u = SK re₀ B B′ rB (winuL rws) β rβ rn rx
    in SmK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cLK re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rye
  SmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃u x m y e} {d′ = F.◃u x′ m′ y′ e′} (du (rx , (refl , ry , rye)))
    with SK re₀ B B′ rB rw₀ β rβ rn rx | cLK re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    SmK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (proj₂ (embK-R (re n) ru (y , e) ry rye))
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    SmK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rye
  -- 进孩子的各行 (◃c)
  SmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (winuS {vs = ws} rw) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = SK re₀ B B′ rB (winuS rw) β rβ rn rx
    in SmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rw (ψ (nd sS h) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  SmK {o = o} {ε} {ρ} re₀@(eS {h = h} {a = a} re) B B′ rB {j} (wincS {c = c₁} {v = v} rv) β rβ rn {d = ◃c x c r} {d′ = F.◃c x′ c′ r′} (dc (rx , rr)) =
    let u = SK re₀ B B′ rB (wincS rv) β rβ rn rx
    in SmK re (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′) (cSK re₀ B B′ rB rx c)
         rv (ψ (nd sS h) o B j (inc c₁ v) β x) (proj₁ u) (proj₂ u) rr
  SmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} (winuL {vs = ws} rws) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr))) =
    let u = SK re₀ B B′ rB (winuL rws) β rβ rn rx
    in SmK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cLK re₀ B B′ rB rx m)
         (rws m) (ψ (nd sL g) o B j (inu ws) β x) (proj₁ u) (proj₂ u) rr
  SmK {o = o} {ε} {ρ} re₀@(eL {g = g} {g′ = g′} rr₀ re) B B′ rB {j} rw₀@(wincL n {v = v} rv) β rβ rn {d = ◃c x m r} {d′ = F.◃c x′ m′ r′} (dc (rx , (refl , rr)))
    with SK re₀ B B′ rB rw₀ β rβ rn rx | cLK re₀ B B′ rB rx | way g (proj₁ o) m n | F.way g′ (proj₂ ρ) m n | way-R rr₀ m n
  ... | r₀ | cB | inj₁ u | F.fwd u′ | rfwd ru =
    SmK (re n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′) (cB n)
      rv (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) (embK-mono-R (re n) ru rr)
  ... | r₀ | cB | inj₂ u | F.bwd u′ | rbwd ru =
    SmK (re m) (λ i w → ψ (nd sL g) o B i (inc m w) (B i (inc m w)) x) (F.dL g′ ε ρ B′ m x′) (cB m)
      (∙-R rv ru) (ψ (nd sL g) o B j (inc n v) β x) (proj₁ r₀) (proj₂ r₀) rr
  SmK re B B′ rB rw β rβ rn {d = ◃t d₁ d₂} (dt (r₁ , r₂)) = dt (SmK re B B′ rB rw β rβ rn r₁ , SmK re B B′ rB rw β rβ rn r₂)

  cSK : ∀ {h a o ε ρ} → (re : RelEK (nd sS h) (F.suc a) o ε ρ) → (B : Base (nd sS h)) (B′ : F.Base (F.suc a))
      → RelBase (nd sS h) (F.suc a) B B′ → {x : Tr (nd sS h)} {x′ : F.Tr (F.suc a)} → RelT (nd sS h) (F.suc a) x x′ → (c : ⊤)
      → RelBase (h c) a (λ i w → ψ (nd sS h) o B i (inc c w) (B i (inc c w)) x) (F.dS a ε ρ B′ x′)
  cSK re B B′ rB rx c i i′ w w′ rw =
    let rb = rB i i′ (inc c w) (F.ins w′) (wincS rw) in SK re B B′ rB (wincS rw) (B i (inc c w)) (proj₁ rb) (proj₂ rb) rx

  cLK : ∀ {g g′ o ε ρ} → (re : RelEK (nd sL g) (F.lim g′) o ε ρ) → (B : Base (nd sL g)) (B′ : F.Base (F.lim g′))
      → RelBase (nd sL g) (F.lim g′) B B′ → {x : Tr (nd sL g)} {x′ : F.Tr (F.lim g′)} → RelT (nd sL g) (F.lim g′) x x′ → (n : ℕ)
      → RelBase (g n) (g′ n) (λ i w → ψ (nd sL g) o B i (inc n w) (B i (inc n w)) x) (F.dL g′ ε ρ B′ n x′)
  cLK re B B′ rB rx n i i′ w w′ rw =
    let rb = rB i i′ (inc n w) (F.inl n w′) (wincL n rw) in SK re B B′ rB (wincL n rw) (B i (inc n w)) (proj₁ rb) (proj₂ rb) rx
```
