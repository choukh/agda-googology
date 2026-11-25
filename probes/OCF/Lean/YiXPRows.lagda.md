# 槽位标签作参数: 结点、上折、路径证据、自身、嵌入各行

> 验收文件 (读记号)。编译定理 (条件): `YiGTNode`, `YiGTUp`, `YiGTIndex`, `YiGTSelf`, `YiGTEmb` 的各行对任意槽位标签 `Lab` 成立, 前提仍是框架 `NodeFrame`, `UpFrame` 与路径证据 `IndexOK`。
> 来源: 逐行搬自上述五个文件, 关系换成 [YiXPRel](YiXPRel.lagda.md) 的 `R`, 槽位余尾换成 `Lab (at ℓ p)`; 只有 `KeepSpec` 改写成对 `Keep` 的一般形式 `KeepG` (内容不变), 好让孩子层的递归定义性地对上。
> 证明不用 `Lab` 的任何性质; 框架有无居民取决于 `Lab` (见 [YiXPFrame](YiXPFrame.lagda.md))。不否定什么。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.YiRWBlock using (L)
import OCF.Align.EboLeanDef as E
module OCF.Lean.YiXPRows (Lab : L → E.T → Set) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLKIface using (OK; feed; updated-ok)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiANFam using (Pen; cofG; fsnG)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiTSNote using (gt0)
open import OCF.Lean.YiGTGen using (app≤ν; Ω≤ψ)
import OCF.Lean.YiHCRel as H
open import OCF.Lean.YiXPRel Lab
```

## Ω 行 (来源 `YiGTNode`)

```agda
KeepG : ∀ j (ν : E.T) {X : Set} {x₀ : X} → (E.T → X → Set) → (κ : E.T) → Keep j X x₀ → Set
KeepG j ν LX κ nothing = E.cmpᵀ (E.sucT κ) ν ≡ E.gt
KeepG j ν LX κ (just (q , cv , eq)) =
  Pen (E.cmpᵀ (E.sucT κ) ν) × Lab (at j q) κ × (∀ η c → Low j q η c → LX η (cv c))

KeepSpec : ∀ ℓ j ν (p : Pos ℓ) κ → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set
KeepSpec ℓ j ν p κ K = KeepG j ν (Low ℓ p) κ K

NodeFrame : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
NodeFrame ℓ o j w ν = (p : Pos ℓ) (κ : E.T) → Lab (at ℓ p) κ
  → KeepSpec ℓ j ν p κ (kp ℓ o p w)

start-prefix : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) t → PrefixU B t
  → (p : Pos ℓ) (κ : E.T) → Lab (at ℓ p) κ → (g : Br ℓ p → Tr ℓ)
  → Low ℓ p (E.Ωt κ) (feed ℓ o r B p g (fromBr ℓ p zero))
start-prefix ℓ o r B t pref p κ nu g = low-from ℓ p
  (weakenᴿ (at ℓ p) (closeᴿ (at ℓ p) (Ω≤ψ κ t) (pref p κ nu))
    (ψ-⊵ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p))
      (g (fromBr ℓ p zero))))

chain′ : ∀ ℓ → StepU′ ℓ → (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → ∀ a (p : Pos ℓ) κ → Lab (at ℓ p) κ → E.cof a ≡ E.cΩ κ
  → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → Low ℓ p η c → R ℓ (E.fsT a η) (g c))
  → ∀ n → Low ℓ p (E.γT (t ++ a) κ n)
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))
chain′ ℓ st o r B gb t pref a p κ nu e g hg zero = start-prefix ℓ o r B t pref p κ nu g
chain′ ℓ st o r B gb t pref a p κ nu e g hg (suc n) =
  st o r B gb t pref a p κ nu e g n
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))
    (chain′ ℓ st o r B gb t pref a p κ nu e g hg n)
    (hg (E.γT (t ++ a) κ n) _ (chain′ ℓ st o r B gb t pref a p κ nu e g hg n))

ChainAt : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set
ChainAt ℓ o r B t a p κ g = ∀ n → Low ℓ p (E.γT (t ++ a) κ n)
  (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

module Core (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (β : Tr⁺ j) where
  F : Tr ℓ → Tr⁺ j
  F x = ψ ℓ o r B j w β x

  node-at : ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Lab (at ℓ p) κ
    → (∀ η c → Low ℓ p η c → R ℓ (E.fsT a η) (g c))
    → (∀ η c → Low ℓ p η c → R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → (K : Keep j (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ j ν p κ K
    → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ K (λ c → F (g c)) (feed ℓ o r B p g)))
  node-at p {a} {κ} g e nu hg bh hc (just (q , cv , eq)) (pen , nuq , low) =
    nodeψ j ν t a q e pen nuq (λ η c lc → bh η (cv c) (low η c lc))
  node-at p {a} {κ} g e nu hg bh hc nothing gt =
    limᴿ j (cofG ν (t ++ a) gt (cof++Ω t a e))
      (λ n → subst (λ z → R j z
        (proj₁ (limc⁺ (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))))))
        (sym (trans (fsnG ν (t ++ a) n gt (cof++Ω t a e))
          (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a (E.γT (t ++ a) κ n) e))))
        (cumᴿ j (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))) (suc n)
          (bh (E.γT (t ++ a) κ n) _ (hc n))))

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Lab (at ℓ p) κ
    → (∀ η c → Low ℓ p η c → R ℓ (E.fsT a η) (g c))
    → (∀ η c → Low ℓ p η c → R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
  node-row frame p {κ = κ} g e nu hg bh hc = node-at p g e nu hg bh hc (kp ℓ o p w) (frame p κ nu)

module Row (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (gb : OK B) (pref : PrefixU B t) (st : StepU′ ℓ) (β : Tr⁺ j) where
  open Core ℓ j o r B w ν t β using (F)

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Lab (at ℓ p) κ
    → (∀ η c → Low ℓ p η c → R ℓ (E.fsT a η) (g c))
    → (∀ η c → Low ℓ p η c → R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
  node-row fr p {a} {κ} g e nu hg bh = Core.node-row ℓ j o r B w ν t β fr p g e nu hg bh
    (chain′ ℓ st o r B gb t pref a p κ nu e g hg)
```

## 上折 (来源 `YiGTUp`)

```agda
UpFrame : ∀ {ℓ} → E.T → (j : L) → Dn ℓ j → Set
UpFrame {ℓ} ν j d = (p : Pos j) (κ : E.T) → Lab (at j p) κ
  → Pen (E.cmpᵀ (E.sucT κ) ν) × Lab (at ℓ (mv d p)) κ
    × (∀ η c → Low ℓ (mv d p) η c → Low j p η (mvBr d p c))

down-frame : ∀ {ℓ} ν s h (d : Dn ℓ (nd s h)) → UpFrame ν (nd s h) d
  → (c : Ch s) → UpFrame ν (h c) (down d c)
down-frame ν s h d fr c p κ nu = fr (inj₂ (c , inj₂ p)) κ nu

up-zero : ∀ {ℓ} ν (d : Dn ℓ zero) t (β : Tr⁺ ℓ)
  → R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → R zero a x
  → R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up zero d β x))
up-zero {ℓ} ν d t β mb (H.mz {x = x}) =
  ++[] (λ z → R ℓ (E.ψ ν z ∷ []) (proj₁ (Up zero d β x))) t
    (zlᴿ ℓ (λ y → proj₁ (Up zero d β y)) (Upm zero d β) mb x)
up-zero {ℓ} ν d t β mb (H.m1 {t = a} {x = x} e m) =
  nextψ ℓ ν t a e (Up zero d β x) (up-zero ν d t β mb m)
up-zero {ℓ} ν d t β mb (H.mL {t = a} {x = x} e m) =
  limψ ℓ ν t a e (proj₁ (Up zero d β x)) (λ n → up-zero ν d t β mb (m n))
up-zero ν d t β mb (H.mΩ {p = ()} _ _ _)
up-zero ν d t β mb (H.mU {c = ()} _ _)
up-zero {ℓ} ν d t β mb (H.mw m q) = weakᴿ ℓ (up-zero ν d t β mb m) (Upm zero d β q)
up-zero {ℓ} ν d t β mb (H.mc le m) = closeᴿ ℓ (app≤ν ν t le) (up-zero ν d t β mb m)

UpAt : L → Set
UpAt j = ∀ {ℓ} ν (d : Dn ℓ j) → UpFrame ν j d
  → (t : E.T) (β : Tr⁺ ℓ) → R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → R j a x
  → R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up j d β x))

fold-up : ∀ s h → ((c : Ch s) → UpAt (h c)) → UpAt (nd s h)
fold-up s h child {ℓ} ν d fr t β mb (H.mz {x = x}) =
  ++[] (λ z → R ℓ (E.ψ ν z ∷ []) (proj₁ (Up (nd s h) d β x))) t
    (zlᴿ ℓ (λ y → proj₁ (Up (nd s h) d β y)) (Upm (nd s h) d β) mb x)
fold-up s h child {ℓ} ν d fr t β mb (H.m1 {t = a} {x = x} e m) =
  nextψ ℓ ν t a e (Up (nd s h) d β x) (fold-up s h child ν d fr t β mb m)
fold-up s h child {ℓ} ν d fr t β mb (H.mL {t = a} {x = x} e m) =
  limψ ℓ ν t a e (proj₁ (Up (nd s h) d β x))
    (λ n → fold-up s h child ν d fr t β mb (m n))
fold-up s h child {ℓ} ν d fr t β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
  nodeψ ℓ ν t a (mv d p) e (proj₁ (fr p κ nu)) (proj₁ (proj₂ (fr p κ nu)))
    (λ η c lc → fold-up s h child ν d fr t β mb
      (m η (mvBr d p c) (proj₂ (proj₂ (fr p κ nu)) η c lc)))
fold-up s h child {ℓ} ν d fr t β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} m ch) =
  subst (λ z → R ℓ (E.ψ ν z ∷ [])
    (proj₁ (Up (h c) (down d c) (Up (nd s h) d β x) y))) (++-assoc t a b)
    (child c ν (down d c) (down-frame ν s h d fr c) (t ++ a)
      (Up (nd s h) d β x) (fold-up s h child ν d fr t β mb m) ch)
fold-up s h child {ℓ} ν d fr t β mb (H.mw m q) =
  weakᴿ ℓ (fold-up s h child ν d fr t β mb m) (Upm (nd s h) d β q)
fold-up s h child {ℓ} ν d fr t β mb (H.mc le m) =
  closeᴿ ℓ (app≤ν ν t le) (fold-up s h child ν d fr t β mb m)

up-pres : ∀ j → UpAt j
up-pres zero ν d fr = up-zero ν d
up-pres (nd s h) = fold-up s h (λ c → up-pres (h c))

self-child : ∀ s h (o : Ok (nd s h)) ν → NodeFrame (nd s h) o (nd s h) self ν
  → (c : Ch s) → UpFrame ν (h c) (down {s = s} {h = h} stop c)
self-child s h o ν fr c p κ nu = proj₁ (fr (inj₂ (c , inj₂ p)) κ nu) , nu , λ η z lc → lc
```

## 路径证据 (来源 `YiGTIndex`)

```agda
CWReq : ∀ {A B : Set} → A ⊎ B → (A → Set) → (B → Set) → Set
CWReq (inj₁ a) F G = F a
CWReq (inj₂ b) F G = G b

DWReq : ∀ {A B : Set} → Maybe (A ⊎ B) → (A → Set) → (B → Set) → Set
DWReq (just w) F G = CWReq w F G
DWReq nothing F G = ⊥

mutual
  IndexOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set
  IndexOK ℓ o r j w ν = NodeFrame ℓ o j w ν × RouteOK ℓ o r j w ν

  RouteOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set
  RouteOK ℓ o r .ℓ self ν = ⊤
  RouteOK (nd s h) o r j (inu ws) ν = (c : Ch s) → IndexOK (h c) (proj₂ o c) (proj₂ r c) j (ws c) ν
  RouteOK (nd (sΩ k) h) o r j (ink v) ν = (c : Tr k) →
    IndexOK (h c) (proj₂ o c) (proj₂ r c) j (v ∙ proj₂ (proj₁ o) c) ν
  RouteOK (nd sS h) o r j (inc c′ v) ν = IndexOK (h c′) (proj₂ o c′) (proj₂ r c′) j v ν
  RouteOK (nd sL h) o r j (inc n v) ν = (m : Ch sL) → CWReq (way h (proj₁ o) m n)
    (λ u → IndexOK (h n) (proj₂ o n) (proj₂ r n) j v ν)
    (λ u → IndexOK (h m) (proj₂ o m) (proj₂ r m) j (v ∙ u) ν)
  RouteOK (nd (sΩ k) h) o r j (inc c′ v) ν = (c : Tr k) → DWReq (proj₁ r c c′)
    (λ u → IndexOK (h c) (proj₂ o c) (proj₂ r c) j (v ∙ u) ν)
    (λ u → IndexOK (h c′) (proj₂ o c′) (proj₂ r c′) j v ν)

zero-spec : ∀ ℓ (p : Pos ℓ) κ (K : Keep zero (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ zero [] p κ K
zero-spec ℓ p κ nothing = gt0 κ
zero-spec ℓ p κ (just (() , _))

zero-frame : ∀ ℓ (o : Ok ℓ) (w : zero ≤ ℓ) → NodeFrame ℓ o zero w []
zero-frame ℓ o w p κ nu = zero-spec ℓ p κ _

index-zero : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → IndexOK ℓ o r zero (z≤ ℓ) []
index-zero zero o r = zero-frame zero o self , tt
index-zero (nd s h) o r = zero-frame (nd s h) o (z≤ (nd s h))
  , λ c → index-zero (h c) (proj₂ o c) (proj₂ r c)

SlotPres : L → Set
SlotPres ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → (p : Pos ℓ) (ν : E.T) → Lab (at ℓ p) ν
  → ∀ {a x} → R ℓ a x
  → R (at ℓ p) (E.ψ ν (t ++ a) ∷ [])
      (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) x))

shift-prefix : ∀ s h → SlotPres (nd s h)
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (t : E.T) → PrefixU B t → ∀ {a x} → R (nd s h) a x → (c : Ch s)
  → PrefixU (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) (t ++ a)
shift-prefix s h sp o r B gb t pref m c p ν nu = sp o r B gb t pref (inj₂ (c , inj₂ p)) ν nu m

PresAt : L → Set
PresAt ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → (j : L) (w : j ≤ ℓ) (ν : E.T) → IndexOK ℓ o r j w ν
  → (β : Tr⁺ j) → R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → R ℓ a x
  → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

Kit : L → Set
Kit zero = ⊤
Kit (nd s h) = SlotPres (nd s h) × StepU′ (nd s h) × ((c : Ch s) → Kit (h c))
```

## 自身行 (来源 `YiGTSelf`)

```agda
zero-self : (o : Ok zero) (r : Rb zero) (B : Base zero) (t ν : E.T) (β : Tr⁺ zero)
  → R zero (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → R zero a x
  → R zero (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))
zero-self o r B t ν β mb (H.mz {x = x}) =
  ++[] (λ z → R zero (E.ψ ν z ∷ []) (proj₁ (ψ zero o r B zero self β x))) t
    (zlᴿ zero (λ y → proj₁ (ψ zero o r B zero self β y)) (mono zero o r B zero self β) mb x)
zero-self o r B t ν β mb (H.m1 {t = a} {x = x} e m) =
  nextψ zero ν t a e (ψ zero o r B zero self β x) (zero-self o r B t ν β mb m)
zero-self o r B t ν β mb (H.mL {t = a} {x = x} e m) =
  limψ zero ν t a e (proj₁ (ψ zero o r B zero self β x))
    (λ n → zero-self o r B t ν β mb (m n))
zero-self o r B t ν β mb (H.mΩ {p = ()} _ _ _)
zero-self o r B t ν β mb (H.mU {c = ()} _ _)
zero-self o r B t ν β mb (H.mw m d) =
  weakᴿ zero (zero-self o r B t ν β mb m) (mono zero o r B zero self β d)
zero-self o r B t ν β mb (H.mc le m) =
  closeᴿ zero (app≤ν ν t le) (zero-self o r B t ν β mb m)

module Self (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h))
  (B : Base (nd s h)) (ν t : E.T) (fr : NodeFrame (nd s h) o (nd s h) self ν)
  (β : Tr⁺ (nd s h)) (mb : R (nd s h) (E.ψ ν t ∷ []) (proj₁ β)) where
  F : Tr (nd s h) → Tr⁺ (nd s h)
  F x = ψ (nd s h) o r B (nd s h) self β x

  LF : ∀ {a x} → R (nd s h) a x → R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (F x))
  LF (H.mz {x = x}) = ++[] (λ z → R (nd s h) (E.ψ ν z ∷ []) (proj₁ (F x))) t
    (zlᴿ (nd s h) (λ y → proj₁ (F y)) (mono (nd s h) o r B (nd s h) self β) mb x)
  LF (H.m1 {t = a} {x = x} e m) = nextψ (nd s h) ν t a e (F x) (LF m)
  LF (H.mL {t = a} {x = x} e m) = limψ (nd s h) ν t a e (proj₁ (F x)) (λ n → LF (m n))
  LF (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    nodeψ (nd s h) ν t a p e (proj₁ (fr p κ nu)) nu (λ η c lc → LF (m η c lc))
  LF (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} m ch) =
    subst (λ z → R (nd s h) (E.ψ ν z ∷ [])
      (proj₁ (Up (h c) (down {s = s} {h = h} stop c) (F x) y))) (++-assoc t a b)
      (up-pres (h c) ν (down {s = s} {h = h} stop c) (self-child s h o ν fr c)
        (t ++ a) (F x) (LF m) ch)
  LF (H.mw m d) = weakᴿ (nd s h) (LF m) (mono (nd s h) o r B (nd s h) self β d)
  LF (H.mc le m) = closeᴿ (nd s h) (app≤ν ν t le) (LF m)

self-pres : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) ν t → NodeFrame ℓ o ℓ self ν
  → (β : Tr⁺ ℓ) → R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → R ℓ a x
  → R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B ℓ self β x))
self-pres zero o r B ν t fr = zero-self o r B t ν
self-pres (nd s h) o r B ν t fr = Self.LF s h o r B ν t fr
```

## 嵌入行 (来源 `YiGTEmb`)

```agda
module Top (s : Sh) (h : Ch s → L) (child : (c : Ch s) → PresAt (h c))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h))
  (gb : OK B) (t : E.T) (pref : PrefixU B t) where
  cb : (x : Tr (nd s h)) (c : Ch s) → Base (h c)
  cb x c i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

  child-at : ∀ j ν {a b x} (c : Ch s) (v : j ≤ h c) → IndexOK (h c) (proj₂ o c) (proj₂ r c) j v ν
    → (β : Tr⁺ j) → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ β) → R (nd s h) a x
    → PrefixU (cb x c) (t ++ a) → (y : Tr (h c)) → R (h c) b y
    → R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (h c) (proj₂ o c) (proj₂ r c) (cb x c) j v β y))
  child-at j ν {a} {b} {x} c v ic β mb m pc y ch = child c (proj₂ o c) (proj₂ r c) (cb x c)
    (updated-ok s h o r B gb x c) (t ++ a) pc
    j v ν ic β mb ch

emb-row : ∀ s h (child : (c : Ch s) → PresAt (h c))
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)
  → (t : E.T) (pref : PrefixU B t) → ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
  → (β : Tr⁺ j) → ∀ {a b x} (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → R (nd s h) a x
  → ((d : Ch s) → PrefixU (Top.cb s h child o r B gb t pref x d) (t ++ a))
  → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ (nd s h) o r B j w β x))
  → R (h c) b y
  → R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (nd s h) o r B j w β (up x c y e)))
emb-row s h child o r B gb t pref .(nd s h) self ν (fr , rt) β {a} c y e m pc mx ch =
  up-pres (h c) ν (down {s = s} {h = h} stop c) (self-child s h o ν fr c) (t ++ a)
    (ψ (nd s h) o r B (nd s h) self β _) mx ch
emb-row s h child o r B gb t pref j (inu ws) ν (fr , rt) β c y e m pc mx ch =
  Top.child-at s h child o r B gb t pref j ν c (ws c) (rt c) _ mx m (pc c) y ch
emb-row (sΩ k) h child o r B gb t pref j (ink v) ν (fr , rt) β c y e m pc mx ch =
  Top.child-at (sΩ k) h child o r B gb t pref j ν c (v ∙ proj₂ (proj₁ o) c) (rt c) _ mx m (pc c) y ch
emb-row sS h child o r B gb t pref j (inc tt v) ν (fr , rt) β tt y e m pc mx ch =
  Top.child-at sS h child o r B gb t pref j ν tt v rt _ mx m (pc tt) y ch
emb-row sL h child o r B gb t pref j (inc n v) ν (fr , rt) β m y e q pc mx ch
  with way h (proj₁ o) m n | rt m
... | inj₁ u | ic = Top.child-at sL h child o r B gb t pref j ν n v ic _ mx q (pc n)
  (proj₁ (emb (h n) (proj₂ o n) u (y , e))) (emb-pres (h n) (proj₂ o n) u (y , e) ch)
... | inj₂ u | ic = Top.child-at sL h child o r B gb t pref j ν m (v ∙ u) ic _ mx q (pc m) y ch
emb-row (sΩ k) h child o r B gb t pref j (inc c′ v) ν (fr , rt) β c y e m pc mx ch
  with proj₁ r c c′ | rt c
... | just (inj₁ u) | ic = Top.child-at (sΩ k) h child o r B gb t pref j ν c (v ∙ u) ic _ mx m (pc c) y ch
... | just (inj₂ u) | ic = Top.child-at (sΩ k) h child o r B gb t pref j ν c′ v ic _ mx m (pc c′)
  (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))) (emb-pres (h c′) (proj₂ o c′) u (y , e) ch)
... | nothing | ()
```
