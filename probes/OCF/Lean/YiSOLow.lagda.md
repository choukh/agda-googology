# 换基折叠的多目标系统: 回退行与链步对一切层号一次给出

> 验收文件 (读记号). 判决: 编译定理 (条件), 不改树、折叠、合法性. 状态是 (合法证据, 换基证据, 底), 目标 j, 路径, 底值与目标读法 κ 全部量化 (`Keepᵗ`), 参照 ψ_κ(K ++ t); 不变式 `SlotBd`: 每个槽位上的底支配 ψ_κ(K). `Main.lowAll`: 零, 后继, ℕ 极限, 放宽, 向下封闭, 全部回退行 (`inu`, `ink`, 后继与 ℕ 极限形状的 `inc`, `back`), 结点上 "保留且参照穿透" 与 "走链且参照坍缩" 两格, 对一切层号用一次归纳证出.
> 余下三条前提: 保留判定与参照不一致的结点 (`NodeMis`), 自身行即上折 (`SelfRow`), 换基行 (`RebRow`); 都带树的域 `Domˢ`. 判断: 域取全体时 `RebRow` 在值上不成立 (见 [YiSOEnd](YiSOEnd.lagda.md) 文首), 所以域是必要的.
> 不给出什么: 三条前提没有实填, 也没有给出满足封闭条件且使前提成立的域. 来源: 链步照 `YiWREnd.chain←slot`, 保留一格用 `YiQDFold.kp-good` 与 `YiGTGen.nodeψ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSOLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (chLᵍ; ChTᵍ; chTᵍ; upᵍ; slTᵍ)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiGTGen using (weakᴿ; weakenᴿ; closeᴿ; limᴿ; cumᴿ; nextψ; limψ; nodeψ; app≤ν; Ω≤ψ; emb-pres)
open import OCF.Lean.YiANFam using (Pen; cofG; fsnG)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiFIGen using (low→)
open import OCF.Lean.YiQDFold using (GoodK; kp-good)
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiWREnd using (gradedᴮ; domsᴮ; genᴮ; mz′; slT-fb; ψ-⊵ᴮ; emptyᵀ)
open Row gradedᴮ domsᴮ using (Rules)
```

## 状态, 换基证据处处在场, 槽位读法

`Good`: 每个 Ω 形状上都有 `Schema` (塔各项的 `rb-tw` 如此, `good-tw`); 没有它时嵌入行是回退到第 0 层的 `⊞`, 不在本系统里.

```agda
Stˢ : L → Set
Stˢ a = Ok a × Rb a × Base a

stepˢ : ∀ {a} → Stˢ a → (c : CH a) → Tr a → Stˢ (chLᵍ a c)
stepˢ {nd s h} (o , r , B) c x = proj₂ o c , proj₂ r c , λ i u → BS.ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

Good : (ℓ : L) → Rb ℓ → Set
Good zero          _ = ⊤
Good (nd sS h)     r = ∀ c → Good (h c) (proj₂ r c)
Good (nd sL h)     r = ∀ c → Good (h c) (proj₂ r c)
Good (nd (sΩ k) h) r = (Σ (Schema k h) λ S → proj₁ r ≡ just S) × (∀ c → Good (h c) (proj₂ r c))

good-ch : ∀ s h (r : Rb (nd s h)) → Good (nd s h) r → ∀ c → Good (h c) (proj₂ r c)
good-ch sS     h r g = g
good-ch sL     h r g = g
good-ch (sΩ k) h r g = proj₂ g

good-rbO : (a b : L) (ra : Rb a) (oa : Ok a) (ob : OkO a b) → Good a ra → Good (a ⊕ b) (rbO a b ra oa ob)
good-rbO a zero          ra oa ob g = g
good-rbO a (nd sS h)     ra oa ob g = λ c → good-rbO a (h c) ra oa (proj₂ ob c) g
good-rbO a (nd sL h)     ra oa ob g = λ c → good-rbO a (h c) ra oa (proj₂ ob c) g
good-rbO a (nd (sΩ k) h) ra oa ob g = (_ , refl) , λ c → good-rbO a (h c) ra oa (proj₂ ob c) g

good-tw : ∀ n → Good (tw n) (rb-tw n)
good-tw zero    = tt
good-tw (suc n) = (_ , refl) , λ c →
  good-rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c) (good-tw n)

mutual
  nu-rd : ∀ ℓ p {κ} → GR.Nu ℓ p κ → GR.Rd (at ℓ p) κ
  nu-rd (nd s h)      (inj₂ (c , t)) = nu-rd⁼ (h c) t
  nu-rd (nd (sΩ k) h) (inj₁ t)       = nu-rd⁼ k t

  nu-rd⁼ : ∀ a t {κ} → GR.Nu⁼ a t κ → GR.Rd (proj₁ (sl⁼ a t)) κ
  nu-rd⁼ a (inj₁ _) q = q
  nu-rd⁼ a (inj₂ p) q = nu-rd a p q

mutual
  rd-nu : ∀ ℓ p {κ} → GR.Rd (at ℓ p) κ → GR.Nu ℓ p κ
  rd-nu (nd s h)      (inj₂ (c , t)) = rd-nu⁼ (h c) t
  rd-nu (nd (sΩ k) h) (inj₁ t)       = rd-nu⁼ k t

  rd-nu⁼ : ∀ a t {κ} → GR.Rd (proj₁ (sl⁼ a t)) κ → GR.Nu⁼ a t κ
  rd-nu⁼ a (inj₁ _) q = q
  rd-nu⁼ a (inj₂ p) q = rd-nu a p q

trR : ∀ {A A′ : L} (e : A ≡ A′) {η} {x : Tr A} → GR.R A η x → GR.R A′ η (subst Tr e x)
trR refl r = r
```

## 多目标的陈述与不变式

`Keepᵗ st K t x`: 对一切目标 j, 路径 w, 底值 β, 目标读法 κ, 底值支配 ψ_κ(K) 时 x 的折叠支配 ψ_κ(K ++ t). `SlotBd st K`: 每个槽位 p 与它的每个读法 κ 上, 底在槽位层的值支配 ψ_κ(K). 嵌入一步之后孩子层的 `SlotBd` 就是 x 在孩子各槽位上的 `Keepᵗ` (`slot-step`).

```agda
Keepᵗ : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
Keepᵗ {a} (o , r , B) K t x = ∀ j (w : j ≤ a) (β : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)
  → GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B j w β x))

SlotBd : ∀ {a} → Stˢ a → E.T → Set
SlotBd {a} (o , r , B) K = (p : Pos a) → ∀ {κ} → GR.Nu a p κ → GR.R (at a p) (E.ψ κ K ∷ []) (proj₁ (B (at a p) (posW a p)))

slot-step : ∀ {s h} (st : Stˢ (nd s h)) K → SlotBd st K → (c : Ch s) → ∀ {t x} → Keepᵗ st K t x → SlotBd (stepˢ st c x) (K ++ t)
slot-step {s} {h} (o , r , B) K bd c kx p′ {κ} nu =
  kx (at (h c) p′) (inc c (posW (h c) p′)) (B (at (h c) p′) (inc c (posW (h c) p′))) κ (nu-rd (h c) p′ nu) (bd (inj₂ (c , inj₂ p′)) nu)
```

## 域

树的域随状态: 沿第一位置序向下, 对结点分支, 嵌入的孩子材料 (在孩子层的状态下) 封闭; ℕ 极限形状上材料搬进目标所在孩子时也在域内 (`dem`). 取全体是实例 (`allˢ`).

```agda
record Domˢ : Set₁ where
  field
    Dm  : ∀ {a} → Stˢ a → Tr a → Set
    dw  : ∀ {a} (st : Stˢ a) {x x′ : Tr a} → a ⊢ x ◃ x′ → Dm st x′ → Dm st x
    dnd : ∀ {a} (st : Stˢ a) (p : Pos a) (g : Br a p → Tr a) → Dm st (Ω p g) → ∀ c → Dm st (g c)
    dch : ∀ {s h} (st : Stˢ (nd s h)) (c : Ch s) (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
        → Dm st (up x c y e) → Dm (stepˢ st c x) y
    dem : ∀ {g} (st : Stˢ (nd sL g)) (m n : ℕ) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g m ≤ g n)
        → Dm st (up x m y e) → Dm (stepˢ st n x) (proj₁ (emb (g n) (proj₂ (proj₁ st) n) u (y , e)))

allˢ : Domˢ
allˢ = record { Dm = λ _ _ → ⊤ ; dw = λ _ _ _ → tt ; dnd = λ _ _ _ _ _ → tt ; dch = λ _ _ _ _ _ _ → tt ; dem = λ _ _ _ _ _ _ _ _ → tt }
```

## 结点: 一致的两格

固定状态, 结点 `Ω p g`, 槽位读法 ν, 目标与目标读法 κ. `c = cmpᵀ (ν+1) κ`. 保留且 c 是 `lt`/`eq`: 参照的余尾穿透, 用 `nodeψ`, 槽位层号与分支关系沿 `kp-good` 搬运 (`keptPen`). 走链且 c 是 `gt`: 参照坍缩成 γ 链, 链点由 `hQ` 在槽位目标上的一份给出 (`chain`, 即 `YiWREnd.chain←slot` 的论证放进同一个归纳), 再用目标 j 上的一份 (`dropGt`). 不一致的两格 (`Mis`) 留给前提.

```agda
data Mis {j : L} {X : Set} {x₀ : X} : Keep j X x₀ → E.Cmp → Set where
  kept-gt : ∀ {e} → Mis (just e) E.gt
  drop-lt : Mis nothing E.lt
  drop-eq : Mis nothing E.eq

module Node {a} (o : Ok a) (r : Rb a) (B : Base a) (K : E.T) (p : Pos a) {t ν : E.T} (g : Br a p → Tr a)
    (e : E.cof t ≡ E.cΩ ν) (nu : GR.Nu a p ν)
    (bs : GR.R (at a p) (E.ψ ν K ∷ []) (proj₁ (B (at a p) (posW a p))))
    (hQ : ∀ η c → GR.R (at a p) η (slTᵍ a p c) → Keepᵗ (o , r , B) K (E.fsT t η) (g c))
    (j : L) (w : j ≤ a) (β : Tr⁺ j) (κ : E.T) (rd : GR.Rd j κ) (rβ : GR.R j (E.ψ κ K ∷ []) (proj₁ β)) where

  G : Br a p → Tr⁺ j
  G z = BS.ψ a o r B j w β (g z)

  sf : Tr a → Tr (at a p)
  sf y = proj₁ (BS.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y)

  S : Br a p → Br a p
  S z = fromBr a p (sf (g z))

  pt : ℕ → Br a p
  pt = iter S (fromBr a p zero)

  Goal : Keep j (Br a p) (fromBr a p zero) → Set
  Goal m = GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (node⁺ m G S))

  slotQ : ∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R (at a p) (E.ψ ν (K ++ E.fsT t η) ∷ []) (sf (g c))
  slotQ η c l = hQ η c l (at a p) (posW a p) (B (at a p) (posW a p)) ν (nu-rd a p nu) bs

  chain : ∀ k → GR.R (at a p) (E.γT (K ++ t) ν k) (slTᵍ a p (pt (suc k)))
  chain zero = subst (GR.R (at a p) (E.Ωt ν)) (sym (slT-fb a p _))
    (closeᴿ (at a p) (Ω≤ψ ν (K ++ E.fsT t [])) (slotQ [] (fromBr a p zero) (mz′ (at a p))))
  chain (suc k) = subst₂ (GR.R (at a p)) (cong (λ z → E.ψ ν z ∷ []) (sym (fsT++ K t (E.γT (K ++ t) ν k) e))) (sym (slT-fb a p _))
    (slotQ (E.γT (K ++ t) ν k) (pt (suc k)) (chain k))

  dropGt : E.cmpᵀ (E.sucT ν) κ ≡ E.gt → Goal nothing
  dropGt q = limᴿ j (cofG κ (K ++ t) q (cof++Ω K t e)) (λ k →
    subst (λ z → GR.R j z (proj₁ (node⁺ nothing G S)))
      (sym (trans (fsnG κ (K ++ t) k q (cof++Ω K t e)) (cong (λ z → E.ψ κ z ∷ []) (fsT++ K t (E.γT (K ++ t) ν k) e))))
      (cumᴿ j (λ n → G (pt n)) (suc k) (hQ (E.γT (K ++ t) ν k) (pt (suc k)) (chain k) j w β κ rd rβ)))

  keptPen : (q : Pos j) (cv : Br j q → Br a p) (x : cv (fromBr j q zero) ≡ fromBr a p zero)
    → GoodK (at a p) (slTᵍ a p) (just (q , cv , x)) → Pen (E.cmpᵀ (E.sucT ν) κ) → Goal (just (q , cv , x))
  keptPen q cv x (eq , cm) pen = nodeψ j κ K t q e pen (rd-nu j q (subst (λ A → GR.Rd A ν) (sym eq) (nu-rd a p nu)))
    (λ η c l → hQ η (cv c) (subst (GR.R (at a p) η) (sym (cm c)) (trR eq (low→ j q l))) j w β κ rd rβ)

  go : (m : Keep j (Br a p) (fromBr a p zero)) → GoodK (at a p) (slTᵍ a p) m → (c : E.Cmp) → E.cmpᵀ (E.sucT ν) κ ≡ c
     → (Mis m c → Goal m) → Goal m
  go (just (q , cv , x)) gk E.lt eqc mis = keptPen q cv x gk (inj₁ eqc)
  go (just (q , cv , x)) gk E.eq eqc mis = keptPen q cv x gk (inj₂ eqc)
  go (just _)            gk E.gt eqc mis = mis kept-gt
  go nothing             gk E.gt eqc mis = dropGt eqc
  go nothing             gk E.lt eqc mis = mis drop-lt
  go nothing             gk E.eq eqc mis = mis drop-eq

  node : (Mis (kp a o p w) (E.cmpᵀ (E.sucT ν) κ) → Goal (kp a o p w)) → Goal (kp a o p w)
  node = go (kp a o p w) (kp-good a o p w) (E.cmpᵀ (E.sucT ν) κ) refl
```

## 三条前提与充分性

`NodeMis`: 保留判定与参照不一致的结点 (保留而参照坍缩; 走链而参照穿透). `SelfRow`: 目标是本层 (路径 `self`) 时嵌入行是上折 `Up`. `RebRow`: Ω 形状上目标经指定孩子且 `route` 落在地板之上, 像是替身加第 0 层的尾项. 回退行都落进孩子层的同一条陈述, 上下文接成 K ++ t (`fb`).

```agda
module Sys (𝒟 : Domˢ) where
  open Domˢ 𝒟

  NodeMis : Set
  NodeMis = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
    → (p : Pos a) {t ν : E.T} (g : Br a p → Tr a) → Dm (o , r , B) (Ω p g) → E.cof t ≡ E.cΩ ν → GR.Nu a p ν
    → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
    → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → Keepᵗ (o , r , B) K (E.fsT t η) (g c))
    → ∀ j (w : j ≤ a) (β : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)
    → Mis (kp a o p w) (E.cmpᵀ (E.sucT ν) κ)
    → GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B j w β (Ω p g)))

  SelfRow : Set
  SelfRow = ∀ {s h} (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (c : Ch s) {u : E.T}
    (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → Dm (o , r , B) (up x c y e)
    → ∀ (β′ : Tr⁺ (nd s h)) κ K′ → GR.Rd (nd s h) κ → GR.R (nd s h) (E.ψ κ K′ ∷ []) (proj₁ β′) → GR.R (h c) u y
    → GR.R (nd s h) (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up (h c) (down stop c) β′ y))

  RebRow : Set
  RebRow = ∀ {k h} (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rs : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
    (c : Tr k) {u : E.T} (x : Tr (nd (sΩ k) h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → Dm (o , (just S , rs) , B) (up x c y e)
    → ∀ j (c′ : Tr k) (v : j ≤ h c′) (fl : floor S ≤ j) (β′ : Tr⁺ j) κ K′ → GR.Rd j κ → GR.R j (E.ψ κ K′ ∷ []) (proj₁ β′)
    → GR.R (h c) u y
    → GR.R j (E.ψ κ (K′ ++ u) ∷ [])
        (proj₁ (seen S j (downOk (h c′) (proj₂ o c′) j v) fl β′ c ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))

  module Main (nm : NodeMis) (sr : SelfRow) (rr : RebRow) where

    Qᴰ : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
    Qᴰ st K t x = Dm st x → Keepᵗ st K t x

    mutual
      lowAll : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
        → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Keepᵗ (o , r , B) K t x
      lowAll a o r B gd K bd = genᴮ a (Qᴰ (o , r , B) K) (rules a o r B gd K bd)
        (λ le _ q d j w β κ rd rβ → closeᴿ j (app≤ν κ K le) (q d j w β κ rd rβ))

      rules : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → Rules a (Qᴰ (o , r , B) K)
      rules a o r B gd K bd = record
        { qz = λ {t} {x} e0 d j w β κ rd rβ →
            subst (λ u → GR.R j (E.ψ κ (K ++ u) ∷ []) (proj₁ (BS.ψ a o r B j w β x))) (sym (emptyᵀ t e0))
              (subst (λ u → GR.R j (E.ψ κ u ∷ []) (proj₁ (BS.ψ a o r B j w β x))) (sym (++-identityʳ K))
                (weakenᴿ j rβ (ψ-⊵ᴮ a o r B j w β x)))
        ; q1 = λ {t} {x} e1 _ q d j w β κ rd rβ →
            nextψ j κ K t e1 (BS.ψ a o r B j w β x) (q (dw (o , r , B) ◃s d) j w β κ rd rβ)
        ; qL = λ {t} {x} eω _ h d j w β κ rd rβ → limψ j κ K t eω _ (λ n → h n d j w β κ rd rβ)
        ; qΩ = λ p {t} {ν} g e nu hR hQ d j w β κ rd rβ →
            Node.node o r B K p g e nu (bd p nu) (λ η c l → hQ η c l (dnd (o , r , B) p g d c)) j w β κ rd rβ
              (nm o r B gd K bd p g d e nu hR (λ η c l → hQ η c l (dnd (o , r , B) p g d c)) j w β κ rd rβ)
        ; qU = embR a o r B gd K bd
        ; qw = λ {t} {x} {x′} _ q lt d j w β κ rd rβ →
            weakᴿ j (q (dw (o , r , B) lt d) j w β κ rd rβ) (BS.mono a o r B j w β lt) }

      embR : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
        → (c : CH a) {t u : E.T} {x : Tr a} (y : ChTᵍ a c) → GR.R a t x → Qᴰ (o , r , B) K t x → GR.R (chLᵍ a c) u (chTᵍ a c y)
        → Qᴰ (o , r , B) K (t ++ u) (upᵍ x c y)
      embR (nd s h) o r B gd K bd c {x = x} (y , e) rx qx ry d =
        row s h o r B gd K bd c x y e (qx (dw (o , r , B) (◃u x c y e) d)) ry d

      fb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) {y′ : Tr (h c)} → Keepᵗ (o , r , B) K t x → GR.R (h c) u y′
        → Dm (stepˢ (o , r , B) c x) y′
        → ∀ j (w′ : j ≤ h c) (β′ : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ β′)
        → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ [])
            (proj₁ (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) j w′ β′ y′))
      fb s h o r B gd K bd c {t} {u} x {y′} kx ry d′ j w′ β′ κ rd rβ′ =
        subst (λ z → GR.R j (E.ψ κ z ∷ [])
            (proj₁ (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) j w′ β′ y′)))
          (++-assoc K t u)
          (lowAll (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x)
            (good-ch s h r gd c) (K ++ t) (slot-step (o , r , B) K bd c kx) ry d′ j w′ β′ κ rd rβ′)

      row : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
        → Keepᵗ (o , r , B) K t x → GR.R (h c) u y → Dm (o , r , B) (up x c y e)
        → ∀ j (w : j ≤ nd s h) (β : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)
        → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ []) (proj₁ (BS.ψ (nd s h) o r B j w β (up x c y e)))
      row s h o r B gd K bd c {t} {u} x y e kx ry d _ self β κ rd rβ =
        subst (λ z → GR.R (nd s h) (E.ψ κ z ∷ []) (proj₁ (Up (h c) (down stop c) (BS.ψ (nd s h) o r B (nd s h) self β x) y)))
          (++-assoc K t u)
          (sr o r B c x y e d (BS.ψ (nd s h) o r B (nd s h) self β x) κ (K ++ t) rd (kx (nd s h) self β κ rd rβ) ry)
      row s h o r B gd K bd c x y e kx ry d j (inu ws) β κ rd rβ =
        fb s h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) j (ws c) (BS.ψ (nd s h) o r B j (inu ws) β x) κ rd
          (kx j (inu ws) β κ rd rβ)
      row (sΩ k) h o r B gd K bd c x y e kx ry d j (ink v) β κ rd rβ =
        fb (sΩ k) h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) j (v ∙ proj₂ (proj₁ o) c)
          (BS.ψ (nd (sΩ k) h) o r B j (ink v) β x) κ rd (kx j (ink v) β κ rd rβ)
      row sS h o r B gd K bd c x y e kx ry d j (inc c′ v) β κ rd rβ =
        fb sS h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) j v (BS.ψ (nd sS h) o r B j (inc c′ v) β x) κ rd
          (kx j (inc c′ v) β κ rd rβ)
      row sL g o r B gd K bd m {t} {u} x y e kx ry d j (inc n v) β κ rd rβ =
        cW-ind (λ Z → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ []) (proj₁ Z)) (way g (proj₁ o) m n)
          (λ u′ → fb sL g o r B gd K bd n x kx (emb-pres (g n) (proj₂ o n) u′ (y , e) ry) (dem (o , r , B) m n x y e u′ d)
                    j v (BS.ψ (nd sL g) o r B j (inc n v) β x) κ rd (kx j (inc n v) β κ rd rβ))
          (λ u′ → fb sL g o r B gd K bd m x kx ry (dch (o , r , B) m x y e d)
                    j (v ∙ u′) (BS.ψ (nd sL g) o r B j (inc n v) β x) κ rd (kx j (inc n v) β κ rd rβ))
      row (sΩ k) h o (.(just S) , rs) B ((S , refl) , gs) K bd c {t} {u} x y e kx ry d j (inc c′ v) β κ rd rβ =
        cW-ind (λ Z → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ []) (proj₁ Z)) (route S j c′ v)
          (λ u′ → fb (sΩ k) h o (just S , rs) B ((S , refl) , gs) K bd c x kx ry (dch (o , (just S , rs) , B) c x y e d)
                    j (back S c u′) (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) κ rd (kx j (inc c′ v) β κ rd rβ))
          (λ u′ → subst (λ z → GR.R j (E.ψ κ z ∷ [])
                      (proj₁ (seen S j (downOk (h c′) (proj₂ o c′) j v) u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) c
                              ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
                    (++-assoc K t u)
                    (rr o S rs B c x y e d j c′ v u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) κ (K ++ t) rd
                      (kx j (inc c′ v) β κ rd rβ) ry))
```

## 槽位目标上的一份

`core`: 状态 st 在槽位 p 上朝槽位层的折叠 (底值取底在槽位层上的值) 把 `R a η y` 变成以 ψ_κ(K ++ η) 为参照的关系; 即 `YiWREnd.Wire.LowSlot` 的结论, 前提换成 `Good` 与 `SlotBd`.

```agda
    core : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → (p : Pos a) → ∀ {κ} → GR.Nu a p κ
      → ∀ {η y} → GR.R a η y → Dm (o , r , B) y
      → GR.R (at a p) (E.ψ κ (K ++ η) ∷ []) (proj₁ (BS.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y))
    core {a} o r B gd K bd p {κ} nu ry d =
      lowAll a o r B gd K bd ry d (at a p) (posW a p) (B (at a p) (posW a p)) κ (nu-rd a p nu) (bd p nu)
```
