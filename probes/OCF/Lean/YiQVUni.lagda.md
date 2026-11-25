# 统一读回域 (二): 读法一致量化的多目标系统; "保留而参照坍缩" 归到读法一侧

> 验收文件 (读记号). 判决: 编译定理 (条件), 不改树、折叠、合法性. 把 `YiSOLow.Keepᵗ` 里逐点的目标读法 κ 换成对目标层一切读法一致的前提与结论 (`Bdᵘ`, `Keepᵘ`): 树保留而参照坍缩的一格 (`NodeMis` 的 `kept-gt`, 以及整条 `UpMis`) 由目标层上一条只关于读法的条件 `Raise` 给出 (取一个不低于 ν+1 的读法, 用参照穿透的一格, 再沿项序降回), 不再是前提 (`upAllᵘ` 无别的前提; `lowAllᵘ`).
> 余下的前提: 树走链而参照余尾保持 (`NodeDrop`), 换基行 (`RebRowᵘ`), 根上的 `RootBd`, `RootIn`, `RootRaise`, 出口条件 (`ebo-endᵘ`).
> 不给出什么: `NodeDrop`, `RebRowᵘ` 没有实填也没有否定; `Raise` 对一切合法层号不成立 (`¬raise-flat`, 反例是常值的 ℕ 极限层号, 不在读回域里). 来源: 归纳的骨架逐行照 `YiSOLow.Sys.Main` 与 `YiSOUp.UpAll`. 塔第 1 项的实例见 [YiQVTw1](YiQVTw1.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQVUni where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
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
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLLLeafNeg as N
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (_≤ᵀ_; gt→<; Pen→≤; <-≤)
open import OCF.Align.Value using (_≼_; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiGTGen using (weakᴿ; weakenᴿ; closeᴿ; limᴿ; cumᴿ; nextψ; limψ; nodeψ; app≤ν; Ω≤ψ; emb-pres)
open import OCF.Lean.YiANFam using (Pen; cofG; fsnG)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiFIGen using (low→)
open import OCF.Lean.YiQDFold using (GoodK; kp-good; mv-good)
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (exitᵍ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs; reference)
open import OCF.Lean.YiGLDom using (dom-top; dom-keel)
open import OCF.Lean.YiWREnd using (gradedᴮ; domsᴮ; genᴮ; mz′; slT-fb; ψ-⊵ᴮ; emptyᵀ; EBOᴮ; baseᴮ; betaᴮ; twcᴮ; upperᴮ)
open import OCF.Lean.YiSOLow
open import OCF.Lean.YiSOUp using (Up-⊵)
open import OCF.Lean.YiSOEnd using (rootˢ; RootBd; module End)
open Row gradedᴮ domsᴮ using (Rules)
open ExSuff gradedᵍ domsᵍ using (Exit₀; Keel⁻)
```

## 一致读法的陈述; 读法一侧的条件

`Bdᵘ j K β`: β 支配 ψ_κ(K), 对目标层 j 的一切读法 κ. `Raise j q`: 目标层的槽位 q 的每个读法 ν, 目标层有一个不低于 ν+1 的读法. `lower`: κ < ν+1 ≤ κ′ 时 ψ_κ(X) 在项序上不高于 ψ_κ′(X).

```agda
Bdᵘ : (j : L) → E.T → Tr⁺ j → Set
Bdᵘ j K β = ∀ κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)

Raise : (j : L) → Pos j → Set
Raise j q = ∀ {ν} → GR.Nu j q ν → Σ E.T λ κ′ → GR.Rd j κ′ × Pen (E.cmpᵀ (E.sucT ν) κ′)

LvRaise : L → Set
LvRaise j = (q : Pos j) → Raise j q

SlotRaise : L → Set
SlotRaise a = (p : Pos a) → LvRaise (at a p)

lower : ∀ {ν κ κ′} X → E.cmpᵀ (E.sucT ν) κ ≡ E.gt → Pen (E.cmpᵀ (E.sucT ν) κ′) → (E.ψ κ X ∷ []) ≤ᵀ (E.ψ κ′ X ∷ [])
lower {ν} {κ} {κ′} X q pen = inj₁ (E.hd< (E.lv< (<-≤ (gt→< (E.sucT ν) κ q) (Pen→≤ (E.sucT ν) κ′ pen))))

rd0 : ∀ {κ} → GR.Rd zero κ → κ ≡ []
rd0 {κ} (GR.c0 e) = emptyᵀ κ e
rd0 (GR.ca ())
rd0 (GR.cL e h) = ⊥-elim (bad (subst (E.natT 1 E.<ᵀ_) (rd0 (h 2)) (N.fsn-big e)))
  where
  bad : E.natT 1 E.<ᵀ [] → ⊥
  bad ()
rd0 (GR.cc le r) with rd0 r
... | refl with le
... | inj₂ refl = refl

Keepᵘ : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
Keepᵘ {a} (o , r , B) K t x = ∀ j (w : j ≤ a) (β : Tr⁺ j) → LvRaise j → Bdᵘ j K β → Bdᵘ j (K ++ t) (BS.ψ a o r B j w β x)

slot→bd : ∀ {a} (st : Stˢ a) K → SlotBd st K → (p : Pos a) → Bdᵘ (at a p) K (proj₂ (proj₂ st) (at a p) (posW a p))
slot→bd {a} (o , r , B) K bd p κ rd = bd p (rd-nu a p rd)

slot-stepᵘ : ∀ {s h} (st : Stˢ (nd s h)) K → SlotBd st K → SlotRaise (nd s h) → (c : Ch s) → ∀ {t x} → Keepᵘ st K t x
  → SlotBd (stepˢ st c x) (K ++ t)
slot-stepᵘ {s} {h} (o , r , B) K bd sr c kx p′ {κ} nu =
  kx (at (h c) p′) (inc c (posW (h c) p′)) (B (at (h c) p′) (inc c (posW (h c) p′))) (sr (inj₂ (c , inj₂ p′)))
    (λ κ′ rd′ → bd (inj₂ (c , inj₂ p′)) (rd-nu (h c) p′ rd′)) κ (nu-rd (h c) p′ nu)
```

## 上折: 只用 `LvRaise`

`YiSOUp.UpMis` 的一格 (上折总保留, 参照坍缩) 在这里由 `LvRaise ℓ` 给出; 没有别的前提.

```agda
UpQᵘ : ∀ {ℓ j′} → Dn ℓ j′ → E.T → Tr j′ → Set
UpQᵘ {ℓ} {j′} d u y = ∀ (b : Tr⁺ ℓ) K′ → Bdᵘ ℓ K′ b → Bdᵘ ℓ (K′ ++ u) (Up j′ d b y)

mutual
  upAllᵘ : ∀ {ℓ} → LvRaise ℓ → (j′ : L) (d : Dn ℓ j′) → ∀ {u y} → GR.R j′ u y → UpQᵘ d u y
  upAllᵘ lr j′ d = genᴮ j′ (UpQᵘ d) (rulesU lr j′ d) (λ le _ q b K′ Pb κ rd → closeᴿ _ (app≤ν κ K′ le) (q b K′ Pb κ rd))

  rulesU : ∀ {ℓ} → LvRaise ℓ → (j′ : L) (d : Dn ℓ j′) → Rules j′ (UpQᵘ d)
  rulesU {ℓ} lr j′ d = record
    { qz = λ {u} {x} e0 b K′ Pb κ rd →
        subst (λ z → GR.R ℓ (E.ψ κ (K′ ++ z) ∷ []) (proj₁ (Up j′ d b x))) (sym (emptyᵀ u e0))
          (subst (λ z → GR.R ℓ (E.ψ κ z ∷ []) (proj₁ (Up j′ d b x))) (sym (++-identityʳ K′))
            (weakenᴿ ℓ (Pb κ rd) (Up-⊵ j′ d b x)))
    ; q1 = λ {u} {x} e1 _ q b K′ Pb κ rd → nextψ ℓ κ K′ u e1 (Up j′ d b x) (q b K′ Pb κ rd)
    ; qL = λ {u} {x} eω _ h b K′ Pb κ rd → limψ ℓ κ K′ u eω _ (λ n → h n b K′ Pb κ rd)
    ; qΩ = λ p {u} {ν} g e nu hR hQ b K′ Pb κ rd →
        nodeU lr j′ d p g e nu hQ b K′ Pb (mv-good d p) κ rd (E.cmpᵀ (E.sucT ν) κ) refl
    ; qU = embU lr j′ d
    ; qw = λ {u} {x} {x′} _ q lt b K′ Pb κ rd → weakᴿ ℓ (q b K′ Pb κ rd) (Upm j′ d b lt) }

  keptU : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) (p : Pos j′) {u ν : E.T} (g : Br j′ p → Tr j′) → E.cof u ≡ E.cΩ ν → GR.Nu j′ p ν
    → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → UpQᵘ d (E.fsT u η) (g c))
    → ∀ (b : Tr⁺ ℓ) K′ → Bdᵘ ℓ K′ b
    → (gk : Σ (at ℓ (mv d p) ≡ at j′ p) λ e → ∀ z → slTᵍ j′ p (mvBr d p z) ≡ subst Tr e (slTᵍ ℓ (mv d p) z))
    → ∀ κ → GR.Rd ℓ κ → Pen (E.cmpᵀ (E.sucT ν) κ)
    → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g)))
  keptU {ℓ} j′ d p {u} {ν} g e nu hQ b K′ Pb (eq , cm) κ rd pen =
    nodeψ ℓ κ K′ u (mv d p) e pen (rd-nu ℓ (mv d p) (subst (λ A → GR.Rd A ν) (sym eq) (nu-rd j′ p nu)))
      (λ η c l → hQ η (mvBr d p c) (subst (GR.R (at j′ p) η) (sym (cm c)) (trR eq (low→ ℓ (mv d p) l))) b K′ Pb κ rd)

  nodeU : ∀ {ℓ} → LvRaise ℓ → (j′ : L) (d : Dn ℓ j′) (p : Pos j′) {u ν : E.T} (g : Br j′ p → Tr j′) → E.cof u ≡ E.cΩ ν → GR.Nu j′ p ν
    → (∀ η c → GR.R (at j′ p) η (slTᵍ j′ p c) → UpQᵘ d (E.fsT u η) (g c))
    → ∀ (b : Tr⁺ ℓ) K′ → Bdᵘ ℓ K′ b
    → (gk : Σ (at ℓ (mv d p) ≡ at j′ p) λ e → ∀ z → slTᵍ j′ p (mvBr d p z) ≡ subst Tr e (slTᵍ ℓ (mv d p) z))
    → ∀ κ → GR.Rd ℓ κ → (c : E.Cmp) → E.cmpᵀ (E.sucT ν) κ ≡ c
    → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b (Ω p g)))
  nodeU lr j′ d p g e nu hQ b K′ Pb gk κ rd E.lt eqc = keptU j′ d p g e nu hQ b K′ Pb gk κ rd (inj₁ eqc)
  nodeU lr j′ d p g e nu hQ b K′ Pb gk κ rd E.eq eqc = keptU j′ d p g e nu hQ b K′ Pb gk κ rd (inj₂ eqc)
  nodeU {ℓ} lr j′ d p {u} {ν} g e nu hQ b K′ Pb gk κ rd E.gt eqc
    with lr (mv d p) (rd-nu ℓ (mv d p) (subst (λ A → GR.Rd A ν) (sym (proj₁ gk)) (nu-rd j′ p nu)))
  ... | κ′ , rd′ , pen′ = closeᴿ ℓ (lower (K′ ++ u) eqc pen′) (keptU j′ d p g e nu hQ b K′ Pb gk κ′ rd′ pen′)

  embU : ∀ {ℓ} → LvRaise ℓ → (j′ : L) (d : Dn ℓ j′) (c : CH j′) {t u : E.T} {x : Tr j′} (y : ChTᵍ j′ c) → GR.R j′ t x → UpQᵘ d t x
    → GR.R (chLᵍ j′ c) u (chTᵍ j′ c y) → UpQᵘ d (t ++ u) (upᵍ x c y)
  embU {ℓ} lr (nd s h) d c {t} {u} {x} (y , e) rx qx ry b K′ Pb κ rd =
    subst (λ z → GR.R ℓ (E.ψ κ z ∷ []) (proj₁ (Up (h c) (down d c) (Up (nd s h) d b x) y))) (++-assoc K′ t u)
      (upAllᵘ lr (h c) (down d c) ry (Up (nd s h) d b x) (K′ ++ t) (qx b K′ Pb) κ rd)
```

## 结点

固定状态, 结点, 目标 j, 底值 β 与它对一切读法的支配. 保留: 读法 κ 使参照穿透时用 `nodeψ`; 使参照坍缩时取 `Raise` 给的读法 κ′, 在 κ′ 上用穿透的一格, 再用 `lower` 降回 κ. 走链: 参照坍缩时同 `YiSOLow.Node.dropGt`; 参照穿透的一格留给前提 `dp`.

```agda
module Nodeᵘ {a} (o : Ok a) (r : Rb a) (B : Base a) (K : E.T) (p : Pos a) {t ν : E.T} (g : Br a p → Tr a)
    (e : E.cof t ≡ E.cΩ ν) (nu : GR.Nu a p ν)
    (bs : Bdᵘ (at a p) K (B (at a p) (posW a p))) (lrs : LvRaise (at a p))
    (hQ : ∀ η c → GR.R (at a p) η (slTᵍ a p c) → Keepᵘ (o , r , B) K (E.fsT t η) (g c))
    (j : L) (w : j ≤ a) (β : Tr⁺ j) (lr : LvRaise j) (Pβ : Bdᵘ j K β) where

  G : Br a p → Tr⁺ j
  G z = BS.ψ a o r B j w β (g z)

  sf : Tr a → Tr (at a p)
  sf y = proj₁ (BS.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y)

  S : Br a p → Br a p
  S z = fromBr a p (sf (g z))

  pt : ℕ → Br a p
  pt = iter S (fromBr a p zero)

  Goal : Keep j (Br a p) (fromBr a p zero) → E.T → Set
  Goal m κ = GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (node⁺ m G S))

  slotQ : ∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R (at a p) (E.ψ ν (K ++ E.fsT t η) ∷ []) (sf (g c))
  slotQ η c l = hQ η c l (at a p) (posW a p) (B (at a p) (posW a p)) lrs bs ν (nu-rd a p nu)

  chain : ∀ k → GR.R (at a p) (E.γT (K ++ t) ν k) (slTᵍ a p (pt (suc k)))
  chain zero = subst (GR.R (at a p) (E.Ωt ν)) (sym (slT-fb a p _))
    (closeᴿ (at a p) (Ω≤ψ ν (K ++ E.fsT t [])) (slotQ [] (fromBr a p zero) (mz′ (at a p))))
  chain (suc k) = subst₂ (GR.R (at a p)) (cong (λ z → E.ψ ν z ∷ []) (sym (fsT++ K t (E.γT (K ++ t) ν k) e))) (sym (slT-fb a p _))
    (slotQ (E.γT (K ++ t) ν k) (pt (suc k)) (chain k))

  dropGt : ∀ κ → GR.Rd j κ → E.cmpᵀ (E.sucT ν) κ ≡ E.gt → Goal nothing κ
  dropGt κ rd q = limᴿ j (cofG κ (K ++ t) q (cof++Ω K t e)) (λ k →
    subst (λ z → GR.R j z (proj₁ (node⁺ nothing G S)))
      (sym (trans (fsnG κ (K ++ t) k q (cof++Ω K t e)) (cong (λ z → E.ψ κ z ∷ []) (fsT++ K t (E.γT (K ++ t) ν k) e))))
      (cumᴿ j (λ n → G (pt n)) (suc k) (hQ (E.γT (K ++ t) ν k) (pt (suc k)) (chain k) j w β lr Pβ κ rd)))

  nuq : (q : Pos j) → at j q ≡ at a p → GR.Nu j q ν
  nuq q eq = rd-nu j q (subst (λ A → GR.Rd A ν) (sym eq) (nu-rd a p nu))

  keptPen : (q : Pos j) (cv : Br j q → Br a p) (x : cv (fromBr j q zero) ≡ fromBr a p zero)
    → GoodK (at a p) (slTᵍ a p) (just (q , cv , x)) → ∀ κ → GR.Rd j κ → Pen (E.cmpᵀ (E.sucT ν) κ) → Goal (just (q , cv , x)) κ
  keptPen q cv x (eq , cm) κ rd pen = nodeψ j κ K t q e pen (nuq q eq)
    (λ η c l → hQ η (cv c) (subst (GR.R (at a p) η) (sym (cm c)) (trR eq (low→ j q l))) j w β lr Pβ κ rd)

  keptGt : (q : Pos j) (cv : Br j q → Br a p) (x : cv (fromBr j q zero) ≡ fromBr a p zero)
    → GoodK (at a p) (slTᵍ a p) (just (q , cv , x)) → ∀ κ → GR.Rd j κ → E.cmpᵀ (E.sucT ν) κ ≡ E.gt → Goal (just (q , cv , x)) κ
  keptGt q cv x gk κ rd qgt with lr q (nuq q (proj₁ gk))
  ... | κ′ , rd′ , pen′ = closeᴿ j (lower (K ++ t) qgt pen′) (keptPen q cv x gk κ′ rd′ pen′)

  go : (m : Keep j (Br a p) (fromBr a p zero)) → GoodK (at a p) (slTᵍ a p) m
     → (∀ κ → GR.Rd j κ → Pen (E.cmpᵀ (E.sucT ν) κ) → m ≡ nothing → Goal m κ)
     → ∀ κ → GR.Rd j κ → (c : E.Cmp) → E.cmpᵀ (E.sucT ν) κ ≡ c → Goal m κ
  go (just (q , cv , x)) gk dp κ rd E.lt eqc = keptPen q cv x gk κ rd (inj₁ eqc)
  go (just (q , cv , x)) gk dp κ rd E.eq eqc = keptPen q cv x gk κ rd (inj₂ eqc)
  go (just (q , cv , x)) gk dp κ rd E.gt eqc = keptGt q cv x gk κ rd eqc
  go nothing             gk dp κ rd E.gt eqc = dropGt κ rd eqc
  go nothing             gk dp κ rd E.lt eqc = dp κ rd (inj₁ eqc) refl
  go nothing             gk dp κ rd E.eq eqc = dp κ rd (inj₂ eqc) refl

  node : (∀ κ → GR.Rd j κ → Pen (E.cmpᵀ (E.sucT ν) κ) → kp a o p w ≡ nothing → Goal (kp a o p w) κ)
    → ∀ κ → GR.Rd j κ → Goal (kp a o p w) κ
  node dp κ rd = go (kp a o p w) (kp-good a o p w) dp κ rd (E.cmpᵀ (E.sucT ν) κ) refl
```

## 两条前提与充分性

`NodeDrop`: 结点走链 (`kp` 是 `nothing`) 而读法 κ 使参照的余尾保持 Ω (ν+1 ≤ κ). `RebRowᵘ`: `YiSOLow.Sys.RebRow` 的一致读法形式.

```agda
module Sysᵘ (𝒟 : Domˢ) where
  open Domˢ 𝒟

  NodeDrop : Set
  NodeDrop = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → SlotRaise a → ∀ K → SlotBd (o , r , B) K
    → (p : Pos a) {t ν : E.T} (g : Br a p → Tr a) → Dm (o , r , B) (Ω p g) → E.cof t ≡ E.cΩ ν → GR.Nu a p ν
    → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
    → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → Keepᵘ (o , r , B) K (E.fsT t η) (g c))
    → ∀ j (w : j ≤ a) (β : Tr⁺ j) → LvRaise j → Bdᵘ j K β
    → ∀ κ → GR.Rd j κ → Pen (E.cmpᵀ (E.sucT ν) κ) → kp a o p w ≡ nothing
    → GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B j w β (Ω p g)))

  RebRowᵘ : Set
  RebRowᵘ = ∀ {k h} (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rs : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
    (c : Tr k) {u : E.T} (x : Tr (nd (sΩ k) h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → Dm (o , (just S , rs) , B) (up x c y e)
    → ∀ j (c′ : Tr k) (v : j ≤ h c′) (fl : floor S ≤ j) (β′ : Tr⁺ j) K′ → LvRaise j → Bdᵘ j K′ β′
    → GR.R (h c) u y
    → Bdᵘ j (K′ ++ u) (seen S j (downOk (h c′) (proj₂ o c′) j v) fl β′ c ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

  module Mainᵘ (nd′ : NodeDrop) (rr : RebRowᵘ) where

    Qᴰ : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
    Qᴰ st K t x = Dm st x → Keepᵘ st K t x

    mutual
      lowAllᵘ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → SlotRaise a → ∀ K → SlotBd (o , r , B) K
        → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Keepᵘ (o , r , B) K t x
      lowAllᵘ a o r B gd sr K bd = genᴮ a (Qᴰ (o , r , B) K) (rulesᵘ a o r B gd sr K bd)
        (λ le _ q d j w β lr Pβ κ rd → closeᴿ j (app≤ν κ K le) (q d j w β lr Pβ κ rd))

      rulesᵘ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → SlotRaise a → ∀ K → SlotBd (o , r , B) K → Rules a (Qᴰ (o , r , B) K)
      rulesᵘ a o r B gd sr K bd = record
        { qz = λ {t} {x} e0 d j w β lr Pβ κ rd →
            subst (λ u → GR.R j (E.ψ κ (K ++ u) ∷ []) (proj₁ (BS.ψ a o r B j w β x))) (sym (emptyᵀ t e0))
              (subst (λ u → GR.R j (E.ψ κ u ∷ []) (proj₁ (BS.ψ a o r B j w β x))) (sym (++-identityʳ K))
                (weakenᴿ j (Pβ κ rd) (ψ-⊵ᴮ a o r B j w β x)))
        ; q1 = λ {t} {x} e1 _ q d j w β lr Pβ κ rd →
            nextψ j κ K t e1 (BS.ψ a o r B j w β x) (q (dw (o , r , B) ◃s d) j w β lr Pβ κ rd)
        ; qL = λ {t} {x} eω _ h d j w β lr Pβ κ rd → limψ j κ K t eω _ (λ n → h n d j w β lr Pβ κ rd)
        ; qΩ = λ p {t} {ν} g e nu hR hQ d j w β lr Pβ →
            Nodeᵘ.node o r B K p g e nu (slot→bd (o , r , B) K bd p) (sr p) (λ η c l → hQ η c l (dnd (o , r , B) p g d c)) j w β lr Pβ
              (λ κ rd pen eqn → nd′ o r B gd sr K bd p g d e nu hR (λ η c l → hQ η c l (dnd (o , r , B) p g d c)) j w β lr Pβ κ rd pen eqn)
        ; qU = embRᵘ a o r B gd sr K bd
        ; qw = λ {t} {x} {x′} _ q lt d j w β lr Pβ κ rd →
            weakᴿ j (q (dw (o , r , B) lt d) j w β lr Pβ κ rd) (BS.mono a o r B j w β lt) }

      embRᵘ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → SlotRaise a → ∀ K → SlotBd (o , r , B) K
        → (c : CH a) {t u : E.T} {x : Tr a} (y : ChTᵍ a c) → GR.R a t x → Qᴰ (o , r , B) K t x → GR.R (chLᵍ a c) u (chTᵍ a c y)
        → Qᴰ (o , r , B) K (t ++ u) (upᵍ x c y)
      embRᵘ (nd s h) o r B gd sr K bd c {x = x} (y , e) rx qx ry d =
        rowᵘ s h o r B gd sr K bd c x y e (qx (dw (o , r , B) (◃u x c y e) d)) ry d

      fbᵘ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → SlotRaise (nd s h)
        → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) {y′ : Tr (h c)} → Keepᵘ (o , r , B) K t x → GR.R (h c) u y′
        → Dm (stepˢ (o , r , B) c x) y′
        → ∀ j (w′ : j ≤ h c) (β′ : Tr⁺ j) → LvRaise j → Bdᵘ j (K ++ t) β′
        → Bdᵘ j (K ++ (t ++ u))
            (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) j w′ β′ y′)
      fbᵘ s h o r B gd sr K bd c {t} {u} x {y′} kx ry d′ j w′ β′ lr Pβ′ κ rd =
        subst (λ z → GR.R j (E.ψ κ z ∷ [])
            (proj₁ (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) j w′ β′ y′)))
          (++-assoc K t u)
          (lowAllᵘ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x)
            (good-ch s h r gd c) (λ p′ → sr (inj₂ (c , inj₂ p′))) (K ++ t) (slot-stepᵘ (o , r , B) K bd sr c kx) ry d′ j w′ β′ lr Pβ′ κ rd)

      rowᵘ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → SlotRaise (nd s h)
        → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
        → Keepᵘ (o , r , B) K t x → GR.R (h c) u y → Dm (o , r , B) (up x c y e)
        → ∀ j (w : j ≤ nd s h) (β : Tr⁺ j) → LvRaise j → Bdᵘ j K β
        → Bdᵘ j (K ++ (t ++ u)) (BS.ψ (nd s h) o r B j w β (up x c y e))
      rowᵘ s h o r B gd sr K bd c {t} {u} x y e kx ry d _ self β lr Pβ κ rd =
        subst (λ z → GR.R (nd s h) (E.ψ κ z ∷ []) (proj₁ (Up (h c) (down stop c) (BS.ψ (nd s h) o r B (nd s h) self β x) y)))
          (++-assoc K t u)
          (upAllᵘ lr (h c) (down stop c) ry (BS.ψ (nd s h) o r B (nd s h) self β x) (K ++ t) (kx (nd s h) self β lr Pβ) κ rd)
      rowᵘ s h o r B gd sr K bd c x y e kx ry d j (inu ws) β lr Pβ =
        fbᵘ s h o r B gd sr K bd c x kx ry (dch (o , r , B) c x y e d) j (ws c) (BS.ψ (nd s h) o r B j (inu ws) β x) lr
          (kx j (inu ws) β lr Pβ)
      rowᵘ (sΩ k) h o r B gd sr K bd c x y e kx ry d j (ink v) β lr Pβ =
        fbᵘ (sΩ k) h o r B gd sr K bd c x kx ry (dch (o , r , B) c x y e d) j (v ∙ proj₂ (proj₁ o) c)
          (BS.ψ (nd (sΩ k) h) o r B j (ink v) β x) lr (kx j (ink v) β lr Pβ)
      rowᵘ sS h o r B gd sr K bd c x y e kx ry d j (inc c′ v) β lr Pβ =
        fbᵘ sS h o r B gd sr K bd c x kx ry (dch (o , r , B) c x y e d) j v (BS.ψ (nd sS h) o r B j (inc c′ v) β x) lr
          (kx j (inc c′ v) β lr Pβ)
      rowᵘ sL g o r B gd sr K bd m {t} {u} x y e kx ry d j (inc n v) β lr Pβ κ rd =
        cW-ind (λ Z → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ []) (proj₁ Z)) (way g (proj₁ o) m n)
          (λ u′ → fbᵘ sL g o r B gd sr K bd n x kx (emb-pres (g n) (proj₂ o n) u′ (y , e) ry) (dem (o , r , B) m n x y e u′ d)
                    j v (BS.ψ (nd sL g) o r B j (inc n v) β x) lr (kx j (inc n v) β lr Pβ) κ rd)
          (λ u′ → fbᵘ sL g o r B gd sr K bd m x kx ry (dch (o , r , B) m x y e d)
                    j (v ∙ u′) (BS.ψ (nd sL g) o r B j (inc n v) β x) lr (kx j (inc n v) β lr Pβ) κ rd)
      rowᵘ (sΩ k) h o (.(just S) , rs) B ((S , refl) , gs) sr K bd c {t} {u} x y e kx ry d j (inc c′ v) β lr Pβ κ rd =
        cW-ind (λ Z → GR.R j (E.ψ κ (K ++ (t ++ u)) ∷ []) (proj₁ Z)) (route S j c′ v)
          (λ u′ → fbᵘ (sΩ k) h o (just S , rs) B ((S , refl) , gs) sr K bd c x kx ry (dch (o , (just S , rs) , B) c x y e d)
                    j (back S c u′) (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) lr (kx j (inc c′ v) β lr Pβ) κ rd)
          (λ u′ → subst (λ z → GR.R j (E.ψ κ z ∷ [])
                      (proj₁ (seen S j (downOk (h c′) (proj₂ o c′) j v) u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) c
                              ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
                    (++-assoc K t u)
                    (rr o S rs B c x y e d j c′ v u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B j (inc c′ v) β x) (K ++ t) lr
                      (kx j (inc c′ v) β lr Pβ) ry κ rd))
```

## 终点

根状态, 目标第 0 层 (只有空读法, `rd0`; 没有槽位, `LvRaise` 空成立). `RootRaise`: 塔各项每个槽位层上的 `LvRaise`.

```agda
RootRaise : Set
RootRaise = ∀ n → SlotRaise (tw n)

module Endᵘ (𝒟 : Domˢ) where
  open Sysᵘ 𝒟
  open End 𝒟 using (RootIn)

  module _ (nd′ : NodeDrop) (rr : RebRowᵘ) (rb : RootBd) (ri : RootIn) (rz : RootRaise) where
    open Mainᵘ nd′ rr

    foldedᵘ : ∀ n → GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)
    foldedᵘ n = lowAllᵘ (tw n) (Ok-tw n) (rb-tw n) (baseᴮ n) (good-tw n) (rz n) [] (rb n) (dom-top (dom-keel n)) (ri n)
      zero (z≤ (tw n)) (betaᴮ n) (λ ())
      (λ κ rd → subst (λ z → GR.R zero (E.ψ z [] ∷ []) (proj₁ (betaᴮ n))) (sym (rd0 rd)) (H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n))))
      [] (GR.c0 refl)

    ebo-endᵘ : (∀ n → H.Exᴴ (foldedᵘ n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
    ebo-endᵘ ex = ≼-trans reference (l≼ (λ n → ≼-trans (Exit₀.exit exitᵍ (foldedᵘ n) (ex n) (hs n)) (upperᴮ n)))
```

## `Raise` 对一切合法层号不成立

常值的 ℕ 极限层号 `nd sL (λ _ → zero)` (合法): 读法只有空, 而孩子侧槽位的读法也是空, 没有不低于 1 的读法. 这个层号不是任何树的读回 (ℕ 极限的相邻项严格步进), 所以读作 `Raise` 要限制在读回层号上.

```agda
flat : L
flat = nd sL (λ _ → zero)

ok-flat : Ok flat
ok-flat = (λ n → self) , λ n → tt

rd-flat : ∀ {κ} → GR.Rd flat κ → κ ≡ []
rd-flat {κ} (GR.c0 e) = emptyᵀ κ e
rd-flat (GR.ca (inj₁ (c , q))) = rd0 q
rd-flat (GR.cL e h) = ⊥-elim (bad (subst (E.natT 1 E.<ᵀ_) (rd-flat (h 2)) (N.fsn-big e)))
  where
  bad : E.natT 1 E.<ᵀ [] → ⊥
  bad ()
rd-flat (GR.cc le r) with rd-flat r
... | refl with le
... | inj₂ refl = refl

¬raise-flat : LvRaise flat → ⊥
¬raise-flat lr with lr (inj₂ (zero , inj₁ tt)) {ν = []} (GR.c0 refl)
... | κ′ , rd′ , pen with rd-flat rd′
... | refl with pen
... | inj₁ ()
... | inj₂ ()
```
