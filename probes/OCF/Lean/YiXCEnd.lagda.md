# 换基候选的终点: 第 0 层目标不带 mc, 出口条件换成两条第 0 层的行

> 验收文件 (读记号). 判决: 编译定理 (条件), 不改树、折叠、合法性. 第 0 层目标另做一次归纳 (`low⁰`), 输出是不带 mc 的 `YiKVRel.M⁰`, 出口无条件; 结点在第 0 层目标上总是走链 (不用 `NodeMis`), 链点与孩子的底取 `YiSOLow.Sys.Main.lowAll`. 终点 `ebo-endᶜ` 的前提: 域, `NodeMis`, `SelfRow`, `RebRow`, `RootBd`, `RootIn`, 加第 0 层目标上的换基行 `RebRow⁰` 与向下封闭行 `CloseRow⁰`; 不再有对 `folded n` 这个证明项的出口条件.
> 闭合行是必要的 (`close-needed`: 第 0 层目标的陈述 `Low⁰` 推出它; `low⁰-all` 是反方向). `close←nf`: 两个参照都是标准形时闭合行成立; 这个标准形前提对一切上下文一致陈述时不成立 (`¬closeNF-all`, 反例是层号 0 上的非标准形上下文, 读作量化域太宽).
> 不给出什么: `RebRow⁰`, `CloseRow⁰` 没有实填; 塔上实际出现的上下文与 mc 对是否都是标准形没有查. 来源: 各行照 `YiSOLow.Sys.Main` (`rules`, `embR`, `row`, `fb`), 结点照 `YiSOLow.Node.dropGt`, 终点照 `YiSOEnd.End`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXCEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

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
import OCF.Lean.YiHCCheck as HC
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; Ctbl; c∷; c[]; nf-hd; nfp-a; nf-le)
open import OCF.Align.Value using (_≼_; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiGTGen using (app≤ν; emb-pres; closeᴿ)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (cofG; fsnG)
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiWREnd using (gradedᴮ; domsᴮ; genᴮ; ψ-⊵ᴮ; emptyᵀ; sucgt; twcᴮ; upperᴮ; EBOᴮ; baseᴮ; betaᴮ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (exitᵍ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs; reference)
open import OCF.Lean.YiGLDom using (dom-top; dom-keel)
open import OCF.Lean.YiSOLow
open import OCF.Lean.YiSOUp using (UpMis; module UpAll)
open import OCF.Lean.YiSOEnd using (RootBd; module End)
open import OCF.Lean.YiXCVar using (down⁰; elimᴴ; ω₀; ¬1ω)
open Row gradedᴮ domsᴮ using (Rules)
open ExSuff gradedᵍ domsᵍ using (Exit₀; Keel⁻)
```

## 第 0 层目标上的后继与 ℕ 极限 (照 `YiGTGen.nextψ`, `limψ`, 关系换成不带 mc 的)

```agda
nextψᴷ : ∀ t a → E.cof a ≡ E.c1 → (β : Tr⁺ zero)
  → K.M⁰ (E.ψ [] (t ++ E.pred a) ∷ []) (proj₁ β) → K.M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (next⁺ β))
nextψᴷ t a e β m = K.G⁰.m-next β (cofψ1 [] (t ++ a) (cof++1 t a e))
  (λ n → trans (fsnψ1 [] (t ++ a) n (cof++1 t a e)) (cong (λ z → replicate n (E.ψ [] z)) (pred++ t a e))) m

limψᴷ : ∀ t a → E.cof a ≡ E.cω → (x : Tr zero)
  → (∀ n → K.M⁰ (E.ψ [] (t ++ E.fsn a n) ∷ []) x) → K.M⁰ (E.ψ [] (t ++ a) ∷ []) x
limψᴷ t a e x m = K.mL (cofψω [] (t ++ a) (cof++ω t a e))
  (λ n → subst (λ z → K.M⁰ z x) (sym (trans (fsnψω [] (t ++ a) n (cof++ω t a e)) (cong (λ z → E.ψ [] z ∷ []) (fsn++ t a n e)))) (m n))
```

## 陈述与两条第 0 层的行

`Z st K t x`: 对一切路径 w 与底值 β, β 对着 ψ₀(K) 时 x 朝第 0 层的折叠对着 ψ₀(K ++ t), 关系不带 mc. `CloseRow⁰`: 输入推导的 mc 结点 (s ≤ t) 上从 t 的一份得 s 的一份. `RebRow⁰`: `RebRow` 取目标第 0 层.

```agda
module Zero (𝒟 : Domˢ) where
  open Domˢ 𝒟
  open Sys 𝒟

  Z : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
  Z {a} (o , r , B) K t x = (w : zero ≤ a) (β : Tr⁺ zero) → K.M⁰ (E.ψ [] K ∷ []) (proj₁ β)
    → K.M⁰ (E.ψ [] (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B zero w β x))

  CloseRow⁰ : Set
  CloseRow⁰ = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
    → ∀ {s t x} → s ≤ᵀ t → GR.R a t x → Dm (o , r , B) x → Z (o , r , B) K t x → Z (o , r , B) K s x

  RebRow⁰ : Set
  RebRow⁰ = ∀ {k h} (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rs : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
    (c : Tr k) {u : E.T} (x : Tr (nd (sΩ k) h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → Dm (o , (just S , rs) , B) (up x c y e)
    → ∀ (c′ : Tr k) (v : zero ≤ h c′) (fl : floor S ≤ zero) (β′ : Tr⁺ zero) K′ → K.M⁰ (E.ψ [] K′ ∷ []) (proj₁ β′)
    → GR.R (h c) u y
    → K.M⁰ (E.ψ [] (K′ ++ u) ∷ [])
        (proj₁ (seen S zero (downOk (h c′) (proj₂ o c′) zero v) fl β′ c ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
```

## 闭合行的充分条件与它的否定

```agda
  CloseNF⁰ : Set
  CloseNF⁰ = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
    → ∀ {s t x} → s ≤ᵀ t → GR.R a t x → Dm (o , r , B) x → NF (E.ψ [] (K ++ s) ∷ []) × NF (E.ψ [] (K ++ t) ∷ [])

  close←nf : CloseNF⁰ → CloseRow⁰
  close←nf f o r B gd K bd le rx d zt w β rβ with f o r B gd K bd le rx d
  ... | ns , nt = down⁰ ns nt (c∷ c[]) (app≤ν [] K le) (zt w β rβ)
```

闭合行也是必要的: 第 0 层目标的陈述 `Low⁰` 对一切输入推导 (含 mc) 成立时, 闭合行就是它在 `closeᴿ le rx` 上的一份.

```agda
  Low⁰ : Set
  Low⁰ = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
    → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Z (o , r , B) K t x

  close-needed : Low⁰ → CloseRow⁰
  close-needed L {a} o r B gd K bd le rx d _ = L o r B gd K bd (closeᴿ a le rx) d
```

`RebRow⁰` 就是目标第 0 层的 `RebRow` 连同同一推导的 `Exᴴ` (同 `YiMXEnd.LowKeepᴱ` 的形状).

```agda
  RebRowᴱ : Set
  RebRowᴱ = ∀ {k h} (o : Ok (nd (sΩ k) h)) (S : Schema k h) (rs : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
    (c : Tr k) {u : E.T} (x : Tr (nd (sΩ k) h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → Dm (o , (just S , rs) , B) (up x c y e)
    → ∀ (c′ : Tr k) (v : zero ≤ h c′) (fl : floor S ≤ zero) (β′ : Tr⁺ zero) K′ → GR.R zero (E.ψ [] K′ ∷ []) (proj₁ β′)
    → GR.R (h c) u y
    → Σ (GR.R zero (E.ψ [] (K′ ++ u) ∷ [])
        (proj₁ (seen S zero (downOk (h c′) (proj₂ o c′) zero v) fl β′ c ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))) H.Exᴴ

  rebrow⁰←ᴱ : RebRowᴱ → RebRow⁰
  rebrow⁰←ᴱ f o S rs B c x y e d c′ v fl β′ K′ rβ ry =
    elimᴴ (proj₁ (f o S rs B c x y e d c′ v fl β′ K′ (HC.of⁰ rβ) ry)) (proj₂ (f o S rs B c x y e d c′ v fl β′ K′ (HC.of⁰ rβ) ry))
```

## 第 0 层目标的归纳

结点: 目标第 0 层没有槽位, `kp` 只能是 `nothing`, 参照 ψ₀(K ++ t) 的余尾是 ω (`sucgt`), 所以只有走链一格. 链点 `Node.chain` 用 `lowAll` 在槽位层的一份 (底值条件经 `HC.of⁰` 转成带 mc 的关系).

```agda
  module Main⁰ (nm : NodeMis) (sr : SelfRow) (rr : RebRow) (rr⁰ : RebRow⁰) (cl : CloseRow⁰) where
    open Main nm sr rr using (lowAll)

    Qᶻ : ∀ {a} → Stˢ a → E.T → E.T → Tr a → Set
    Qᶻ st K t x = Dm st x → Z st K t x

    node⁰ : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
      → (p : Pos a) {t ν : E.T} (g : Br a p → Tr a) (e : E.cof t ≡ E.cΩ ν) (nu : GR.Nu a p ν)
      → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
      → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → Z (o , r , B) K (E.fsT t η) (g c))
      → Dm (o , r , B) (Ω p g) → Z (o , r , B) K t (Ω p g)
    node⁰ {a} o r B gd K bd p {t} {ν} g e nu hR hZ d w β rβ = go (kp a o p w)
      where
      module N = Node o r B K p g e nu (bd p nu) (λ η c l → lowAll a o r B gd K bd (hR η c l) (dnd (o , r , B) p g d c))
                   zero w β [] (GR.c0 refl) (HC.of⁰ rβ)
      go : (m : Keep zero (Br a p) (fromBr a p zero)) → K.M⁰ (E.ψ [] (K ++ t) ∷ []) (proj₁ (node⁺ m N.G N.S))
      go (just (() , _))
      go nothing = K.mL (cofG [] (K ++ t) (sucgt ν) (cof++Ω K t e)) (λ k →
        subst (λ z → K.M⁰ z (proj₁ (node⁺ nothing N.G N.S)))
          (sym (trans (fsnG [] (K ++ t) k (sucgt ν) (cof++Ω K t e)) (cong (λ z → E.ψ [] z ∷ []) (fsT++ K t (E.γT (K ++ t) ν k) e))))
          (K.G⁰.m-cum (λ n → N.G (N.pt n)) (suc k) (hZ (E.γT (K ++ t) ν k) (N.pt (suc k)) (N.chain k) w β rβ)))

    mutual
      low⁰ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
        → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Z (o , r , B) K t x
      low⁰ a o r B gd K bd = genᴮ a (Qᶻ (o , r , B) K) (rules⁰ a o r B gd K bd)
        (λ le rx q d → cl o r B gd K bd le rx d (q d))

      rules⁰ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → Rules a (Qᶻ (o , r , B) K)
      rules⁰ a o r B gd K bd = record
        { qz = λ {t} {x} e0 d w β rβ →
            subst (λ u → K.M⁰ (E.ψ [] (K ++ u) ∷ []) (proj₁ (BS.ψ a o r B zero w β x))) (sym (emptyᵀ t e0))
              (subst (λ u → K.M⁰ (E.ψ [] u ∷ []) (proj₁ (BS.ψ a o r B zero w β x))) (sym (++-identityʳ K))
                (K.G⁰.m⊴ rβ (ψ-⊵ᴮ a o r B zero w β x)))
        ; q1 = λ {t} {x} e1 _ q d w β rβ → nextψᴷ K t e1 (BS.ψ a o r B zero w β x) (q (dw (o , r , B) ◃s d) w β rβ)
        ; qL = λ {t} {x} eω _ h d w β rβ → limψᴷ K t eω _ (λ n → h n d w β rβ)
        ; qΩ = λ p {t} {ν} g e nu hR hQ d →
            node⁰ o r B gd K bd p g e nu hR (λ η c l → hQ η c l (dnd (o , r , B) p g d c)) d
        ; qU = emb⁰ a o r B gd K bd
        ; qw = λ {t} {x} {x′} _ q lt d w β rβ → K.mw (q (dw (o , r , B) lt d) w β rβ) (BS.mono a o r B zero w β lt) }

      emb⁰ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K
        → (c : CH a) {t u : E.T} {x : Tr a} (y : ChTᵍ a c) → GR.R a t x → Qᶻ (o , r , B) K t x → GR.R (chLᵍ a c) u (chTᵍ a c y)
        → Qᶻ (o , r , B) K (t ++ u) (upᵍ x c y)
      emb⁰ (nd s h) o r B gd K bd c {x = x} (y , e) rx qx ry d =
        row⁰ s h o r B gd K bd c x y e (qx (dw (o , r , B) (◃u x c y e) d))
          (lowAll (nd s h) o r B gd K bd rx (dw (o , r , B) (◃u x c y e) d)) ry d

      fb⁰ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) {y′ : Tr (h c)} → Keepᵗ (o , r , B) K t x → GR.R (h c) u y′
        → Dm (stepˢ (o , r , B) c x) y′
        → (w′ : zero ≤ h c) (β′ : Tr⁺ zero) → K.M⁰ (E.ψ [] (K ++ t) ∷ []) (proj₁ β′)
        → K.M⁰ (E.ψ [] (K ++ (t ++ u)) ∷ [])
            (proj₁ (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) zero w′ β′ y′))
      fb⁰ s h o r B gd K bd c {t} {u} x {y′} kx ry d′ w′ β′ rβ′ =
        subst (λ z → K.M⁰ (E.ψ [] z ∷ [])
            (proj₁ (BS.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x) zero w′ β′ y′)))
          (++-assoc K t u)
          (low⁰ (h c) (proj₂ o c) (proj₂ r c) (λ i u′ → BS.ψ (nd s h) o r B i (inc c u′) (B i (inc c u′)) x)
            (good-ch s h r gd c) (K ++ t) (slot-step (o , r , B) K bd c kx) ry d′ w′ β′ rβ′)

      row⁰ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → Good (nd s h) r → ∀ K → SlotBd (o , r , B) K
        → (c : Ch s) {t u : E.T} (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
        → Z (o , r , B) K t x → Keepᵗ (o , r , B) K t x → GR.R (h c) u y → Dm (o , r , B) (up x c y e)
        → Z (o , r , B) K (t ++ u) (up x c y e)
      row⁰ s h o r B gd K bd c x y e zx kx ry d (inu ws) β rβ =
        fb⁰ s h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) (ws c) (BS.ψ (nd s h) o r B zero (inu ws) β x) (zx (inu ws) β rβ)
      row⁰ (sΩ k) h o r B gd K bd c x y e zx kx ry d (ink v) β rβ =
        fb⁰ (sΩ k) h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) (v ∙ proj₂ (proj₁ o) c)
          (BS.ψ (nd (sΩ k) h) o r B zero (ink v) β x) (zx (ink v) β rβ)
      row⁰ sS h o r B gd K bd c x y e zx kx ry d (inc c′ v) β rβ =
        fb⁰ sS h o r B gd K bd c x kx ry (dch (o , r , B) c x y e d) v (BS.ψ (nd sS h) o r B zero (inc c′ v) β x) (zx (inc c′ v) β rβ)
      row⁰ sL g o r B gd K bd m {t} {u} x y e zx kx ry d (inc n v) β rβ =
        cW-ind (λ Z′ → K.M⁰ (E.ψ [] (K ++ (t ++ u)) ∷ []) (proj₁ Z′)) (way g (proj₁ o) m n)
          (λ u′ → fb⁰ sL g o r B gd K bd n x kx (emb-pres (g n) (proj₂ o n) u′ (y , e) ry) (dem (o , r , B) m n x y e u′ d)
                    v (BS.ψ (nd sL g) o r B zero (inc n v) β x) (zx (inc n v) β rβ))
          (λ u′ → fb⁰ sL g o r B gd K bd m x kx ry (dch (o , r , B) m x y e d)
                    (v ∙ u′) (BS.ψ (nd sL g) o r B zero (inc n v) β x) (zx (inc n v) β rβ))
      row⁰ (sΩ k) h o (.(just S) , rs) B ((S , refl) , gs) K bd c {t} {u} x y e zx kx ry d (inc c′ v) β rβ =
        cW-ind (λ Z′ → K.M⁰ (E.ψ [] (K ++ (t ++ u)) ∷ []) (proj₁ Z′)) (route S zero c′ v)
          (λ u′ → fb⁰ (sΩ k) h o (just S , rs) B ((S , refl) , gs) K bd c x kx ry (dch (o , (just S , rs) , B) c x y e d)
                    (back S c u′) (BS.ψ (nd (sΩ k) h) o (just S , rs) B zero (inc c′ v) β x) (zx (inc c′ v) β rβ))
          (λ u′ → subst (λ z → K.M⁰ (E.ψ [] z ∷ [])
                      (proj₁ (seen S zero (downOk (h c′) (proj₂ o c′) zero v) u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B zero (inc c′ v) β x) c
                              ⊞ BS.ψ (h c) (proj₂ o c) (rs c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
                    (++-assoc K t u)
                    (rr⁰ o S rs B c x y e d c′ v u′ (BS.ψ (nd (sΩ k) h) o (just S , rs) B zero (inc c′ v) β x) (K ++ t)
                      (zx (inc c′ v) β rβ) ry))
```

## 终点

```agda
    low⁰-all : Low⁰
    low⁰-all {a} o r B gd K bd rx d = low⁰ a o r B gd K bd rx d

    module _ (rb : RootBd) (ri : End.RootIn 𝒟) where
      folded⁰ : ∀ n → K.M⁰ (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)
      folded⁰ n = low⁰ (tw n) (Ok-tw n) (rb-tw n) (baseᴮ n) (good-tw n) [] (rb n) (dom-top (dom-keel n)) (ri n)
        (z≤ (tw n)) (betaᴮ n) (K.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)))

      ebo-endᶜ : toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
      ebo-endᶜ = ≼-trans reference (l≼ (λ n →
        ≼-trans (Exit₀.exit exitᵍ (HC.of⁰ (folded⁰ n)) (HC.ex-of⁰ (folded⁰ n)) (hs n)) (upperᴮ n)))
```

自身行换成上折的一格 (`YiSOUp.UpMis`, 同 `YiSOTw1.EndU`).

```agda
ebo-endᶜᵁ : (𝒟 : Domˢ) → UpMis → Sys.NodeMis 𝒟 → Sys.RebRow 𝒟 → Zero.RebRow⁰ 𝒟 → Zero.CloseRow⁰ 𝒟
  → RootBd → End.RootIn 𝒟 → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
ebo-endᶜᵁ 𝒟 um nm rr rr⁰ cl rb ri = Zero.Main⁰.ebo-endᶜ 𝒟 nm (UpAll.self←up um 𝒟) rr rr⁰ cl rb ri
```

`CloseNF⁰` 在域取全体时不成立: 层号 0 (没有槽位, `SlotBd` 空), 上下文 K = 1 + ω, 输入 mz, s = t = 0; ψ₀(1 + ω) 不是标准形.

```agda
¬closeNF-all : Zero.CloseNF⁰ allˢ → ⊥
¬closeNF-all f = ¬1ω (nf-le (nfp-a (nf-hd (proj₁
  (f (Ok-tw 0) (rb-tw 0) (B₀ zero) tt (E.𝟏 ∷ ω₀) (λ ()) {s = []} {t = []} {x = zero} (inj₂ refl) H.mz tt)))))
```

前提各自可满足: 空域上两条新行空洞地成立 (`RootIn` 在空域上不成立; 联合可满足性同 `YiSOEnd.End` 一样未知).

```agda
noneˢ : Domˢ
noneˢ = record { Dm = λ _ _ → ⊥ ; dw = λ _ _ () ; dnd = λ _ _ _ () ; dch = λ _ _ _ _ _ () ; dem = λ _ _ _ _ _ _ _ () }

close-none : Zero.CloseRow⁰ noneˢ
close-none o r B gd K bd le rx ()

rebrow⁰-none : Zero.RebRow⁰ noneˢ
rebrow⁰-none o S rs B c x y e ()
```
