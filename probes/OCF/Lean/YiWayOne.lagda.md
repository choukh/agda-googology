# 产出端折叠的 `T⁺ʷᵖ` 不低于 ψ₀(Ω_Ω+1) 与 ψ₀(Ω_Ω+Ω₁) (无前提)

验收文件. 编译定理 `ΩΩ+1ᵖ`, `χ₁≼ᵖ : S2.χ 1 ≼ NA.read T⁺ʷᵖ` (参照由 `S2.χ1-label` 验收为 ψ₀(Ω_Ω+Ω₁)), 只是下界. [YiDlVOne](YiDlVOne.lagda.md) 搬到 [YiProdFold](YiProdFold.lagda.md): 消费端的单调要带标注的第一位置 `CpA`, 由带标注的加法 (`plusA-cp`) 与沿路径诱导的标注 (`cpInd`) 拼出; 外层折叠的标注由 `fgC` 去掉.
上下文引理 `Ctx.ctx` 对一族满足四条单步的函数陈述, 实例两个: 外层观察 `Fo` 与根结点的内层折叠 `gk₁ᵖ` (它带同支标注; 目标层 0 上两者不定义性相同).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; lev; succ; psum; chain; dnLc; add-cp; nodeAt-dn)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; none; at; Kfk; nrmk; nrmk-lgl; Pk; Lw-tw)
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′; run; ΩT′; ΨN′-dn)
open import OCF.Lean.YiZipFold using (rootZ)
open import OCF.Lean.YiCtxFold using (SB)
open import OCF.Lean.YiCtxAnn using
  ( Mk; noM; sucM; limM; lcM; Pv; noP; sucP; limP; lcP; mS; mL; mE; mB; pS; pL; pM; pB; CpA; DnA; cmpe₀ )
open import OCF.Lean.YiProdArith using (NE; NE-plus; NE-Kfk; plusM; plusP; KfkM; KfkP; plusA-weak; plusA-cp; fgC)
open import OCF.Lean.YiProdFold using
  ( PX; pos; mvx; selfR; sub₂; subℕ; subΩ; Xm; Ψs; Ψᵖ; Ψᵖ-cp; ptsΩ; Φ; Φmk; Φpv; NE-Φ; Φ-cpA; chT; chP
  ; noS; fx; T⁺ʷᵖ )
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValRel using (read≅)
open import OCF.Lean.YiWayRel using (WR′)
open import OCF.Lean.YiDlVBtbo using (Vw; psum≽)
open import OCF.Lean.YiDlVOne using (cp≼)
open import OCF.Lean.YiWayBtbo using (Pᵖ; ptRᵖ; FRᵖ; btbo-Twᵖ2)
open import OCF.Lean.YiWayInto using (ΩT₀)
import OCF.Lean.YiBtboLower as YB
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Stage2 as S2
open Pk
```

## 1 `top` 是一切值的第一位置; 沿路径诱导的标注

```agda
topKfk : ∀ i {m} (T : Raw i → Raw m) → (∀ η → Cp m G.top (T η)) → ∀ ξ → Cp m G.top (Kfk i T ξ)
topKfk i T h G.zero = h G.zero
topKfk i T h (G.suc a) = inj₂ (0 , topKfk i T h a)
topKfk i T h (G.lim f) = inj₂ (0 , topKfk i T h (f 0))
topKfk i T h (G.lc r g) = inj₂ (topKfk i T h (g (Lay.tp (Lo i r))))
topKfk zero T h (G.em () a)
topKfk (suc i) T h (G.em _ a) = topKfk i _ (λ b → h _) a
topKfk (lim f) T h (G.em n a) = topKfk (f n) _ (λ b → h _) a
topKfk (lc k g) T h (G.em (η , l) a) = topKfk (g η) _ (λ b → h _) a
topKfk i T h G.top = h G.top

topΦ : ∀ m {k} (V : Lw k) X ξ → Cp m G.top (Φ m V X ξ)
topΦ m V X G.zero = inj₁ refl
topΦ m V X (G.suc a) = inj₂ (0 , topΦ m V X a)
topΦ m V X (G.lim f) = inj₂ (0 , topΦ m V X (f 0))
topΦ m V X (G.lc r g) = inj₂ (topΦ m V X (g (mvx X r (Lay.tp (Lo m (pos X r))))))
topΦ m w0 X (G.em () a)
topΦ m (ws V) X (G.em _ a) = topΦ m V (sub₂ X) a
topΦ m (wl V st) X (G.em n a) = topΦ m (V n) (subℕ X n) a
topΦ m (wΩ V w) X (G.em (η , l) a) = topΦ m (V η l) (subΩ X η l) a
topΦ m w0 X G.top = inj₂ (0 , inj₁ refl)
topΦ m (ws V) X G.top = inj₂ (topΦ m V (sub₂ X) _)
topΦ m (wl V st) X G.top = inj₂ (0 , topΦ m (V 0) (subℕ X 0) G.top)
topΦ m (wΩ {k} {g} V none) X G.top = inj₂ (0 , topΦ m (V G.top tt) (subΩ X _ _) G.top)
topΦ m (wΩ {k} {g} V (at ρ e)) X G.top =
  inj₂ (topKfk k _ (λ η → topΦ m (V (nrmk k η) (nrmk-lgl k η)) (subΩ X _ _) G.top) _)

topΨs : ∀ m j (w : Way′ m j) (gm : (η : Raw j) → Pv η → Raw m) c cp → (∀ η ρ → Cp m G.top (gm η ρ)) →
  Cp m G.top (Ψs m j w gm c cp)
topΨs m j (keep′ p t) gm c cp h = inj₂ (nodeAt-dn m p G.lc dnLc (λ η → gm (run t η) noP) (h _ _))
topΨs m j fold′ gm c cp h = inj₂ (0 , h (c 0) (cp 0))

topΩT : ∀ m j (u : Way′ m j) K o → (∀ η → Cp m G.top (K η)) → Cp m G.top (o 0) → Cp m G.top (ΩT′ m j u K o)
topΩT m j (keep′ p t) K o hK ho = inj₂ (nodeAt-dn m p G.lc dnLc (λ η → K (run t η)) (hK _))
topΩT m j fold′ K o hK ho = inj₂ (0 , ho)

topᵖ : ∀ m {k} (V : Lw k) S x ξ μ π → Cp m G.top (Ψᵖ m V S x ξ μ π)
topᵖ m V S x G.zero μ π = inj₁ refl
topᵖ m V S x (G.suc a) μ π = inj₂ (0 , topᵖ m V S x a (mS μ) (pS π))
topᵖ m V S x (G.lim f) μ π = inj₂ (0 , topᵖ m V S x (f 0) (mL μ 0) (pL π 0))
topᵖ m {k} V S x (G.lc r g) μ π =
  inj₂ (ΨN′-dn m k r (x r (mE μ)) _ _ (topᵖ m V S x (g (Lay.tp (Lo k r))) (mB μ _) (pB π _)))
topᵖ m w0 S x (G.em () a) μ π
topᵖ m (ws V) S x (G.em _ a) μ π = topᵖ m V _ _ a noM noP
topᵖ m (wl V st) S x (G.em n a) μ π = topᵖ m (V n) _ _ a noM noP
topᵖ m (wΩ V w) S x (G.em (η , l) a) μ π = topᵖ m (V η l) _ _ a noM noP
topᵖ m w0 S x G.top μ π = inj₂ (0 , inj₁ refl)
topᵖ m {suc k} (ws V) S x G.top μ π =
  topΨs m k (x (inj₁ tt) nothing) _ (chT k V) (chP k V) (λ η ρ → topᵖ m V _ _ η noM ρ)
topᵖ m (wl V st) S x G.top μ π = inj₂ (0 , topᵖ m (V 0) _ _ G.top noM noP)
topᵖ m (wΩ {k} {g} V w) S x G.top μ π = topΩT m k (rootZ m k g w (λ r → x r nothing)) _ _
  (topKfk k _ (λ η → topᵖ m (V (nrmk k η) (nrmk-lgl k η)) _ _ G.top noM noP))
  (topᵖ m (V G.top tt) _ _ G.top noM noP)

module _ {k : LF} {S : Pre k → Set} where
  cpInd : ∀ {a t : Raw k} → Cp k a t → ∀ μ π → Σ (Mk S a) λ μ₀ → Σ (Pv a) λ π₀ → CpA S (a , μ₀ , π₀) t μ π
  dnInd : ∀ {a} (t : Raw k) → Dn k a t → ∀ μ π → Σ (Mk S a) λ μ₀ → Σ (Pv a) λ π₀ → DnA S (a , μ₀ , π₀) t μ π
  cpInd (inj₁ refl) μ π = μ , π , inj₁ refl
  cpInd (inj₂ p) μ π = proj₁ (dnInd _ p μ π) , proj₁ (proj₂ (dnInd _ p μ π)) , inj₂ (proj₂ (proj₂ (dnInd _ p μ π)))
  dnInd G.zero () μ π
  dnInd (G.suc d) p μ π = cpInd p (mS μ) (pS π)
  dnInd (G.lim f) (n , p) μ π =
    proj₁ (cpInd p (mL μ n) (pL π n)) , proj₁ (proj₂ (cpInd p (mL μ n) (pL π n))) , (n , proj₂ (proj₂ (cpInd p (mL μ n) (pL π n))))
  dnInd (G.lc r g) p μ π = cpInd p (mB μ _) (pB π _)
  dnInd {G.em i x} (G.em j d) p μ π = noM , noP , p
  dnInd {G.zero} (G.em j d) () μ π
  dnInd {G.suc _} (G.em j d) () μ π
  dnInd {G.lim _} (G.em j d) () μ π
  dnInd {G.lc _ _} (G.em j d) () μ π
  dnInd {G.top} (G.em j d) () μ π
  dnInd G.top () μ π
```

## 2 链的第 1 点

```agda
V2 : Lw (tw 2)
V2 = Lw-tw 2

Sp : Pre (tw 2) → Set
Sp = SB (tw 2) (G.top , tt , inj₁ tt)

p₀ : Pre (tw 2)
p₀ = G.top , tt , inj₁ tt

S₀ : Pre (tw 2) → Set
S₀ r = noS {suc (tw 2)} (inj₂ r)

x₀ : Xm zero (tw 2) S₀
x₀ r = fx zero (suc (tw 2)) (inj₂ r)

VT : (η : R) → Lw (up zero (nrmk zero η))
VT η = Vw (nrmk zero η) (nrmk-lgl zero η)

XT : (η : R) → PX (tw 2) (up zero (nrmk zero η))
XT η = subΩ (selfR (tw 2)) (nrmk zero η) (nrmk-lgl zero η)

Tt′ : R → Raw (tw 2)
Tt′ η = Φ (tw 2) (VT η) (XT η) G.top

μT : ∀ η → Mk Sp (Tt′ η)
μT η = Φmk (VT η) (XT η) Sp (λ _ → nothing) G.top

πT : ∀ η → Pv (Tt′ η)
πT η = Φpv (VT η) (XT η) G.top

gK′ : R → Raw (tw 2)
gK′ ζ = plus (tw 2) G.top (Kfk zero Tt′ ζ)

ch1 : chT (tw 2) V2 1 ≡ G.lc p₀ gK′
ch1 = refl

πc : Pv (G.lc p₀ gK′)
πc = chP (tw 2) V2 1

pB-form : ∀ ζ → pB πc ζ ≡ plusP noP (Kfk zero Tt′ ζ) (KfkP zero πT ζ)
pB-form ζ = refl

pM-form : ∀ ζ → pM πc ζ ≡ plusM noM (Kfk zero Tt′ ζ) (KfkM zero μT ζ)
pM-form ζ = refl

Fo : R → R
Fo ζ = Ψᵖ zero V2 S₀ x₀ (gK′ ζ) noM (pB πc ζ)

gk₁ᵖ : R → R
gk₁ᵖ ζ = Ψᵖ zero V2 Sp (cmpe₀ p₀) (gK′ ζ) (pM πc ζ) (pB πc ζ)

dᵖ : ℕ → R
dᵖ = chain zero gk₁ᵖ

T⁺-formᵖ : T⁺ʷᵖ ≡ G.lim (λ n → Ψᵖ zero V2 S₀ x₀ (chT (tw 2) V2 n) noM (chP (tw 2) V2 n))
T⁺-formᵖ = refl

term₁ᵖ : Ψᵖ zero V2 S₀ x₀ (chT (tw 2) V2 1) noM (chP (tw 2) V2 1) ≡ G.lim (λ n → Fo (dᵖ n))
term₁ᵖ = refl
```

## 3 单步

`up≼`: 消费端在带标注的第一位置上单调. 根位置的下界 `btbo-gen` 对一切 `S`, `x` (目标层 0 上的派发只能折叠).

```agda
up≼ : ∀ {S} (x : Xm zero (tw 2) S) {A μA πA B μB πB} → CpA S (A , μA , πA) B μB πB →
  NA.read (Ψᵖ zero V2 S x A μA πA) ≼ NA.read (Ψᵖ zero V2 S x B μB πB)
up≼ x c = cp≼ (Ψᵖ-cp zero V2 _ x c)

wr0 : ∀ {j : M.LF} {j′ : N.LF} (w′ : Way′ N.zero j′) → WR′ M.zero N.zero {j} MF.fold w′
wr0 (keep′ () t)
wr0 fold′ = tt

btbo-gen : ∀ S (x : Xm zero (tw 2) S) → D.BTBOᴵ ≼ NA.read (Ψᵖ zero V2 S x G.top noM noP)
btbo-gen S x = ≼-trans YB.btbo (l≼ (λ n → ΩT₀ _ _ _ n (≼-trans
  (≅→≼ (read≅ (FRᵖ (proj₁ (ptRᵖ n)) _ _ (proj₂ (ptRᵖ n)) (λ r r′ q ε → wr0 _))))
  (psum≽ (λ i → Ψᵖ zero (Vw (co (Pᵖ i)) (lw (Pᵖ i))) (λ r → S (co (Pᵖ i) , lw (Pᵖ i) , r))
    (λ r → x (co (Pᵖ i) , lw (Pᵖ i) , r)) G.top noM noP) n))))

NEK : ∀ ξ → NE (Kfk zero Tt′ ξ)
NEK = NE-Kfk zero (λ η → NE-Φ (VT η) (XT η) G.top)

hzK : ∀ ξ → CpA Sp (G.top , noM , noP) (gK′ ξ) (pM πc ξ) (pB πc ξ)
hzK ξ = plusA-weak noM noP (Kfk zero Tt′ ξ) (KfkM zero μT ξ) (KfkP zero πT ξ) (NEK ξ)

hsK : ∀ a → CpA Sp (G.suc (gK′ a) , sucM (pM πc a) , sucP (pB πc a)) (gK′ (G.suc a)) (pM πc (G.suc a)) (pB πc (G.suc a))
hsK a = inj₂ (1 , plusA-cp noM noP (plus (tw 2) (Kfk zero Tt′ a) (Tt′ (G.suc a))) _ _
  (NE-plus (Tt′ (G.suc a)) (NEK a) (NE-Φ (VT (G.suc a)) (XT (G.suc a)) G.top))
  (plusA-cp (KfkM zero μT a) (KfkP zero πT a) (Tt′ (G.suc a)) (μT (G.suc a)) (πT (G.suc a))
    (NE-Φ (VT (G.suc a)) (XT (G.suc a)) G.top)
    (proj₂ (proj₂ (cpInd (topΦ (tw 2) (VT (G.suc a)) (XT (G.suc a)) G.top) (μT (G.suc a)) (πT (G.suc a)))))))
```

`top` 处: `gK′ top` 是根结点, 它的内层折叠的链第 1 点.

```agda
X₀ : PX (tw 2) (suc zero)
X₀ = subΩ (selfR (tw 2)) G.top tt

gm₀′ : R → Raw (tw 2)
gm₀′ = Φ (tw 2) w0 (sub₂ X₀)

G₀ : R → Raw (tw 2)
G₀ ζ = plus (tw 2) G.top (gm₀′ ζ)

top-form : gK′ G.top ≡ G.lc p₀ G₀
top-form = refl

GK₃ : R → R
GK₃ ζ = Ψᵖ zero V2 Sp (cmpe₀ p₀) (G₀ ζ) (pM (pB πc G.top) ζ) (pB (pB πc G.top) ζ)

eᵖ : ℕ → R
eᵖ = chain zero GK₃

c₃a : Cp zero (G.suc G.top) (eᵖ 1)
c₃a = add-cp zero G.lc dnLc G.top (topᵖ zero V2 Sp (cmpe₀ p₀) (G₀ G.top) (pM (pB πc G.top) G.top) (pB (pB πc G.top) G.top))

y₀ : Raw (tw 2)
y₀ = gm₀′ G.top

c₃d : CpA Sp (G.suc (gK′ G.zero) , sucM (pM πc G.zero) , sucP (pB πc G.zero))
  (G₀ (G.suc G.top)) (mB (pM πc G.top) (G.suc G.top)) (pB (pB πc G.top) (G.suc G.top))
c₃d = inj₂ (1 , plusA-cp noM noP (plus (tw 2) y₀ y₀) _ _ (NE-plus y₀ (NE-Φ w0 (sub₂ X₀) G.top) (NE-Φ w0 (sub₂ X₀) G.top))
  (plusA-cp (Φmk w0 (sub₂ X₀) Sp (λ _ → nothing) G.top) (Φpv w0 (sub₂ X₀) G.top) y₀ _ _ (NE-Φ w0 (sub₂ X₀) G.top)
    (proj₂ (proj₂ (cpInd (topΦ (tw 2) w0 (sub₂ X₀) G.top) _ _)))))

c₃c : CpA Sp (G₀ (G.suc G.top) , mB (pM πc G.top) (G.suc G.top) , pB (pB πc G.top) (G.suc G.top))
  (G₀ (eᵖ 1)) (mB (pM πc G.top) (eᵖ 1)) (pB (pB πc G.top) (eᵖ 1))
c₃c = plusA-cp noM noP (gm₀′ (eᵖ 1)) _ _ (NE-Φ w0 (sub₂ X₀) (eᵖ 1)) (Φ-cpA w0 (sub₂ X₀) Sp (λ _ → nothing) c₃a)
```

## 4 上下文引理 (对一族函数) 与两个实例

```agda
module Ctx (F : R → R) (B : R) (hb : D.BTBOᴵ ≼ NA.read B) (hz : ∀ ξ → NA.read B ≼ NA.read (F ξ))
  (hs : ∀ a → NA.read (succ zero (F a)) ≼ NA.read (F (G.suc a)))
  (ht : NA.read (succ zero (F G.zero)) ≼ NA.read (F G.top))
  (hl : ∀ f n {X : L.Ordᶜ L.zero} → X ≼ NA.read (F (f n)) → X ≼ NA.read (F (G.lim f))) where

  ctx : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ →
    L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (F ξ)
  ctx z≼ ξ q = ≼-trans hb (hz ξ)
  ctx (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (F a) (ctx p a refl)) (hs a)
  ctx (s≼s p) G.top refl = ≼-trans (NA.suc-lower (F G.zero) (ctx p G.zero refl)) ht
  ctx (≼l n p) (G.lim f) refl = hl f n (ctx p (f n) refl)
  ctx (l≼ h) ξ q = l≼ (λ n → ctx (h n) ξ q)
  ctx (≼i {p = ()} x ex p) ξ q
  ctx (i≼ {p = ()} h) ξ q
  ctx (≼u {r = ()} p) ξ q
  ctx (u≼ {r = ()} p) ξ q

module Ci = Ctx gk₁ᵖ (Ψᵖ zero V2 Sp (cmpe₀ p₀) G.top noM noP) (btbo-gen Sp (cmpe₀ p₀))
  (λ ξ → up≼ (cmpe₀ p₀) (hzK ξ)) (λ a → up≼ (cmpe₀ p₀) (hsK a))
  (≼-trans (up≼ (cmpe₀ p₀) c₃d) (≼-trans (up≼ (cmpe₀ p₀) c₃c) (≼l 1 (≼-refl _))))
  (λ f n q → ≼l n q)

module Co = Ctx Fo (Ψᵖ zero V2 S₀ x₀ G.top noM noP) (btbo-gen S₀ x₀)
  (λ ξ → up≼ x₀ (fgC Sp S₀ _ _ _ (hzK ξ))) (λ a → up≼ x₀ (fgC Sp S₀ _ _ _ (hsK a)))
  (≼-trans (up≼ x₀ (fgC Sp S₀ _ _ _ c₃d)) (≼-trans (up≼ x₀ (fgC Sp S₀ _ _ _ c₃c)) (≼l 1 (≼-refl _))))
  (λ f n q → ≼l n q)
```

## 5 ψ₀(Ω_Ω+1) 与 ψ₀(Ω_Ω+Ω₁)

```agda
c₁ : Cp (tw 2) (G.suc G.top) (chT (tw 2) V2 1)
c₁ = inj₂ (inj₂ (inj₂ (0 , inj₁ refl)))

s≼ᵖ : NA.read (succ zero (Ψᵖ zero V2 S₀ x₀ G.top noM noP)) ≼ NA.read T⁺ʷᵖ
s≼ᵖ = ≼l 1 (up≼ x₀ (fgC S₀ S₀ _ _ _ (proj₂ (proj₂ (cpInd {S = S₀} c₁ noM πc)))))

ΩΩ+1ᵖ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read T⁺ʷᵖ
ΩΩ+1ᵖ = ≼-trans (NA.suc-lower {x = L.Ω S2.ℓ₀} (Ψᵖ zero V2 S₀ x₀ G.top noM noP) (btbo-gen S₀ x₀)) s≼ᵖ

ch≼ᵖ : ∀ m → S2.ch m ≼ NA.read (dᵖ m)
ch≼ᵖ zero = ≼-refl _
ch≼ᵖ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ (S2.ch m))))))
  (NA.plus≽ (dᵖ m) (gk₁ᵖ (dᵖ m)) (Ci.ctx (ch≼ᵖ m) (dᵖ m) refl))

χ₁≼ᵖ : S2.χ 1 ≼ NA.read T⁺ʷᵖ
χ₁≼ᵖ = ≼l 1 (l≼ (λ m → ≼l m (Co.ctx (ch≼ᵖ m) (dᵖ m) refl)))
```
