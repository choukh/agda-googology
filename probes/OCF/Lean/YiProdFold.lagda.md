# 来历的产出端: 自折叠的输出带上同支标注, 消费端读标注

非验收文件. 编译定理, 无前提: 对一切派发 `D` 与证据来源 `E`, `Ψᵖ-lgl` 成立; 闭项 `TΛᵖ` (读法 ψ₀(Λ)), `Twᵖ`, `T⁺ʷᵖ` 合法. 消费端 `Ψᵖ` 逐字照 [YiCtxAnn](YiCtxAnn.lagda.md) 的 `Ψᴹ`, 嵌入与 `top` 的子句写全; 后继层号 `top` 那一句的链改由产出端 `Φ` 给: `Φ` 是只保留的自折叠 (派发 `PX` 带位置, 分支域上的搬运, 与同支证据的传递 `evx`), 输出在 Ω 结点层号上带标注 (`Φmk`, `Φpv`), 链点的标注由带标注的加法接起来 (`chP`).
同支证据只在两处产生: `Φ` 在 Ω 结点层号的某一支 `η` 里折叠 (嵌入或 `Kfk` 的内层折叠) 时, 这一支里的两个位置的证据是 `refl` (`subΩ`); 其余处只传递. 不判定两棵裸树相等. 有限测试在 [YiProdTest](YiProdTest.lagda.md). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiProdFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  (Br; lgLc; lev; R; succ; psum; succ-lgl; psum-lgl; plus-lgl; plus-weak; nodeAt; nodeAt-lgl)
open import OCF.Lean.YiLamFold using
  ( Kfk; Kfk-br; Kfk-lgl; Kfk-cp; nrmk; nrmk-lgl; Wit; none; at; Lw; w0; ws; wl; wΩ; Pk; pk; Lw-tw; VΛ )
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′; Ext′; run; ΨN′; ΨN′-dn; ΨN′-lgl; ΩT′; ΩT′-lgl; Br-run)
open import OCF.Lean.YiZipFold using (rootZ; dl′)
open import OCF.Lean.YiCtxFold using (Ev; SB; evF; module FoldC)
open import OCF.Lean.YiCtxAnn using
  ( Mk; noM; limM; lcM; Pv; noP; limP; lcP; mS; mL; mE; mB; pS; pL; pM; pB; An; CpA; DnA; LglA; cpA-no; dnA-no; lglA-no )
open import OCF.Lean.YiProdArith
open Pk
```

## 1 产出端的派发

`PX m k`: 源位置 `r` 保留到目标位置 `pos r`, 分支域上的搬运 `mvx r`; `evx r r′ e`: 源里同支 (证据 `e`) 时目标里同支的证据. 自派发 `selfR` 原样传递; 进 Ω 结点层号的第 `η` 支 (`subΩ`) 时, 这一支里的两个位置给 `refl`.

```agda
record PX (m k : LF) : Set where
  constructor px
  field
    pos : Pre k → Pre m
    mvx : (r : Pre k) → Lay.A (Lo m (pos r)) → Lay.A (Lo k r)
    mtp : ∀ r → mvx r (Lay.tp (Lo m (pos r))) ≡ Lay.tp (Lo k r)
    mle : ∀ r {a b} → Le (Lo m (pos r)) a b → Le (Lo k r) (mvx r a) (mvx r b)
    mlg : ∀ r a → Lay.lg (Lo m (pos r)) a → Lay.lg (Lo k r) (mvx r a)
    evx : (r r′ : Pre k) → Maybe (SB k r r′) → Maybe (SB m (pos r) (pos r′))
open PX public

selfR : ∀ k → PX k k
selfR k = px (λ r → r) (λ r a → a) (λ r → refl) (λ r e → e) (λ r a l → l) (λ r r′ e → e)

sub₂ : ∀ {m k} → PX m (suc k) → PX m k
sub₂ x = px (λ r → pos x (inj₂ r)) (λ r → mvx x (inj₂ r)) (λ r → mtp x (inj₂ r)) (λ r → mle x (inj₂ r))
  (λ r → mlg x (inj₂ r)) (λ r r′ _ → evx x (inj₂ r) (inj₂ r′) nothing)

subℕ : ∀ {m f} → PX m (lim f) → ∀ n → PX m (f n)
subℕ x n = px (λ r → pos x (n , r)) (λ r → mvx x (n , r)) (λ r → mtp x (n , r)) (λ r → mle x (n , r))
  (λ r → mlg x (n , r)) (λ r r′ _ → evx x (n , r) (n , r′) nothing)

subΩ : ∀ {m k g} → PX m (lc k g) → ∀ η → Lgl k η → PX m (g η)
subΩ x η l = px (λ r → pos x (η , l , r)) (λ r → mvx x (η , l , r)) (λ r → mtp x (η , l , r))
  (λ r → mle x (η , l , r)) (λ r → mlg x (η , l , r)) (λ r r′ _ → evx x (η , l , r) (η , l , r′) (just refl))
```

根的分支域: `Wit` 的位置 `ρ` 的分支域搬成层号 `k` 的树.

```agda
rtv : ∀ {k} (g : Raw k → LF) (ρ : Pre (g G.top)) → lev (g G.top) ρ ≡ k → Lay.A (Lo (g G.top) ρ) → Raw k
rtv g ρ e a = subst Raw e (cv (g G.top) ρ a)

sR-lg : ∀ {a b : LF} (e : a ≡ b) (t : Raw a) → Lgl a t → Lgl b (subst Raw e t)
sR-lg refl t l = l

sR-cp : ∀ {a b : LF} (e : a ≡ b) {t u : Raw a} → Cp a t u → Cp b (subst Raw e t) (subst Raw e u)
sR-cp refl c = c

rt-lg : ∀ {k} (g : Raw k → LF) ρ e a → Lay.lg (Lo (g G.top) ρ) a → Lgl k (rtv g ρ e a)
rt-lg g ρ e a l = sR-lg e _ (cv-lg (g G.top) ρ a l)

rt-cp : ∀ {k} (g : Raw k → LF) ρ e {a b} → Le (Lo (g G.top) ρ) a b → Cp k (rtv g ρ e a) (rtv g ρ e b)
rt-cp g ρ e p = sR-cp e (cv-le (g G.top) ρ p)
```

## 2 后继层号 `top` 那一句

保留时与旧的相同 (分支不带标注); 折叠时链点带标注.

```agda
Xm : LF → (k : LF) → (Pre k → Set) → Set
Xm m k S = (r : Pre k) → Maybe (S r) → Way′ m (lev k r)

Ψs : ∀ m j → Way′ m j → ((η : Raw j) → Pv η → Raw m) → (c : ℕ → Raw j) → (∀ n → Pv (c n)) → Raw m
Ψs m j (keep′ p t) gm c cp = nodeAt m p G.lc (λ η → gm (run t η) noP)
Ψs m j fold′ gm c cp = G.lim (λ n → gm (c n) (cp n))

Ψs-lgl : ∀ m j (w : Way′ m j) gm c cp → Br (layer j) m (λ η → gm η noP) →
  (∀ n → Cp m (gm (c n) (cp n)) (gm (c (suc n)) (cp (suc n)))) → (∀ n → Lgl m (gm (c n) (cp n))) →
  Lgl m (Ψs m j w gm c cp)
Ψs-lgl m j (keep′ p t) gm c cp b st lg = nodeAt-lgl m p G.lc lgLc _ (Br-run t (λ η → gm η noP) b)
Ψs-lgl m j fold′ gm c cp b st lg = st , lg
```

## 3 折叠

```agda
module Prod (D : ∀ k K → Ext′ k K) (E : Ev) where
  open FoldC D E using (cmpe)

  Ψᵖ : ∀ m {k} → Lw k → (S : Pre k → Set) → Xm m k S → (t : Raw k) → Mk S t → Pv t → Raw m
  Ψᴬ : ∀ m {k} → Lw k → (S : Pre k → Set) → Xm m k S → An S → Raw m
  Ψᵖ-cp : ∀ m {k} (V : Lw k) S x {a : An S} {t μ π} → CpA S a t μ π → Cp m (Ψᴬ m V S x a) (Ψᵖ m V S x t μ π)
  Ψᵖ-dn : ∀ m {k} (V : Lw k) S x (a : An S) t μ π → DnA S a t μ π → Dn m (Ψᴬ m V S x a) (Ψᵖ m V S x t μ π)
  Ψᵖ-lgl : ∀ m {k} (V : Lw k) S x t μ π → LglA S t μ π → Lgl m (Ψᵖ m V S x t μ π)
  ptsΩ : ∀ k (g : Raw k → LF) → (∀ η → Lgl k η → Lw (g η)) → ℕ → Pk k

  Φ : ∀ m {k} → Lw k → PX m k → Raw k → Raw m
  Φ-cp : ∀ m {k} (V : Lw k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Φ m V x ξ) (Φ m V x ξ′)
  Φ-dn : ∀ m {k} (V : Lw k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Φ m V x ξ) (Φ m V x ξ′)
  Φ-lgl : ∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Φ m V x ξ)

  Φmk : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) (S : Pre (lc j h) → Set) → ((r : Pre k) → Maybe (S (pos x r))) →
    ∀ ξ → Mk S (Φ (lc j h) V x ξ)
  Φpv : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) ξ → Pv (Φ (lc j h) V x ξ)
  NE-Φ : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) ξ → NE (Φ (lc j h) V x ξ)
  Φ-cpA : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ {ξ ξ′} → Cp k ξ ξ′ →
    CpA S (Φ _ V x ξ , Φmk V x S σ ξ , Φpv V x ξ) (Φ _ V x ξ′) (Φmk V x S σ ξ′) (Φpv V x ξ′)
  Φ-dnA : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ {ξ} ξ′ → Dn k ξ ξ′ →
    DnA S (Φ _ V x ξ , Φmk V x S σ ξ , Φpv V x ξ) (Φ _ V x ξ′) (Φmk V x S σ ξ′) (Φpv V x ξ′)
  Φ-lglA : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ ξ → Lgl k ξ →
    LglA S (Φ _ V x ξ) (Φmk V x S σ ξ) (Φpv V x ξ)

  chT : ∀ k → Lw k → ℕ → Raw k
  chP : ∀ k (V : Lw k) n → Pv (chT k V n)
  chLb : ∀ k (V : Lw k) n → Lgl k (chT k V n)
  chL : ∀ k (V : Lw k) (S : Pre k → Set) n → LglA S (chT k V n) noM (chP k V n)
  chC : ∀ k (V : Lw k) (S : Pre k → Set) n → CpA S (chT k V n , noM , chP k V n) (chT k V (suc n)) noM (chP k V (suc n))
```

消费端. 结点那一句照 `Ψᴹ`; 嵌入下与 `top` 上没有标注.

```agda
  Ψᴬ m V S x (t , μ , π) = Ψᵖ m V S x t μ π

  Ψᵖ m V S x G.zero μ π = G.top
  Ψᵖ m V S x (G.suc a) μ π = succ m (Ψᵖ m V S x a (mS μ) (pS π))
  Ψᵖ m V S x (G.lim f) μ π = G.lim (λ n → Ψᵖ m V S x (f n) (mL μ n) (pL π n))
  Ψᵖ m {k} V S x (G.lc r g) μ π =
    ΨN′ m k r (x r (mE μ)) (λ ζ → Ψᵖ m V S x (g ζ) (mB μ ζ) (pB π ζ))
      (λ ζ → Ψᵖ (lev k r) V (SB k r) (cmpe V r) (g ζ) (pM π ζ) (pB π ζ))
  Ψᵖ m (ws V) S x (G.em _ a) μ π = Ψᵖ m V (λ r → S (inj₂ r)) (λ r → x (inj₂ r)) a noM noP
  Ψᵖ m (wl V st) S x (G.em n a) μ π = Ψᵖ m (V n) (λ r → S (n , r)) (λ r → x (n , r)) a noM noP
  Ψᵖ m (wΩ V w) S x (G.em (η , l) a) μ π = Ψᵖ m (V η l) (λ r → S (η , l , r)) (λ r → x (η , l , r)) a noM noP
  Ψᵖ m w0 S x G.top μ π = succ m G.top
  Ψᵖ m {suc k} (ws V) S x G.top μ π =
    Ψs m k (x (inj₁ tt) nothing) (λ η ρ → Ψᵖ m V (λ r → S (inj₂ r)) (λ r → x (inj₂ r)) η noM ρ) (chT k V) (chP k V)
  Ψᵖ m (wl V st) S x G.top μ π = G.lim (psum m (λ n → Ψᵖ m (V n) (λ r → S (n , r)) (λ r → x (n , r)) G.top noM noP))
  Ψᵖ m (wΩ {k} {g} V w) S x G.top μ π =
    ΩT′ m k (rootZ m k g w (λ r → x r nothing))
      (Kfk k (λ η → Ψᵖ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → S (nrmk k η , nrmk-lgl k η , r))
        (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top noM noP))
      (psum m (λ n → Ψᵖ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ r → S (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r))
        (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top noM noP))

  ptsΩ k g V zero = pk G.top tt
  ptsΩ k g V (suc n) =
    pk (plus k (co (ptsΩ k g V n)) (Ψᵖ k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ _ → ⊥)
         (λ r _ → D k (g (co (ptsΩ k g V n))) r) G.top noM noP))
       (plus-lgl k _ _ (lw (ptsΩ k g V n)) (Ψᵖ-lgl k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ _ → ⊥)
         (λ r _ → D k (g (co (ptsΩ k g V n))) r) G.top noM noP tt))

  Ψᵖ-cp m V S x (inj₁ refl) = inj₁ refl
  Ψᵖ-cp m V S x {a} {t} {μ} {π} (inj₂ p) = inj₂ (Ψᵖ-dn m V S x a t μ π p)

  Ψᵖ-dn m V S x a (G.suc d) μ π p = 0 , Ψᵖ-cp m V S x p
  Ψᵖ-dn m V S x a (G.lim f) μ π (n , p) = n , Ψᵖ-cp m V S x p
  Ψᵖ-dn m {k} V S x a (G.lc r g) μ π p = ΨN′-dn m k r (x r (mE μ)) _ _ (Ψᵖ-cp m V S x p)
  Ψᵖ-dn m (ws V) S x (G.em _ y , _) (G.em _ d) μ π (refl , p) = Ψᵖ-dn m V _ _ (y , noM , noP) d noM noP (dnA-no _ d p)
  Ψᵖ-dn m (wl V st) S x (G.em n y , _) (G.em _ d) μ π (refl , p) =
    Ψᵖ-dn m (V n) _ _ (y , noM , noP) d noM noP (dnA-no _ d p)
  Ψᵖ-dn m (wΩ V w) S x (G.em (η , l) y , _) (G.em _ d) μ π (refl , p) =
    Ψᵖ-dn m (V η l) _ _ (y , noM , noP) d noM noP (dnA-no _ d p)
  Ψᵖ-dn m V S x (G.zero , _) (G.em j d) μ π ()
  Ψᵖ-dn m V S x (G.suc _ , _) (G.em j d) μ π ()
  Ψᵖ-dn m V S x (G.lim _ , _) (G.em j d) μ π ()
  Ψᵖ-dn m V S x (G.lc _ _ , _) (G.em j d) μ π ()
  Ψᵖ-dn m V S x (G.top , _) (G.em j d) μ π ()
  Ψᵖ-dn m V S x a G.zero μ π ()
  Ψᵖ-dn m V S x a G.top μ π ()

  Ψᵖ-lgl m V S x G.zero μ π l = tt
  Ψᵖ-lgl m V S x (G.suc a) μ π l = succ-lgl m _ (Ψᵖ-lgl m V S x a (mS μ) (pS π) l)
  Ψᵖ-lgl m V S x (G.lim f) μ π (st , lf) = (λ n → Ψᵖ-cp m V S x (st n)) , (λ n → Ψᵖ-lgl m V S x _ _ _ (lf n))
  Ψᵖ-lgl m {k} V S x (G.lc r g) μ π (lg , mo , li) = ΨN′-lgl m k r (x r (mE μ)) _ _
    ((λ ζ l → Ψᵖ-lgl m V S x _ _ _ (lg ζ l)) , (λ ζ ζ′ l e l′ → Ψᵖ-cp m V S x (mo ζ ζ′ l e l′)))
    (λ ζ l → Ψᵖ-lgl (lev k r) V (SB k r) (cmpe V r) _ _ _ (li ζ l))
  Ψᵖ-lgl m (ws V) S x (G.em _ a) μ π l = Ψᵖ-lgl m V _ _ a noM noP (lglA-no _ a l)
  Ψᵖ-lgl m (wl V st) S x (G.em n a) μ π l = Ψᵖ-lgl m (V n) _ _ a noM noP (lglA-no _ a l)
  Ψᵖ-lgl m (wΩ V w) S x (G.em (η , lη) a) μ π l = Ψᵖ-lgl m (V η lη) _ _ a noM noP (lglA-no _ a l)
  Ψᵖ-lgl m w0 S x G.top μ π l = succ-lgl m G.top tt
  Ψᵖ-lgl m {suc k} (ws V) S x G.top μ π l = Ψs-lgl m k (x (inj₁ tt) nothing) _ (chT k V) (chP k V)
    ((λ η l → Ψᵖ-lgl m V _ _ η noM noP (lglA-no _ η l)) , (λ η η′ l e l′ → Ψᵖ-cp m V _ _ (cpA-no _ e)))
    (λ n → Ψᵖ-cp m V _ _ (chC k V _ n)) (λ n → Ψᵖ-lgl m V _ _ _ _ _ (chL k V _ n))
  Ψᵖ-lgl m (wl V st) S x G.top μ π l = psum-lgl m _ (λ n → Ψᵖ-lgl m (V n) _ _ G.top noM noP tt)
  Ψᵖ-lgl m (wΩ {k} {g} V w) S x G.top μ π l = ΩT′-lgl m k (rootZ m k g w (λ r → x r nothing)) _ _
    (Kfk-br k _ (λ η → Ψᵖ-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ _ G.top noM noP tt))
    (psum-lgl m _ (λ n → Ψᵖ-lgl m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) _ _ G.top noM noP tt))
```

产出端: 只保留的自折叠. 根见证缺时取部分和的极限 (同旧的 `ΩT′` 折叠一项).

```agda
  Φ m V x G.zero = G.top
  Φ m V x (G.suc a) = succ m (Φ m V x a)
  Φ m V x (G.lim f) = G.lim (λ n → Φ m V x (f n))
  Φ m V x (G.lc r g) = G.lc (pos x r) (λ a → Φ m V x (g (mvx x r a)))
  Φ m (ws V) x (G.em _ a) = Φ m V (sub₂ x) a
  Φ m (wl V st) x (G.em n a) = Φ m (V n) (subℕ x n) a
  Φ m (wΩ V w) x (G.em (η , l) a) = Φ m (V η l) (subΩ x η l) a
  Φ m w0 x G.top = succ m G.top
  Φ m {suc k} (ws V) x G.top = G.lc (pos x (inj₁ tt)) (λ a → Φ m V (sub₂ x) (mvx x (inj₁ tt) a))
  Φ m (wl V st) x G.top = G.lim (psum m (λ n → Φ m (V n) (subℕ x n) G.top))
  Φ m (wΩ {k} {g} V none) x G.top =
    G.lim (psum m (λ n → Φ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) G.top))
  Φ m (wΩ {k} {g} V (at ρ e)) x G.top = G.lc (pos x (G.top , tt , ρ)) (λ a →
    Kfk k (λ η → Φ m (V (nrmk k η) (nrmk-lgl k η)) (subΩ x (nrmk k η) (nrmk-lgl k η)) G.top)
      (rtv g ρ e (mvx x (G.top , tt , ρ) a)))

  Φ-cp m V x (inj₁ refl) = inj₁ refl
  Φ-cp m V x (inj₂ p) = inj₂ (Φ-dn m V x _ p)

  Φ-dn m V x (G.suc d) p = 0 , Φ-cp m V x p
  Φ-dn m V x (G.lim f) (n , p) = n , Φ-cp m V x p
  Φ-dn m V x {ξ} (G.lc r g) p =
    subst (λ u → Cp m (Φ m V x ξ) (Φ m V x (g u))) (sym (mtp x r)) (Φ-cp m V x p)
  Φ-dn m (ws V) x {G.em _ a} (G.em _ d) (refl , p) = Φ-dn m V (sub₂ x) d p
  Φ-dn m (wl V st) x {G.em n a} (G.em _ d) (refl , p) = Φ-dn m (V n) (subℕ x n) d p
  Φ-dn m (wΩ V w) x {G.em (η , l) a} (G.em _ d) (refl , p) = Φ-dn m (V η l) (subΩ x η l) d p

  Φ-lgl m V x G.zero l = tt
  Φ-lgl m V x (G.suc a) l = succ-lgl m _ (Φ-lgl m V x a l)
  Φ-lgl m V x (G.lim f) (st , lf) = (λ n → Φ-cp m V x (st n)) , (λ n → Φ-lgl m V x (f n) (lf n))
  Φ-lgl m V x (G.lc r g) (lg , mo) =
    (λ a l → Φ-lgl m V x _ (lg _ (mlg x r a l))) ,
    (λ a a′ l e l′ → Φ-cp m V x (mo _ _ (mlg x r a l) (mle x r e) (mlg x r a′ l′)))
  Φ-lgl m (ws V) x (G.em _ a) l = Φ-lgl m V (sub₂ x) a l
  Φ-lgl m (wl V st) x (G.em n a) l = Φ-lgl m (V n) (subℕ x n) a l
  Φ-lgl m (wΩ V w) x (G.em (η , lη) a) l = Φ-lgl m (V η lη) (subΩ x η lη) a l
  Φ-lgl m w0 x G.top l = succ-lgl m G.top tt
  Φ-lgl m {suc k} (ws V) x G.top l =
    (λ a l → Φ-lgl m V (sub₂ x) _ (mlg x (inj₁ tt) a l)) ,
    (λ a a′ l e l′ → Φ-cp m V (sub₂ x) (mle x (inj₁ tt) e))
  Φ-lgl m (wl V st) x G.top l = psum-lgl m _ (λ n → Φ-lgl m (V n) (subℕ x n) G.top tt)
  Φ-lgl m (wΩ {k} {g} V none) x G.top l =
    psum-lgl m _ (λ n → Φ-lgl m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) G.top tt)
  Φ-lgl m (wΩ {k} {g} V (at ρ e)) x G.top l =
    (λ a l → Kfk-lgl k _ (λ η → Φ-lgl m (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) G.top tt) _
      (rt-lg g ρ e _ (mlg x (G.top , tt , ρ) a l))) ,
    (λ a a′ l e′ l′ → Kfk-cp k _ (rt-cp g ρ e (mle x (G.top , tt , ρ) e′)))
```

产出端的标注. `σ`: 每个输出结点 (来自源位置 `r`) 相对外层目标的证据; 结点自己的分支上的证据是 `evx r · nothing`.

```agda
  Φmk V x S σ G.zero = noM
  Φmk V x S σ (G.suc a) = succM (Φmk V x S σ a)
  Φmk V x S σ (G.lim f) = limM (λ n → Φmk V x S σ (f n))
  Φmk V x S σ (G.lc r g) = lcM (σ r) (λ a → Φmk V x S σ (g (mvx x r a)))
  Φmk (ws V) x S σ (G.em _ a) = Φmk V (sub₂ x) S (λ r → σ (inj₂ r)) a
  Φmk (wl V st) x S σ (G.em n a) = Φmk (V n) (subℕ x n) S (λ r → σ (n , r)) a
  Φmk (wΩ V w) x S σ (G.em (η , l) a) = Φmk (V η l) (subΩ x η l) S (λ r → σ (η , l , r)) a
  Φmk w0 x S σ G.top = succM noM
  Φmk (ws V) x S σ G.top = lcM (σ (inj₁ tt)) (λ a → Φmk V (sub₂ x) S (λ r → σ (inj₂ r)) (mvx x (inj₁ tt) a))
  Φmk (wl V st) x S σ G.top = psumM (λ n → Φmk (V n) (subℕ x n) S (λ r → σ (n , r)) G.top)
  Φmk (wΩ {k} {g} V none) x S σ G.top =
    psumM (λ n → Φmk (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) S
      (λ r → σ (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top)
  Φmk (wΩ {k} {g} V (at ρ e)) x S σ G.top = lcM (σ (G.top , tt , ρ)) (λ a →
    KfkM k (λ η → Φmk (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) S (λ r → σ (nrmk k η , nrmk-lgl k η , r)) G.top)
      (rtv g ρ e (mvx x (G.top , tt , ρ) a)))

  Φpv V x G.zero = noP
  Φpv V x (G.suc a) = succP (Φpv V x a)
  Φpv V x (G.lim f) = limP (λ n → Φpv V x (f n))
  Φpv V x (G.lc r g) =
    lcP (λ a → Φmk V x (SB _ (pos x r)) (λ r′ → evx x r r′ nothing) (g (mvx x r a))) (λ a → Φpv V x (g (mvx x r a)))
  Φpv (ws V) x (G.em _ a) = Φpv V (sub₂ x) a
  Φpv (wl V st) x (G.em n a) = Φpv (V n) (subℕ x n) a
  Φpv (wΩ V w) x (G.em (η , l) a) = Φpv (V η l) (subΩ x η l) a
  Φpv w0 x G.top = succP noP
  Φpv (ws V) x G.top =
    lcP (λ a → Φmk V (sub₂ x) (SB _ (pos x (inj₁ tt))) (λ r′ → evx x (inj₁ tt) (inj₂ r′) nothing) (mvx x (inj₁ tt) a))
      (λ a → Φpv V (sub₂ x) (mvx x (inj₁ tt) a))
  Φpv (wl V st) x G.top = psumP (λ n → Φpv (V n) (subℕ x n) G.top)
  Φpv (wΩ {k} {g} V none) x G.top =
    psumP (λ n → Φpv (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) G.top)
  Φpv (wΩ {k} {g} V (at ρ e)) x G.top =
    lcP (λ a → KfkM k (λ η → Φmk (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) (SB _ (pos x (G.top , tt , ρ)))
          (λ r′ → evx x (G.top , tt , ρ) (nrmk k η , nrmk-lgl k η , r′) nothing) G.top)
          (rtv g ρ e (mvx x (G.top , tt , ρ) a)))
      (λ a → KfkP k (λ η → Φpv (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) G.top) (rtv g ρ e (mvx x (G.top , tt , ρ) a)))

  NE-Φ V x G.zero = tt
  NE-Φ V x (G.suc a) = NE-succ (NE-Φ V x a)
  NE-Φ V x (G.lim f) = λ n → NE-Φ V x (f n)
  NE-Φ V x (G.lc r g) = λ a → NE-Φ V x (g (mvx x r a))
  NE-Φ (ws V) x (G.em _ a) = NE-Φ V (sub₂ x) a
  NE-Φ (wl V st) x (G.em n a) = NE-Φ (V n) (subℕ x n) a
  NE-Φ (wΩ V w) x (G.em (η , l) a) = NE-Φ (V η l) (subΩ x η l) a
  NE-Φ w0 x G.top = NE-succ tt
  NE-Φ (ws V) x G.top = λ a → NE-Φ V (sub₂ x) _
  NE-Φ (wl V st) x G.top = NE-psum _ (λ n → NE-Φ (V n) (subℕ x n) G.top)
  NE-Φ (wΩ {k} {g} V none) x G.top = NE-psum _ (λ n → NE-Φ (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) G.top)
  NE-Φ (wΩ {k} {g} V (at ρ e)) x G.top = λ a → NE-Kfk k (λ η → NE-Φ (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) G.top) _

  Φ-cpA V x S σ (inj₁ refl) = inj₁ refl
  Φ-cpA V x S σ (inj₂ p) = inj₂ (Φ-dnA V x S σ _ p)

  Φ-dnA V x S σ (G.suc d) p = 0 , Φ-cpA V x S σ p
  Φ-dnA V x S σ (G.lim f) (n , p) = n , Φ-cpA V x S σ p
  Φ-dnA V x S σ {ξ} (G.lc r g) p =
    subst (λ u → CpA S (Φ _ V x ξ , Φmk V x S σ ξ , Φpv V x ξ) (Φ _ V x (g u)) (Φmk V x S σ (g u)) (Φpv V x (g u)))
      (sym (mtp x r)) (Φ-cpA V x S σ p)
  Φ-dnA (ws V) x S σ {G.em _ a} (G.em _ d) (refl , p) = Φ-dnA V (sub₂ x) S _ d p
  Φ-dnA (wl V st) x S σ {G.em n a} (G.em _ d) (refl , p) = Φ-dnA (V n) (subℕ x n) S _ d p
  Φ-dnA (wΩ V w) x S σ {G.em (η , l) a} (G.em _ d) (refl , p) = Φ-dnA (V η l) (subΩ x η l) S _ d p

  Φ-lglA V x S σ G.zero l = tt
  Φ-lglA V x S σ (G.suc a) l = succA-lgl _ _ (NE-Φ V x a) (Φ-lglA V x S σ a l)
  Φ-lglA V x S σ (G.lim f) (st , lf) = (λ n → Φ-cpA V x S σ (st n)) , (λ n → Φ-lglA V x S σ (f n) (lf n))
  Φ-lglA V x S σ (G.lc r g) (lg , mo) =
    (λ a l → Φ-lglA V x S σ _ (lg _ (mlg x r a l))) ,
    (λ a a′ l e l′ → Φ-cpA V x S σ (mo _ _ (mlg x r a l) (mle x r e) (mlg x r a′ l′))) ,
    (λ a l → Φ-lglA V x _ _ _ (lg _ (mlg x r a l)))
  Φ-lglA (ws V) x S σ (G.em _ a) l = Φ-lglA V (sub₂ x) S _ a l
  Φ-lglA (wl V st) x S σ (G.em n a) l = Φ-lglA (V n) (subℕ x n) S _ a l
  Φ-lglA (wΩ V w) x S σ (G.em (η , lη) a) l = Φ-lglA (V η lη) (subΩ x η lη) S _ a l
  Φ-lglA w0 x S σ G.top l = succA-lgl noM noP tt tt
  Φ-lglA (ws V) x S σ G.top l =
    (λ a l → Φ-lglA V (sub₂ x) S _ _ (mlg x (inj₁ tt) a l)) ,
    (λ a a′ l e l′ → Φ-cpA V (sub₂ x) S _ (mle x (inj₁ tt) e)) ,
    (λ a l → Φ-lglA V (sub₂ x) _ _ _ (mlg x (inj₁ tt) a l))
  Φ-lglA (wl V st) x S σ G.top l =
    psumA-lgl _ _ _ (λ n → NE-Φ (V n) (subℕ x n) G.top) (λ n → Φ-lglA (V n) (subℕ x n) S (λ r → σ (n , r)) G.top tt)
  Φ-lglA (wΩ {k} {g} V none) x S σ G.top l =
    psumA-lgl _ _ _ (λ n → NE-Φ (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) G.top)
      (λ n → Φ-lglA (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (subΩ x _ _) S
        (λ r → σ (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top tt)
  Φ-lglA (wΩ {k} {g} V (at ρ e)) x S σ G.top l =
    (λ a l → KfkA-lgl k _ _ (λ η → NE-Φ (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) G.top)
      (λ η → Φ-lglA (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) S _ G.top tt) _ (rt-lg g ρ e _ (mlg x (G.top , tt , ρ) a l))) ,
    (λ a a′ l e′ l′ → KfkA-cp k _ _ (rt-cp g ρ e (mle x (G.top , tt , ρ) e′))) ,
    (λ a l → KfkA-lgl k _ _ (λ η → NE-Φ (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) G.top)
      (λ η → Φ-lglA (V (nrmk k η) (nrmk-lgl k η)) (subΩ x _ _) _ _ G.top tt) _ (rt-lg g ρ e _ (mlg x (G.top , tt , ρ) a l)))
```

链: 下一点是 `c + Φ c`; Ω 结点层号上标注由带标注的加法接起来, 其余层号上不带标注.

```agda
  chT k V zero = G.top
  chT k V (suc n) = plus k (chT k V n) (Φ k V (selfR k) (chT k V n))

  chP (lc j h) V zero = noP
  chP (lc j h) V (suc n) =
    plusP (chP (lc j h) V n) (Φ (lc j h) V (selfR _) (chT _ V n)) (Φpv V (selfR _) (chT _ V n))
  chP zero V n = noP
  chP (suc k) V n = noP
  chP (lim f) V n = noP

  chLb k V zero = tt
  chLb k V (suc n) = plus-lgl k _ _ (chLb k V n) (Φ-lgl k V (selfR k) _ (chLb k V n))

  chL (lc j h) V S zero = tt
  chL (lc j h) V S (suc n) = fgL (λ _ → ⊥) S _ _ _
    (plusA-lgl noM (chP _ V n) (Φ _ V (selfR _) (chT _ V n)) (Φmk V (selfR _) (λ _ → ⊥) (λ _ → nothing) (chT _ V n))
      (Φpv V (selfR _) (chT _ V n)) (NE-Φ V (selfR _) (chT _ V n)) (chL _ V (λ _ → ⊥) n)
      (Φ-lglA V (selfR _) (λ _ → ⊥) (λ _ → nothing) (chT _ V n) (chLb _ V n)))
  chL zero V S n = lglA-no S _ (chLb zero V n)
  chL (suc k) V S n = lglA-no S _ (chLb (suc k) V n)
  chL (lim f) V S n = lglA-no S _ (chLb (lim f) V n)

  chC (lc j h) V S n = fgC (λ _ → ⊥) S _ _ _
    (plusA-weak noM (chP _ V n) (Φ _ V (selfR _) (chT _ V n)) (Φmk V (selfR _) (λ _ → ⊥) (λ _ → nothing) (chT _ V n))
      (Φpv V (selfR _) (chT _ V n)) (NE-Φ V (selfR _) (chT _ V n)))
  chC zero V S n = cpA-no S (plus-weak zero _ _)
  chC (suc k) V S n = cpA-no S (plus-weak (suc k) _ _)
  chC (lim f) V S n = cpA-no S (plus-weak (lim f) _ _)
```

## 4 实例与闭项

```agda
open Prod dl′ evF public

noS : ∀ {k} → Pre k → Set
noS _ = ⊥

fx : ∀ m k → Xm m k noS
fx m k r _ = fold′

TΛᵖ : R
TΛᵖ = Ψᵖ zero VΛ noS (fx zero Λ) G.top noM noP

TΛᵖ-legal : Lgl zero TΛᵖ
TΛᵖ-legal = Ψᵖ-lgl zero VΛ noS (fx zero Λ) G.top noM noP tt

Twᵖ : ℕ → R
Twᵖ n = Ψᵖ zero (Lw-tw n) noS (fx zero (tw n)) G.top noM noP

Twᵖ-legal : ∀ n → Lgl zero (Twᵖ n)
Twᵖ-legal n = Ψᵖ-lgl zero (Lw-tw n) noS (fx zero (tw n)) G.top noM noP tt

-- 读法 ψ₀(Ω_{Ω+1})
T⁺ʷᵖ : R
T⁺ʷᵖ = Ψᵖ zero (ws (Lw-tw 2)) noS (fx zero (suc (tw 2))) G.top noM noP

T⁺ʷᵖ-legal : Lgl zero T⁺ʷᵖ
T⁺ʷᵖ-legal = Ψᵖ-lgl zero (ws (Lw-tw 2)) noS (fx zero (suc (tw 2))) G.top noM noP tt
```
