# 来历作为逐次出现的标注: 标注进入第一位置关系时折叠保合法

非验收文件. 编译定理, 无前提: 标注 `Mk` (结点上相对当前目标的同支证据), `Pv` (每个结点给分支标上相对它自己的证据); 折叠 `Ψᴹ` 在结点上把标注的证据交给 `cmpe`. 带标注的第一位置关系 `CpA` (相等情形要标注也相等) 与合法性 `LglA` 下, `Ψᴹ-lgl` 对一切派发, 证据来源, 目标关系成立; 不带标注时就是原来的合法性 (`lglA-no`).
有限测试 (§4): 结点带证据时卡住的那一对保留 (`stuck-kept`); 跨支那一对对一切标注只走 `D` (`cross-anyM`, 编译定理). 没有做: 规范计算里的标注从哪里来 (自折叠的输出要带上满足 `LglA` 的标注). 标注不进第一位置关系时的反面在 [YiCtxNeg](YiCtxNeg.lagda.md) §2.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCtxAnn where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; R; succ; succ-lgl)
open import OCF.Lean.YiLamFold using (Lw)
open import OCF.Lean.YiDlInst using (V2; rN)
open import OCF.Lean.YiDlLost using (pN; LN) renaming (s to sN)
open import OCF.Lean.YiZipWay
open import OCF.Lean.YiZipFold using (dl′)
open import OCF.Lean.YiCtxFold using (Ev; SB; evF; module FoldC)
open import OCF.Lean.YiCtxTest using (gate-no; q₂; r₃)
```

## 1 标注

`noM`, `noP`: 下面都没有标注.

```agda
data Mk {k : LF} (S : Pre k → Set) : Raw k → Set where
  noM  : ∀ {t} → Mk S t
  sucM : ∀ {a} → Mk S a → Mk S (G.suc a)
  limM : ∀ {f} → (∀ n → Mk S (f n)) → Mk S (G.lim f)
  lcM  : ∀ {r h} → Maybe (S r) → (∀ ζ → Mk S (h ζ)) → Mk S (G.lc r h)

data Pv {k : LF} : Raw k → Set where
  noP  : ∀ {t} → Pv t
  sucP : ∀ {a} → Pv a → Pv (G.suc a)
  limP : ∀ {f} → (∀ n → Pv (f n)) → Pv (G.lim f)
  lcP  : ∀ {r h} → (∀ ζ → Mk (SB k r) (h ζ)) → (∀ ζ → Pv (h ζ)) → Pv (G.lc r h)

module _ {k : LF} {S : Pre k → Set} where
  mS : ∀ {a} → Mk S (G.suc a) → Mk S a
  mS noM = noM
  mS (sucM μ) = μ
  mL : ∀ {f} → Mk S (G.lim f) → ∀ n → Mk S (f n)
  mL noM n = noM
  mL (limM μ) n = μ n
  mE : ∀ {r h} → Mk S (G.lc r h) → Maybe (S r)
  mE noM = nothing
  mE (lcM e μ) = e
  mB : ∀ {r h} → Mk S (G.lc r h) → ∀ ζ → Mk S (h ζ)
  mB noM ζ = noM
  mB (lcM e μ) = μ

module _ {k : LF} where
  pS : ∀ {a} → Pv {k} (G.suc a) → Pv a
  pS noP = noP
  pS (sucP π) = π
  pL : ∀ {f} → Pv {k} (G.lim f) → ∀ n → Pv (f n)
  pL noP n = noP
  pL (limP π) n = π n
  pM : ∀ {r h} → Pv {k} (G.lc r h) → ∀ ζ → Mk (SB k r) (h ζ)
  pM noP ζ = noM
  pM (lcP μ π) = μ
  pB : ∀ {r h} → Pv {k} (G.lc r h) → ∀ ζ → Pv (h ζ)
  pB noP ζ = noP
  pB (lcP μ π) = π
```

## 2 带标注的第一位置关系与合法性

结点的合法性多一项: 分支带上相对这个结点的标注后也合法 (内层折叠用它). 嵌入与 `top` 下不带标注, 用原来的关系.

```agda
module _ {k : LF} where
  An : (Pre k → Set) → Set
  An S = Σ (Raw k) λ t → Mk S t × Pv t

  CpA : ∀ S → An S → (t : Raw k) → Mk S t → Pv t → Set
  DnA : ∀ S → An S → (t : Raw k) → Mk S t → Pv t → Set
  CpA S a t μ π = (a ≡ (t , μ , π)) ⊎ DnA S a t μ π

  DnA S a G.zero μ π = ⊥
  DnA S a (G.suc d) μ π = CpA S a d (mS μ) (pS π)
  DnA S a (G.lim f) μ π = Σ ℕ λ n → CpA S a (f n) (mL μ n) (pL π n)
  DnA S a (G.lc r g) μ π = CpA S a (g (Lay.tp (Lo k r))) (mB μ _) (pB π _)
  DnA S (G.em i x , _) (G.em j d) μ π = Dn k (G.em i x) (G.em j d)
  DnA S a (G.em j d) μ π = ⊥
  DnA S a G.top μ π = ⊥

  LglA : ∀ S (t : Raw k) → Mk S t → Pv t → Set
  LglA S G.zero μ π = ⊤
  LglA S (G.suc a) μ π = LglA S a (mS μ) (pS π)
  LglA S (G.lim f) μ π =
    (∀ n → CpA S (f n , mL μ n , pL π n) (f (suc n)) (mL μ (suc n)) (pL π (suc n))) ×
    (∀ n → LglA S (f n) (mL μ n) (pL π n))
  LglA S (G.lc r g) μ π =
    (∀ ζ → Lay.lg (Lo k r) ζ → LglA S (g ζ) (mB μ ζ) (pB π ζ)) ×
    (∀ ζ ζ′ → Lay.lg (Lo k r) ζ → Le (Lo k r) ζ ζ′ → Lay.lg (Lo k r) ζ′ →
      CpA S (g ζ , mB μ ζ , pB π ζ) (g ζ′) (mB μ ζ′) (pB π ζ′)) ×
    (∀ ζ → Lay.lg (Lo k r) ζ → LglA (SB k r) (g ζ) (pM π ζ) (pB π ζ))
  LglA S (G.em i a) μ π = Lgl k (G.em i a)
  LglA S G.top μ π = ⊤
```

不带标注时就是原来的合法性.

```agda
  cpA-no : ∀ S {t t′} → Cp k t t′ → CpA S (t , noM , noP) t′ noM noP
  dnA-no : ∀ S {t} t′ → Dn k t t′ → DnA S (t , noM , noP) t′ noM noP
  cpA-no S (inj₁ refl) = inj₁ refl
  cpA-no S (inj₂ p) = inj₂ (dnA-no S _ p)
  dnA-no S (G.suc d) p = cpA-no S p
  dnA-no S (G.lim f) (n , p) = n , cpA-no S p
  dnA-no S (G.lc r g) p = cpA-no S p
  dnA-no S {G.em i a} (G.em j d) p = p
  dnA-no S {G.zero} (G.em j d) ()
  dnA-no S {G.suc _} (G.em j d) ()
  dnA-no S {G.lim _} (G.em j d) ()
  dnA-no S {G.lc _ _} (G.em j d) ()
  dnA-no S {G.top} (G.em j d) ()

  lglA-no : ∀ S t → Lgl k t → LglA S t noM noP
  lglA-no S G.zero l = tt
  lglA-no S (G.suc a) l = lglA-no S a l
  lglA-no S (G.lim f) (st , lf) = (λ n → cpA-no S (st n)) , (λ n → lglA-no S (f n) (lf n))
  lglA-no S (G.lc r g) (lg , mo) =
    (λ ζ l → lglA-no S (g ζ) (lg ζ l)) , (λ ζ ζ′ l e l′ → cpA-no S (mo ζ ζ′ l e l′)) ,
    (λ ζ l → lglA-no (SB k r) (g ζ) (lg ζ l))
  lglA-no S (G.em i a) l = l
  lglA-no S G.top l = tt
```

## 3 逐次出现证据的折叠, 与它的合法性

```agda
module Marked (D : ∀ k K → Ext′ k K) (E : Ev) where
  open FoldC D E

  Xm : LF → (k : LF) → (Pre k → Set) → Set
  Xm m k S = (r : Pre k) → Maybe (S r) → Way′ m (lev k r)

  Ψᴹ : ∀ m {k} → Lw k → (S : Pre k → Set) → Xm m k S → (t : Raw k) → Mk S t → Pv t → Raw m
  Ψᴹ m V S x G.zero μ π = G.top
  Ψᴹ m V S x (G.suc a) μ π = succ m (Ψᴹ m V S x a (mS μ) (pS π))
  Ψᴹ m V S x (G.lim f) μ π = G.lim (λ n → Ψᴹ m V S x (f n) (mL μ n) (pL π n))
  Ψᴹ m {k} V S x (G.lc r g) μ π =
    ΨN′ m k r (x r (mE μ)) (λ ζ → Ψᴹ m V S x (g ζ) (mB μ ζ) (pB π ζ))
      (λ ζ → Ψᴹ (lev k r) V (SB k r) (cmpe V r) (g ζ) (pM π ζ) (pB π ζ))
  Ψᴹ m V S x t μ π = Ψᶜ m V (λ r → x r nothing) t

  Ψᴬ : ∀ m {k} → Lw k → (S : Pre k → Set) → Xm m k S → An S → Raw m
  Ψᴬ m V S x (t , μ , π) = Ψᴹ m V S x t μ π

  Ψᴹ-cp : ∀ m {k} (V : Lw k) S x {a : An S} {t μ π} → CpA S a t μ π → Cp m (Ψᴬ m V S x a) (Ψᴹ m V S x t μ π)
  Ψᴹ-dn : ∀ m {k} (V : Lw k) S x (a : An S) t μ π → DnA S a t μ π → Dn m (Ψᴬ m V S x a) (Ψᴹ m V S x t μ π)
  Ψᴹ-lgl : ∀ m {k} (V : Lw k) S x t μ π → LglA S t μ π → Lgl m (Ψᴹ m V S x t μ π)

  Ψᴹ-cp m V S x (inj₁ refl) = inj₁ refl
  Ψᴹ-cp m V S x {a} {t} {μ} {π} (inj₂ p) = inj₂ (Ψᴹ-dn m V S x a t μ π p)

  Ψᴹ-dn m V S x a (G.suc d) μ π p = 0 , Ψᴹ-cp m V S x p
  Ψᴹ-dn m V S x a (G.lim f) μ π (n , p) = n , Ψᴹ-cp m V S x p
  Ψᴹ-dn m {k} V S x a (G.lc r g) μ π p = ΨN′-dn m k r (x r (mE μ)) _ _ (Ψᴹ-cp m V S x p)
  Ψᴹ-dn m V S x (G.em i y , _) (G.em j d) μ π p = Ψᶜ-dn m V _ (G.em j d) p
  Ψᴹ-dn m V S x (G.zero , _) (G.em j d) μ π ()
  Ψᴹ-dn m V S x (G.suc _ , _) (G.em j d) μ π ()
  Ψᴹ-dn m V S x (G.lim _ , _) (G.em j d) μ π ()
  Ψᴹ-dn m V S x (G.lc _ _ , _) (G.em j d) μ π ()
  Ψᴹ-dn m V S x (G.top , _) (G.em j d) μ π ()

  Ψᴹ-lgl m V S x G.zero μ π l = tt
  Ψᴹ-lgl m V S x (G.suc a) μ π l = succ-lgl m _ (Ψᴹ-lgl m V S x a (mS μ) (pS π) l)
  Ψᴹ-lgl m V S x (G.lim f) μ π (st , lf) =
    (λ n → Ψᴹ-cp m V S x (st n)) , (λ n → Ψᴹ-lgl m V S x _ _ _ (lf n))
  Ψᴹ-lgl m {k} V S x (G.lc r g) μ π (lg , mo , li) = ΨN′-lgl m k r (x r (mE μ)) _ _
    ((λ ζ l → Ψᴹ-lgl m V S x _ _ _ (lg ζ l)) , (λ ζ ζ′ l e l′ → Ψᴹ-cp m V S x (mo ζ ζ′ l e l′)))
    (λ ζ l → Ψᴹ-lgl (lev k r) V (SB k r) (cmpe V r) _ _ _ (li ζ l))
  Ψᴹ-lgl m V S x (G.em i a) μ π l = Ψᶜ-lgl m V _ (G.em i a) l
  Ψᴹ-lgl m V S x G.top μ π l = Ψᶜ-lgl m V _ G.top tt
```

## 4 有限测试

卡住的那一对: 源树在 `pN` 上的结点带相对 `rN` 的证据时, 折叠到 `LN` 保留在 `YiZipLost` 的槽位 `sN` (`stuck-kept`). 同一支 `ηs = 2 + ω` 里同一机制的一对 (源层号字面是 ℕ 极限, `D` 折叠): 常值序列带同一份证据, 带标注合法 (`const-lglA`), 输出逐项是保留的结点 (`const-kept`), 合法 (`const-legal`).

```agda
open Marked dl′ evF

cmpe₀ : (q r : Pre (tw 2)) → Maybe (SB (tw 2) q r) → Way′ (lev (tw 2) q) (lev (tw 2) r)
cmpe₀ = FoldC.cmpe dl′ evF V2

stuck-kept : Ψᴹ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (G.lc pN (λ _ → G.zero)) (lcM (just refl) (λ _ → noM)) noP ≡
  G.lc sN (λ _ → G.top)
stuck-kept = refl

stuck-old : Ψᴹ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (G.lc pN (λ _ → G.zero)) noM noP ≡ G.lim (λ _ → G.top)
stuck-old = refl

-- 跨支那一对: 标注里能放的证据只有 `nothing` (`2 ≡ 3` 无元素), 所以只走 `D`.
cross-anyM : ∀ (e : Maybe (SB (tw 2) q₂ r₃)) → cmpe₀ q₂ r₃ e ≡ dl′ (lev (tw 2) q₂) (tw 2) r₃
cross-anyM e = gate-no e (λ ()) _ _

ηs : R
ηs = G.suc (G.suc (G.lim (λ _ → G.zero)))

ls : Lgl zero ηs
ls = (λ n → inj₁ refl) , (λ n → tt)

qs rs : Pre (tw 2)
qs = ηs , ls , inj₁ tt
rs = ηs , ls , inj₂ (inj₁ tt)

M : LF
M = lev (tw 2) qs

ts : Raw (tw 2)
ts = G.lc rs (λ _ → G.zero)

μs : ℕ → Mk (SB (tw 2) qs) ts
μs zero = lcM (just refl) (λ _ → noM)
μs (suc n) = lcM nothing (λ _ → noM)

const-lglA : LglA (SB (tw 2) qs) (G.lim (λ _ → ts)) (limM (λ _ → μs 0)) noP
const-lglA = (λ n → inj₁ refl) , (λ n → (λ ζ l → tt) , (λ ζ ζ′ l e l′ → inj₁ refl) , (λ ζ l → tt))

const-kept : Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) (G.lim (λ _ → ts)) (limM (λ _ → μs 0)) noP ≡
  G.lim (λ _ → G.lc (inj₁ tt) (λ _ → G.top))
const-kept = refl

const-legal : Lgl M (Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) (G.lim (λ _ → ts)) (limM (λ _ → μs 0)) noP)
const-legal = Ψᴹ-lgl M V2 (SB (tw 2) qs) (cmpe₀ qs) (G.lim (λ _ → ts)) (limM (λ _ → μs 0)) noP const-lglA
```
