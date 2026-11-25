# YiLamV 关系：主线折叠与 YiLamFold 的折叠在不含 Ω 结点的公共上界上互模拟

验收文件, 编译定理, 无前提. 照 [YiNextValRel](YiNextValRel.lagda.md) §2, §4, [YiNextValPath](YiNextValPath.lagda.md) §3, [YiNextValLgl](YiNextValLgl.lagda.md) §3, 右边换成 [YiLamFold](YiLamFold.lagda.md) 的 `Lw`, `cmpw`, `Ψ`; 公共上界只取 `w0`, `ws`, `wl` (`VRʷ` 不含 `wΩ`).
`ΨRʷ` 树相关, `ΨCpPʷ` 第一位置证明的路径相同, `ΨLglRʷ` 合法性证明相关. 加法与结点两行的部件直接用那三个文件的 (它们只读 `YiNextBase`). 用处在 [YiLamVBtbo](YiLamVBtbo.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamVRel where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanLegal as ML
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiLamFold as W
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValPath
open import OCF.Lean.YiNextValLgl
```

## 1 公共上界与派发

```agda
data VRʷ : ∀ {k k′} → MF.Lv k → W.Lw k′ → Set where
  w0R : VRʷ MF.v0 W.w0
  wsR : ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → VRʷ (MF.vs V) (W.ws V′)
  wlR : ∀ {f : ℕ → M.LF} {f′ : ℕ → N.LF} {V : ∀ n → MF.Lv (f n)} {V′ : ∀ n → W.Lw (f′ n)}
    {st : ∀ n → MF.Shift (f n) (f (suc n))} {st′ : ∀ n → NB.Shift (f′ n) (f′ (suc n))} → (∀ n → VRʷ (V n) (V′ n)) →
    (∀ n q q′ → PR (f n) (f′ n) q q′ → PR (f (suc n)) (f′ (suc n)) (proj₁ (st n q)) (proj₁ (st′ n q′))) →
    VRʷ (MF.vl V st) (W.wl V′ st′)

vLRʷ : ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → LR k k′
vLRʷ w0R = lz
vLRʷ (wsR v) = ls (vLRʷ v)
vLRʷ (wlR v h) = ll (λ n → vLRʷ (v n))

shiftRʷ : ∀ {f : ℕ → M.LF} {f′ : ℕ → N.LF} {st : ∀ n → MF.Shift (f n) (f (suc n))} {st′ : ∀ n → NB.Shift (f′ n) (f′ (suc n))} →
  (∀ n q q′ → PR (f n) (f′ n) q q′ → PR (f (suc n)) (f′ (suc n)) (proj₁ (st n q)) (proj₁ (st′ n q′))) →
  ∀ {n m} (p : n ≤′ m) q q′ → PR (f n) (f′ n) q q′ → PR (f m) (f′ m) (proj₁ (MF.shift st p q)) (proj₁ (W.shiftw st′ p q′))
shiftRʷ h ≤′-refl q q′ e = e
shiftRʷ h (≤′-step p) q q′ e = h _ _ _ (shiftRʷ h p q q′ e)

cmpRʷ : ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → ∀ q q′ → PR k k′ q q′ → ∀ r r′ → PR k k′ r r′ →
  WR (MF.lev k q) (NB.lev k′ q′) (MF.cmp V q r) (W.cmpw V′ q′ r′)
cmpRʷ w0R () q′ e r r′ e′
cmpRʷ (wsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₁ _) e′ = tt
cmpRʷ (wsR v) (inj₁ _) (inj₁ _) e (inj₂ r) (inj₂ r′) e′ = e′
cmpRʷ (wsR v) (inj₂ q) (inj₂ q′) e (inj₁ _) (inj₁ _) e′ = tt
cmpRʷ (wsR v) (inj₂ q) (inj₂ q′) e (inj₂ r) (inj₂ r′) e′ = cmpRʷ v q q′ e r r′ e′
cmpRʷ (wsR v) (inj₁ _) (inj₂ _) () r r′ e′
cmpRʷ (wsR v) (inj₂ _) (inj₁ _) () r r′ e′
cmpRʷ (wsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₂ _) ()
cmpRʷ (wsR v) (inj₁ _) (inj₁ _) e (inj₂ _) (inj₁ _) ()
cmpRʷ (wsR v) (inj₂ _) (inj₂ _) e (inj₁ _) (inj₂ _) ()
cmpRʷ (wsR v) (inj₂ _) (inj₂ _) e (inj₂ _) (inj₁ _) ()
cmpRʷ (wlR {st = st} {st′ = st′} v h) (n , q) (_ , q′) (refl , e) (m , r) (_ , r′) (refl , e′) =
  substR (proj₂ (MF.shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (MF.shift st (≤⇒≤′ (m≤n⊔m n m)) r))
    (proj₂ (W.shiftw st′ (≤⇒≤′ (m≤m⊔n n m)) q′)) (proj₂ (W.shiftw st′ (≤⇒≤′ (m≤n⊔m n m)) r′)) _ _
    (cmpRʷ (v (n ⊔ m)) _ _ (shiftRʷ h (≤⇒≤′ (m≤m⊔n n m)) q q′ e) _ _ (shiftRʷ h (≤⇒≤′ (m≤n⊔m n m)) r r′ e′))
```

## 2 折叠

```agda
ΨRʷ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′} → RR k k′ ξ ξ′ → RR m m′ (MF.Ψ m V x ξ) (W.Ψ m′ V′ x′ ξ′)
ΨRʷ em v xr rz = rt
ΨRʷ em v xr (rs d) = succR em (ΨRʷ em v xr d)
ΨRʷ em v xr (rl d) = rl (λ n → ΨRʷ em v xr (d n))
ΨRʷ em {V = V} {V′} v {x} {x′} xr (rc {r = r} {r′ = r′} q h) =
  ΨNR em (vLRʷ v) r r′ q (x r) (x′ r′) (xr r r′ q) (λ η η′ h′ → ΨRʷ em v xr (h η η′ h′))
    (λ η η′ h′ → ΨRʷ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRʷ v r r′ q q₁ q₁′ e) (h η η′ h′))
ΨRʷ em w0R xr rt = succR em rt
ΨRʷ em (wsR v) {x} {x′} xr rt = ΨnR em (vLRʷ v) (x (inj₁ tt)) (x′ (inj₁ tt)) (xr (inj₁ tt) (inj₁ tt) tt)
  (λ η η′ h → ΨRʷ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) h) (λ η η′ h → ΨRʷ (vLRʷ v) v (λ r r′ e → e) h)
ΨRʷ em (wlR v s) xr rt = rl (psumR em (λ n → ΨRʷ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt))

ΨCpPʷ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Cp k ξ ζ) (p′ : N.Cp k′ ξ′ ζ′) → pCᴹ k p ≡ pCᴺ k′ p′ →
  pCᴹ m (ML.Ψ-cp m V x p) ≡ pCᴺ m′ (W.Ψ-cp m′ V′ x′ p′)
ΨDnPʷ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : W.Lw k′} → VRʷ V V′ → ∀ {x x′} → XR m m′ k k′ x x′ →
  ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Dn k ξ ζ) (p′ : N.Dn k′ ξ′ ζ′) → pDᴹ k ζ p ≡ pDᴺ k′ ζ′ p′ →
  pDᴹ m (MF.Ψ m V x ζ) (ML.Ψ-dn m V x ζ p) ≡ pDᴺ m′ (W.Ψ m′ V′ x′ ζ′) (W.Ψ-dn m′ V′ x′ ζ′ p′)

ΨCpPʷ em v xr d (inj₁ refl) (inj₁ refl) eq = refl
ΨCpPʷ em v xr d (inj₂ p) (inj₂ p′) eq = cong (D ∷_) (ΨDnPʷ em v xr d p p′ (cong tl eq))
ΨCpPʷ em v xr d (inj₁ refl) (inj₂ p′) ()
ΨCpPʷ em v xr d (inj₂ p) (inj₁ refl) ()

ΨDnPʷ em v xr (rs d) p p′ eq = cong (L 0 ∷_) (ΨCpPʷ em v xr d p p′ (cong tl eq))
ΨDnPʷ em v xr (rl d) (n , p) (n′ , p′) eq with cong ix eq
... | refl = cong (L n ∷_) (ΨCpPʷ em v xr (d n) p p′ (cong tl eq))
ΨDnPʷ em {V = V} {V′} v {x} {x′} xr (rc {r = r} {r′ = r′} {g = g} {g′ = g′} q h) p p′ eq =
  ΨNDnP em (vLRʷ v) r r′ q (x r) (x′ r′) (xr r r′ q)
    (λ η → MF.Ψ _ V x (g η)) (λ η → W.Ψ _ V′ x′ (g′ η))
    (λ η → MF.Ψ (MF.lev _ r) V (MF.cmp V r) (g η)) (λ η → W.Ψ (NB.lev _ r′) V′ (W.cmpw V′ r′) (g′ η))
    (ML.Ψ-cp _ V x p) (W.Ψ-cp _ V′ x′ p′) (ΨCpPʷ em v xr (h _ _ (tpR (vLRʷ v) r r′ q)) p p′ (cong tl eq))
```

## 3 合法性证明

```agda
ΨLglRʷ : ∀ {m m′} (em : LR m m′) {k k′} {V : MF.Lv k} {V′ : W.Lw k′} (v : VRʷ V V′) {x x′} (xr : XR m m′ k k′ x x′)
  {ξ ξ′} (d : RR k k′ ξ ξ′) {l l′} → LglR k k′ ξ ξ′ l l′ →
  LglR m m′ (MF.Ψ m V x ξ) (W.Ψ m′ V′ x′ ξ′) (ML.Ψ-lgl m V x ξ l) (W.Ψ-lgl m′ V′ x′ ξ′ l′)
ΨLglRʷ em v xr rz lr = tt
ΨLglRʷ em v xr (rs d) lr = succLglR em (ΨRʷ em v xr d) (ΨLglRʷ em v xr d lr)
ΨLglRʷ em v xr (rl d) lr = (λ n → ΨCpPʷ em v xr (d (suc n)) _ _ (proj₁ lr n)) , (λ n → ΨLglRʷ em v xr (d n) (proj₂ lr n))
ΨLglRʷ em v {x} {x′} xr (rc {r = r} {r′ = r′} q h) lr =
  ΨNLglR em (vLRʷ v) r r′ q (x r) (x′ r′) (xr r r′ q) _ _
    ((λ η η′ hr lη lη′ ll → ΨLglRʷ em v xr (h η η′ hr) (proj₁ lr η η′ hr lη lη′ ll)) ,
     (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
       ΨCpPʷ em v xr (h η₂ η₂′ hr₂) _ _ (proj₂ lr η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq)))
    (λ η η′ hr → ΨRʷ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRʷ v r r′ q q₁ q₁′ e) (h η η′ hr))
    (λ η η′ hr lη lη′ ll → ΨLglRʷ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRʷ v r r′ q q₁ q₁′ e) (h η η′ hr)
       (proj₁ lr η η′ hr lη lη′ ll))
ΨLglRʷ em w0R xr rt lr = succLglR em rt tt
ΨLglRʷ em (wsR v) {x} {x′} xr rt lr = ΨnLglR em (vLRʷ v) (x (inj₁ tt)) (x′ (inj₁ tt)) (xr (inj₁ tt) (inj₁ tt) tt) _ _
  ((λ η η′ hr lη lη′ ll → ΨLglRʷ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr ll) ,
   (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq → ΨCpPʷ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr₂ u u′ eq))
  (λ η η′ hr → ΨRʷ (vLRʷ v) v (λ r r′ e → e) hr) (λ η η′ hr l l′ ll → ΨLglRʷ (vLRʷ v) v (λ r r′ e → e) hr ll)
ΨLglRʷ em (wlR v s) xr rt lr =
  psumLglR em (λ n → ΨRʷ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt)
    (λ n → ΨLglRʷ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt tt)
```
