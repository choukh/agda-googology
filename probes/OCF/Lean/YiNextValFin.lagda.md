# YiNextVal 转运：主线的链点与下一站的链点读回互模拟

**验收文件，档位：编译定理与条件定理。** `co≅`：主线 `T₃` 与下一站 `T₃` 的第 n 个链点读回结构互模拟；`T₃≅`：两个 `T₃` 读回互模拟。
条件定理：`chainP-transfer : ChainP → ChainPⁿ`，`btbo⁺-from-main : ChainP → D.BTBOᴵ ≼ read T⁺` (下一站的 `read`、`T⁺`)。下一站上无条件的下界 (`lower-readⁿ`, `T₃-Ωωⁿ`, `T⁺-Ωω`) 都是下界，不是同值。
关系与互模拟在 [YiNextValRel](YiNextValRel.lagda.md)，合法性证明的对应在 [YiNextValLgl](YiNextValLgl.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextValFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextFold as NF
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiLeanValFin as MV
open import OCF.Lean.YiLeanValRel using (Corr)
open import OCF.Lean.YiLeanValFold using (lower-any)
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValPath
open import OCF.Lean.YiNextValLgl
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ≅→≼; +-mono)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ᵖ_; _≼ˣ_; zᵖ; sᵖ; wᵖ; ≼lᵖ; lᵖ; zˣ; sˣ; wˣ; ≼lˣ; lˣ; VMᵖ; ˣ→ᵖ; ≅→≼ˣ)
```

## 1 第 0 层的树作层号

`sh` 沿第一位置证明的路径走，所以路径相同的两个证明给出相关的位置搬运；于是合法性对应的两棵树读成相关的公共上界。

```agda
upR : ∀ {a a′} → RR M.zero N.zero a a′ → LR (MT.⌜ a ⌝) (NB.⌜ a′ ⌝)
upR rz = lz
upR (rs d) = ls (upR d)
upR (rl d) = ll (λ n → upR (d n))
upR (rc {r = ()} q h)
upR rt = ls lz

shR : ∀ {a a′ b b′} → RR M.zero N.zero b b′ → (p : M.Cp M.zero a b) (p′ : N.Cp N.zero a′ b′) →
  pCᴹ M.zero p ≡ pCᴺ N.zero p′ → ∀ q q′ → PR (MT.⌜ a ⌝) (NB.⌜ a′ ⌝) q q′ →
  PR (MT.⌜ b ⌝) (NB.⌜ b′ ⌝) (proj₁ (MT.sh b p q)) (proj₁ (NT.sh b′ p′ q′))
shR d (inj₁ refl) (inj₁ refl) eq q q′ e = e
shR d (inj₁ refl) (inj₂ p′) ()
shR d (inj₂ p) (inj₁ refl) ()
shR (rs d) (inj₂ p) (inj₂ p′) eq q q′ e = shR d p p′ (cong (λ z → tl (tl z)) eq) q q′ e
shR (rl d) (inj₂ (n , p)) (inj₂ (n′ , p′)) eq q q′ e with cong (λ z → ix (tl z)) eq
... | refl = refl , shR (d n) p p′ (cong (λ z → tl (tl z)) eq) q q′ e
shR (rc {r = ()} _ _) (inj₂ p) (inj₂ p′) eq q q′ e

lvR : ∀ {a a′} → RR M.zero N.zero a a′ → ∀ l l′ → LglR M.zero N.zero a a′ l l′ → VR (MT.lv a l) (NT.lv a′ l′)
lvR rz l l′ lr = v0R
lvR (rs d) l l′ lr = vsR (lvR d l l′ lr)
lvR (rl d) l l′ lr = vlR (λ n → lvR (d n) (proj₂ l n) (proj₂ l′ n) (proj₂ lr n))
  (λ n q q′ e → shR (d (suc n)) (proj₁ l n) (proj₁ l′ n) (proj₁ lr n) q q′ e)
lvR (rc {r = ()} q h) l l′ lr
lvR rt l l′ lr = vsR v0R

FR : ∀ {a a′} → RR M.zero N.zero a a′ → ∀ l l′ → LglR M.zero N.zero a a′ l l′ → RR M.zero N.zero (MT.F a l) (NT.F a′ l′)
FR d l l′ lr = ΨR lz (lvR d l l′ lr) (λ _ _ _ → tt) rt

FLR : ∀ {a a′} (d : RR M.zero N.zero a a′) l l′ (lr : LglR M.zero N.zero a a′ l l′) →
  LglR M.zero N.zero (MT.F a l) (NT.F a′ l′) (MT.F-lgl a l) (NF.Ψ-lgl N.zero (NT.lv a′ l′) (λ _ → NB.fold) N.G.top tt)
FLR d l l′ lr = ΨLglR lz (lvR d l l′ lr) (λ _ _ _ → tt) rt tt
```

## 2 转运定理

```agda
FL : (η : NB.R) (l : N.Lgl N.zero η) → N.Lgl N.zero (NT.F η l)
FL η l = NF.Ψ-lgl N.zero (NT.lv η l) (λ _ → NB.fold) N.G.top tt

nxR : ∀ {p p′} → RR M.zero N.zero (MT.Pt.co p) (NB.co p′) → LglR M.zero N.zero (MT.Pt.co p) (NB.co p′) (MT.Pt.lw p) (NB.lw p′) →
  Σ (RR M.zero N.zero (MT.Pt.co (MT.nx p)) (NB.co (NB.nx NT.F FL p′)))
    λ _ → LglR M.zero N.zero (MT.Pt.co (MT.nx p)) (NB.co (NB.nx NT.F FL p′)) (MT.Pt.lw (MT.nx p)) (NB.lw (NB.nx NT.F FL p′))
nxR d lr = plusR lz d (FR d _ _ lr) , plusLglR lz d (FR d _ _ lr) lr (FLR d _ _ lr)

ptR : ∀ n → Σ (RR M.zero N.zero (MT.Pt.co (MT.pts n)) (NB.co (NT.P₃ n)))
  λ _ → LglR M.zero N.zero (MT.Pt.co (MT.pts n)) (NB.co (NT.P₃ n)) (MT.Pt.lw (MT.pts n)) (NB.lw (NT.P₃ n))
ptR zero = rt , tt
ptR (suc n) = nxR (proj₁ (ptR n)) (proj₂ (ptR n))

co≅ : ∀ n → MA.read (MT.Pt.co (MT.pts n)) L.≅ NA.read (NB.co (NT.P₃ n))
co≅ n = read≅ (proj₁ (ptR n))

T₃R : RR M.zero N.zero MT.T₃ NT.T₃
T₃R = rl (λ n → FR (proj₁ (ptR n)) _ _ (proj₂ (ptR n)))

T₃≅ : MA.read MT.T₃ L.≅ NA.read NT.T₃
T₃≅ = read≅ T₃R
```

## 3 定义域 `≼ᵖ` 对右边的结构互模拟封闭，`ChainP` 的转运

```agda
≼ˣ-≅ : ∀ {a b c : L.Ordᶜ L.zero} → a ≼ˣ b → b L.≅ c → a ≼ˣ c
≼ˣ-≅ zˣ e = zˣ
≼ˣ-≅ (sˣ d ba) (L.s≅ e) = sˣ (≼ˣ-≅ d e) (≼-trans (≅→≼ (L.≅-sym e)) ba)
≼ˣ-≅ (sˣ d ba) (L.upʳ {r = ()} e)
≼ˣ-≅ (wˣ d) (L.s≅ e) = wˣ (≼ˣ-≅ d e)
≼ˣ-≅ (wˣ d) (L.upʳ {r = ()} e)
≼ˣ-≅ (≼lˣ n d) (L.l≅ h) = ≼lˣ n (≼ˣ-≅ d (h n))
≼ˣ-≅ (≼lˣ n d) (L.upʳ {r = ()} e)
≼ˣ-≅ (lˣ d) e = lˣ (λ n → ≼ˣ-≅ (d n) e)

≼ᵖ-≅ : ∀ {a b c : L.Ordᶜ L.zero} → a ≼ᵖ b → b L.≅ c → a ≼ᵖ c
≼ᵖ-≅ zᵖ e = zᵖ
≼ᵖ-≅ (sᵖ d) (L.s≅ e) = sᵖ (≼ᵖ-≅ d e)
≼ᵖ-≅ (sᵖ d) (L.upʳ {r = ()} e)
≼ᵖ-≅ (wᵖ d) (L.s≅ e) = wᵖ (≼ᵖ-≅ d e)
≼ᵖ-≅ (wᵖ d) (L.upʳ {r = ()} e)
≼ᵖ-≅ (≼lᵖ n d) (L.l≅ h) = ≼lᵖ n (≼ᵖ-≅ d (h n))
≼ᵖ-≅ (≼lᵖ n d) (L.upʳ {r = ()} e)
≼ᵖ-≅ (lᵖ d) e = lᵖ (λ n → ≼ˣ-≅ (d n) e)

ChainPⁿ : Set
ChainPⁿ = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ NA.read (NB.co (NT.P₃ m))

chainP-transfer : MV.ChainP → ChainPⁿ
chainP-transfer ch n = proj₁ (ch n) , ≼ᵖ-≅ (proj₂ (ch n)) (co≅ (proj₁ (ch n)))

chainP-back : ChainPⁿ → MV.ChainP
chainP-back ch n = proj₁ (ch n) , ≼ᵖ-≅ (proj₂ (ch n)) (L.≅-sym (co≅ (proj₁ (ch n))))
```

## 4 下一站上的下界

一般的第 0 层合法树先搬到主线 (`toM`，带合法性与路径)，用主线的 `lower-any`, `lower-read`，再经互模拟搬回。

```agda
toM : N.Raw N.zero → M.Raw M.zero
toM N.G.zero = M.G.zero
toM (N.G.suc a) = M.G.suc (toM a)
toM (N.G.lim f) = M.G.lim (λ n → toM (f n))
toM (N.G.lc () g)
toM (N.G.em () a)
toM N.G.top = M.G.top

toM-R : ∀ a → RR M.zero N.zero (toM a) a
toM-R N.G.zero = rz
toM-R (N.G.suc a) = rs (toM-R a)
toM-R (N.G.lim f) = rl (λ n → toM-R (f n))
toM-R (N.G.lc () g)
toM-R (N.G.em () a)
toM-R N.G.top = rt

toM-cp : ∀ {a} b → N.Cp N.zero a b → M.Cp M.zero (toM a) (toM b)
toM-dn : ∀ {a} b → N.Dn N.zero a b → M.Dn M.zero (toM a) (toM b)
toM-cp b (inj₁ refl) = inj₁ refl
toM-cp b (inj₂ p) = inj₂ (toM-dn b p)
toM-dn (N.G.suc b) p = toM-cp b p
toM-dn (N.G.lim f) (n , p) = n , toM-cp (f n) p
toM-dn (N.G.lc () g) p
toM-dn (N.G.em () d) p

toM-p : ∀ {a} b (p : N.Cp N.zero a b) → pCᴹ M.zero (toM-cp b p) ≡ pCᴺ N.zero p
toM-pd : ∀ {a} b (p : N.Dn N.zero a b) → pDᴹ M.zero (toM b) (toM-dn b p) ≡ pDᴺ N.zero b p
toM-p b (inj₁ refl) = refl
toM-p b (inj₂ p) = cong (D ∷_) (toM-pd b p)
toM-pd (N.G.suc b) p = cong (S ∷_) (toM-p b p)
toM-pd (N.G.lim f) (n , p) = cong (L n ∷_) (toM-p (f n) p)
toM-pd (N.G.lc () g) p
toM-pd (N.G.em () d) p

toM-lgl : ∀ a → N.Lgl N.zero a → M.Lgl M.zero (toM a)
toM-lgl N.G.zero l = tt
toM-lgl (N.G.suc a) l = toM-lgl a l
toM-lgl (N.G.lim f) l = (λ n → toM-cp (f (suc n)) (proj₁ l n)) , (λ n → toM-lgl (f n) (proj₂ l n))
toM-lgl (N.G.lc () g) l
toM-lgl (N.G.em () a) l
toM-lgl N.G.top l = tt

toM-LR : ∀ a l → LglR M.zero N.zero (toM a) a (toM-lgl a l) l
toM-LR N.G.zero l = tt
toM-LR (N.G.suc a) l = toM-LR a l
toM-LR (N.G.lim f) l = (λ n → toM-p (f (suc n)) (proj₁ l n)) , (λ n → toM-LR (f n) (proj₂ l n))
toM-LR (N.G.lc () g) l
toM-LR (N.G.em () a) l
toM-LR N.G.top l = tt

F≅ : ∀ a l → MA.read (MT.F (toM a) (toM-lgl a l)) L.≅ NA.read (NT.F a l)
F≅ a l = read≅ (FR (toM-R a) (toM-lgl a l) l (toM-LR a l))

lower-anyⁿ : ∀ a (l : N.Lgl N.zero a) {κ} → Corr κ (MT.⌜ toM a ⌝) → L.ψ⁰ (L.Ω κ) ≼ NA.read (NT.F a l)
lower-anyⁿ a l c = ≼-trans (lower-any (toM a) (toM-lgl a l) c) (≅→≼ (F≅ a l))

cp⊑ⁿ : ∀ a b → N.Cp N.zero a b → NA.read a L.⊑ NA.read b
dn⊑ⁿ : ∀ a b → N.Dn N.zero a b → NA.read a L.⊑ NA.read b
cp⊑ⁿ a b (inj₁ refl) h = h
cp⊑ⁿ a b (inj₂ p) h = dn⊑ⁿ a b p h
dn⊑ⁿ a (N.G.suc b) p h = L.≺s (cp⊑ⁿ a b p h)
dn⊑ⁿ a (N.G.lim f) (n , p) h = L.≺l n (cp⊑ⁿ a (f n) p h)
dn⊑ⁿ a (N.G.lc () g) p h
dn⊑ⁿ a (N.G.em () d) p h

HS-readⁿ : ∀ a → N.Lgl N.zero a → L.HS (NA.read a)
HS-readⁿ N.G.zero l = L.hz
HS-readⁿ (N.G.suc a) l = L.hs (HS-readⁿ a l)
HS-readⁿ (N.G.lim f) l = L.hl (λ n → HS-readⁿ (f n) (proj₂ l n)) (λ n → cp⊑ⁿ (f n) (f (suc n)) (proj₁ l n))
HS-readⁿ (N.G.lc () g) l
HS-readⁿ (N.G.em () a) l
HS-readⁿ N.G.top l = L.hs L.hz

lower-readⁿ : ∀ a (l : N.Lgl N.zero a) → L.ψ⁰ (L.Ω (L.toLevel (NA.read a) (HS-readⁿ a l))) ≼ NA.read (NT.F a l)
lower-readⁿ a l = ≼-trans
  (VMᵖ (NA.read a) (HS-readⁿ a l) (MA.read (toM a)) (MV.HS-read (toM a) (toM-lgl a l))
    (ˣ→ᵖ (≅→≼ˣ (L.≅-sym (read≅ (toM-R a))))))
  (≼-trans (MV.lower-read (toM a) (toM-lgl a l)) (≅→≼ (F≅ a l)))

T₃-ownⁿ : ∀ n → L.ψ⁰ (L.Ω (L.toLevel (NA.read (NB.co (NT.P₃ n))) (HS-readⁿ _ (NB.lw (NT.P₃ n))))) ≼ NA.read NT.T₃
T₃-ownⁿ n = ≼l n (lower-readⁿ (NB.co (NT.P₃ n)) (NB.lw (NT.P₃ n)))

T₃-Ωωⁿ : L.ψ⁰ (L.Ω L.ωᴵ) ≼ NA.read NT.T₃
T₃-Ωωⁿ = ≼-trans MV.T₃-Ωω (≅→≼ T₃≅)
```

## 5 `T⁺`

`btbo-pⁿ`：照主线的 `btbo-p`，只用下一站的链点。`btbo⁺-from-main`：主线证出 `ChainP` 即得 `T⁺` 不低于 BTBO 的参照。
`T⁺-2T₃`：`T⁺` 的第 1 项沿根结点、`top` 的保留结点、ω 倍各取第 0 项走到 `T₃ + T₃` (`YiNextAcc.T₃+1≼T⁺` 的同一条路)。

```agda
btbo-pⁿ : ChainPⁿ → D.BTBOᴵ ≼ NA.read NT.T₃
btbo-pⁿ ch = l≼ (λ n → ≼l (proj₁ (ch n))
  (≼-trans (VMᵖ (D.γ n) (D.cert n) (NA.read (NB.co (NT.P₃ (proj₁ (ch n))))) (HS-readⁿ _ (NB.lw (NT.P₃ (proj₁ (ch n)))))
     (proj₂ (ch n)))
    (lower-readⁿ (NB.co (NT.P₃ (proj₁ (ch n)))) (NB.lw (NT.P₃ (proj₁ (ch n)))))))

btbo⁺-from-main : MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo⁺-from-main ch = NA.FromBTBO.btbo⁺ (btbo-pⁿ (chainP-transfer ch))

btbo₃-from-main : MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T₃
btbo₃-from-main ch = ≼-trans (MV.btbo-p ch) (≅→≼ T₃≅)

T⁺-Ωω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ NA.read NT.T⁺
T⁺-Ωω = ≼-trans T₃-Ωωⁿ NA.T₃≼T⁺

T⁺-2T₃ : (NA.read NT.T₃ L.+ NA.read NT.T₃) ≼ NA.read NT.T⁺
T⁺-2T₃ = ≼l 1 (≼l 0 (≼l 0 (≼l 0 (≼l 1 (≅→≼ (L.≅-sym (NA.read-plus NT.T₃ NT.T₃)))))))

T⁺-2Ωω : (L.ψ⁰ (L.Ω L.ωᴵ) L.+ L.ψ⁰ (L.Ω L.ωᴵ)) ≼ NA.read NT.T⁺
T⁺-2Ωω = ≼-trans (+-mono T₃-Ωωⁿ T₃-Ωωⁿ) T⁺-2T₃
```
