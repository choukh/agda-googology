# 验收一侧: 遗传封闭的关系族在读回层号与有限层号之间的桥

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提. 层号 ℓ 带等式 `e : ℓ ≡ fn N` 时把 ℓ 上的关系读成 [YiHCFam](YiHCFam.lagda.md) 的封闭族 (`MB`, `LwB`), 及 `LFAB`, `embB`, `kcaseB`, `kcaseB₂`, `feedB`.
> 来源: 照 `YiLRBridge` 逐行搬来 (陈述逐字相同, `M` 换成封闭族; 这里没有对推导的归纳, 不加行); 路径的读法 (`τ`, `τ₂`, `comp`, `∙pth`, `NwB`, `slotPsh`) 与关系无关, 直接引用 `YiLRBridge`.
> 用在 [YiHCLim](YiHCLim.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCBridge where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; kp⁼; mapK)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (pt; can; tc)
open import OCF.Lean.YiHCFold using (module Self; LF; GB; mkGB; Qu) renaming (kcase to kcaseR)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r)
open import OCF.Lean.YiHCRel using (mz; mU)
import OCF.Align.EboLeanDef as E
open E using (natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (fn; lev; levP)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; pos⁼; PV; pv; view; levEq; toBr; gen; gtJ)
open import OCF.Lean.YiHCFam using (M; Lw⁼; LwP; toLw; ΩJ)
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ; τ₂; τ∙; τ₂∙; τ₂self; τ₂S; τ₂SS; comp; ∙pth; slotPsh)
```

## 读法

```agda
MB : ∀ {N} (ℓ : L) → ℓ ≡ fn N → E.T → Tr ℓ → Set
MB {N} _ refl = M N

LwB : ∀ {N} (ℓ : L) → ℓ ≡ fn N → (t : Pos⁼ ℓ) → E.T → Br⁼ ℓ t → Set
LwB {N} _ refl = Lw⁼ N

GBB : ∀ {N} (ℓ : L) → ℓ ≡ fn N → Base ℓ → E.T → Set
GBB {N = zero}  _ refl B t₀ = ⊤
GBB {N = suc N} _ refl B t₀ = GB N B t₀

MβB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) → MB ℓ e (Ωᴺ N) (proj₁ (Ωt ℓ))
MβB {N} _ refl = ΩJ N (Ωt (fn N)) ⊴r
```

## 孩子层上折到有限层

```agda
LFA : ∀ {N j} (s : Sb N j) (o : Ok (fn N)) (r : Rb (fn N)) (B : Base (fn N)) (t₀ : E.T) → GBB (fn N) refl B t₀
    → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
    → ∀ {a x} → M N a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn N) o r B (fn j) (pth s) β x))
LFA {N = zero}  s0     o r B t₀ gb β hβ m = Qu o r B self β hβ m
LFA {N = suc N} s0     o r B t₀ gb β hβ m = Self.PF N o r B β hβ m
LFA {N = suc N} (ss s) o r B t₀ gb β hβ m = LF o r (tc s) t₀ B gb β hβ m

LFAB : ∀ {N j} (ℓ : L) (e : ℓ ≡ fn N) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (v : fn j ≤ ℓ) (s : Sb N j) → τ e v ≡ pth s
     → (t₀ : E.T) → GBB ℓ e B t₀ → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
     → ∀ {a x} → MB ℓ e a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ ℓ o r B (fn j) v β x))
LFAB _ refl o r B _ s refl t₀ gb β hβ m = LFA s o r B t₀ gb β hβ m

mkGBB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (B : Base ℓ) (t₀ : E.T)
      → (∀ {i} (si : Sb N i) (u : fn i ≤ ℓ) → τ e u ≡ pth si
           → (proj₁ (Ωt (fn i)) ⊴ proj₁ (B (fn i) u)) × M i (ψᴺ i t₀) (proj₁ (B (fn i) u)))
      → GBB ℓ e B t₀
mkGBB {N = zero}  _ refl B t₀ H = tt
mkGBB {N = suc N} _ refl B t₀ H =
  mkGB (λ si → proj₁ (H (ss si) (inc tt (pth si)) refl)) (λ si → proj₂ (H (ss si) (inc tt (pth si)) refl))
```

## 孩子树沿路径搬进高层

```agda
embM : ∀ {B A} (s′ : Sb B A) (o : Ok (fn B)) (y : Tr (fn A)) (ey : fn A ⊢ zero ◃ y) {s₁}
     → M A s₁ y → M B s₁ (proj₁ (emb (fn B) o (pth s′) (y , ey)))
embM s0      o y ey m = m
embM (ss s′) o y ey m = mU mz (embM s′ (proj₂ o tt) y ey m)

embB : ∀ {A B} (ℓ ℓ′ : L) (e : ℓ ≡ fn A) (e′ : ℓ′ ≡ fn B) (o : Ok ℓ′) (u : ℓ ≤ ℓ′) (s′ : Sb B A) → τ₂ e e′ u ≡ pth s′
     → (y : Tr ℓ) (ey : ℓ ⊢ zero ◃ y) → ∀ {s₁} → MB ℓ e s₁ y → MB ℓ′ e′ s₁ (proj₁ (emb ℓ′ o u (y , ey)))
embB _ _ refl refl o _ s′ refl y ey m = embM s′ o y ey m
```

## 保留判定

槽位 t 朝 `fn j` (路径读成 `pth s`): 不保留时交出 "ν+1 > j", 保留时交出目标层的槽位与 "ν 是它的层号". `kcaseB₂`: 槽位先沿 u 推进高层.

```agda
kcaseV : ∀ {N j} (o : Ok (fn N)) (t : Pos⁼ (fn N)) → PV N t → (s : Sb N j)
       → ∀ {ν} → ν ≡ natT (lev N t) → (Q : Keep (fn j) (Br⁼ (fn N) t) (bz⁼ (fn N) t) → Set)
       → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
       → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ (fn N) t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ (fn N) t)
            → ν ≡ natT (levP j q) → (∀ η c → LwP j q η c → Lw⁼ N t η (cv c)) → Q (just (q , cv , eq)))
       → Q (kp⁼ (fn N) o t (pth s))
kcaseV o .(pos⁼ si) (pv {i} si) s {ν} nu Q dr kc =
  kcaseR o si (can s) Q (λ le → dr (gtJ le eqν)) (λ q cv eq lq lw → kc q cv eq (trans eqν (cong natT (sym lq))) lw)
  where
  eqν : ν ≡ natT i
  eqν = trans nu (cong natT (levEq si))

kcaseB : ∀ {N j} (ℓ : L) (e : ℓ ≡ fn N) (o : Ok ℓ) (t : Pos⁼ ℓ) (v : fn j ≤ ℓ) (s : Sb N j) → τ e v ≡ pth s
       → ∀ {ν} → NwB ℓ e t ν → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
       → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
       → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
            → ν ≡ natT (levP j q) → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
       → Q (kp⁼ ℓ o t v)
kcaseB _ refl o t _ s refl nu Q dr kc = kcaseV o t (view _ t) s nu Q dr kc

lwPsh : ∀ {B A} (s′ : Sb B A) (t : Pos⁼ (fn A)) {η} (c : Br⁼ (fn B) (psh (pth s′) t))
      → Lw⁼ B (psh (pth s′) t) η c → Lw⁼ A t η (pshBr (pth s′) t c)
lwPsh s0      t c l = l
lwPsh (ss s′) t c l = lwPsh s′ t c l

kcaseF : ∀ {B A j} (s′ : Sb B A) (t : Pos⁼ (fn A)) (s : Sb B j) (o : Ok (fn B)) {ν} → ν ≡ natT (lev A t)
       → (Q : Keep (fn j) (Br⁼ (fn B) (psh (pth s′) t)) (bz⁼ (fn B) (psh (pth s′) t)) → Set)
       → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
       → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ (fn B) (psh (pth s′) t))
            (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ (fn B) (psh (pth s′) t))
            → ν ≡ natT (levP j q) → (∀ η c → LwP j q η c → Lw⁼ A t η (pshBr (pth s′) t (cv c))) → Q (just (q , cv , eq)))
       → Q (kp⁼ (fn B) o (psh (pth s′) t) (pth s))
kcaseF s0      t s      o nu Q dr kc = kcaseV o t (view _ t) s nu Q dr kc
kcaseF (ss s′) t s0     o nu Q dr kc =
  kc (inj₂ (tt , psh (pth s′) t)) (λ z → z) refl (trans nu (cong natT (sym (slotPsh s′ t)))) (λ η c l → lwPsh s′ t c l)
kcaseF (ss s′) t (ss s) o nu Q dr kc = kcaseF s′ t s (proj₂ o tt) nu Q dr kc

kcaseB₂ : ∀ {A B j} (ℓ ℓ′ : L) (e : ℓ ≡ fn A) (e′ : ℓ′ ≡ fn B) (o : Ok ℓ′) (u : ℓ ≤ ℓ′) (s′ : Sb B A) → τ₂ e e′ u ≡ pth s′
        → (t : Pos⁼ ℓ) (v : fn j ≤ ℓ′) (s : Sb B j) → τ e′ v ≡ pth s
        → ∀ {ν} → NwB ℓ e t ν → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
        → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
        → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
             → ν ≡ natT (levP j q) → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
        → Q (mapK (pshBr u t) (pshFirst u t) (kp⁼ ℓ′ o (psh u t) v))
kcaseB₂ _ _ refl refl o _ s′ refl t _ s refl nu Q dr kc =
  kcaseF s′ t s o nu (λ K → Q (mapK (pshBr (pth s′) t) (pshFirst (pth s′) t) K)) dr
    (λ q cv eq lq lw → kc q (λ z → pshBr (pth s′) t (cv z)) _ lq lw)
```

## 回灌一步

槽位 t 的分支取 "折到槽位所在层号" 的值 Ψ 时, 分支关系由各个有限子层号上的关系给出.

```agda
feedV : ∀ {N} (t : Pos⁼ (fn N)) → PV N t → ∀ {ν} → ν ≡ natT (lev N t) → (η : E.T) (Ψ : (k : L) → k ≤ fn N → Tr k)
      → (∀ {i} (si : Sb N i) (u : fn i ≤ fn N) → u ≡ pth si → ν ≡ natT i → M i η (Ψ (fn i) u))
      → Lw⁼ N t η (proj₂ (sl⁼ (fn N) t) (Ψ (proj₁ (sl⁼ (fn N) t)) (posW⁼ (fn N) t)))
feedV {N} .(pos⁼ si) (pv {i} si) nu η Ψ H =
  subst (Lw⁼ N (pos⁼ si) η) (sym (gen si Ψ)) (toLw si (H si (pth si) refl (trans nu (cong natT (levEq si)))))

feedB : ∀ {N} (ℓ : L) (e : ℓ ≡ fn N) (t : Pos⁼ ℓ) {ν} → NwB ℓ e t ν → (η : E.T) (Ψ : (k : L) → k ≤ ℓ → Tr k)
      → (∀ {i} (si : Sb N i) (u : fn i ≤ ℓ) → τ e u ≡ pth si → ν ≡ natT i → M i η (Ψ (fn i) u))
      → LwB ℓ e t η (proj₂ (sl⁼ ℓ t) (Ψ (proj₁ (sl⁼ ℓ t)) (posW⁼ ℓ t)))
feedB _ refl t nu η Ψ H = feedV t (view _ t) nu η Ψ H
```
