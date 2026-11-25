# YiGenFold：槽位坐标截到有限部分的链，与它的目标层 0 闭项

**判决 (编译定理)：闭项 `Tᶜ : R` 与 `Lgl zero Tᶜ`，没有前提。链 `pointsᶜ` 与归一链 `pointsᴺ` 是同一个递归，只把 `top` 的保留行里槽位所在的支从 `suc (nrm a)` 换成 `suc (nrm (cut a))`
(`cut` 在极限处归零)；坐标不含极限的各支与归一行相等 (`Gᶜ≡Gκ`)。自目标的折叠 `Φˢᶜ` 保留一切结点；目标层 0 的折叠在一切链点上问到的派发都完全且不多保留 (`chain-honest`)。**
**用了替代行** (`topᶜ`、`rowᶠ`，以及沿用的 `topᴬ` 与 `T₃ᵐ` 里的部分和)，所以不写读法，没有值定理。`top` 在链问到的目标下满足上一轮 `TopBranch` 的保留律 (`top-branch-fin`)。一般形式在 [YiGenFoldDom](YiGenFoldDom.lagda.md)，归一链本身的约化在 [YiGenFoldGap](YiGenFoldGap.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenFoldFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested; cO; up; tw)
open import OCF.Align.YiIrrIf using (R; one; read0; iterate)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (lev; Kept; Tri; below; above; same)
open import OCF.Align.YiLvFoldAdd using (Pos)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiRawFoldBase using (Nd)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br; Link; compare-zero)
open import OCF.Align.YiOmIf using (Ω₁⁺)
open import OCF.Align.YiLvNegKeep using (LPO)
open import OCF.Align.YiOmNegBranch using (TopBranch; top-branch→lpo)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; F₁; F₀-dn; F₁-dn; F₁-cp; F₀-legal; F₁-legal;
  F₀-nested; F₁-nested; F₀-pos; F₁-pos; t₀)
open import OCF.Align.YiOmFoldGap using (Branches; RowLegal; row; row-legal; row-nested)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (pointsᴺ)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenFold
open import OCF.Align.YiGenFoldDom
```

## 1 不含极限的坐标：可判定，两两相连

`LimFree` 是 [YiOmFoldNorm](YiOmFoldNorm.lagda.md) 的谓词 (有限的数)。它由树判定；两个这样的坐标之间的第一位置路径由树算出。

```agda
lf? : ∀ η → LimFree η ⊎ (LimFree η → ⊥)
lf? G.zero = inj₁ tt
lf? (G.suc a) = lf? a
lf? (G.lim f) = inj₂ (λ ())
lf? G.top = inj₂ (λ ())

z≤ : ∀ b → LimFree b → Cp zero G.zero b
z≤ G.zero h = inj₁ refl
z≤ (G.suc b) h = inj₂ (z≤ b h)

sucCp : ∀ a b → LimFree b → Cp zero a b → Cp zero (G.suc a) (G.suc b)
sucCp a b h (inj₁ refl) = inj₁ refl
sucCp a (G.suc b) h (inj₂ p) = inj₂ (sucCp a b h p)

joinF : ∀ a b → LimFree a → LimFree b → Cp zero a b ⊎ Cp zero b a
joinF G.zero b h h′ = inj₁ (z≤ b h′)
joinF (G.suc a) G.zero h h′ = inj₂ (z≤ (G.suc a) h)
joinF (G.suc a) (G.suc b) h h′ with joinF a b h h′
... | inj₁ p = inj₁ (sucCp a b h′ p)
... | inj₂ p = inj₂ (sucCp b a h p)

one≤ : ∀ d → LimFree d → Cp zero one (G.suc d)
one≤ G.zero h = inj₁ refl
one≤ (G.suc d) h = inj₂ (one≤ d h)

lf-lgl : ∀ d → LimFree d → Lgl zero d
lf-lgl G.zero h = tt
lf-lgl (G.suc d) h = lf-lgl d h

gdF : ∀ d → LimFree (G.suc d) → Gd zero raw1 (G.suc d)
gdF d h = one≤ d h , lf-lgl d h , raw0-Nested (G.suc d)

open Spine LimFree lf? joinF gdF public
```

## 2 `top` 的保留行：槽位的支截到有限部分

`cut a`：`a` 在第一个极限之上的那段后继；它不含极限，所以 `suc (nrm (cut a))` 是有限的坐标。`Gᶜ` 与 `YiOmFoldNorm.Gκ` 同一个递归，结点取 `KT (cut a)`。
**替代行**：坐标含极限的支上，保留结点的层号是有限的，不是 `read0 (nrm a)`。

```agda
cut : R → R
cut G.zero = G.zero
cut (G.suc a) = G.suc (cut a)
cut (G.lim f) = G.zero
cut G.top = G.zero

cut-id : ∀ a → LimFree a → cut a ≡ a
cut-id G.zero h = refl
cut-id (G.suc a) h = cong G.suc (cut-id a h)

cut-free : ∀ a → LimFree (nrm (cut a))
cut-free G.zero = tt
cut-free (G.suc a) = cut-free a
cut-free (G.lim f) = tt
cut-free G.top = tt

Gᶜ : R → RΩ
Gᶜ G.zero = t₀
Gᶜ (G.suc a) = plusΩ (Gᶜ a) (KT (cut a))
Gᶜ (G.lim f) = G.lim (λ n → Gᶜ (f n))
Gᶜ G.top = t₀

Gᶜ-first : ∀ η → Cp K₂ω t₀ (Gᶜ η)
Gᶜ-first G.zero = inj₁ refl
Gᶜ-first (G.suc a) = Cp-tr K₂ω (Gᶜ-first a) (plus-weak (Gᶜ a) (KT (cut a)))
Gᶜ-first (G.lim f) = inj₂ (zero , Gᶜ-first (f zero))
Gᶜ-first G.top = inj₁ refl

Gᶜ-cp : ∀ {η} η′ → Cp zero η η′ → Cp K₂ω (Gᶜ η) (Gᶜ η′)
Gᶜ-cp η′ (inj₁ refl) = inj₁ refl
Gᶜ-cp (G.suc b) (inj₂ p) = Cp-tr K₂ω (Gᶜ-cp b p) (plus-weak (Gᶜ b) (KT (cut b)))
Gᶜ-cp (G.lim f) (inj₂ (n , p)) = inj₂ (n , Gᶜ-cp (f n) p)

Gᶜ-legal : ∀ η → Lgl zero η → Lgl K₂ω (Gᶜ η)
Gᶜ-legal G.zero l = F₁-legal G.top tt
Gᶜ-legal (G.suc a) l = plus-lgl (Gᶜ a) (KT (cut a)) (Gᶜ-legal a l) (KT-legal (cut a))
Gᶜ-legal (G.lim f) (st , lf) =
  (λ n → Gᶜ-cp (f (suc n)) (st n)) , (λ n → Gᶜ-legal (f n) (lf n))
Gᶜ-legal G.top l = F₁-legal G.top tt

Gᶜ-nested : ∀ η → Nested K₂ω (Gᶜ η)
Gᶜ-nested G.zero = F₁-nested G.top tt
Gᶜ-nested (G.suc a) = plus-ns (Gᶜ a) (KT (cut a)) (Gᶜ-nested a) (KT-nested (cut a))
Gᶜ-nested (G.lim f) = λ n → Gᶜ-nested (f n)
Gᶜ-nested G.top = F₁-nested G.top tt

βᶜ : Branches
βᶜ η e = Gᶜ η

βᶜ-legal : RowLegal βᶜ
βᶜ-legal = record
  { first = λ η e → Gᶜ-first η
  ; directed = λ η e η′ e′ q → Gᶜ-cp η′ (proj₁ q)
  ; lawful = λ η e → Gᶜ-legal η (proj₁ (proj₂ e))
  ; nested = λ η e → Gᶜ-nested η }

topᶜ : RΩ
topᶜ = row βᶜ

topᶜ-legal : Lgl K₂ω topᶜ
topᶜ-legal = row-legal βᶜ βᶜ-legal

topᶜ-nested : Nested K₂ω topᶜ
topᶜ-nested = row-nested βᶜ βᶜ-legal
```

与归一行的关系：坐标不含极限的支上两者相等 (命题相等)；保留律在这些坐标上成立，槽位的层号是 `read0 a`。

```agda
Gᶜ≡Gκ : ∀ η → LimFree η → Gᶜ η ≡ Gκ η
Gᶜ≡Gκ G.zero h = refl
Gᶜ≡Gκ (G.suc a) h = cong₂ plusΩ (Gᶜ≡Gκ a h) (cong KT (cut-id a h))

cut-keep : ∀ a (e : Gd zero raw1 (G.suc a)) →
  Kept K₂ω (read0 (nrm (cut a))) (βᶜ (G.suc a) e)
cut-keep a e =
  br (G.suc (nrm (cut a))) (γ (cut a)) (inj₁ tt) , refl , cO (read0 (nrm (cut a))) , _ , _ , refl

cut-keep-fin : ∀ a → LimFree a → (e : Gd zero raw1 (G.suc a)) →
  Kept K₂ω (read0 a) (βᶜ (G.suc a) e)
cut-keep-fin a h e =
  subst (λ z → Kept K₂ω (read0 z) (Gᶜ (G.suc a))) (nrm-id a h)
    (subst (λ z → Kept K₂ω (read0 (nrm z)) (Gᶜ (G.suc a))) (cut-id a h) (cut-keep a e))
```

## 3 自目标的折叠

与 `YiOmFoldChain.Φˢ⁺` 逐行相同，只有 `top` 的行换成 `topᶜ`。对一切树有定义；每个结点保留在自己的位置上。

```agda
Φˢᶜ : RΩ → RΩ
Φˢᶜ G.zero = G.top
Φˢᶜ (G.suc a) = successorΩ (Φˢᶜ a)
Φˢᶜ (G.lim f) = G.lim (λ n → Φˢᶜ (f n))
Φˢᶜ (G.lc r c t g) = G.lc r c (Φˢᶜ t) (λ η e → Φˢᶜ (g η e))
Φˢᶜ (G.em (inj₁ _) a) = F₀ a
Φˢᶜ (G.em (inj₂ (inj₁ _)) a) = F₁ a
Φˢᶜ (G.em (inj₂ (inj₂ (η , e))) a) = keepAll (read0 η) (νᴮ η e) a
Φˢᶜ G.top = topᶜ

Φˢᶜ-pos : ∀ ξ → Pos K₂ω (Φˢᶜ ξ)
Φˢᶜ-pos G.zero = tt
Φˢᶜ-pos (G.suc a) = tt
Φˢᶜ-pos (G.lim f) = tt
Φˢᶜ-pos (G.lc r c t g) = tt
Φˢᶜ-pos (G.em (inj₁ _) a) = F₀-pos a
Φˢᶜ-pos (G.em (inj₂ (inj₁ _)) a) = F₁-pos a
Φˢᶜ-pos (G.em (inj₂ (inj₂ (η , e))) a) = KA-pos (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a
Φˢᶜ-pos G.top = tt

Φˢᶜ-cp : ∀ {ξ ξ′} → Cp K₂ω ξ ξ′ → Cp K₂ω (Φˢᶜ ξ) (Φˢᶜ ξ′)
Φˢᶜ-dn : ∀ {ξ} ξ′ → Dn K₂ω ξ ξ′ → Dn K₂ω (Φˢᶜ ξ) (Φˢᶜ ξ′)
Φˢᶜ-cp (inj₁ refl) = inj₁ refl
Φˢᶜ-cp {ξ′ = ξ′} (inj₂ p) = inj₂ (Φˢᶜ-dn ξ′ p)
Φˢᶜ-dn (G.suc b) p = zero , Φˢᶜ-cp p
Φˢᶜ-dn (G.lim f) (n , p) = n , Φˢᶜ-cp p
Φˢᶜ-dn (G.lc r c t g) p = Φˢᶜ-cp p
Φˢᶜ-dn {G.em (inj₁ _) a} (G.em (inj₁ _) T) p = F₀-dn T p
Φˢᶜ-dn {G.em (inj₂ (inj₁ _)) a} (G.em (inj₂ (inj₁ _)) T) p = F₁-dn T p
Φˢᶜ-dn {G.em (inj₂ (inj₂ (η , e))) a} (G.em (inj₂ (inj₂ .(η , e))) T) (refl , p) =
  KA-dn (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) T p
Φˢᶜ-dn {G.em (inj₂ (inj₁ _)) a} G.top p = F₁-cp p

Φˢᶜ-legal : ∀ ξ → Lgl K₂ω ξ → Lgl K₂ω (Φˢᶜ ξ)
Φˢᶜ-legal G.zero l = tt
Φˢᶜ-legal (G.suc a) l = copiesΩ-step (Φˢᶜ a) , copiesΩ-legal (Φˢᶜ a) (Φˢᶜ-legal a l)
Φˢᶜ-legal (G.lim f) (st , lf) = (λ n → Φˢᶜ-cp (st n)) , (λ n → Φˢᶜ-legal (f n) (lf n))
Φˢᶜ-legal (G.lc r c t g) (tg , dir , irr , lt , lg) =
  (λ η e → Φˢᶜ-cp (tg η e)) , (λ η e η′ e′ q → Φˢᶜ-cp (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) , Φˢᶜ-legal t lt , (λ η e → Φˢᶜ-legal (g η e) (lg η e))
Φˢᶜ-legal (G.em (inj₁ _) a) l = F₀-legal a l
Φˢᶜ-legal (G.em (inj₂ (inj₁ _)) a) l = F₁-legal a l
Φˢᶜ-legal (G.em (inj₂ (inj₂ (η , e))) a) l =
  KA-legal (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a l
Φˢᶜ-legal G.top l = topᶜ-legal

Φˢᶜ-nested : ∀ ξ → Nested K₂ω ξ → Nested K₂ω (Φˢᶜ ξ)
Φˢᶜ-nested G.zero nb = tt
Φˢᶜ-nested (G.suc a) nb = copiesΩ-nested (Φˢᶜ a) (Φˢᶜ-nested a nb)
Φˢᶜ-nested (G.lim f) nb = λ n → Φˢᶜ-nested (f n) (nb n)
Φˢᶜ-nested (G.lc r c t g) (l , nl , nt , ng) =
  l , nl , Φˢᶜ-nested t nt , (λ η e → Φˢᶜ-nested (g η e) (ng η e))
Φˢᶜ-nested (G.em (inj₁ _) a) nb = F₀-nested a
Φˢᶜ-nested (G.em (inj₂ (inj₁ _)) a) nb = F₁-nested a nb
Φˢᶜ-nested (G.em (inj₂ (inj₂ (η , e))) a) nb =
  KA-nested (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a nb
Φˢᶜ-nested G.top nb = topᶜ-nested

Φˢᶜ-keep : ∀ r c t g → Kept K₂ω (lev K₂ω r) (Φˢᶜ (G.lc r c t g))
Φˢᶜ-keep r c t g = r , refl , c , _ , _ , refl

Φˢᶜ-top-row : Φˢᶜ G.top ≡ G.lc root₂ raw1 t₀ (λ η e → Gᶜ η)
Φˢᶜ-top-row = refl
```

## 4 定义域对链封闭

```agda
GᶜD : ∀ η → D (Gᶜ η)
GᶜD G.zero = t₀D
GᶜD (G.suc a) = plusD (Gᶜ a) (KT (cut a)) (GᶜD a) (KT-D (cut a) (cut-free a))
GᶜD (G.lim f) = λ n → GᶜD (f n)
GᶜD G.top = t₀D

topᶜD : D topᶜ
topᶜD = t₀D , (λ η e → GᶜD η)

Φˢᶜ-D : ∀ ξ → D ξ → D (Φˢᶜ ξ)
Φˢᶜ-D G.zero d = tt
Φˢᶜ-D (G.suc a) d = copiesD (Φˢᶜ a) (Φˢᶜ-D a d)
Φˢᶜ-D (G.lim f) d = λ n → Φˢᶜ-D (f n) (d n)
Φˢᶜ-D (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) = Φˢᶜ-D t dt , (λ η e → Φˢᶜ-D (g η e) (dg η e))
Φˢᶜ-D (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) =
  Φˢᶜ-D t dt , (λ η e → Φˢᶜ-D (g η e) (dg η e))
Φˢᶜ-D (G.lc (inj₂ (inj₂ (η , e , r))) c t g) (h , dt , dg) =
  h , Φˢᶜ-D t dt , (λ ζ e′ → Φˢᶜ-D (g ζ e′) (dg ζ e′))
Φˢᶜ-D G.top d = topᶜD
```

## 5 链与闭项

链点带坐标与三份无关的证书。起点 `top`；下一点是这一点加上 `Φˢᶜ` 在这一点的输出；观察是目标第 0 层的折叠 `Ψᶠ base`。

```agda
record Ptᶜ : Set where
  constructor ptᶜ
  field
    atᶜ : RΩ
    .dmᶜ : D atᶜ
    .lgᶜ : Lgl K₂ω atᶜ
    .nsᶜ : Nested K₂ω atᶜ
open Ptᶜ public using (atᶜ)

bodyᶜ : Ptᶜ → RΩ
bodyᶜ (ptᶜ ξ d l nb) = Φˢᶜ ξ

obsᶜ : Ptᶜ → R
obsᶜ (ptᶜ ξ d l nb) = Ψᶠ base ξ d l nb

nextᶜ : Ptᶜ → Ptᶜ
nextᶜ (ptᶜ ξ d l nb) = ptᶜ (plusΩ ξ (Φˢᶜ ξ))
  (plusD ξ (Φˢᶜ ξ) d (Φˢᶜ-D ξ d))
  (plus-lgl ξ (Φˢᶜ ξ) l (Φˢᶜ-legal ξ l))
  (plus-ns ξ (Φˢᶜ ξ) nb (Φˢᶜ-nested ξ nb))

startᶜ : Ptᶜ
startᶜ = ptᶜ G.top tt tt tt

pointsᶜ : ℕ → Ptᶜ
pointsᶜ = iterate nextᶜ startᶜ

Tᶜ : R
Tᶜ = G.lim (λ n → obsᶜ (pointsᶜ n))

dmʳ : ∀ n → D (atᶜ (pointsᶜ n))
dmʳ zero = tt
dmʳ (suc n) = plusD (atᶜ (pointsᶜ n)) (bodyᶜ (pointsᶜ n)) (dmʳ n)
  (Φˢᶜ-D (atᶜ (pointsᶜ n)) (dmʳ n))

lgʳ : ∀ n → Lgl K₂ω (atᶜ (pointsᶜ n))
lgʳ zero = tt
lgʳ (suc n) = plus-lgl (atᶜ (pointsᶜ n)) (bodyᶜ (pointsᶜ n)) (lgʳ n)
  (Φˢᶜ-legal (atᶜ (pointsᶜ n)) (lgʳ n))

nsʳ : ∀ n → Nested K₂ω (atᶜ (pointsᶜ n))
nsʳ zero = tt
nsʳ (suc n) = plus-ns (atᶜ (pointsᶜ n)) (bodyᶜ (pointsᶜ n)) (nsʳ n)
  (Φˢᶜ-nested (atᶜ (pointsᶜ n)) (nsʳ n))

obsᶜ-step : ∀ n → Cp zero (obsᶜ (pointsᶜ n)) (obsᶜ (pointsᶜ (suc n)))
obsᶜ-step n =
  Ψᶠ-cp base (atᶜ (pointsᶜ (suc n))) (dmʳ n) (dmʳ (suc n))
    (lgʳ n) (nsʳ n) (lgʳ (suc n)) (nsʳ (suc n))
    (plus-weak (atᶜ (pointsᶜ n)) (bodyᶜ (pointsᶜ n)))

Tᶜ-legal : Lgl zero Tᶜ
Tᶜ-legal = obsᶜ-step ,
  (λ n → Ψᶠ-legal base (atᶜ (pointsᶜ n)) (dmʳ n) (lgʳ n) (nsʳ n))
```

## 6 根上的行

都是 `refl`。`guardsᶜ`：链点是 `Ω₁⁺` 的带守卫坐标。第 0 项是 `tw 3` 的闭项。第 1 个链点与归一链的第 1 个链点只在分支函数上不同 (`Gᶜ` 对 `Gκ`)。

```agda
branchᶜ : (ξ : RΩ) → .(Gd K₂ω G.top ξ) → LF
branchᶜ ξ e = up K₂ω ξ (proj₂ (proj₂ e))

Ω₁⁺-nodeᶜ : Ω₁⁺ ≡ lc K₂ω G.top tt tt (tw 3) branchᶜ
Ω₁⁺-nodeᶜ = refl

Tᶜ-start : atᶜ (pointsᶜ 0) ≡ G.top
Tᶜ-start = refl

Tᶜ-feedback : ∀ n → atᶜ (pointsᶜ (suc n)) ≡ plusΩ (atᶜ (pointsᶜ n)) (Φˢᶜ (atᶜ (pointsᶜ n)))
Tᶜ-feedback n = refl

Tᶜ-term : ∀ n → obsᶜ (pointsᶜ n) ≡ Ψᶠ base (atᶜ (pointsᶜ n)) (dmʳ n) (lgʳ n) (nsʳ n)
Tᶜ-term n = refl

Tᶜ-grow : ∀ n → Dn K₂ω (atᶜ (pointsᶜ n)) (atᶜ (pointsᶜ (suc n)))
Tᶜ-grow n = plus-grow (atᶜ (pointsᶜ n)) (bodyᶜ (pointsᶜ n)) (Φˢᶜ-pos (atᶜ (pointsᶜ n)))

guardsᶜ : ∀ n → Gd K₂ω G.top (atᶜ (pointsᶜ n))
guardsᶜ zero = inj₁ refl , tt , tt
guardsᶜ (suc n) =
  Cp-tr K₂ω (proj₁ (guardsᶜ n)) (inj₂ (Tᶜ-grow n)) , lgʳ (suc n) , nsʳ (suc n)

Tᶜ-branch : ∀ n → branchᶜ (atᶜ (pointsᶜ n)) (guardsᶜ n) ≡ up K₂ω (atᶜ (pointsᶜ n)) (nsʳ n)
Tᶜ-branch n = refl

Tᶜ-term₀ : obsᶜ (pointsᶜ 0) ≡ T₃ᵐ
Tᶜ-term₀ = refl

T₃ᵐ-firstᶜ : Dn zero T₃ᵐ Tᶜ
T₃ᵐ-firstᶜ = zero , inj₁ refl

point₁ᶜ : atᶜ (pointsᶜ 1) ≡
  G.lc root₂ raw1 (plusΩ G.top t₀) (λ η e → plusΩ G.top (Gᶜ η))
point₁ᶜ = refl

point₁ᴺ-form : pointsᴺ 1 ≡
  G.lc root₂ raw1 (plusΩ G.top t₀) (λ η e → plusΩ G.top (Gκ η))
point₁ᴺ-form = refl

point₁-agree : ∀ η → LimFree η → plusΩ G.top (Gᶜ η) ≡ plusΩ G.top (Gκ η)
point₁-agree η h = cong (plusΩ G.top) (Gᶜ≡Gκ η h)
```

## 7 强度的证据：链点上问到的派发

量化域：从 "把第 `n` 个链点折到第 0 层" 出发的调用闭包 `Ask base (pointsᶜ n)` 里的每个结点 (目标 `τ`，位置 `p`)。在其上 `Ψᶠ τ` 满足接口的 `Honest`。
`chain-kept`, `chain-lim` 是同一件事不经接口的写法。

```agda
chain-honest : ∀ n {τ p c t g} (a : Ask base (atᶜ (pointsᶜ n)) τ (G.lc p c t g))
  (d : D (G.lc p c t g)) (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
  Honest (posT τ) (ownAt τ (G.lc p c t g) d l nb) (G.lc p c t g)
chain-honest n a d l nb = honestˢ tt (dmʳ n) a d l nb

chain-dom : ∀ n {τ ξ} → Ask base (atᶜ (pointsᶜ n)) τ ξ → FinT τ × D ξ
chain-dom n a = ask-closed a tt (dmʳ n)

chain-kept : ∀ n {τ p c t g} (a : Ask base (atᶜ (pointsᶜ n)) τ (G.lc p c t g))
  (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
  At (tl τ) (lev K₂ω p) →
  Kept (tl τ) (lev K₂ω p) (Ψᶠ τ (G.lc p c t g) (proj₂ (chain-dom n a)) l nb)
chain-kept n {τ} {p} {c} {t} {g} a l nb =
  proj₁ (honestᴰ τ (proj₁ (chain-dom n a)) p c t g (proj₂ (chain-dom n a)) l nb)

chain-lim : ∀ n {τ p c t g} (a : Ask base (atᶜ (pointsᶜ n)) τ (G.lc p c t g))
  (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
  (At (tl τ) (lev K₂ω p) → ⊥) →
  IsLim (Ψᶠ τ (G.lc p c t g) (proj₂ (chain-dom n a)) l nb)
chain-lim n {τ} {p} {c} {t} {g} a l nb =
  proj₂ (honestᴰ τ (proj₁ (chain-dom n a)) p c t g (proj₂ (chain-dom n a)) l nb)
```

## 8 `top` 在链问到的目标下：上一轮的墙不在这些目标上

链问到的分支目标都在有限坐标的支上 (`chain-dom`)，目标层是有限的数。这时 "层号 `read0 d` 在目标层的位置上" 只对不含极限的 `d` 成立 (`at-fin`)，
而在这些 `d` 上 `rowᶠ` 的分支族满足保留律。所以 `YiOmNegBranch.TopBranch` 的保留律限制到这些目标时有实例，没有前提 (`top-branch-fin`)；
分支取折叠实际用的那一行的分支族 `S`。`TopBranch` 本身 (一切目标) 推出 LPO，那里的探针目标在含极限的坐标的支上。

```agda
FinL : LF → Set
FinL zero = ⊤
FinL (suc k) = FinL k
FinL (lim f) = ⊥
FinL (lc k c w b t g) = ⊥

read-fin : ∀ a → LimFree a → FinL (read0 a)
read-fin G.zero h = tt
read-fin (G.suc a) h = read-fin a h

lev-fin : ∀ m → FinL m → ∀ s → FinL (lev m s)
lev-fin (suc m) h (inj₁ _) = h
lev-fin (suc m) h (inj₂ s) = lev-fin m h s

fin-read : ∀ d → FinL (read0 d) → Cp zero one (G.suc d) → LimFree d
fin-read G.zero h p = tt
fin-read (G.suc d) h (inj₁ ())
fin-read (G.suc d) h (inj₂ p) = fin-read d h p
fin-read (G.lim f) () p
fin-read G.top h (inj₁ ())
fin-read G.top h (inj₂ (inj₁ ()))
fin-read G.top h (inj₂ (inj₂ ()))

at-fin : ∀ η (r : Pre (read0 η)) → LimFree η → ∀ d → Gd zero raw1 (G.suc d) →
  At (lev (read0 η) r) (read0 d) → LimFree d
at-fin η r h d e′ (s , q) =
  fin-read d (subst FinL q (lev-fin (lev (read0 η) r) (lev-fin (read0 η) (read-fin η h) r) s))
    (proj₁ e′)

top-keep : ∀ η e r → LimFree η → ∀ s₀ z d → Gd zero raw1 (G.suc d) →
  At (lev (read0 η) r) (read0 d) →
  Kept (lev (read0 η) r) (read0 d) (TopRow.Row.S η e r s₀ z (G.suc d))
top-keep η e r h s₀ z d e′ a =
  TopRow.Row.S-keep η e r s₀ z d h (at-fin η r h d e′ a) a

-- TopBranch 的同形记录, 目标限制到谓词 Q.
record TopBranchOn (Q : Pre K₂ω → Set) : Set where
  field
    branch : (q : Pre K₂ω) → Q q → (η : R) → .(Gd zero raw1 η) → Raw (lev K₂ω q)
    branch-keep : ∀ q (h : Q q) s (e : Gd zero raw1 (G.suc s)) →
      Link (br (G.suc s) e (inj₁ tt)) q → At (lev K₂ω q) (read0 s) →
      Kept (lev K₂ω q) (read0 s) (branch q h (G.suc s) e)

branchTri : ∀ j → Tri zero j → ((s : Pre j) → lev j s ≡ zero → R → Raw j) → R → Raw j
branchTri j (below () q) mk
branchTri j (above s z) mk = mk s z
branchTri .zero (same refl) mk = λ _ → T₃ᵐ

branchTri-keep : ∀ j (x : Tri zero j) mk k y →
  (∀ s z → Kept j k (mk s z y)) → At j k → Kept j k (branchTri j x mk y)
branchTri-keep j (below () q) mk k y h a
branchTri-keep j (above s z) mk k y h a = h s z
branchTri-keep .zero (same refl) mk k y h (() , q)

branchᶠ : (q : Pre K₂ω) → GoodP q → (η : R) → .(Gd zero raw1 η) → Raw (lev K₂ω q)
branchᶠ (inj₁ (inj₁ _)) h η′ e′ = T₃ᵐ
branchᶠ (inj₂ (inj₁ (inj₁ _))) h η′ e′ = T₃ᵐ
branchᶠ (inj₂ (inj₂ (η , e , r))) h η′ e′ =
  branchTri (lev (read0 η) r) (compare-zero η e r) (TopRow.Row.S η e r) η′

top-branch-fin : TopBranchOn GoodP
top-branch-fin = record { branch = branchᶠ ; branch-keep = keepᶠ }
  where
  keepᶠ : ∀ q (h : GoodP q) s (e : Gd zero raw1 (G.suc s)) →
    Link (br (G.suc s) e (inj₁ tt)) q → At (lev K₂ω q) (read0 s) →
    Kept (lev K₂ω q) (read0 s) (branchᶠ q h (G.suc s) e)
  keepᶠ (inj₁ (inj₁ _)) h s e lk (() , q)
  keepᶠ (inj₂ (inj₁ (inj₁ _))) h s e lk (() , q)
  keepᶠ (inj₂ (inj₂ (η , e₀ , r))) h s e lk a =
    branchTri-keep (lev (read0 η) r) (compare-zero η e₀ r) (TopRow.Row.S η e₀ r)
      (read0 s) (G.suc s) (λ s₀ z → top-keep η e₀ r h s₀ z s e a) a

-- Q 恒真时就是上一轮的 TopBranch, 推出 LPO; 所以边界在目标所在的支的坐标上.
on-all→top-branch : TopBranchOn (λ _ → ⊤) → TopBranch
on-all→top-branch F = record
  { branch = λ q → TopBranchOn.branch F q tt
  ; branch-keep = λ q → TopBranchOn.branch-keep F q tt }

on-all→lpo : TopBranchOn (λ _ → ⊤) → LPO
on-all→lpo F = top-branch→lpo (on-all→top-branch F)

-- 分支族就是 rowᶠ 的分支.
row-branch : ∀ η e r s₀ z δ .(e′ : Gd zero raw1 δ) →
  Nd.gm (TopRow.Row.N η e r s₀ z) δ e′ ≡ TopRow.Row.S η e r s₀ z δ
row-branch η e r s₀ z δ e′ = refl
```
