# YiGenNeg 第 6 项：链上的结点都在归一坐标的支里；上一轮两条否定的探针目标不在链上

**判决 (编译定理)：对一切 `n` 与任何 `Out`，链点 `pointsᴺ n` 的折叠问到的每个目标位置，要么在主干上，要么在某个归一坐标 `suc (nrm a)` 的那一支里 (`asked-norm`)。
`top-branch→lpo` 的目标族 `qα α` (第 `coordᴸ α` 支) 与 `fixed→wlpo` 的目标 `q_f` (第 `suc (suc ω′)` 支) 都不是归一坐标的支，所以不在问到的对里 (`lpo-target-off-chain`, `fixed-target-off-chain`)。**
这不否定那两条定理 (它们的前提是对一切位置的保留律)；它说的是归一链不满足它们的探针。归一链上问到的含极限层号位置的目标在 [YiGenNegWall](YiGenNegWall.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegNorm where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; cO)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiIrrNegWide using (seen; flag; dense)
open import OCF.Align.YiLvFoldAdd using (add)
open import OCF.Align.YiLvNegCompare using (onesᴰ)
open import OCF.Align.YiLvNegCum using (psum)
open import OCF.Align.YiLvNegKeep using (coordᴸ)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br; qα)
open import OCF.Align.YiOmNegBranchFixed using (η_f; q_f)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; t₀)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ)
open import OCF.Align.YiGenNegShape using (top₁; rᴺ)
open import OCF.Align.YiGenNegAsk using (module Asked)
```

## 1 不变量

`NP r`：位置在主干上，或在归一坐标的支里。`NB ξ`：`ξ` 没有嵌入的孩子，一切结点 (第一支与各支里的，对一切带守卫的坐标) 的位置满足 `NP`。

```agda
NP : Pre K₂ω → Set
NP (inj₂ (inj₂ (η , e , r))) = Σ R λ a → η ≡ G.suc (nrm a)
NP (inj₁ _) = ⊤
NP (inj₂ (inj₁ _)) = ⊤

NB : RΩ → Set
NB G.zero = ⊤
NB (G.suc a) = NB a
NB (G.lim f) = ∀ n → NB (f n)
NB (G.lc r c t g) = NP r × NB t × (∀ η (e : GdL K₂ω r c η) → NB (g η e))
NB (G.em i a) = ⊥
NB G.top = ⊤

add₀-NB : ∀ x → NB x → ∀ (a : R) → NB (add zero alg₀ x a)
add₀-NB x nx G.zero = nx
add₀-NB x nx (G.suc a) = add₀-NB x nx a
add₀-NB x nx (G.lim f) = λ n → add₀-NB x nx (f n)
add₀-NB x nx G.top = nx

top₁-NB : ∀ x → NB x → NB (top₁ x)
top₁-NB x nx = tt , nx , (λ η e → add₀-NB x nx η)

plus-NB : ∀ x a → NB x → NB a → NB (plusΩ x a)
plus-NB x G.zero nx na = nx
plus-NB x (G.suc a) nx na = plus-NB x a nx na
plus-NB x (G.lim f) nx na = λ n → plus-NB x (f n) nx (na n)
plus-NB x (G.lc r c t g) nx (np , nt , ng) =
  np , plus-NB x t nx nt , (λ η e → plus-NB x (g η e) nx (ng η e))
plus-NB x G.top nx na =
  tt , top₁-NB x nx , (λ η e → add₀-NB (top₁ x) (top₁-NB x nx) η)

copies-NB : ∀ y → NB y → ∀ n → NB (copiesΩ y n)
copies-NB y ny zero = ny
copies-NB y ny (suc n) = plus-NB y (copiesΩ y n) ny (copies-NB y ny n)

psum-NB : ∀ (g : ℕ → RΩ) → (∀ n → NB (g n)) → ∀ n → NB (psumΩ g n)
psum-NB g ng zero = ng zero
psum-NB g ng (suc n) = plus-NB (psumΩ g n) (g (suc n)) (psum-NB g ng n) (ng (suc n))

F₀-NB : ∀ a → NB (F₀ a)
F₀-NB G.zero = tt
F₀-NB (G.suc a) = copies-NB (F₀ a) (F₀-NB a)
F₀-NB (G.lim f) = λ n → F₀-NB (f n)
F₀-NB G.top = copies-NB G.top tt

t₀-NB : NB t₀
t₀-NB = tt , F₀-NB raw1 , (λ η e → F₀-NB η)

NodNB : ∀ {k} → Nod k → Set
NodNB {k} ν = ∀ r c t (g : (ζ : Low k r) → .(GdL k r c ζ) → RΩ) →
  NB t → (∀ ζ (e : GdL k r c ζ) → NB (g ζ e)) → NB (ν r c t g)

keepAll-NB : ∀ k (ν : Nod k) → NodNB ν → ∀ ξ → NB (keepAll k ν ξ)
keepAll-NB k ν H G.zero = tt
keepAll-NB k ν H (G.suc a) = copies-NB (keepAll k ν a) (keepAll-NB k ν H a)
keepAll-NB k ν H (G.lim f) = λ n → keepAll-NB k ν H (f n)
keepAll-NB k ν H (G.lc r c t g) =
  H r c _ _ (keepAll-NB k ν H t) (λ ζ e → keepAll-NB k ν H (g ζ e))
keepAll-NB (suc k) ν H (G.em _ a) = keepAll-NB k (nS ν) (λ r → H (inj₂ r)) a
keepAll-NB (lim f) ν H (G.em n a) = keepAll-NB (f n) (nL ν n) (λ r → H (n , r)) a
keepAll-NB (lc k c w b t g) ν H (G.em i a) = tt
keepAll-NB zero ν H G.top = copies-NB G.top tt
keepAll-NB (suc k) ν H G.top =
  H (inj₁ tt) (cO k) _ _
    (keepAll-NB k (nS ν) (λ r → H (inj₂ r)) (cO k))
    (λ ζ e → keepAll-NB k (nS ν) (λ r → H (inj₂ r)) ζ)
keepAll-NB (lim f) ν H G.top =
  psum-NB (λ n → keepAll (f n) (nL ν n) G.top)
    (λ n → keepAll-NB (f n) (nL ν n) (λ r → H (n , r)) G.top)
keepAll-NB (lc k c w b t g) ν H G.top = tt

KT-NB : ∀ a → NB (KT a)
KT-NB a = keepAll-NB (suc (read0 (nrm a))) (νᴮ (G.suc (nrm a)) (γ a))
  (λ r c t g nt ng → (a , refl) , nt , ng) G.top

Gκ-NB : ∀ η → NB (Gκ η)
Gκ-NB G.zero = t₀-NB
Gκ-NB (G.suc a) = plus-NB (Gκ a) (KT a) (Gκ-NB a) (KT-NB a)
Gκ-NB (G.lim f) = λ n → Gκ-NB (f n)
Gκ-NB G.top = t₀-NB

Φ-NB : ∀ ξ → NB ξ → NB (Φˢ⁺ ξ)
Φ-NB G.zero nb = tt
Φ-NB (G.suc a) nb = copies-NB (Φˢ⁺ a) (Φ-NB a nb)
Φ-NB (G.lim f) nb = λ n → Φ-NB (f n) (nb n)
Φ-NB (G.lc r c t g) (np , nt , ng) =
  np , Φ-NB t nt , (λ η e → Φ-NB (g η e) (ng η e))
Φ-NB G.top nb = tt , t₀-NB , (λ η e → Gκ-NB η)

points-NB : ∀ n → NB (pointsᴺ n)
points-NB zero = tt
points-NB (suc n) =
  plus-NB (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (points-NB n) (Φ-NB (pointsᴺ n) (points-NB n))
```

## 2 问到的目标都满足 `NP`

对一切规则，含第 1 个内部链点与保留结点的一切支。

```agda
module _ (n : ℕ) (Out : RΩ → R → Set) where
  open Asked (pointsᴺ n) Out

  inv⁰ : ∀ {ξ} → Ask⁰ ξ → NB ξ
  inv : ∀ {q ξ} → Ask q ξ → NP q × NB ξ

  inv⁰ z-start = points-NB n
  inv⁰ (z-suc p) = inv⁰ p
  inv⁰ (z-lim p m) = inv⁰ p m
  inv⁰ (z-obs p e) = proj₂ (proj₂ (inv⁰ p)) _ e
  inv⁰ (z-next p e₀ y o e₁) = proj₂ (proj₂ (inv⁰ p)) _ e₁

  inv (z-own p e) = proj₁ (inv⁰ p) , proj₂ (proj₂ (inv⁰ p)) _ e
  inv (o-suc p) = inv p
  inv (o-lim p m) = proj₁ (inv p) , proj₂ (inv p) m
  inv (o-keep p a η e) = proj₁ (inv p) , proj₂ (proj₂ (proj₂ (inv p))) η e
  inv (o-own p a e) = proj₁ (proj₂ (inv p)) , proj₂ (proj₂ (proj₂ (inv p))) _ e

  asked-norm : ∀ {q ξ} → Ask q ξ → NP q
  asked-norm p = proj₁ (inv p)
```

## 3 上一轮的两个探针目标不是归一坐标的支

归一的极限是部分和：第 2 项至少是 3。`1 + dense α` 的各项是 1 或 2，`ω′` 的各项是 1。

```agda
predᴿ : R → R
predᴿ (G.suc x) = x
predᴿ G.zero = G.zero
predᴿ (G.lim f) = G.zero
predᴿ G.top = G.zero

atᴿ : ℕ → R → R
atᴿ n (G.lim f) = f n
atᴿ n G.zero = G.zero
atᴿ n (G.suc x) = G.zero
atᴿ n G.top = G.zero

sx-nz : ∀ (w z : R) → G.zero ≡ G.suc w +ʳ z → ⊥
sx-nz w G.zero ()
sx-nz w (G.suc z) ()
sx-nz w (G.lim f) ()
sx-nz w G.top ()

no-norm-seq : ∀ b₀ b₂ (x y z : R) → one +ʳ flag b₀ ≡ x →
  one +ʳ flag b₂ ≡ (x +ʳ G.suc y) +ʳ G.suc z → ⊥
no-norm-seq b₀ false x y z e₀ e = sx-nz (x +ʳ y) z (cong predᴿ e)
no-norm-seq false true x y G.zero refl e = sx-nz G.zero y (cong predᴿ (cong predᴿ e))
no-norm-seq true true x y G.zero refl e = sx-nz one y (cong predᴿ (cong predᴿ e))
no-norm-seq b₀ true x y (G.suc z) e₀ e = sx-nz (x +ʳ y) z (cong predᴿ (cong predᴿ e))
no-norm-seq b₀ true x y (G.lim f) e₀ e with cong predᴿ e
... | ()
no-norm-seq b₀ true x y G.top e₀ e with cong predᴿ (cong predᴿ e)
... | ()

dense-not-norm : ∀ α a → one +ʳ dense α ≡ nrm a → ⊥
dense-not-norm α (G.lim f) e =
  no-norm-seq (seen α 0) (seen α 2) (nrm (f 0)) (nrm (f 1)) (nrm (f 2))
    (cong (atᴿ 0) e) (cong (atᴿ 2) e)

coordᴸ-not-norm : ∀ α a → coordᴸ α ≡ G.suc (nrm a) → ⊥
coordᴸ-not-norm α a e = dense-not-norm α a (cong predᴿ e)

ones-not-norm : ∀ a → onesᴰ ≡ nrm a → ⊥
ones-not-norm (G.lim f) e = step (nrm (f 0)) (nrm (f 1)) (cong (atᴿ 0) e) (cong (atᴿ 1) e)
  where
  step : ∀ (x y : R) → one ≡ x → one ≡ x +ʳ G.suc y → ⊥
  step x y refl e₁ = sx-nz G.zero y (cong predᴿ e₁)

η_f-not-norm : ∀ a → η_f ≡ G.suc (nrm a) → ⊥
η_f-not-norm (G.suc a) e = ones-not-norm a (cong predᴿ (cong predᴿ e))

lpo-target-off-chain : ∀ n Out α {ξ} → Asked.Ask (pointsᴺ n) Out (qα α) ξ → ⊥
lpo-target-off-chain n Out α p with asked-norm n Out p
... | a , e = coordᴸ-not-norm α a e

fixed-target-off-chain : ∀ n Out {ξ} → Asked.Ask (pointsᴺ n) Out q_f ξ → ⊥
fixed-target-off-chain n Out p with asked-norm n Out p
... | a , e = η_f-not-norm a e

-- 对照: 本轮的目标 rᴺ a 在归一坐标的支里.
rᴺ-norm : ∀ a → NP (rᴺ a)
rᴺ-norm a = a , refl
```
