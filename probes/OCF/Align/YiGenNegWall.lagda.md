# YiGenNeg 第 4 项：第 2 个链点上，保留结点的各支把一切坐标带到一个含极限层号位置的目标之下

**判决 (编译定理，无函数外延)：第 2 个链点的根上第 1 个内部链点是 `1 + y` 且 `y` 的最左叶是 1 时 (`LeftOne`；由折叠的四行推出，见 [YiGenNegLeft](YiGenNegLeft.lagda.md))，对 `(r*, P₁)` 在问到的对里：
目标 `r*` 的层号是 `suc M*` (`M*` 是极限层号)，`P₁` 的根在根槽位上要保留，它的各支对一切坐标都被问到 (`probe`)。这些对上 `Honest` 推出：对每个 `α` 弱判定层号的字面相等 `Eqᴸ α` (`chain→weak-eq`)。**
不是矛盾：`Locate` 下 `Honest` 处处有模型 (`oracle-honest`)。前面的目标层只有 0 与 1，那里派发可判定 (`r₁-dec`)。只用到保留行的最弱联系 (`KeepRowAt`)。
`Eqᴸ α` 推出 `α` 全假；反向要函数外延，见 [YiGenNegWallWlpo](YiGenNegWallWlpo.lagda.md) (条件)。问到的对的定义在 [YiGenNegAsk](YiGenNegAsk.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegWall where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiIrrNegWide using (seen; seen-hit; flag; dense)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiLvNegCompare using (At; no-same; bodyᴸ)
open import OCF.Align.YiLvNegCert using (ω′)
open import OCF.Align.YiLvNegCum using (psum)
open import OCF.Align.YiLvNegKeep using (Locate; coordᴸ; coordᴸ-guard)
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiRawNegOmega
  using (K₂ω; root₂; br; read-shape; not-true; true≢false; placeᵒ; placeᵒ-kept; placeᵒ-lim)
open import OCF.Align.YiOmNegBranch using (at-one-dec)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (t₀)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenNegShape
open import OCF.Align.YiGenNegAsk
open import OCF.Align.YiGenNegLeft using (Rows; premise₂; Outˢ; rowsˢ; yˢ; outˢ; guardˢ)
```

## 1 两个目标与探针的层号

`r₁`：第 2 支的根，层号 1。`r*`：第 `suc (nrm (suc ω′))` 支的根，层号 `suc M*`，`M* = read0 (nrm ω′)` 是 ℕ 极限 (各项是 1, 3, 5, … 的读回)。
探针坐标 `coordᴸ α = suc (1 + dense α)` 对一切 `α` 有闭的相关守卫；`P₁` 在这个坐标上的那一支的根在 `rᴺ (cᶜ α)` 上，层号 `kᶜ α`。

```agda
two : R
two = G.suc one

r₁ : Pre K₂ω
r₁ = rᴺ one

r₁-level : lev K₂ω r₁ ≡ suc zero
r₁-level = refl

a* : R
a* = G.suc ω′

e* : Gd zero raw1 (G.suc a*)
e* = inj₂ (inj₂ (inj₂ (zero , inj₁ refl))) , ((λ _ → inj₁ refl) , (λ _ → tt)) ,
  raw0-Nested (G.suc a*)

M* L* : LF
M* = read0 (nrm ω′)
L* = suc M*

r* : Pre K₂ω
r* = rᴺ a*

r*-level : lev K₂ω r* ≡ L*
r*-level = refl

M*-lim : M* ≡ lim (λ n → read0 (psum (λ _ → one) n))
M*-lim = refl

cᶜ : (ℕ → Bool) → R
cᶜ α = one +ʳ dense α

kᶜ : (ℕ → Bool) → LF
kᶜ α = read0 (nrm (cᶜ α))

probe-root : ∀ α → Σ (Pre K₂ω) λ r → (lev K₂ω r ≡ kᶜ α) ×
  Σ (Low K₂ω r) λ c → Σ RΩ λ t → Σ ((ζ : Low K₂ω r) → .(GdL K₂ω r c ζ) → RΩ) λ g →
  B₁ (coordᴸ α) ≡ G.lc r c t g
probe-root α = rᴺ (cᶜ α) , refl , _ , _ , _ , refl
```

## 2 链上的路径

前提只有一处依赖折叠：根上的第 1 个内部链点 `1 + y`，`y` 是第 0 层折叠在起点那一支上的输出，最左叶是 1。
然后：`B₂ 2` 的根在 `r₁` 上 (层号 1)，它的推进问 "目标在 `r₁`" 的折叠；沿保留结点的下界那一支走到 `N₂`；`N₂` 的根 (层号 0) 在目标层 1 之下，保留，各支都问到；
其中第 `suc a*` 支的根 `r*` 在目标之上，它的推进问 "目标在 `r*`" 的折叠；再沿保留结点走到 `P₁`，`P₁` 的根保留，各支都问到。

```agda
module Path (Out : RΩ → R → Set) (y : R) (out : Out (B₂ one) y) (ly : LeftOne y)
  (e₁ : Gd zero raw1 (plus zero one y)) where
  open Asked (pointsᴺ 2) Out

  to-two : ∀ {z} → LeftOne z → Ask⁰ (B₂ (plus zero one z)) → Ask⁰ (B₂ two)
  to-two lo-one p = p
  to-two lo-top p = p
  to-two (lo-lim l) p = to-two l (z-lim p 0)

  a-two : Ask⁰ (B₂ two)
  a-two = to-two ly (z-next z-start s₀ y out e₁)

  a₁₀ : At (suc zero) zero
  a₁₀ = inj₁ tt , refl

  a-own : Ask r₁ (C₃ (plusΩ (Gκ one) (keepAll (suc zero) (νᴺ one) G.top)))
  a-own = z-own a-two (inj₁ refl , tt , tt)

  thru₃ : ∀ X → Ask r₁ (C₃ (topᴬ X)) → Ask r₁ (C₃ X)
  thru₃ X p = o-lim (o-keep (o-lim (o-keep p a₁₀ raw1 s₀) 0) a₁₀ raw1 s₀) 0

  a-one : Ask r₁ (C₃ (Gκ one))
  a-one = thru₃ (Gκ one) (o-lim (o-keep a-own a₁₀ raw1 s₀) 0)

  a-t₀ : Ask r₁ (C₃ t₀)
  a-t₀ = thru₃ t₀ (o-lim (o-keep a-one a₁₀ raw1 s₀) 0)

  a-N₂ : Ask r₁ N₂
  a-N₂ = o-lim (o-keep (o-lim (o-keep (o-lim (o-keep a-t₀ a₁₀ raw1 s₀) 0)
    a₁₀ raw1 s₀) 0) a₁₀ raw1 s₀) 0

  -- N₂ 的根保留: 各支对一切带守卫的坐标都被问到.
  a-all : ∀ η (e : Gd zero raw1 η) → Ask r₁ (plusΩ P₁ (Gκ η))
  a-all η e = o-keep a-N₂ a₁₀ η e

  above* : At L* (suc zero)
  above* = inj₂ (1 , inj₂ (inj₁ tt)) , refl

  b-own : Ask r* (plusΩ P₁ (plusΩ (Gκ a*) (keepAll L* (νᴺ a*) G.top)))
  b-own = o-own (a-all (G.suc a*) e*) above* (inj₁ refl , tt , tt)

  az* : At L* zero
  az* = inj₂ (0 , inj₁ tt) , refl

  aM* : At L* M*
  aM* = inj₁ tt , refl

  sᵀ : Gd M* G.top G.top
  sᵀ = inj₁ refl , tt , tt

  thru : ∀ X → Ask r* (plusΩ P₁ (topᴬ X)) → Ask r* (plusΩ P₁ X)
  thru X p = o-suc (o-keep (o-suc (o-keep p az* raw1 s₀)) az* raw1 s₀)

  b-a* : Ask r* (plusΩ P₁ (Gκ a*))
  b-a* = thru (Gκ a*)
    (o-lim (o-keep (o-lim (o-keep b-own aM* G.top sᵀ) 0) az* raw1 s₀) 0)

  b-ω : Ask r* (plusΩ P₁ (Gκ ω′))
  b-ω = thru (Gκ ω′)
    (o-lim (o-keep (o-lim (o-keep b-a* aM* G.top sᵀ) 0) az* raw1 s₀) 0)

  b-t₀ : Ask r* (plusΩ P₁ t₀)
  b-t₀ = thru t₀ (o-lim (o-keep (o-lim b-ω 0) az* raw1 s₀) 0)

  b-P₁ : Ask r* P₁
  b-P₁ = o-suc (o-keep (o-suc (o-keep (o-lim (o-keep b-t₀ az* raw1 s₀) 0)
    az* raw1 s₀)) az* raw1 s₀)

  -- P₁ 的根保留: 各支对一切带守卫的坐标都被问到.
  b-all : ∀ η (e : Gd zero raw1 η) → Ask r* (B₁ η)
  b-all η e = o-keep b-P₁ az* η e

  probe : ∀ α → Ask r* (B₁ (coordᴸ α))
  probe α = b-all (coordᴸ α) (coordᴸ-guard α)
```

目标层 1 上不碰墙：位置上的层号只有 0，看头就能判定。

```agda
r₁-dec : ∀ k → At (lev K₂ω r₁) k ⊎ (At (lev K₂ω r₁) k → ⊥)
r₁-dec = at-one-dec
```

## 3 保留行的最弱联系，与它推出的判定

`HonestAt q y ξ`：`Honest` 在根上的内容，输出写成 `y`。`KeepRowAt q g`：目标在 `q`，被折的是根槽位上以 `g` 为分支的结点；
保留结点的各支 `branch η e` 相对于原来的各支 `g η e` 派发完全且不多保留。记录不写保留结点怎样装进输出，也不含折叠律以外的东西。

```agda
HonestAt : ∀ q → Raw (lev K₂ω q) → RΩ → Set
HonestAt q y (G.lc r c t g) =
  (At (lev K₂ω q) (lev K₂ω r) → Kept (lev K₂ω q) (lev K₂ω r) y) ×
  ((At (lev K₂ω q) (lev K₂ω r) → ⊥) → IsLim y)
HonestAt q y G.zero = ⊤
HonestAt q y (G.suc a) = ⊤
HonestAt q y (G.lim f) = ⊤
HonestAt q y (G.em i T) = ⊤
HonestAt q y G.top = ⊤

record KeepRowAt (q : Pre K₂ω) (g : (η : R) → .(Gd zero raw1 η) → RΩ) : Set where
  field
    branch : (η : R) → .(Gd zero raw1 η) → Raw (lev K₂ω q)
    branch-honest : ∀ η (e : Gd zero raw1 η) → HonestAt q (branch η e) (g η e)

Weak : Set → Set
Weak A = (A → ⊥) ⊎ ((A → ⊥) → ⊥)

row→weak : KeepRowAt r* (λ η e → B₁ η) → ∀ α → Weak (At L* (kᶜ α))
row→weak K α =
  read-shape (branch (coordᴸ α) (coordᴸ-guard α))
    (proj₁ (branch-honest (coordᴸ α) (coordᴸ-guard α)))
    (proj₂ (branch-honest (coordᴸ α) (coordᴸ-guard α)))
  where open KeepRowAt K

honest→at : ∀ q (F : OwnFold q) ξ (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ) →
  Honest q F ξ → HonestAt q (F ξ l nb) ξ
honest→at q F (G.lc r c t g) l nb h = h l nb
honest→at q F G.zero l nb h = tt
honest→at q F (G.suc a) l nb h = tt
honest→at q F (G.lim f) l nb h = tt
honest→at q F (G.em i T) l nb h = tt
honest→at q F G.top l nb h = tt

B₁-lgl : ∀ η → Gd zero raw1 η → Lgl K₂ω (B₁ η)
B₁-lgl η e = plus-lgl G.top (Gκ η) tt (Gκ-legal η (proj₁ (proj₂ e)))

B₁-ns : ∀ η → Nested K₂ω (B₁ η)
B₁-ns η = plus-ns G.top (Gκ η) tt (Gκ-nested η)

module FromHonest (Out : RΩ → R → Set) (y : R) (out : Out (B₂ one) y) (ly : LeftOne y)
  (e₁ : Gd zero raw1 (plus zero one y))
  (F : ∀ q → OwnFold q)
  (hon : ∀ {q ξ} → Asked.Ask (pointsᴺ 2) Out q ξ → Honest q (F q) ξ) where
  open Path Out y out ly e₁

  honest→row : KeepRowAt r* (λ η e → B₁ η)
  honest→row = record
    { branch = λ η e → F r* (B₁ η) (B₁-lgl η e) (B₁-ns η)
    ; branch-honest = λ η e →
        honest→at r* (F r*) (B₁ η) (B₁-lgl η e) (B₁-ns η) (hon (b-all η e)) }

  honest→weak : ∀ α → Weak (At L* (kᶜ α))
  honest→weak = row→weak honest→row
```

## 4 在目标层 `suc M*` 的位置上，就是字面等于 `M*`

`suc M*` 的位置上的层号：根上是 `M*`，其余都是有限层号的读回，不是 ℕ 极限；`kᶜ α` 是 ℕ 极限。

```agda
Eqᴸ : (ℕ → Bool) → Set
Eqᴸ α = kᶜ α ≡ M*

num-not-lim : ∀ n (s : Pre (read0 (psum (λ _ → one) n))) {f} →
  lev (read0 (psum (λ _ → one) n)) s ≡ lim f → ⊥
num-not-lim zero (inj₁ _) ()
num-not-lim (suc n) (inj₁ _) ()
num-not-lim (suc zero) (inj₂ (inj₁ _)) ()
num-not-lim (suc (suc n)) (inj₂ (inj₁ _)) ()
num-not-lim (suc n) (inj₂ (inj₂ s)) e = num-not-lim n s e

at→eq : ∀ α → At L* (kᶜ α) → Eqᴸ α
at→eq α (inj₁ _ , e) = sym e
at→eq α (inj₂ (n , s) , e) = ⊥-elim (num-not-lim n s e)

eq→at : ∀ α → Eqᴸ α → At L* (kᶜ α)
eq→at α e = inj₁ tt , sym e

weak-map : ∀ {A B : Set} → (A → B) → (B → A) → Weak A → Weak B
weak-map f g (inj₁ no) = inj₁ (λ b → no (g b))
weak-map f g (inj₂ nn) = inj₂ (λ nb → nn (λ a → nb (f a)))

WeakEq : Set
WeakEq = ∀ α → Weak (Eqᴸ α)

row→weak-eq : KeepRowAt r* (λ η e → B₁ η) → WeakEq
row→weak-eq K α = weak-map (at→eq α) (eq→at α) (row→weak K α)

-- 合起来: 第 0 层折叠的图满足四行, 链点 1 + y 带守卫, 问到的对上 Honest 成立, 则 WeakEq.
chain→weak-eq : (Out : RΩ → R → Set) → Rows Out →
  (y : R) → Out (B₂ one) y → Gd zero raw1 (plus zero one y) →
  (F : ∀ q → OwnFold q) →
  (∀ {q ξ} → Asked.Ask (pointsᴺ 2) Out q ξ → Honest q (F q) ξ) → WeakEq
chain→weak-eq Out H y out e₁ F hon =
  row→weak-eq (FromHonest.honest→row Out y out (premise₂ H out) e₁ F hon)
```

`Eqᴸ α` 推出 `α` 全假，不用函数外延：两边逐项相等，对项数归纳，部分和也逐项相等。

```agda
no-fix : ∀ A → suc A ≡ A → ⊥
no-fix A e = no-same {i = suc A} (inj₁ tt , refl) e

predᴸ : LF → LF
predᴸ (suc x) = x
predᴸ zero = zero
predᴸ (lim f) = zero
predᴸ (lc k c w b t g) = zero

step₀ : ∀ b → read0 (nrm (one +ʳ flag b)) ≡ suc zero → b ≡ false
step₀ false e = refl
step₀ true ()

stepˢ : ∀ X b → read0 (X +ʳ G.suc (nrm (one +ʳ flag b))) ≡ read0 (X +ʳ G.suc one) → b ≡ false
stepˢ X false e = refl
stepˢ X true e = ⊥-elim (no-fix (suc (suc (read0 X))) e)

Uᶜ : (ℕ → Bool) → ℕ → R
Uᶜ α m = nrm (one +ʳ flag (seen α m))

term-eq : ∀ α → Eqᴸ α → ∀ j → read0 (psum (Uᶜ α) j) ≡ read0 (psum (λ _ → one) j)
term-eq α e j = cong (λ x → bodyᴸ x j) e

seen-all : ∀ α → Eqᴸ α → ∀ j →
  (seen α j ≡ false) × (psum (Uᶜ α) j ≡ psum (λ _ → one) j)
seen-all α e zero =
  step₀ (seen α 0) (term-eq α e 0) ,
  cong (λ b → nrm (one +ʳ flag b)) (step₀ (seen α 0) (term-eq α e 0))
seen-all α e (suc j) = sf , cong₂ (λ X b → X +ʳ G.suc (nrm (one +ʳ flag b))) pj sf
  where
  pj : psum (Uᶜ α) j ≡ psum (λ _ → one) j
  pj = proj₂ (seen-all α e j)
  sf : seen α (suc j) ≡ false
  sf = stepˢ (psum (λ _ → one) j) (seen α (suc j))
    (trans (cong (λ X → read0 (X +ʳ G.suc (Uᶜ α (suc j)))) (sym pj)) (term-eq α e (suc j)))

eq→false : ∀ α → Eqᴸ α → ∀ n → α n ≡ false
eq→false α e n = not-true (α n) (λ p →
  true≢false (trans (sym (seen-hit α n p)) (proj₁ (seen-all α e n))))

-- 不用函数外延能得到的一半: 不等, 或 α 全假. 另一半 (不等推出 α 不全假) 要函数外延.
weak-eq→half : WeakEq → ∀ α → (Eqᴸ α → ⊥) ⊎ (∀ n → α n ≡ false)
weak-eq→half w α with w α
... | inj₁ no = inj₁ no
... | inj₂ nn = inj₂ (λ n → not-true (α n) (λ p →
    nn (λ e → true≢false (trans (sym p) (eq→false α e n)))))
```

## 5 前提可满足

`Honest` 处处成立的折叠族在排中律的实例 `Locate` 下存在；四行、起点那一支上的输出与链点的守卫有实例 ([YiGenNegLeft](YiGenNegLeft.lagda.md) §4)。所以 §3、§4 的结论不是矛盾。

```agda
Fᵒ : Locate → ∀ q → OwnFold q
Fᵒ orc q (G.lc r c t g) l nb =
  placeᵒ (lev K₂ω q) (lev K₂ω r) (orc (lev K₂ω q) (lev K₂ω r))
Fᵒ orc q G.zero l nb = G.zero
Fᵒ orc q (G.suc a) l nb = G.zero
Fᵒ orc q (G.lim f) l nb = G.zero
Fᵒ orc q (G.em i T) l nb = G.zero
Fᵒ orc q G.top l nb = G.zero

oracle-honest : (orc : Locate) → ∀ q ξ → Honest q (Fᵒ orc q) ξ
oracle-honest orc q (G.lc r c t g) = λ l nb →
  placeᵒ-kept (lev K₂ω q) (lev K₂ω r) (orc (lev K₂ω q) (lev K₂ω r)) ,
  placeᵒ-lim (lev K₂ω q) (lev K₂ω r) (orc (lev K₂ω q) (lev K₂ω r))
oracle-honest orc q G.zero = tt
oracle-honest orc q (G.suc a) = tt
oracle-honest orc q (G.lim f) = tt
oracle-honest orc q (G.em i T) = tt
oracle-honest orc q G.top = tt

-- 一切前提在 Locate 下同时可满足 (第 0 层折叠的图取骨架的值 valˢ).
premises-model : Locate → WeakEq
premises-model orc =
  chain→weak-eq Outˢ rowsˢ yˢ outˢ guardˢ (Fᵒ orc) (λ {q} {ξ} p → oracle-honest orc q ξ)
```
