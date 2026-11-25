# YiDiag 验收：第 2 步结构不互模拟，机制是部分和；逐项的写法不合法

**验收文件，档位：编译定理 (否定) 与有限测试。** `no-γ₂ : ¬ (read (pt 2) ≅ D.γ 2)`：第 2 个链点与参照的 γ₂ 不结构互模拟，所以 "∀ n → read (pt n) ≅ D.γ n" 对这棵树不成立。
有限测试：沿同一条路径，被验收一侧是极限、参照是后继，把非零目标层的部分和换成逐项的变体 `Ψᵗ` 后也是后继。`no-termwise`：逐项的写法在层号 ω 上不合法 (现有的第一位置)。
不否定 C3 的 `⊑ᴵ` 形式，也不否定值上的持平。树在 [YiDiagTw3](YiDiagTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagAccNeg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
open import OCF.Lean.YiDiagFold
open import OCF.Lean.YiDiagTw3 using (R; F; pt; lv; ⌜_⌝)
open import OCF.Lean.YiDiagAcc using (read)
import OCF.Align.Level as L
import OCF.Align.Diagonal as Diag
import OCF.Align.Uniform as Un
open L using (_≅_)

module D = Diag.Diagonal Un.Uniform
```

## 1 第 2 个链点与参照不结构互模拟

逐项取极限的分量 (下标 1, 2, 2, 1, 1, 1, 0, 0)，到达一处：被验收一侧是 `lim`，参照是 `suc`。

```agda
li : ∀ {F G : ℕ → L.Ordᶜ L.zero} → L.lim F ≅ L.lim G → ∀ n → F n ≅ G n
li (L.l≅ h) = h

ls : ∀ {F : ℕ → L.Ordᶜ L.zero} {x : L.Ordᶜ L.zero} → ¬ (L.lim F ≅ L.suc x)
ls ()

no-γ₂ : ¬ (read (pt 2) ≅ D.γ 2)
no-γ₂ e = ls (li (li (li (li (li (li (li (li e 1) 2) 2) 1) 1) 1) 0) 0)
```

## 2 机制 (有限测试与行)

路径上第 5 个下标处，被验收一侧取的是层号 ω 上 `top` 折到目标层 ω 的部分和 (`psum-row`，`refl`)，第 1 项是 `h₀ + h₁`；参照逐项，是 `h₁`。
`h₀` 被加在底部，折到第 0 层后第 0 项是极限，参照的是 1。`Ψᵗ` 是把非零目标层的部分和换成逐项的变体 (不合法，见 §3)，只作测试。

```agda
ω₀ : R
ω₀ = mult zero G.top

psum-row : Ψ ⌜ ω₀ ⌝ (lv ω₀) (self ⌜ ω₀ ⌝) G.top ≡
  G.lim (psum ⌜ ω₀ ⌝ (λ n → Ψ ⌜ ω₀ ⌝ (lv (iter (plus zero G.top) G.zero n)) (λ r → self ⌜ ω₀ ⌝ (n , r)) G.top))
psum-row = refl

Ψᵗ : ∀ m {k} → Lv k → Ext m k → Raw k → Raw m
Ψᵗ m V x G.zero = G.top
Ψᵗ m V x (G.suc a) = mult m (Ψᵗ m V x a)
Ψᵗ m V x (G.lim f) = G.lim (λ n → Ψᵗ m V x (f n))
Ψᵗ m {k} V x (G.lc r g) =
  ΨN m k r (x r) (λ η → Ψᵗ m V x (g η)) (λ η → Ψᵗ (lev k r) V (cmp V r) (g η))
Ψᵗ m (vs V) x (G.em _ a) = Ψᵗ m V (λ r → x (inj₂ r)) a
Ψᵗ m (vl V) x (G.em n a) = Ψᵗ m (V n) (λ r → x (n , r)) a
Ψᵗ m v0 x G.top = mult m G.top
Ψᵗ m {suc k} (vs V) x G.top =
  Ψn m k (x (inj₁ tt)) (λ η → Ψᵗ m V (λ r → x (inj₂ r)) η) (λ η → Ψᵗ k V (self k) η)
Ψᵗ m (vl V) x G.top = G.lim (λ n → Ψᵗ m (V n) (λ r → x (n , r)) G.top)

ptᵗ : ℕ → R
ptᵗ = iter (λ η → Ψᵗ zero (lv η) (λ _ → tt) G.top) G.top

at : L.Ordᶜ L.zero → List ℕ → L.Ordᶜ L.zero
at (L.lim h) (n ∷ p) = at (h n) p
at x p = x

hd : L.Ordᶜ L.zero → ℕ
hd L.zero = 0
hd (L.suc _) = 1
hd (L.lim _) = 2
hd (L.limᵢ () _)
hd (L.up () _)

path : List ℕ
path = 1 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ []

test-ours : hd (at (read (pt 2)) path) ≡ 2
test-ours = refl

test-ref : hd (at (D.γ 2) path) ≡ 1
test-ref = refl

test-termwise : hd (at (read (ptᵗ 2)) path) ≡ 1
test-termwise = refl
```

## 3 逐项的写法不合法

层号 ω (`⌜ ωR ⌝`，合法的 `ωR` 的读回) 上，`top` 折到目标层 ω 自身、派发 `self` (各支保留在自己的槽位) 时，逐项的极限不合法：
第 1 项 (槽位 `(1, 根)` 上的零层结点) 不是第 2 项的第一位置。证法：第 2 项的一切第一位置都满足 `Ok` (槽位 `(1, 根)` 上的结点，`top` 支是后继)，第 1 项不满足。

```agda
finR : ℕ → R
finR zero = G.zero
finR (suc n) = G.suc (finR n)

ωR : R
ωR = G.lim finR

finR-lgl : ∀ n → Lgl zero (finR n)
finR-lgl zero = tt
finR-lgl (suc n) = finR-lgl n

ωR-lgl : Lgl zero ωR
ωR-lgl = (λ n → inj₂ (inj₁ refl)) , finR-lgl

K : LF
K = ⌜ ωR ⌝

termᵗ : ℕ → Raw K
termᵗ n = Ψ K (lv (finR n)) (λ r → self K (n , r)) G.top

IsSuc : Raw K → Set
IsSuc (G.suc _) = ⊤
IsSuc _ = ⊥

slot₁ : Pre K
slot₁ = 1 , inj₁ tt

data Ok : Raw K → Set where
  oz : Ok G.zero
  ot : Ok G.top
  os : ∀ {t} → Ok t → Ok (G.suc t)
  ol : ∀ {h} → (∀ n → Ok (h n)) → Ok (G.lim h)
  on : ∀ {r g} → IsSuc (g (Lay.tp (Lo K r))) ⊎ ¬ (r ≡ slot₁) → Ok (g (Lay.tp (Lo K r))) → Ok (G.lc r g)

T₁ : Raw K
T₁ = termᵗ 1

avoid : ∀ t → Ok t → ¬ Cp K T₁ t
avoid t (on (inj₁ ()) o) (inj₁ refl)
avoid t (on (inj₂ ne) o) (inj₁ refl) = ne refl
avoid (G.suc d) (os o) (inj₂ p) = avoid d o p
avoid (G.lim h) (ol o) (inj₂ (n , p)) = avoid (h n) (o n) p
avoid (G.lc r g) (on c o) (inj₂ p) = avoid (g (Lay.tp (Lo K r))) o p
avoid G.top ot (inj₂ ())

FarOK : (k : LF) → (Pre k → Set) → Set
FarOK zero F = ⊤
FarOK (suc zero) F = ⊤
FarOK (suc (suc k)) F = F (inj₁ tt) × FarOK (suc k) (λ r → F (inj₂ r))
FarOK (suc (lim f)) F = ⊥
FarOK (suc (lc k g)) F = ⊥
FarOK (lim f) F = ⊥
FarOK (lc k g) F = ⊥

addTop : ∀ k (B : Bld K k) (F : Pre k → Set) →
  (∀ r g → Ok (g (Lay.tp (Lo k r))) → IsSuc (g (Lay.tp (Lo k r))) ⊎ F r → Ok (B r g)) → FarOK k F →
  ∀ y → Ok y → Ok (add k B y G.top)
addTop zero B F hb fo y oy = os oy
addTop (suc zero) B F hb fo y oy = hb (inj₁ tt) _ (os oy) (inj₁ tt)
addTop (suc (suc k)) B F hb (f₁ , fo) y oy = hb (inj₁ tt) _
  (addTop (suc k) (λ r → B (inj₂ r)) (λ r → F (inj₂ r)) (λ r g o c → hb (inj₂ r) g o c) fo y oy) (inj₂ f₁)

deep : ∀ n (F : Pre ⌜ finR n ⌝ → Set) → (∀ r → F r) → FarOK ⌜ finR n ⌝ F
deep zero F h = tt
deep (suc zero) F h = tt
deep (suc (suc n)) F h = h (inj₁ tt) , deep (suc n) (λ r → F (inj₂ r)) (λ r → h (inj₂ r))

step-ok : ∀ i y → Ok y → Ok (add ⌜ finR i ⌝ (λ r → G.lc (i , r)) y G.top)
step-ok zero y oy = os oy
step-ok (suc zero) y oy = on (inj₁ tt) (os oy)
step-ok (suc (suc i)) y oy = addTop ⌜ finR (suc (suc i)) ⌝ (λ r → G.lc (suc (suc i) , r))
  (λ r → ¬ ((suc (suc i) , r) ≡ slot₁)) (λ r g o c → on c o)
  ((λ ()) , deep (suc i) _ (λ r ())) y oy

acc-ok : ∀ m → Ok (acc (λ i y → add ⌜ finR i ⌝ (λ r → G.lc (i , r)) y G.top) G.top m)
acc-ok zero = ot
acc-ok (suc m) = step-ok m _ (acc-ok m)

isSuc-plus : ∀ w → IsSuc w → IsSuc (plus K G.top w)
isSuc-plus (G.suc w) tt = tt

ok-plus : ∀ {z} → Ok z → Ok (plus K G.top z)
ok-plus oz = ot
ok-plus ot = ol (λ n → acc-ok (suc n))
ok-plus (os o) = os (ok-plus o)
ok-plus (ol o) = ol (λ n → ok-plus (o n))
ok-plus {G.lc r g} (on (inj₁ s) o) = on (inj₁ (isSuc-plus (g (Lay.tp (Lo K r))) s)) (ok-plus o)
ok-plus (on (inj₂ ne) o) = on (inj₂ ne) (ok-plus o)

ok-mult : Ok (mult K G.top)
ok-mult = ol go
  where
  go : ∀ n → Ok (iter (plus K G.top) G.zero n)
  go zero = oz
  go (suc n) = ok-plus (go n)

ok-term₂ : Ok (termᵗ 2)
ok-term₂ = on (inj₂ (λ ())) (on (inj₂ (λ ())) ok-mult)

no-termwise : ¬ Lgl K (G.lim termᵗ)
no-termwise (st , _) = avoid (termᵗ 2) ok-term₂ (st 1)
```
