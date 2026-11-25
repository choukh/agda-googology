# YiOver 参照一侧：加法、第 1 层折叠与好树

**验收文件，档位：编译定理 (引理)。** `+ₚ`, `ψ₁-mono`：加法与目标层 1 的折叠 `ψ₁` (即 `YiLvValBase.Ψ 1`) 保持 [YiOverRef](YiOverRef.lagda.md) 的 `≤ₚ`。`Gd`：结点的分支对下标单调、后继处至少加一、第 1 支不低于 1 (`SC`)，对 `ψ₁` 与加法封闭。
`step-γ`：累加一步 `X + ψ₁ X` 落在不累加的参照两步之内；`O2ref`：`Ω₁ + ψ₁ Ω₁ ≤ₚ ψ₁ Ω₁` (第 1 层的左加数在下标 ≥ 1 的分支上被吸收)。只谈第 1 层的参照树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOverOps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open import OCF.Lean.YiOverRef

𝟙₁ Ω₁ : T₁
𝟙₁ = L.suc L.zero
Ω₁ = L.Ω (L.suc L.zero)

ψ₁ : T₁ → T₁
ψ₁ = L.ψ {i = L.suc L.zero} {k = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ q → L.suc q)

Sim₀ Simₐ : Set
Sim₀ = L.Simᴵ L.zero (L.suc (L.suc L.zero))
Simₐ = L.Simᴵ L.zero (L.suc L.zero)

B : Sim₀ → T₀ → T₁
B σ = L.ψ {i = L.suc L.zero} {k = L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero σ

σ₂ : Sim₀
σ₂ q = L.suc (L.suc q)

tr⁻≈ : ∀ (y : T₀) → (L.tr⁻ L.z≅ y ≼ y) × (y ≼ L.tr⁻ L.z≅ y)
tr⁻≈ L.zero = z≼ , z≼
tr⁻≈ (L.suc y) = s≼s (proj₁ (tr⁻≈ y)) , s≼s (proj₂ (tr⁻≈ y))
tr⁻≈ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (tr⁻≈ (f n)))) , l≼ (λ n → ≼l n (proj₂ (tr⁻≈ (f n))))
tr⁻≈ (L.limᵢ () f)
tr⁻≈ (L.up () x)

z≤ : ∀ b → L.zero ≤ₚ b
z≤ L.zero = zz
z≤ (L.suc b) = ws (z≤ b)
z≤ (L.lim f) = ≤l 0 (z≤ (f 0))
z≤ (L.limᵢ L.zero g) = i1 (z≤ (g 𝟙))
z≤ (L.limᵢ (L.suc ()) g)
z≤ (L.up L.zero y) = fu fz z≼
```

## 1 加法

第 0 层的尾巴 (`up` 在加法里展开成第 0 层的树) 单独处理。

```agda
infl⁰ : ∀ {a a′} → a ≤ₚ a′ → ∀ {σ : Simₐ} (y : T₀) → a ≤ₚ L.add a′ σ y
infl⁰ p L.zero = p
infl⁰ p (L.suc y) = ws (infl⁰ p y)
infl⁰ p (L.lim f) = ≤l 0 (infl⁰ p (f 0))
infl⁰ p (L.limᵢ () f)
infl⁰ p (L.up () x)

add-mono⁰ : ∀ {a a′} → a ≤ₚ a′ → ∀ {σ σ′ : Simₐ} {x y : T₀} → x ≼ y → L.add a σ x ≤ₚ L.add a′ σ′ y
add-mono⁰ p {y = y} z≼ = infl⁰ p y
add-mono⁰ p (s≼s q) = ss (add-mono⁰ p q)
add-mono⁰ p (≼l n q) = ≤l n (add-mono⁰ p q)
add-mono⁰ p (l≼ h) = l≤ (λ n → add-mono⁰ p (h n))
add-mono⁰ p (≼i {p = ()} x ex q)
add-mono⁰ p (i≼ {p = ()} h)
add-mono⁰ p (≼u {r = ()} q)
add-mono⁰ p (u≼ {r = ()} q)

add-flat : ∀ {a a′} → a ≤ₚ a′ → ∀ {σ′ : Simₐ} {b : T₁} {y : T₀} → Flat b → b ≼ y → (a L.+ b) ≤ₚ L.add a′ σ′ y
add-flat p {y = y} fb z≼ = infl⁰ p y
add-flat p (fs fb) (s≼s q) = ss (add-flat p fb q)
add-flat p fb (≼l n q) = ≤l n (add-flat p fb q)
add-flat p (fl fb) (l≼ h) = l≤ (λ n → add-flat p (fb n) (h n))
add-flat p fb (≼i {p = ()} x ex q)
add-flat p () (i≼ h)
add-flat p fb (≼u {r = ()} q)
add-flat p fu (u≼ q) = add-mono⁰ p q

+ₚ : ∀ {a a′ b b′} → a ≤ₚ a′ → b ≤ₚ b′ → (a L.+ b) ≤ₚ (a′ L.+ b′)
+ₚ p zz = p
+ₚ p (ss q) = ss (+ₚ p q)
+ₚ p (ws q) = ws (+ₚ p q)
+ₚ p (≤l n q) = ≤l n (+ₚ p q)
+ₚ p (l≤ h) = l≤ (λ n → +ₚ p (h n))
+ₚ p (ii h) = ii (λ x y o r → +ₚ p (h x y o r))
+ₚ p (i1 q) = i1 (+ₚ p q)
+ₚ p (fu fb q) = add-flat p fb q

iterₚ : ∀ {A A′} → A ≤ₚ A′ → ∀ n → iterᴸ (A L.+_) L.zero n ≤ₚ iterᴸ (A′ L.+_) L.zero n
iterₚ p zero = zz
iterₚ p (suc n) = +ₚ p (iterₚ p n)
```

## 2 目标层 1 的折叠

```agda
Ω≤Ω : Ω₁ ≤ₚ Ω₁
Ω≤Ω = ii (λ x y o p → fu fu (u≼ p))

Ω≤B : ∀ (σ : Sim₀) (y : T₀) → Ω₁ ≤ₚ B σ y
Ω≤B σ L.zero = Ω≤Ω
Ω≤B σ (L.suc y) = ≤l 1 (Ω≤B σ y)
Ω≤B σ (L.lim f) = ≤l 0 (Ω≤B σ (f 0))
Ω≤B σ (L.limᵢ () f)
Ω≤B σ (L.up () x)

B-mono : ∀ {σ σ′ : Sim₀} {x y : T₀} → x ≼ y → B σ x ≤ₚ B σ′ y
B-mono {σ′ = σ′} {y = y} z≼ = Ω≤B σ′ y
B-mono (s≼s q) = l≤ (λ n → ≤l n (iterₚ (B-mono q) n))
B-mono (≼l n q) = ≤l n (B-mono q)
B-mono (l≼ h) = l≤ (λ n → B-mono (h n))
B-mono (≼i {p = ()} x ex q)
B-mono (i≼ {p = ()} h)
B-mono (≼u {r = ()} q)
B-mono (u≼ {r = ()} q)

B-flat : ∀ {σ′ : Sim₀} {a : T₁} {y : T₀} → Flat a → a ≼ y → ψ₁ a ≤ₚ B σ′ y
B-flat {σ′} {y = y} fa z≼ = Ω≤B σ′ y
B-flat (fs fa) (s≼s q) = l≤ (λ n → ≤l n (iterₚ (B-flat fa q) n))
B-flat fa (≼l n q) = ≤l n (B-flat fa q)
B-flat (fl fa) (l≼ h) = l≤ (λ n → B-flat (fa n) (h n))
B-flat fa (≼i {p = ()} x ex q)
B-flat () (i≼ h)
B-flat fa (≼u {r = ()} q)
B-flat fu (u≼ q) = B-mono q

ψ₁-mono : ∀ {a b} → a ≤ₚ b → ψ₁ a ≤ₚ ψ₁ b
ψ₁-mono zz = Ω≤Ω
ψ₁-mono (ss p) = l≤ (λ n → ≤l n (iterₚ (ψ₁-mono p) n))
ψ₁-mono (ws p) = ≤l 1 (ψ₁-mono p)
ψ₁-mono (≤l n p) = ≤l n (ψ₁-mono p)
ψ₁-mono (l≤ h) = l≤ (λ n → ψ₁-mono (h n))
ψ₁-mono (ii h) = ii (λ x y o p → ψ₁-mono (h (L.tr⁻ L.z≅ x) (L.tr⁻ L.z≅ y)
  (≼-trans o (proj₂ (tr⁻≈ x))) (≼-trans (proj₁ (tr⁻≈ x)) (≼-trans p (proj₂ (tr⁻≈ y))))))
ψ₁-mono (i1 p) = i1 (ψ₁-mono p)
ψ₁-mono (fu fa q) = B-flat fa q
```

## 3 好树

```agda
Mono¹ Dbl¹ Pos : (T₀ → T₁) → Set
Mono¹ f = ∀ x y → 𝟙 ≼ x → x ≼ y → f x ≤ₚ f y
Dbl¹ f = ∀ y → 𝟙 ≼ y → L.suc (f y) ≤ₚ f (L.suc y)
Pos f = 𝟙₁ ≤ₚ f 𝟙

record SC (f : T₀ → T₁) : Set where
  constructor sc
  field
    mo : Mono¹ f
    db : Dbl¹ f
    po : Pos f

data Gd : T₁ → Set where
  gz : Gd L.zero
  gs : ∀ {a} → Gd a → Gd (L.suc a)
  gl : ∀ {f : ℕ → T₁} → (∀ n → Gd (f n)) → Gd (L.lim f)
  gi : ∀ {f : T₀ → T₁} → SC f → (∀ x → 𝟙 ≼ x → Gd (f x)) → Gd (L.limᵢ L.zero f)
  gu : ∀ {y : T₀} → Gd (L.up L.zero y)

reflₚ : ∀ {a} → Gd a → a ≤ₚ a
reflₚ gz = zz
reflₚ (gs g) = ss (reflₚ g)
reflₚ (gl g) = l≤ (λ n → ≤l n (reflₚ (g n)))
reflₚ (gi s gb) = ii (SC.mo s)
reflₚ (gu {y}) = fu fu (u≼ (≼-refl y))

pos-Ω : 𝟙₁ ≤ₚ Ω₁
pos-Ω = i1 (fu (fs fz) (s≼s z≼))

pos-B : ∀ (σ : Sim₀) (y : T₀) → 𝟙₁ ≤ₚ B σ y
pos-B σ L.zero = pos-Ω
pos-B σ (L.suc y) = ≤l 1 (pos-B σ y)
pos-B σ (L.lim f) = ≤l 0 (pos-B σ (f 0))
pos-B σ (L.limᵢ () f)
pos-B σ (L.up () x)

pos-ψ₁ : ∀ X → 𝟙₁ ≤ₚ ψ₁ X
pos-ψ₁ L.zero = pos-Ω
pos-ψ₁ (L.suc X) = ≤l 1 (pos-ψ₁ X)
pos-ψ₁ (L.lim f) = ≤l 0 (pos-ψ₁ (f 0))
pos-ψ₁ (L.limᵢ L.zero f) = i1 (pos-ψ₁ (f 𝟙))
pos-ψ₁ (L.limᵢ (L.suc ()) f)
pos-ψ₁ (L.up L.zero y) = pos-B σ₂ y

pos-add⁰ : ∀ X {σ : Simₐ} {y : T₀} → 𝟙₁ ≼ y → 𝟙₁ ≤ₚ L.add X σ y
pos-add⁰ X (s≼s q) = ss (z≤ _)
pos-add⁰ X (≼l n q) = ≤l n (pos-add⁰ X q)
pos-add⁰ X (≼i {p = ()} x ex q)
pos-add⁰ X (≼u {r = ()} q)

pos-+ : ∀ X {b} → 𝟙₁ ≤ₚ b → 𝟙₁ ≤ₚ (X L.+ b)
pos-+ X (ss p) = ss (z≤ _)
pos-+ X (ws p) = ws (pos-+ X p)
pos-+ X (≤l n p) = ≤l n (pos-+ X p)
pos-+ X (i1 p) = i1 (pos-+ X p)
pos-+ X (fu fa q) = pos-add⁰ X q

suc≤ψ₁suc : ∀ Z → ψ₁ Z ≤ₚ ψ₁ Z → L.suc (ψ₁ Z) ≤ₚ ψ₁ (L.suc Z)
suc≤ψ₁suc Z r = ≤l 2 (+ₚ r (pos-ψ₁ Z))

SC-ψ₁ : ∀ {f} → SC f → SC (λ y → ψ₁ (f (L.tr⁻ L.z≅ y)))
SC-ψ₁ {f} s = sc mo′ db′ (pos-ψ₁ (f 𝟙)) where
  t : T₀ → T₀
  t = L.tr⁻ L.z≅
  mo′ : Mono¹ (λ y → ψ₁ (f (t y)))
  mo′ x y o p = ψ₁-mono (SC.mo s (t x) (t y) (≼-trans o (proj₂ (tr⁻≈ x)))
    (≼-trans (proj₁ (tr⁻≈ x)) (≼-trans p (proj₂ (tr⁻≈ y)))))
  db′ : Dbl¹ (λ y → ψ₁ (f (t y)))
  db′ y o = trans (suc≤ψ₁suc (f (t y)) (ψ₁-mono (SC.mo s (t y) (t y) o′ (≼-refl _))))
      (ψ₁-mono (SC.db s (t y) o′))
    where o′ = ≼-trans o (proj₂ (tr⁻≈ y))

SC-+ : ∀ {X f} → X ≤ₚ X → SC f → SC (λ y → X L.+ f y)
SC-+ {X} r s = sc (λ x y o p → +ₚ r (SC.mo s x y o p)) (λ y o → +ₚ r (SC.db s y o)) (pos-+ X (SC.po s))

SC-up : SC (L.up L.zero)
SC-up = sc (λ x y o p → fu fu (u≼ p)) (λ y o → fu (fs fu) (s≼s (u≼ (≼-refl y)))) (fu (fs fz) (s≼s z≼))

Gd-Ω : Gd Ω₁
Gd-Ω = gi SC-up (λ x o → gu)

Gd-add⁰ : ∀ {X} → Gd X → ∀ {σ : Simₐ} (y : T₀) → Gd (L.add X σ y)
Gd-add⁰ g L.zero = g
Gd-add⁰ g (L.suc y) = gs (Gd-add⁰ g y)
Gd-add⁰ g (L.lim f) = gl (λ n → Gd-add⁰ g (f n))
Gd-add⁰ g (L.limᵢ () f)
Gd-add⁰ g (L.up () x)

Gd-+ : ∀ {X Y} → Gd X → Gd Y → Gd (X L.+ Y)
Gd-+ gX gz = gX
Gd-+ gX (gs g) = gs (Gd-+ gX g)
Gd-+ gX (gl g) = gl (λ n → Gd-+ gX (g n))
Gd-+ gX (gi s gb) = gi (SC-+ (reflₚ gX) s) (λ x o → Gd-+ gX (gb x o))
Gd-+ gX (gu {y}) = Gd-add⁰ gX y

Gd-iter : ∀ {A} → Gd A → ∀ n → Gd (iterᴸ (A L.+_) L.zero n)
Gd-iter g zero = gz
Gd-iter g (suc n) = Gd-+ g (Gd-iter g n)

Gd-B : ∀ (σ : Sim₀) (y : T₀) → Gd (B σ y)
Gd-B σ L.zero = Gd-Ω
Gd-B σ (L.suc y) = gl (Gd-iter (Gd-B σ y))
Gd-B σ (L.lim f) = gl (λ n → Gd-B σ (f n))
Gd-B σ (L.limᵢ () f)
Gd-B σ (L.up () x)

Gd-ψ₁ : ∀ {X} → Gd X → Gd (ψ₁ X)
Gd-ψ₁ gz = Gd-Ω
Gd-ψ₁ (gs g) = gl (Gd-iter (Gd-ψ₁ g))
Gd-ψ₁ (gl g) = gl (λ n → Gd-ψ₁ (g n))
Gd-ψ₁ (gi s gb) = gi (SC-ψ₁ s) (λ x o → Gd-ψ₁ (gb (L.tr⁻ L.z≅ x) (≼-trans o (proj₂ (tr⁻≈ x)))))
Gd-ψ₁ (gu {y}) = Gd-B σ₂ y
```

## 4 累加与不累加的参照

`Inv X`：`suc X ≤ₚ ψ₁ X`。`step-γ`：`X ≤ₚ Y` 时累加一步落在 `ψ₁ (ψ₁ Y)` 之下 (经 `ψ₁ (suc Y)` 的第 2 项)。

```agda
Inv : T₁ → Set
Inv X = L.suc X ≤ₚ ψ₁ X

inv-Ω : Inv Ω₁
inv-Ω = i1 (≤l 2 (+ₚ Ω≤Ω pos-Ω))

inv-ψ₁ : ∀ {X} → Gd X → Inv X → Inv (ψ₁ X)
inv-ψ₁ {X} g v = trans (suc≤ψ₁suc X (reflₚ (Gd-ψ₁ g))) (ψ₁-mono v)

≤ψ₁ : ∀ {X} → Gd X → Inv X → X ≤ₚ ψ₁ X
≤ψ₁ g v = trans (ws (reflₚ g)) v

step-γ : ∀ {X Y} → Gd Y → Inv Y → X ≤ₚ Y → (X L.+ ψ₁ X) ≤ₚ ψ₁ (ψ₁ Y)
step-γ g v p = trans (≤l 2 (+ₚ (trans p (≤ψ₁ g v)) (ψ₁-mono p))) (ψ₁-mono v)
```

第 1 层的吸收，只对 `Ω₁` 一步：分支下标 ≥ 1 时 `Ω₁ + B x ≤ₚ B y`。

```agda
ΩΩ≤B : ∀ (σ : Sim₀) {y : T₀} → 𝟙 ≼ y → (Ω₁ L.+ Ω₁) ≤ₚ B σ y
ΩΩ≤B σ {L.suc y} (s≼s q) = ≤l 2 (+ₚ (Ω≤B σ y) (Ω≤B σ y))
ΩΩ≤B σ (≼l n q) = ≤l n (ΩΩ≤B σ q)
ΩΩ≤B σ (≼i {p = ()} x ex q)
ΩΩ≤B σ (≼u {r = ()} q)

s→1 : ∀ {a b : T₀} → L.suc a ≼ b → 𝟙 ≼ b
s→1 (s≼s q) = s≼s z≼
s→1 (≼l n q) = ≼l n (s→1 q)
s→1 (≼i {p = ()} x ex q)
s→1 (≼u {r = ()} q)

absB : ∀ {σ σ′ : Sim₀} (x : T₀) {y : T₀} → 𝟙 ≼ y → x ≼ y → (Ω₁ L.+ B σ x) ≤ₚ B σ′ y
absB {σ′ = σ′} L.zero o d = ΩΩ≤B σ′ o
absB {σ} {σ′} (L.suc x) o (s≼s {b = y} d) = l≤ (λ k → ≤l (suc k) (stp k))
  where
  stp : ∀ k → (Ω₁ L.+ iterᴸ (B σ x L.+_) L.zero k) ≤ₚ iterᴸ (B σ′ y L.+_) L.zero (suc k)
  stp zero = Ω≤B σ′ y
  stp (suc k) = +ₚ (Ω≤B σ′ y) (+ₚ (B-mono d) (iterₚ (B-mono d) k))
absB (L.suc x) o (≼l n d) = ≤l n (absB (L.suc x) (s→1 d) d)
absB (L.suc x) o (≼i {p = ()} x′ ex q)
absB (L.suc x) o (≼u {r = ()} q)
absB (L.lim f) o d = l≤ (λ n → absB (f n) o (≼-trans (≼l n (≼-refl (f n))) d))
absB (L.limᵢ () f) o d
absB (L.up () y) o d

O2ref : (Ω₁ L.+ ψ₁ Ω₁) ≤ₚ ψ₁ Ω₁
O2ref = ii (λ x y o p → absB (L.tr⁻ L.z≅ x)
  (≼-trans o (≼-trans p (proj₂ (tr⁻≈ y))))
  (≼-trans (proj₁ (tr⁻≈ x)) (≼-trans p (proj₂ (tr⁻≈ y)))))
```
