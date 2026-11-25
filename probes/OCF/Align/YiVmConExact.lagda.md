# YiVmCon：保值的前驱嵌入与带证据的值单调

**验收文件，档位：编译定理与条件定理。** 新不变量 `XEmb`：前驱嵌入 `PEmb` 加上 "每个前驱的像与它值相等"。保值使左极限的拼接无需一致性前提 (`XEmb-limˡ`)；代价是后继要两边的顶值相等 (`XEmb-suc`)。
由此对两个带证据的定义域证 `VMᴸ` 与 `Crux`：`≼ˣ` (每一步后继都带顶的值相等) 与更宽的 `≼ᵖ` (只有在左极限之下的后继要带)；`VMᵖ`, `Cruxᵖ`, `embᵖ` 是无条件定理。§6 另记有公共字面上界时的结构证法 (`VMᵇ`, `Cruxᵇ`)。
一般的 `VMᴸ` 只是条件定理 `tri→vm`，前提 `Tri` (值序上的分裂) 推出 LPO (`YiVmConLPO`)。不否定 `VMᴸ`：`≼ᵖ` 不等于 `≼` 只说明这个定义域是真子域。实例见 `YiVmConInst`，链上的约化见 `YiVmConChain`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmConExact where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
import OCF.Align.Level as L
open L using (Ordᴵ; Ordᶜ; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; _<ᴵ_; via; forget; HS; toLevel)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; s≼s⁻; ≼lim⁻; ≅→≼; ⊑→≼)
open import OCF.Align.BTBOFullLe using (⊑≅)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-limʳ; PEmb-limˡ; PEmb-suc)
open import OCF.Align.YiMonoVM using (VMᴸ; Crux; EmbV; embV→vm; crux→vm)
```

## 1 层号的值

`V` 把层号读回第 0 层的树。字面前驱的值严格更小 (`V-≺`)，第 0 层的值序无自反 (`irr`)；于是同一层号下两个值相等的前驱 `≅ᴵ` (`≈→≅`, 用有界三歧 `<ᴵ-dec` 排除另两支)。

```agda
V : Ordᴵ → Ordᶜ L.zero
V = forget

V-≅ : ∀ {a b} → a ≅ᴵ b → V a ≼ V b
V-≅ L.z≅     = z≼
V-≅ (L.s≅ e) = s≼s (V-≅ e)
V-≅ (L.l≅ h) = l≼ (λ n → ≼l n (V-≅ (h n)))

V-< : ∀ {c a} → c <ᴵ a → L.suc (V c) ≼ V a
V-< L.zero      = s≼s (≼-refl _)
V-< (L.suc p)   = ≼-suc (V-< p)
V-< (L.lim n p) = ≼l n (V-< p)

V-≺ : ∀ {c a} → c ≺ᴵ a → L.suc (V c) ≼ V a
V-≺ (via e p) = ≼-trans (s≼s (V-≅ e)) (V-< p)

irr : ∀ (v : Ordᶜ L.zero) → ¬ (L.suc v ≼ v)
irr L.zero ()
irr (L.suc v) d = irr v (s≼s⁻ d)
irr (L.lim f) d with ≼lim⁻ d
... | n , d′ = irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) d′)
irr (L.limᵢ () f) d
irr (L.up () x) d

≈→≅ : ∀ {b c d} → c ≺ᴵ b → d ≺ᴵ b → V c ≼ V d → V d ≼ V c → c ≅ᴵ d
≈→≅ (via e p) (via e′ q) cd dc with L.<ᴵ-dec p q
... | inj₁ r = ⊥-elim (irr _ (≼-trans (V-≺ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e r) (L.≅ᴵ-sym e′))) dc))
... | inj₂ (inj₁ r) = ⊥-elim (irr _ (≼-trans (V-≺ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e′ r) (L.≅ᴵ-sym e))) cd))
... | inj₂ (inj₂ r) = L.≅ᴵ-trans e (L.≅ᴵ-trans r (L.≅ᴵ-sym e′))

Vt : ∀ x (h : HS x) → V (toLevel x h) ≼ x
Vt x h = ≅→≼ (L.forget-toLevel x h)

tV : ∀ x (h : HS x) → x ≼ V (toLevel x h)
tV x h = ≅→≼ (L.≅-sym (L.forget-toLevel x h))
```

## 2 保值嵌入 `XEmb`

```agda
record XEmb (a b : Ordᴵ) : Set where
  field
    P   : PEmb a b
    ex  : ∀ {c} (r : c ≺ᴵ a) → V (map P r) ≼ V c
    ex′ : ∀ {c} (r : c ≺ᴵ a) → V c ≼ V (map P r)
open XEmb

XEmb-⊑ : ∀ {a b} → a ⊑ᴵ b → XEmb a b
XEmb-⊑ k = record { P = PEmb-⊑ k ; ex = λ r → ≼-refl _ ; ex′ = λ r → ≼-refl _ }

XEmb-limʳ : ∀ {a f s} n → XEmb a (f n) → XEmb a (L.lim f s)
XEmb-limʳ n X = record { P = PEmb-limʳ n (P X) ; ex = ex X ; ex′ = ex′ X }

XEmb-sucʳ : ∀ {a b} → XEmb a b → XEmb a (L.suc b)
XEmb-sucʳ X = record { P = PEmb-∘ (P X) (PEmb-⊑ (L.Sim→⊑ᴵ L.suc)) ; ex = ex X ; ex′ = ex′ X }

XEmb-∘ : ∀ {a b c} → XEmb a b → XEmb b c → XEmb a c
XEmb-∘ X Y = record
  { P = PEmb-∘ (P X) (P Y)
  ; ex = λ r → ≼-trans (ex Y (bnd (P X) r)) (ex X r)
  ; ex′ = λ r → ≼-trans (ex′ X r) (ex′ Y (bnd (P X) r)) }
```

左极限：各项都保值，公共前驱的两个像值相等，又都在 `b` 之下，故 `≅ᴵ` (`≈→≅`)；`PEmb-limˡ` 的一致性前提由此得到，不必比较各项的推导。

```agda
XEmb-limˡ : ∀ {f s b} → (∀ n → XEmb (f n) b) → XEmb (L.lim f s) b
XEmb-limˡ {f} {s} {b} X = record { P = Q ; ex = e₁ ; ex′ = e₂ } where
  k : ∀ n m {c} (r : c ≺ᴵ f n) (t : c ≺ᴵ f m) → map (P (X n)) r ≅ᴵ map (P (X m)) t
  k n m r t = ≈→≅ (bnd (P (X n)) r) (bnd (P (X m)) t)
    (≼-trans (ex (X n) r) (ex′ (X m) t)) (≼-trans (ex (X m) t) (ex′ (X n) r))
  Q : PEmb (L.lim f s) b
  Q = PEmb-limˡ {s = s} (λ n → P (X n)) k
  e₁ : ∀ {c} (r : c ≺ᴵ L.lim f s) → V (map Q r) ≼ V c
  e₁ (via e (L.lim n q)) = ex (X n) (via e q)
  e₂ : ∀ {c} (r : c ≺ᴵ L.lim f s) → V c ≼ V (map Q r)
  e₂ (via e (L.lim n q)) = ex′ (X n) (via e q)

XEmb-suc : ∀ {a b} → XEmb a b → V a ≼ V b → V b ≼ V a → XEmb (L.suc a) (L.suc b)
XEmb-suc {a} {b} X ab ba = record { P = PEmb-suc (P X) ; ex = e₁ ; ex′ = e₂ } where
  e₁ : ∀ {c} (r : c ≺ᴵ L.suc a) → V (map (PEmb-suc (P X)) r) ≼ V c
  e₁ (via e L.zero)    = ≼-trans ba (V-≅ (L.≅ᴵ-sym e))
  e₁ (via e (L.suc q)) = ex X (via e q)
  e₂ : ∀ {c} (r : c ≺ᴵ L.suc a) → V c ≼ V (map (PEmb-suc (P X)) r)
  e₂ (via e L.zero)    = ≼-trans (V-≅ e) ab
  e₂ (via e (L.suc q)) = ex′ X (via e q)
```

## 3 两个定义域

`≼ˣ`：值序的推导，后继对后继 (`sˣ`) 要带顶的反向不等式 (于是顶值相等)，另有右侧后继的弱化 `wˣ`。`≼ᵖ`：后继对后继不带证据 (`sᵖ`)，只有左极限 (`lᵖ`) 要求各项属于 `≼ˣ`。

```agda
infix 4 _≼ˣ_ _≼ᵖ_

data _≼ˣ_ : Ordᶜ L.zero → Ordᶜ L.zero → Set where
  zˣ  : ∀ {b} → L.zero ≼ˣ b
  sˣ  : ∀ {a b} → a ≼ˣ b → b ≼ a → L.suc a ≼ˣ L.suc b
  wˣ  : ∀ {a b} → a ≼ˣ b → a ≼ˣ L.suc b
  ≼lˣ : ∀ {a g} n → a ≼ˣ g n → a ≼ˣ L.lim g
  lˣ  : ∀ {f b} → (∀ n → f n ≼ˣ b) → L.lim f ≼ˣ b

data _≼ᵖ_ : Ordᶜ L.zero → Ordᶜ L.zero → Set where
  zᵖ  : ∀ {b} → L.zero ≼ᵖ b
  sᵖ  : ∀ {a b} → a ≼ᵖ b → L.suc a ≼ᵖ L.suc b
  wᵖ  : ∀ {a b} → a ≼ᵖ b → a ≼ᵖ L.suc b
  ≼lᵖ : ∀ {a g} n → a ≼ᵖ g n → a ≼ᵖ L.lim g
  lᵖ  : ∀ {f b} → (∀ n → f n ≼ˣ b) → L.lim f ≼ᵖ b

ˣ→≼ : ∀ {a b} → a ≼ˣ b → a ≼ b
ˣ→≼ zˣ        = z≼
ˣ→≼ (sˣ d _)  = s≼s (ˣ→≼ d)
ˣ→≼ (wˣ d)    = ≼-suc (ˣ→≼ d)
ˣ→≼ (≼lˣ n d) = ≼l n (ˣ→≼ d)
ˣ→≼ (lˣ d)    = l≼ (λ n → ˣ→≼ (d n))

ˣ→ᵖ : ∀ {a b} → a ≼ˣ b → a ≼ᵖ b
ˣ→ᵖ zˣ        = zᵖ
ˣ→ᵖ (sˣ d _)  = sᵖ (ˣ→ᵖ d)
ˣ→ᵖ (wˣ d)    = wᵖ (ˣ→ᵖ d)
ˣ→ᵖ (≼lˣ n d) = ≼lᵖ n (ˣ→ᵖ d)
ˣ→ᵖ (lˣ d)    = lᵖ d

ᵖ→≼ : ∀ {a b} → a ≼ᵖ b → a ≼ b
ᵖ→≼ zᵖ        = z≼
ᵖ→≼ (sᵖ d)    = s≼s (ᵖ→≼ d)
ᵖ→≼ (wᵖ d)    = ≼-suc (ᵖ→≼ d)
ᵖ→≼ (≼lᵖ n d) = ≼l n (ᵖ→≼ d)
ᵖ→≼ (lᵖ d)    = l≼ (λ n → ˣ→≼ (d n))
```

`≼ˣ` 含自反与结构的前驱包含 (于是含 `HS` 的步进)。

```agda
reflˣ : ∀ x → x ≼ˣ x
reflˣ L.zero        = zˣ
reflˣ (L.suc a)     = sˣ (reflˣ a) (≼-refl a)
reflˣ (L.lim f)     = lˣ (λ n → ≼lˣ n (reflˣ (f n)))
reflˣ (L.limᵢ () f)
reflˣ (L.up () x)

≅→≼ˣ : ∀ {a b : Ordᶜ L.zero} → a L.≅ b → a ≼ˣ b
≅→≼ˣ L.z≅     = zˣ
≅→≼ˣ (L.s≅ e) = sˣ (≅→≼ˣ e) (≅→≼ (L.≅-sym e))
≅→≼ˣ (L.l≅ h) = lˣ (λ n → ≼lˣ n (≅→≼ˣ (h n)))
≅→≼ˣ (L.lᵢ≅ {p = ()} e h)
≅→≼ˣ (L.upˡ {r = ()} e)
≅→≼ˣ (L.upʳ {r = ()} e)

≺→sˣ : ∀ {c b : Ordᶜ L.zero} → c L.≺ b → L.suc c ≼ˣ b
≺→sˣ (L.≺z e)    = sˣ (≅→≼ˣ e) (≅→≼ (L.≅-sym e))
≺→sˣ (L.≺s h)    = wˣ (≺→sˣ h)
≺→sˣ (L.≺l n h)  = ≼lˣ n (≺→sˣ h)
≺→sˣ (L.≺i {p = ()} x ex h)
≺→sˣ (L.≺u {r = ()} h)

⊑→≼ˣ : ∀ (a : Ordᶜ L.zero) {b : Ordᶜ L.zero} → a L.⊑ b → a ≼ˣ b
⊑→≼ˣ L.zero        k = zˣ
⊑→≼ˣ (L.suc a)     k = ≺→sˣ (k (L.≺z (L.≅-refl⁰ a)))
⊑→≼ˣ (L.lim f)     k = lˣ (λ n → ⊑→≼ˣ (f n) (λ h → k (L.≺l n h)))
⊑→≼ˣ (L.limᵢ () f) k
⊑→≼ˣ (L.up () x)   k
```

## 4 定义域上的值单调

```agda
embˣ : ∀ x (hx : HS x) y (hy : HS y) → x ≼ˣ y → XEmb (toLevel x hx) (toLevel y hy)
embˣ _ hx y hy zˣ = XEmb-⊑ L.z⊑
embˣ (L.suc a) hx (L.suc b) hy (sˣ d e) =
  XEmb-suc (embˣ a (L.hs⁻ hx) b (L.hs⁻ hy) d)
    (≼-trans (Vt a (L.hs⁻ hx)) (≼-trans (ˣ→≼ d) (tV b (L.hs⁻ hy))))
    (≼-trans (Vt b (L.hs⁻ hy)) (≼-trans e (tV a (L.hs⁻ hx))))
embˣ x hx (L.suc b) hy (wˣ d) = XEmb-sucʳ (embˣ x hx b (L.hs⁻ hy) d)
embˣ x hx (L.lim g) hy (≼lˣ n d) = XEmb-limʳ n (embˣ x hx (g n) (L.hl₁ hy n) d)
embˣ (L.lim f) hx y hy (lˣ d) = XEmb-limˡ (λ n → embˣ (f n) (L.hl₁ hx n) y hy (d n))

embᵖ : ∀ x (hx : HS x) y (hy : HS y) → x ≼ᵖ y → PEmb (toLevel x hx) (toLevel y hy)
embᵖ _ hx y hy zᵖ = PEmb-⊑ L.z⊑
embᵖ (L.suc a) hx (L.suc b) hy (sᵖ d) = PEmb-suc (embᵖ a (L.hs⁻ hx) b (L.hs⁻ hy) d)
embᵖ x hx (L.suc b) hy (wᵖ d) = PEmb-∘ (embᵖ x hx b (L.hs⁻ hy) d) (PEmb-⊑ (L.Sim→⊑ᴵ L.suc))
embᵖ x hx (L.lim g) hy (≼lᵖ n d) = PEmb-limʳ n (embᵖ x hx (g n) (L.hl₁ hy n) d)
embᵖ (L.lim f) hx y hy (lᵖ d) = P (XEmb-limˡ (λ n → embˣ (f n) (L.hl₁ hx n) y hy (d n)))

VMᵖ : ∀ (x : Ordᶜ L.zero) (hx : HS x) (y : Ordᶜ L.zero) (hy : HS y) → x ≼ᵖ y →
  L.ψ⁰ (L.Ω (toLevel x hx)) ≼ L.ψ⁰ (L.Ω (toLevel y hy))
VMᵖ x hx y hy d = Ψ-emb (embᵖ x hx y hy d)

Cruxᵖ : ∀ (x : Ordᶜ L.zero) (hx : HS x) (y : Ordᶜ L.zero) (hy : HS y) → x ≼ᵖ y →
  L.ψ⁰ (L.Ω (L.suc (toLevel x hx))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel y hy)))
Cruxᵖ x hx y hy d = Ψ-emb (PEmb-suc (embᵖ x hx y hy d))
```

## 5 一般情形的约化

`Cplᵖ`：每个值序推导都能改写进 `≼ᵖ`。`Tri`：值序上的分裂，`a ≼ b` 时要么顶值相等，要么严格。`Tri` 推出 `≼ˣ` 的完备性，对 (y, x) 字典序递归。

```agda
Cplᵖ : Set
Cplᵖ = ∀ (x y : Ordᶜ L.zero) → x ≼ y → x ≼ᵖ y

cpl→embV : Cplᵖ → EmbV
cpl→embV c x hx y hy d = embᵖ x hx y hy (c x y d)

cpl→vm : Cplᵖ → VMᴸ
cpl→vm c = embV→vm (cpl→embV c)

cpl→crux : Cplᵖ → Crux
cpl→crux c x hx y hy d = Cruxᵖ x hx y hy (c x y d)

Tri : Set
Tri = ∀ (a b : Ordᶜ L.zero) → a ≼ b → b ≼ a ⊎ L.suc a ≼ b

tri→cplˣ : Tri → ∀ (x y : Ordᶜ L.zero) → x ≼ y → x ≼ˣ y
tri→cplˣ t L.zero y d = zˣ
tri→cplˣ t (L.lim f) y d = lˣ (λ n → tri→cplˣ t (f n) y (≼-trans (≼l n (≼-refl (f n))) d))
tri→cplˣ t (L.suc a) L.zero ()
tri→cplˣ t (L.suc a) (L.suc b) d with t a b (s≼s⁻ d)
... | inj₁ e = sˣ (tri→cplˣ t a b (s≼s⁻ d)) e
... | inj₂ e = wˣ (tri→cplˣ t (L.suc a) b e)
tri→cplˣ t (L.suc a) (L.lim g) d with ≼lim⁻ d
... | n , e = ≼lˣ n (tri→cplˣ t (L.suc a) (g n) e)
tri→cplˣ t (L.suc a) (L.limᵢ () f) d
tri→cplˣ t (L.suc a) (L.up () x) d
tri→cplˣ t (L.limᵢ () f) y d
tri→cplˣ t (L.up () x) y d

tri→vm : Tri → VMᴸ
tri→vm t = cpl→vm (λ x y d → ˣ→ᵖ (tri→cplˣ t x y d))
```

## 6 有公共字面上界时

两个层号都是同一个 `ℓ` 的字面前驱时，有界三歧加值序排除 `b ≺ a`，剩下的两支都给结构可比，`Ψ⁰-mono` 直接给出 `VMᴸ` 与 `Crux` 的结论。这就是结构证法的定义域；参照对角链与链点的层号不在其中 (`YiMonoBreak.no-L`)。

```agda
cmpᵇ : ∀ {a b ℓ} → a ≺ᴵ ℓ → b ≺ᴵ ℓ → V a ≼ V b → a ≺ᴵ b ⊎ a ≅ᴵ b
cmpᵇ (via e p) (via e′ q) ab with L.<ᴵ-dec p q
... | inj₁ r = inj₁ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e r) (L.≅ᴵ-sym e′))
... | inj₂ (inj₁ r) = ⊥-elim (irr _ (≼-trans (V-≺ (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ e′ r) (L.≅ᴵ-sym e))) ab))
... | inj₂ (inj₂ r) = inj₂ (L.≅ᴵ-trans e (L.≅ᴵ-trans r (L.≅ᴵ-sym e′)))

⊑ᵇ : ∀ {a b} → a ≺ᴵ b ⊎ a ≅ᴵ b → a ⊑ᴵ b
⊑ᵇ (inj₁ (via e p)) = L.⊑ᴵ-trans (⊑≅ L.⊑ᴵ-refl e) (L.Sim→⊑ᴵ (λ q → L.<ᴵ-trans q p))
⊑ᵇ (inj₂ e)         = ⊑≅ L.⊑ᴵ-refl e

s⊑ᵇ : ∀ {a b} → a ≺ᴵ b ⊎ a ≅ᴵ b → L.suc a ⊑ᴵ L.suc b
s⊑ᵇ (inj₁ (via e p)) = L.s⊑ e (L.suc p)
s⊑ᵇ (inj₂ e)         = L.s⊑ e L.zero

VMᵇ : ∀ (x : Ordᶜ L.zero) (hx : HS x) (y : Ordᶜ L.zero) (hy : HS y) {ℓ} →
  toLevel x hx ≺ᴵ ℓ → toLevel y hy ≺ᴵ ℓ → x ≼ y →
  L.ψ⁰ (L.Ω (toLevel x hx)) ≼ L.ψ⁰ (L.Ω (toLevel y hy))
VMᵇ x hx y hy rx ry d =
  ⊑→≼ _ (L.Ψ⁰-mono (⊑ᵇ (cmpᵇ rx ry (≼-trans (Vt x hx) (≼-trans d (tV y hy))))))

Cruxᵇ : ∀ (x : Ordᶜ L.zero) (hx : HS x) (y : Ordᶜ L.zero) (hy : HS y) {ℓ} →
  toLevel x hx ≺ᴵ ℓ → toLevel y hy ≺ᴵ ℓ → x ≼ y →
  L.ψ⁰ (L.Ω (L.suc (toLevel x hx))) ≼ L.ψ⁰ (L.Ω (L.suc (toLevel y hy)))
Cruxᵇ x hx y hy rx ry d =
  ⊑→≼ _ (L.Ψ⁰-mono (s⊑ᵇ (cmpᵇ rx ry (≼-trans (Vt x hx) (≼-trans d (tV y hy))))))
```
