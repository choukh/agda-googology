# YiSuc 吸收：第 1 层参照上 Ω₁ 被 ψ₁ 的输出吸收，压平的严格单调

**验收文件，档位：编译定理。** `refabs : Pos a → Two (ψ⁰ (F₁ (read a))) (ψ⁰ (Ω₁ + F₁ (read a)))` (a 的各个 ℕ 极限支都 ≥ 1，主线的链点都满足，`pos-chain`)；`strict : x ≺ x′ → flat (F₁ x) ≺ flat (F₁ x′)`。
办法：压平到第 0 层比较。`fb`：两个语境压平后两向，则接上同一个第 1 层的尾巴 (`𝒩`：由 Ω₁ 与形如 `W + … + up v` 的结点经和、后继、ℕ 极限生成) 后仍两向；结点处两边的链都不累加，只用 `+ˣ`, `ψ⁰ˣ`。只谈参照框架 (与主线的读回)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucAbs where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read)
import OCF.Align.Level as L
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; sˣ; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ˣ→≼; ⊑→≼ˣ)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ; +ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainFlat using (flat; ψ⁰-flat)
open import OCF.Lean.YiFlatObs using (flat-≅; HS-flat)
open import OCF.Lean.YiFlatWit using (W0; wz; wl; wi; wu; zz; W0-≅; addW)
open import OCF.Lean.YiUBRed using (Two)
open import OCF.Lean.YiSucLx using (T₁; F₁)
open import OCF.Lean.YiSucPar using (Ω₁; CtxR; ε; _▸_; plugR; pR-suc; pR-lim; pR-node; FU; ≅-≡; Two-sub;
  trans≡; selfF; goodF)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 语境的拼接与自互模拟

```agda
cat : CtxR → T₁ → CtxR → CtxR
cat D W ε = D ▸ W
cat D W (E ▸ A) = cat D W E ▸ A

pR-cat : ∀ X D W E Z → plugR X D (plugR W E Z) ≡ plugR X (cat D W E) Z
pR-cat X D W ε Z = refl
pR-cat X D W (E ▸ A) Z = pR-cat X D W E (A L.+ Z)

AllS : CtxR → Set
AllS ε = ⊤
AllS (D ▸ A) = AllS D × A L.≅ A

selfS : ∀ {X} D {Z Z′} → X L.≅ X → AllS D → Z L.≅ Z′ → plugR X D Z L.≅ plugR X D Z′
selfS ε sX a e = L.add-≅ sX e
selfS (D ▸ A) sX (a , sA) e = selfS D sX a (L.add-≅ sA e)

up≅ : ∀ (e : T₀) → L._≅_ {L.suc L.zero} {L.suc L.zero} (L.up L.zero e) (L.up L.zero e)
up≅ e = L.upˡ (L.upʳ (L.≅-refl⁰ e))

≅-≡ʳ : ∀ {a b c : T₀} → a L.≅ b → b ≡ c → a L.≅ c
≅-≡ʳ e refl = e

two-s : ∀ {a b : T₀} → Two a b → Two (L.suc a) (L.suc b)
two-s (p , q) = sˣ p (ˣ→≼ q) , sˣ q (ˣ→≼ p)
```

## 2 第 1 层的尾巴

```agda
data 𝒩 : T₁ → Set where
  nz : 𝒩 L.zero
  ns : ∀ {Z} → 𝒩 Z → 𝒩 (L.suc Z)
  nl : ∀ {F} → (∀ n → 𝒩 (F n)) → 𝒩 (L.lim F)
  nΩ : 𝒩 Ω₁
  nn : ∀ (g : T₀ → T₁) W E → W L.≅ W → AllS E → (∀ v → g v ≡ plugR W E (L.up L.zero v)) →
    𝒩 (plugR W E L.zero) → 𝒩 (L.limᵢ {i = L.zero} L.zero g)

n+ : ∀ {X} → 𝒩 X → X L.≅ X → ∀ {Z} → 𝒩 Z → 𝒩 (X L.+ Z)
n+ hX sX nz = hX
n+ hX sX (ns h) = ns (n+ hX sX h)
n+ hX sX (nl h) = nl (λ n → n+ hX sX (h n))
n+ {X} hX sX nΩ = nn (λ v → X L.+ L.up L.zero v) X ε sX tt (λ v → refl) hX
n+ {X} hX sX (nn g W E sW aE eq h) =
  nn (λ v → X L.+ g v) X (cat ε W E) sX (allS-cat aE)
    (λ v → trans≡ (cong (X L.+_) (eq v)) (pR-cat X ε W E (L.up L.zero v)))
    (subst 𝒩 (pR-cat X ε W E L.zero) (n+ hX sX h))
  where
  allS-cat : ∀ {E′} → AllS E′ → AllS (cat ε W E′)
  allS-cat {E′ = ε} a = tt , sW
  allS-cat {E′ = E′ ▸ A} (a , sA) = allS-cat a , sA

n-iter : ∀ {A} → 𝒩 A → A L.≅ A → ∀ k → 𝒩 (iterᴸ (A L.+_) L.zero k)
n-iter hA sA zero = nz
n-iter hA sA (suc k) = n+ hA sA (n-iter hA sA k)

nF : ∀ (y : T₀) → 𝒩 (F₁ y)
nF L.zero = nΩ
nF (L.suc y) = nl (n-iter (nF y) (selfF y))
nF (L.lim f) = nl (λ n → nF (f n))
nF (L.limᵢ () g)
nF (L.up () y)
```

## 3 换语境

`NodeFlat`：两个层号 0 的结点，分支压平后是 `B + e` 与 `B′ + e`，`B`, `B′` 两向，则两个结点压平后两向 (两条链都不累加)。

```agda
module NodeFlat (g g′ : T₀ → T₁) (B B′ : T₀) (hB : Two B B′)
  (lgE : ∀ e → flat (g e) L.≅ (B L.+ e)) (lgE′ : ∀ e → flat (g′ e) L.≅ (B′ L.+ e))
  (sg : ∀ e → g e L.≅ g e) (sg′ : ∀ e → g′ e L.≅ g′ e) where

  step : (T₀ → T₁) → T₀ → T₀
  step h x = L.ψ {i = L.zero} {k = L.suc L.zero} {ℓ = L.suc L.zero} L.zero (λ r → r) (h x)

  ψ≅ : ∀ (h : T₀ → T₁) (C : T₀) → (∀ e → flat (h e) L.≅ (C L.+ e)) → (∀ e → h e L.≅ h e) →
    ∀ x → step h x L.≅ L.ψ⁰ (C L.+ x)
  ψ≅ h C lh sh x = L.≅-trans (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (sh x)))
    (L.≅-trans (ψ⁰-flat (h x)) (L.ψ⁰-≅ (lh x)))

  e e′ : ℕ → T₀
  e = iterᴸ (step g) (L.suc L.zero)
  e′ = iterᴸ (step g′) (L.suc L.zero)

  add2 : ∀ {x x′} → Two x x′ → Two (B L.+ x) (B′ L.+ x′)
  add2 (p , q) = +ˣ (proj₁ hB) (ˣ→≼ (proj₂ hB)) p , +ˣ (proj₂ hB) (ˣ→≼ (proj₁ hB)) q

  chain : ∀ n → Two (e n) (e′ n)
  chain zero = reflˣ _ , reflˣ _
  chain (suc n) =
    transˣ (≅→≼ˣ (ψ≅ g B lgE sg (e n)))
      (transˣ (ψ⁰ˣ (proj₁ (add2 (chain n)))) (≅→≼ˣ (L.≅-sym (ψ≅ g′ B′ lgE′ sg′ (e′ n))))) ,
    transˣ (≅→≼ˣ (ψ≅ g′ B′ lgE′ sg′ (e′ n)))
      (transˣ (ψ⁰ˣ (proj₂ (add2 (chain n)))) (≅→≼ˣ (L.≅-sym (ψ≅ g B lgE sg (e n)))))

  term : ∀ n → Two (flat (g (e n))) (flat (g′ (e′ n)))
  term n = transˣ (≅→≼ˣ (lgE (e n))) (transˣ (proj₁ (add2 (chain n))) (≅→≼ˣ (L.≅-sym (lgE′ (e′ n))))) ,
    transˣ (≅→≼ˣ (lgE′ (e′ n))) (transˣ (proj₂ (add2 (chain n))) (≅→≼ˣ (L.≅-sym (lgE (e n)))))

  result : Two (flat (L.limᵢ {i = L.zero} L.zero g)) (flat (L.limᵢ {i = L.zero} L.zero g′))
  result = lˣ (λ n → ≼lˣ n (proj₁ (term n))) , lˣ (λ n → ≼lˣ n (proj₂ (term n)))

fb : ∀ {X D X′ D′} → X L.≅ X → AllS D → X′ L.≅ X′ → AllS D′ → ∀ {Z} → 𝒩 Z →
  Two (flat (plugR X D L.zero)) (flat (plugR X′ D′ L.zero)) → Two (flat (plugR X D Z)) (flat (plugR X′ D′ Z))
fb sX aD sX′ aD′ nz h = h
fb {X} {D} {X′} {D′} sX aD sX′ aD′ (ns {Z} n) h =
  Two-sub (cong flat (sym (pR-suc X D Z))) (cong flat (sym (pR-suc X′ D′ Z))) (two-s (fb sX aD sX′ aD′ n h))
fb {X} {D} {X′} {D′} sX aD sX′ aD′ (nl {F} n) h =
  Two-sub (cong flat (sym (pR-lim X D F))) (cong flat (sym (pR-lim X′ D′ F)))
    (lˣ (λ k → ≼lˣ k (proj₁ (fb sX aD sX′ aD′ (n k) h))) , lˣ (λ k → ≼lˣ k (proj₂ (fb sX aD sX′ aD′ (n k) h))))
fb {X} {D} {X′} {D′} sX aD sX′ aD′ nΩ h =
  Two-sub (cong flat (sym (pR-node X D (L.up L.zero)))) (cong flat (sym (pR-node X′ D′ (L.up L.zero))))
    (NodeFlat.result (λ v → plugR X D (L.up L.zero v)) (λ v → plugR X′ D′ (L.up L.zero v)) _ _ h
      (FU X D) (FU X′ D′) (λ v → selfS D sX aD (up≅ v)) (λ v → selfS D′ sX′ aD′ (up≅ v)))
fb {X} {D} {X′} {D′} sX aD sX′ aD′ (nn g W E sW aE eq n) h =
  Two-sub (cong flat (sym (pR-node X D g))) (cong flat (sym (pR-node X′ D′ g)))
    (NodeFlat.result (λ v → plugR X D (g v)) (λ v → plugR X′ D′ (g v)) _ _ (fb sX aD sX′ aD′ n h)
      (lg X D) (lg X′ D′) (sl X D sX aD) (sl X′ D′ sX′ aD′))
  where
  lg : ∀ X₀ D₀ v → flat (plugR X₀ D₀ (g v)) L.≅ (flat (plugR X₀ D₀ (plugR W E L.zero)) L.+ v)
  lg X₀ D₀ v = ≅-≡ (cong flat (trans≡ (cong (plugR X₀ D₀) (eq v)) (pR-cat X₀ D₀ W E (L.up L.zero v))))
    (≅-≡ʳ (FU X₀ (cat D₀ W E) v) (cong (λ t → flat t L.+ v) (sym (pR-cat X₀ D₀ W E L.zero))))
  sl : ∀ X₀ D₀ → X₀ L.≅ X₀ → AllS D₀ → ∀ v → plugR X₀ D₀ (g v) L.≅ plugR X₀ D₀ (g v)
  sl X₀ D₀ s a v = selfS D₀ s a (subst (λ t → t L.≅ t) (sym (eq v)) (selfS E sW aE (up≅ v)))
```

## 4 Ω₁ 被吸收

`Pos a`：沿后继与 ℕ 极限，a 的每一支都 ≥ 1 (底部是 `top` 或 1)。

```agda
data Pos : R → Set where
  pt : Pos G.top
  p1 : Pos (G.suc G.zero)
  ps : ∀ {a} → Pos a → Pos (G.suc a)
  pl : ∀ {f} → (∀ n → Pos (f n)) → Pos (G.lim f)

pos-plus : ∀ {a} → Pos a → ∀ y → Pos (plus zero a y)
pos-plus p G.zero = p
pos-plus p (G.suc y) = ps (pos-plus p y)
pos-plus p (G.lim f) = pl (λ n → pos-plus p (f n))
pos-plus p (G.lc () g)
pos-plus p (G.em () a)
pos-plus p G.top = ps p

Ω≼F : ∀ {a} → Pos a → flat Ω₁ ≼ˣ flat (F₁ (read a))
Ω≼F pt = ≼lˣ 1 (reflˣ _)
Ω≼F p1 = ≼lˣ 1 (reflˣ _)
Ω≼F (ps p) = ≼lˣ 1 (Ω≼F p)
Ω≼F (pl p) = ≼lˣ 0 (Ω≼F (p 0))

flat-abs : ∀ {a} → Pos a → Two (flat (F₁ (read a))) (flat (Ω₁ L.+ F₁ (read a)))
flat-abs pt = one
  where
  one : Two (flat (F₁ (L.suc L.zero))) (flat (Ω₁ L.+ F₁ (L.suc L.zero)))
  one = lˣ (λ k → ≼lˣ k (⊑→≼ˣ _ (L.hl₂ (HS-flat (goodF G.top tt) (selfF (L.suc L.zero))) k))) ,
        lˣ (λ k → ≼lˣ (suc k) (reflˣ _))
flat-abs p1 = flat-abs pt
flat-abs {G.suc a} (ps p) =
  lˣ (λ { zero → zˣ ; (suc k) → ≼lˣ (suc k) (proj₁ (fbk k)) }) ,
  lˣ (λ { zero → ≼lˣ 1 (Ω≼F p) ; (suc k) → ≼lˣ (suc k) (proj₂ (fbk k)) })
  where
  A : T₁
  A = F₁ (read a)
  fbk : ∀ k → Two (flat (A L.+ iterᴸ (A L.+_) L.zero k)) (flat (Ω₁ L.+ (A L.+ iterᴸ (A L.+_) L.zero k)))
  fbk k = fb {D = ε} {D′ = ε ▸ A} (selfF (read a)) tt (L.Ω-refl _) (tt , selfF (read a))
    (n-iter (nF (read a)) (selfF (read a)) k) (flat-abs p)
flat-abs (pl p) = lˣ (λ n → ≼lˣ n (proj₁ (flat-abs (p n)))) , lˣ (λ n → ≼lˣ n (proj₂ (flat-abs (p n))))

refabs : ∀ {a} → Pos a → Two (L.ψ⁰ (F₁ (read a))) (L.ψ⁰ (Ω₁ L.+ F₁ (read a)))
refabs {a} p =
  transˣ (≅→≼ˣ (ψ⁰-flat (F₁ (read a))))
    (transˣ (ψ⁰ˣ (proj₁ (flat-abs p))) (≅→≼ˣ (L.≅-sym (ψ⁰-flat (Ω₁ L.+ F₁ (read a)))))) ,
  transˣ (≅→≼ˣ (ψ⁰-flat (Ω₁ L.+ F₁ (read a))))
    (transˣ (ψ⁰ˣ (proj₂ (flat-abs p))) (≅→≼ˣ (L.≅-sym (ψ⁰-flat (F₁ (read a))))))
```

## 5 压平的严格单调

```agda
W0F : ∀ (y : T₀) → W0 (F₁ y)
W0F L.zero = wi (λ z d → wu (W0-≅ (wz zz) (L.≅-sym d)))
W0F (L.suc y) = wl 1 (W0F y)
W0F (L.lim f) = wl 0 (W0F (f 0))
W0F (L.limᵢ () g)
W0F (L.up () y)

F≅ : ∀ {x b : T₀} → x L.≅ b → F₁ x L.≅ F₁ b
F≅ e = L.ψ-≅ (L.≅ᴵ-refl _) (L.tr⁻-≅ L.z≅ (L.≅-tr⁻ L.z≅ e))

strict : ∀ {x x′ : T₀} → x L.≺ x′ → flat (F₁ x) L.≺ flat (F₁ x′)
strict {x} (L.≺z {b = b} e) = L.≺l 2 (L.≺-respˡ (L.≅-sym (flat-≅ (F≅ e))) (addW {σ = λ q → q} (W0F b)))
strict (L.≺s d) = L.≺l 1 (strict d)
strict (L.≺l n d) = L.≺l n (strict d)
strict (L.≺i {p = ()} z ez d)
strict (L.≺u {r = ()} d)
```
