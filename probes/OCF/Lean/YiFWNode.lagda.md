# B7 候选的结点行：保持条件与实际派发反例
> 原型。新关系允许带同构的逐点结点行；旧 `kp` 配新关系却不自动单调，反例使用非零常值分支。
> 来源：`YiRC-RCE.Need.both` 的交换条件、`YiRWOps.cum` 与 `YiRWFold.node⁺` 的形状；只否定此组合，未否定 B7。
> 因而指定孩子行尚未接成全折叠；入口障碍为 `node-not-step`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFWNode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as O
import OCF.Lean.YiRWOps as R
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
open import OCF.Lean.YiFWBlock
open import OCF.Lean.YiFWCompat

both-kept : ∀ {S S′ : Sg} {p p′ : P S} (e : E S p p′)
  {q q′ : P S′} (e′ : E S′ q q′)
  (c : B S′ q → B S p) (c′ : B S′ q′ → B S p′)
  → (∀ z → c (cv S′ e′ z) ≡ cv S e (c′ z))
  → {g : B S p → T S′} {g′ : B S p′ → T S′}
  → (∀ z → Lt S′ (g (cv S e z)) (g′ z))
  → Lt S′ (Ω q (λ z → g (c z))) (Ω q′ (λ z → g′ (c′ z)))
both-kept {S} {S′} e e′ c c′ comm {g} {g′} h =
  ◃σ e′ λ z → subst (λ t → Lt S′ (g t) (g′ (c′ z))) (sym (comm z)) (h (c′ z))

-- 对指定孩子坐标 y 的局部行：不附加回退尾巴，但仍须给出 H 与同构。
through : ∀ {S : Sg} → (β : T S) (p : P S) → (B S p → T S) → T S
through β p H = Ω p (λ z → β + H z)

through-low : ∀ {S : Sg} (β : T S) (p : P S) (H : B S p → T S)
  → Lt S zero (H (b₀ S p)) → Lt S β (through β p H)
through-low β p H nz = ◃t (+-mono β nz) ◃w

through-step : ∀ {S : Sg} (β : T S) {p q : P S} (e : E S p q)
  (H : B S p → T S) (H′ : B S q → T S)
  → (∀ z → Lt S (H (cv S e z)) (H′ z))
  → Lt S (through β p H) (through β q H′)
through-step β e H H′ h = ◃σ e (λ z → +-mono β (h z))

T⁺ : O.L → Set
T⁺ j = Σ (T (Sig j)) (Lt (Sig j) zero)

cum : ∀ {S : Sg} → (ℕ → T S) → ℕ → T S
cum G zero = G zero
cum G (suc n) = cum G n + G (suc n)

nextA : ∀ {S : Sg} (b : T S) → Lt S zero b → ∀ n → Lt S (R.iter (b +_) b n) (R.iter (b +_) b (suc n))
nextA b nb zero = +-mono b nb
nextA b nb (suc n) = +-mono b (nextA b nb n)

next⁺ : ∀ {j} → T⁺ j → T⁺ j
next⁺ (b , nb) = lim (R.iter (b +_) b) (nextA b nb) , ◃t nb (◃l 0)

node : ∀ {j X x₀} → F.Keep j X x₀ → (X → T⁺ j) → (X → X) → T⁺ j
node (just (q , c , e)) G step =
  Ω q (λ z → proj₁ (G (c z))) , ◃t (proj₂ (G (c (O.fromBr _ q O.zero)))) ◃w
node {x₀ = x₀} nothing G step =
  lim (cum (λ n → proj₁ (G (R.iter step x₀ n)))) (λ n → +-mono _ (proj₂ (G (R.iter step x₀ (suc n))))) ,
  ◃t (proj₂ (G x₀)) (◃l 0)

NoΩ : ∀ {S : Sg} → T S → Set
NoΩ zero = ⊤
NoΩ (suc x) = NoΩ x
NoΩ (lim f a) = ∀ n → NoΩ (f n)
NoΩ (Ω p g) = ⊥
NoΩ (up x c y e) = NoΩ x

NoΩ-down : ∀ {S : Sg} {x y : T S} → Lt S x y → NoΩ y → NoΩ x
NoΩ-down ◃s hy = hy
NoΩ-down (◃l n) hy = hy n
NoΩ-down ◃w ()
NoΩ-down (◃u x c y e) hy = hy
NoΩ-down (◃c x c d) hy = hy
NoΩ-down (◃t d e) hy = NoΩ-down d (NoΩ-down e hy)
NoΩ-down (◃σ e h) ()

NoΩ-plus : ∀ {S : Sg} (x y : T S) → NoΩ x → NoΩ y → NoΩ (x + y)
NoΩ-plus x zero hx hy = hx
NoΩ-plus x (suc y) hx hy = NoΩ-plus x y hx hy
NoΩ-plus x (lim f a) hx hy = λ n → NoΩ-plus x (f n) hx (hy n)
NoΩ-plus x (Ω p g) hx ()
NoΩ-plus x (up y c z e) hx hy = NoΩ-plus x y hx hy

NoΩ-cum : ∀ {S : Sg} (G : ℕ → T S) → (∀ n → NoΩ (G n)) → ∀ n → NoΩ (cum G n)
NoΩ-cum G h zero = h zero
NoΩ-cum G h (suc n) = NoΩ-plus (cum G n) (G (suc n)) (NoΩ-cum G h n) (h (suc n))

NoΩ-iter : ∀ {S : Sg} (b : T S) → NoΩ b → ∀ n → NoΩ (R.iter (b +_) b n)
NoΩ-iter b hb zero = hb
NoΩ-iter b hb (suc n) = NoΩ-plus b (R.iter (b +_) b n) hb (NoΩ-iter b hb n)

NoΩ-next : ∀ {j} (b : T⁺ j) → NoΩ (proj₁ b) → NoΩ (proj₁ (next⁺ b))
NoΩ-next (b , nb) hb = NoΩ-iter b hb

one : O.L
one = O.nd O.sS (λ _ → O.zero)

p : O.Pos one
p = inj₂ (tt , inj₁ tt)

parent : O.L
parent = O.nd (O.sΩ one) (λ _ → one)

ok-one : P.Ok one
ok-one = tt , λ _ → tt

ok-parent : P.Ok parent
ok-parent = (ok-one , (λ _ → P.self)) , λ _ → ok-one

w : one P.≤ parent
w = P.inc O.zero P.self

pi pc : O.Pos parent
pi = inj₁ (inj₂ p)
pc = inj₂ (O.zero , inj₂ p)

eq-pi-pc : E (Sig parent) pi pc
eq-pi-pc = refl , record
  { cv = λ x → x ; back = λ x → x
  ; cv-back = λ _ → refl ; back-cv = λ _ → refl
  ; first = refl ; forward = λ d → d ; backward = λ d → d }

kp-index : F.kp parent ok-parent pi w ≡ just (p , (λ x → x) , refl)
kp-index = refl

kp-child : F.kp parent ok-parent pc w ≡ nothing
kp-child = refl

source-step : Lt (Sig parent) (Ω pi (λ _ → zero)) (Ω pc (λ _ → suc zero))
source-step = ◃σ eq-pi-pc (λ _ → ◃s)

branch-output-step : Lt (Sig one) (suc zero) (proj₁ (next⁺ {one} (suc zero , ◃s)))
branch-output-step = ◃l 0

left right : T (Sig one)
left = proj₁ (node (F.kp parent ok-parent pi w) (λ _ → suc zero , ◃s) (λ x → x))
right = proj₁ (node (F.kp parent ok-parent pc w) (λ _ → next⁺ (suc zero , ◃s)) (λ x → x))

right-NoΩ : NoΩ right
right-NoΩ = NoΩ-cum (λ _ → proj₁ (next⁺ {one} (suc zero , ◃s))) (λ _ → NoΩ-next (suc zero , ◃s) tt)

node-not-step : Lt (Sig one) left right → ⊥
node-not-step d = NoΩ-down d right-NoΩ

record NodePres : Set where
  field
    preserve : (a b : O.Pos parent) (e : E (Sig parent) a b)
      (G : O.Br parent a → T⁺ one) (G′ : O.Br parent b → T⁺ one)
      (step : O.Br parent a → O.Br parent a) (step′ : O.Br parent b → O.Br parent b)
      → (∀ z → Lt (Sig one) (proj₁ (G (cv (Sig parent) e z))) (proj₁ (G′ z)))
      → Lt (Sig one)
          (proj₁ (node (F.kp parent ok-parent a w) G step))
          (proj₁ (node (F.kp parent ok-parent b w) G′ step′))

no-node-pres : NodePres → ⊥
no-node-pres pres = node-not-step (NodePres.preserve pres pi pc eq-pi-pc
  (λ _ → suc zero , ◃s) (λ _ → next⁺ (suc zero , ◃s))
  (λ x → x) (λ x → x) (λ _ → branch-output-step))

-- 构造侧的前提在同一组槽位与非零分支上有实例。
local-row-step : Lt (Sig flat)
  (through zero p₀ (λ _ → suc zero))
  (through zero p₁ (λ _ → suc (suc zero)))
local-row-step = through-step zero same-branches _ _ (λ _ → ◃s)
```
