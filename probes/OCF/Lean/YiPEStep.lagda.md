# YiPE 一步：平移嵌入与链上一步的约化

**验收文件，档位：编译定理与条件定理。** 层号的左加 `⊕` 与平移嵌入 `PEmb-shift : PEmb b (x ⊕ b)`；读回的和 `toLevel (X + Y) ≅ᴵ toLevel X ⊕ toLevel Y` (`toLevel-+`)。
链上一步归约到两条：参照一侧 ψ⁰∘Ω 对嵌入的函子性 `FUNC`，同一层号上参照对主线折叠的结构下界 `KEY`；`emb-FK : FUNC → KEY → EmbTⁿ` (取 m = n)。`KEY` 在 m = 0 是定理 (`key₀`)；两条在 `Tri` 下成立 (`tri→FUNC`, `tri→KEY`；`Tri` 推出 LPO)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPEStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanFold using (fold)
open import OCF.Lean.YiLeanTw3 using (T₃; F; F-lgl; pts; obs; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (κ; HS-read; lower-read; chain-cum)
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
import OCF.Align.Level as L
open L using (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
import OCF.Align.Uniform as Un
open import OCF.Align.Value using (_≼_; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘)
open import OCF.Align.YiVmConExact using (_≼ᵖ_; ≼lˣ; lᵖ; embᵖ; embˣ; XEmb; Tri; tri→cplˣ)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ)
open import OCF.Lean.YiChainBase using (transˣ)
open import OCF.Lean.YiChainOne using (cc; Gc; module Phi)
open Phi using (PHI)
open import OCF.Lean.YiPEBase using (EmbTⁿ; btbo-embⁿ; btbo-emb⁺)
```

## 1 层号的左加与平移嵌入

`x ⊕ b` 把 `b` 的结构放在 `x` 之上；极限的步进由 `⊕-⊑` 现场给出 (与 `toLevel` 同样的互递归)。

```agda
infixl 6 _⊕_
_⊕_ : Ordᴵ → Ordᴵ → Ordᴵ
⊕-⊑ : ∀ x {a b} → a ⊑ᴵ b → (x ⊕ a) ⊑ᴵ (x ⊕ b)
⊕-≅ : ∀ x {a b} → a ≅ᴵ b → (x ⊕ a) ≅ᴵ (x ⊕ b)
⊕-< : ∀ x {c b} → c <ᴵ b → (x ⊕ c) <ᴵ (x ⊕ b)
⊑⊕ : ∀ x b → x ⊑ᴵ (x ⊕ b)

x ⊕ L.zero = x
x ⊕ L.suc b = L.suc (x ⊕ b)
x ⊕ L.lim f s = L.lim (λ n → x ⊕ f n) (λ n → ⊕-⊑ x (s n))

⊕-⊑ x {b = b} L.z⊑ = ⊑⊕ x b
⊕-⊑ x (L.s⊑ e q) = L.s⊑ (⊕-≅ x e) (⊕-< x q)
⊕-⊑ x (L.l⊑ h) = L.l⊑ (λ n → ⊕-⊑ x (h n))

⊕-≅ x L.z≅ = L.≅ᴵ-refl x
⊕-≅ x (L.s≅ e) = L.s≅ (⊕-≅ x e)
⊕-≅ x (L.l≅ h) = L.l≅ (λ n → ⊕-≅ x (h n))

⊕-< x L.zero = L.zero
⊕-< x (L.suc p) = L.suc (⊕-< x p)
⊕-< x (L.lim n p) = L.lim n (⊕-< x p)

⊑⊕ x L.zero = L.⊑ᴵ-refl
⊑⊕ x (L.suc b) = L.⊑ᴵ-trans (⊑⊕ x b) (L.Sim→⊑ᴵ L.suc)
⊑⊕ x (L.lim f s) = L.⊑ᴵ-trans (⊑⊕ x (f 0)) (L.Sim→⊑ᴵ (L.lim 0))

⊕-≺ : ∀ x {c b} → c ≺ᴵ b → (x ⊕ c) ≺ᴵ (x ⊕ b)
⊕-≺ x (via e p) = via (⊕-≅ x e) (⊕-< x p)

PEmb-shift : ∀ x b → PEmb b (x ⊕ b)
map (PEmb-shift x b) {c} r = x ⊕ c
bnd (PEmb-shift x b) r = ⊕-≺ x r
mono (PEmb-shift x b) r s lt = ⊕-≺ x lt
coh (PEmb-shift x b) r s e = ⊕-≅ x e
```

## 2 沿 `≅ᴵ` 搬嵌入；读回的和

```agda
PEmb-≅ʳ : ∀ {a b b′} → PEmb a b → b ≅ᴵ b′ → PEmb a b′
map (PEmb-≅ʳ P e) = map P
bnd (PEmb-≅ʳ P e) r = L.≺ᴵ-respʳ (bnd P r) e
mono (PEmb-≅ʳ P e) = mono P
coh (PEmb-≅ʳ P e) = coh P

PEmb-≅ˡ : ∀ {a a′ b} → a′ ≅ᴵ a → PEmb a b → PEmb a′ b
map (PEmb-≅ˡ e P) r = map P (L.≺ᴵ-respʳ r e)
bnd (PEmb-≅ˡ e P) r = bnd P (L.≺ᴵ-respʳ r e)
mono (PEmb-≅ˡ e P) r s lt = mono P (L.≺ᴵ-respʳ r e) (L.≺ᴵ-respʳ s e) lt
coh (PEmb-≅ˡ e P) r s d = coh P (L.≺ᴵ-respʳ r e) (L.≺ᴵ-respʳ s e) d

HS-≅ : ∀ {a b : L.Ordᶜ L.zero} → L.HS a → a L.≅ b → L.HS b
HS-≅ L.hz L.z≅ = L.hz
HS-≅ (L.hs h) (L.s≅ e) = L.hs (HS-≅ h e)
HS-≅ (L.hl h st) (L.l≅ k) =
  L.hl (λ n → HS-≅ (h n) (k n)) (λ n d → L.≺-respʳ (st n (L.≺-respʳ d (L.≅-sym (k n)))) (k (suc n)))
HS-≅ h (L.upʳ {r = ()} e)

toLevel-+ : ∀ (X Y : L.Ordᶜ L.zero) (hX : L.HS X) (hY : L.HS Y) (h : L.HS (X L.+ Y)) →
  L.toLevel (X L.+ Y) h ≅ᴵ (L.toLevel X hX ⊕ L.toLevel Y hY)
toLevel-+ X L.zero hX hY h = L.toLevel-≅ h hX (L.≅-refl⁰ X)
toLevel-+ X (L.suc y) hX hY h = L.s≅ (toLevel-+ X y hX (L.hs⁻ hY) (L.hs⁻ h))
toLevel-+ X (L.lim f) hX hY h = L.l≅ (λ n → toLevel-+ X (f n) hX (L.hl₁ hY n) (L.hl₁ h n))
toLevel-+ X (L.limᵢ () f) hX hY h
toLevel-+ X (L.up () x) hX hY h
```

## 3 链上一步

`L⁺ a` 是参照 ψ⁰(Ω_a) 读成的层号；`D.L (n+1)` 定义性地是 `L⁺ (D.L n)`。`Fκ m` 是链点 m 上主线折叠值读成的层号。

```agda
L⁺ : Ordᴵ → Ordᴵ
L⁺ a = L.toLevel (L.ψ⁰ (L.Ω a)) (Un.Uniform a)

Fκ : ℕ → Ordᴵ
Fκ m = L.toLevel (read (obs (pts m))) (HS-read (obs (pts m)) (F-lgl (co (pts m)) (lw (pts m))))

FUNC : Set
FUNC = ∀ {a b} → PEmb a b → PEmb (L⁺ a) (L⁺ b)

KEY : Set
KEY = ∀ m → PEmb (L⁺ (κ m)) (Fκ m)

shift-κ : ∀ m → PEmb (Fκ m) (κ (suc m))
shift-κ m =
  PEmb-≅ʳ (PEmb-≅ʳ (PEmb-shift (κ m) (Fκ m))
    (L.≅ᴵ-sym (toLevel-+ (read (co (pts m))) (read (obs (pts m))) _ _ hsum)))
    (L.toLevel-≅ hsum _ (L.≅-sym (chain-cum m)))
  where
  hsum : L.HS (read (co (pts m)) L.+ read (obs (pts m)))
  hsum = HS-≅ (HS-read (co (pts (suc m))) (lw (pts (suc m)))) (chain-cum m)

module FromFK (func : FUNC) (key : KEY) where
  emb : ∀ n → PEmb (D.L n) (κ n)
  emb zero = PEmb-⊑ L.⊑ᴵ-refl
  emb (suc n) = PEmb-∘ (func (emb n)) (PEmb-∘ (key n) (shift-κ n))

emb-FK : FUNC → KEY → EmbTⁿ
emb-FK func key n = n , FromFK.emb func key n

btbo-FK : FUNC → KEY → D.BTBOᴵ ≼ read T₃
btbo-FK func key = btbo-embⁿ (emb-FK func key)

btbo-FK⁺ : FUNC → KEY → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo-FK⁺ func key = btbo-emb⁺ (emb-FK func key)
```

## 4 前提的实例

`key₀`：链点 0 是 `top`，`F top` 的第 k 项是内层链点 cₖ 上的第 0 层折叠，经 `Gc` 与 `PHI`。`func-⊑`：结构可比时 `FUNC` 的结论。

```agda
key₀ : PEmb (L⁺ (κ 0)) (Fκ 0)
key₀ = embᵖ (D.γ 1) (D.cert 1) (read (obs (pts 0))) _
  (lᵖ (λ k → ≼lˣ k (transˣ (ψ⁰ˣ (Gc k)) (proj₁ (PHI (λ _ → fold) (cc k))))))

func-⊑ : ∀ {a b} → a ⊑ᴵ b → PEmb (L⁺ a) (L⁺ b)
func-⊑ {a} {b} k = PEmb-⊑ (L.toLevel-⊑ (Un.Uniform a) (Un.Uniform b) (L.Ψ⁰-mono k))

tri→FUNC : Tri → FUNC
tri→FUNC t {a} {b} P = XEmb.P (embˣ _ (Un.Uniform a) _ (Un.Uniform b) (tri→cplˣ t _ _ (Ψ-emb P)))

tri→KEY : Tri → KEY
tri→KEY t m = XEmb.P (embˣ _ (Un.Uniform (κ m)) _ _ (tri→cplˣ t _ _ (lower-read (co (pts m)) (lw (pts m)))))
```
