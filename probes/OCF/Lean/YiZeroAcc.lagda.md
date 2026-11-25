# YiZero 验收：链点的层号与参照对角线不结构可比

**验收文件，档位：编译定理 (否定与正对照)。** 判据 C2 不通过：`no-L : ∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)`，`κ m` 是第 `m` 个链点读成的层号。
机制：链点 ηₙ₊₁ = ηₙ + (任意树) 从 `top` 起，每个 ℕ 极限的第 0 项非零 (`NZ-add` 对加数没有任何要求，`nz-any`)，于是没有 ≅ᴵ ω 的字面前驱；与折叠的基本列无关。
正对照：ω 倍从零起之后折叠值里有字面的 ω+1 (`sω-F1`)，主线没有。块与闭项在 [YiZeroTw3](YiZeroTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroAcc where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import OCF.Lean.YiZeroCore
open import OCF.Lean.YiZeroFold
open import OCF.Lean.YiZeroLegal
open import OCF.Lean.YiZeroTw3
open Pt
import OCF.Align.Level as L
open L using (_<ᴵ_; _≅ᴵ_; _⊑ᴵ_)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiMonoBreak using (sω-L1; L-chain)
open import OCF.Align.YiVmConExact using (_≼ᵖ_; ˣ→ᵖ; reflˣ)
```

## 1 读回与层号 κ

```agda
read : R → L.Ordᶜ L.zero
read G.zero = L.zero
read (G.suc a) = L.suc (read a)
read (G.lim f) = L.lim (λ n → read (f n))
read (G.lc () g)
read (G.em () a)
read G.top = L.suc L.zero

cp⊑ : ∀ {a} b → Cp zero a b → read a L.⊑ read b
cp⊑ b (inj₁ refl) h = h
cp⊑ (G.suc b) (inj₂ p) h = L.≺s (cp⊑ b p h)
cp⊑ (G.lim f) (inj₂ (n , p)) h = L.≺l n (cp⊑ (f n) p h)
cp⊑ G.top (inj₂ refl) ()

HS-read : ∀ a → Lgl zero a → L.HS (read a)
HS-read G.zero l = L.hz
HS-read (G.suc a) l = L.hs (HS-read a l)
HS-read (G.lim f) (st , lf) = L.hl (λ n → HS-read (f n) (lf n)) (λ n → cp⊑ (f (suc n)) (st n))
HS-read G.top l = L.hs L.hz

κ : ℕ → L.Ordᴵ
κ m = L.toLevel (read (co (pts m))) (HS-read (co (pts m)) (lw (pts m)))
```

## 2 没有零起点的极限

`NZ a`：`a` 里每个 ℕ 极限的第 0 项非零。这样的树读成的层号，字面前驱都不 ≅ᴵ ω (ω 的第 0 项是零)。

```agda
NZ0 NZ : R → Set
NZ0 G.zero = ⊥
NZ0 (G.suc a) = ⊤
NZ0 (G.lim f) = ⊤
NZ0 (G.lc () g)
NZ0 (G.em () a)
NZ0 G.top = ⊤
NZ G.zero = ⊤
NZ (G.suc a) = NZ a
NZ (G.lim f) = NZ0 (f 0) × (∀ n → NZ (f n))
NZ (G.lc () g)
NZ (G.em () a)
NZ G.top = ⊤

not0 : ∀ a h → NZ0 a → ¬ (L.zero ≅ᴵ L.toLevel (read a) h)
not0 G.zero h () e
not0 (G.suc a) h z ()
not0 (G.lim f) h z ()
not0 (G.lc () g) h z e
not0 (G.em () a) h z e
not0 G.top h z ()

notω : ∀ a h → NZ a → ¬ (L.ωᴵ ≅ᴵ L.toLevel (read a) h)
notω G.zero h z ()
notω (G.suc a) h z ()
notω (G.lim f) h (z0 , z) (L.l≅ k) = not0 (f 0) (L.hl₁ h 0) z0 (k 0)
notω (G.lc () g) h z e
notω (G.em () a) h z e
notω G.top h z ()

noω : ∀ a h → NZ a → ∀ {c} → c <ᴵ L.toLevel (read a) h → ¬ (L.ωᴵ ≅ᴵ c)
noω G.zero h z ()
noω (G.suc a) h z L.zero = notω a (L.hs⁻ h) z
noω (G.suc a) h z (L.suc q) = noω a (L.hs⁻ h) z q
noω (G.lim f) h (z0 , z) (L.lim n q) = noω (f n) (L.hl₁ h n) (z n) q
noω (G.lc () g) h z q
noω (G.em () a) h z q
noω G.top h z L.zero ()
noω G.top h z (L.suc ())

no-sω : ∀ a h → NZ a → ¬ (L.suc L.ωᴵ ⊑ᴵ L.toLevel (read a) h)
no-sω a h z (L.s⊑ e q) = noω a h z q e
```

`NZ-add`：加数 `c` 任意 (不要合法，不看它是不是折叠值)。于是任何 "上一点放在叶上" 的链 (`nz-any`, 第 `i` 步加上 `s i η`) 都保持 `NZ`。

```agda
NZ0-add : ∀ x c → NZ0 x → NZ0 (plus zero x c)
NZ0-add x G.zero h = h
NZ0-add x (G.suc c) h = tt
NZ0-add x (G.lim f) h = tt
NZ0-add x (G.lc () g) h
NZ0-add x (G.em () a) h
NZ0-add x G.top h = tt

NZ-add : ∀ x c → NZ0 x → NZ x → NZ (plus zero x c)
NZ-add x G.zero h0 h = h
NZ-add x (G.suc c) h0 h = NZ-add x c h0 h
NZ-add x (G.lim f) h0 h = NZ0-add x (f 0) h0 , λ n → NZ-add x (f n) h0 h
NZ-add x (G.lc () g) h0 h
NZ-add x (G.em () a) h0 h
NZ-add x G.top h0 h = h

nz-any : ∀ (s : ℕ → R → R) n → NZ0 (acc (λ i η → plus zero η (s i η)) G.top n) × NZ (acc (λ i η → plus zero η (s i η)) G.top n)
nz-any s zero = tt , tt
nz-any s (suc n) = NZ0-add _ (s n _) (proj₁ (nz-any s n)) , NZ-add _ (s n _) (proj₁ (nz-any s n)) (proj₂ (nz-any s n))

inv-nz : ∀ n → NZ0 (co (pts n)) × NZ (co (pts n))
inv-nz zero = tt , tt
inv-nz (suc n) = NZ0-add (co (pts n)) (obs (pts n)) (proj₁ (inv-nz n)) ,
  NZ-add (co (pts n)) (obs (pts n)) (proj₁ (inv-nz n)) (proj₂ (inv-nz n))
```

## 3 判据 C2：不通过

```agda
no-sω-κ : ∀ m → ¬ (L.suc L.ωᴵ ⊑ᴵ κ m)
no-sω-κ m = no-sω (co (pts m)) _ (proj₂ (inv-nz m))

no-L : ∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)
no-L n m le = no-sω-κ m (L.⊑ᴵ-trans sω-L1 (L.⊑ᴵ-trans (L-chain n) le))

C2 : ∀ m → ¬ (D.L 1 ⊑ᴵ κ m)
C2 = no-L 0

L0⊑κ0 : D.L 0 ⊑ᴵ κ 0
L0⊑κ0 = L.⊑ᴵ-refl

γ0≼ᵖ : D.γ 0 ≼ᵖ read (co (pts 0))
γ0≼ᵖ = ˣ→ᵖ (reflˣ _)
```

## 4 正对照：折叠值里有字面的 ω+1

`F (fin 1)` 的第 1 项的第 1 项是 `succ (Ψ top)`，其第 2 项是 `W + W`，再第 1 项是 `W + top = suc W`，`W = succ top` 读成字面的 ω (第 0 项是零)。

```agda
sucs : ℕ → R → R
sucs zero x = x
sucs (suc n) x = G.suc (sucs n x)

plus-sucs : ∀ x y n → plus zero x (sucs n y) ≡ sucs n (plus zero x y)
plus-sucs x y zero = refl
plus-sucs x y (suc n) = cong G.suc (plus-sucs x y n)

sucs-s : ∀ n x → sucs n (G.suc x) ≡ G.suc (sucs n x)
sucs-s zero x = refl
sucs-s (suc n) x = cong G.suc (sucs-s n x)

accN : ∀ n → acc (λ _ z → plus zero G.top z) G.zero (suc n) ≡ sucs n G.top
accN zero = refl
accN (suc n) = trans (cong (plus zero G.top) (accN n)) (trans (plus-sucs G.top G.top n) (sucs-s n G.top))

natS : ∀ n h → L.natᴵ (suc n) ≅ᴵ L.toLevel (read (sucs n G.top)) h
natS zero h = L.s≅ L.z≅
natS (suc n) h = L.s≅ (natS n (L.hs⁻ h))

natA : ∀ n h → L.natᴵ n ≅ᴵ L.toLevel (read (acc (λ _ z → plus zero G.top z) G.zero n)) h
natA zero h = L.z≅
natA (suc n) = subst (λ t → ∀ h → L.natᴵ (suc n) ≅ᴵ L.toLevel (read t) h) (sym (accN n)) (natS n)

W : R
W = succ zero G.top

ω≅W : ∀ h → L.ωᴵ ≅ᴵ L.toLevel (read W) h
ω≅W h = L.l≅ (λ n → natA n (L.hl₁ h n))

fin : ℕ → R
fin zero = G.zero
fin (suc n) = G.suc (fin n)

sω-F1 : L.suc L.ωᴵ ⊑ᴵ L.toLevel (read (F (fin 1) tt)) (HS-read _ (F-lgl (fin 1) tt))
sω-F1 = L.s⊑ (ω≅W _) (L.lim 1 (L.lim 1 (L.lim 2 (L.lim 1 L.zero))))
```
