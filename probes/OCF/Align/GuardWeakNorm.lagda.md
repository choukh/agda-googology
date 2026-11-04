# 规范化之后分支值是后继: $\Omega$ 上的定理

> 不含记号. 结论写在 [GuardWeak](GuardWeak.lagda.md). 这是设计的那一句话 ("规范化后分支值总是后继, 所以 `bra` 对 `bra` 比较的是字面的值") 在 $c_1=\Omega$ 上的定理, 对一切 $\eta$ (含极限), 一切路径.
>
> - `nv`: $c_1+1$ 里的节点 `suc r₁`, 节点模 $\approx$ 是 $\lceil j\rceil$. 规范化之后要么是 `suc (fst self)` ($j\cong0$), 要么是 `suc (bra (b+1) e self)`, $b\cong j$. **节点是极限层穿过的也一样. 地板是 $b+1$ 这个帧, 不是穿过的 $\eta$.**
> - `belR-suc`: 帧有证据时, 被它支配的后继分支 $a$ 的字面证据一定读得到 (`belR` 答 `just`). 只用弱证据 `Simᴵ`. **这就是 `no-join` 不挡的原因: 比较的两边都是字面的前驱.**
> - `no-guard`: 为什么极限节点的位置不一定下降. 分支 $\lim f$ 上的极限节点 $f\,n$ 要成为分支, 要 $1\sqsubseteq f\,n$, 这从 $1\sqsubseteq\lim f$ 推不出. 所以 `Reader` 的 `xC` 这条路留在 $\lim f$ (`rec` 里 `nothing` 的情形). 这是证书的卡点之一.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakNorm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightCum hiding (ψ; _+_)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardReadCut using (Ab; LZ)
open import OCF.Align.GuardWeakRd using (Nw; RdV; rvF; rvN; rdΩ₁; Tc-Ω₁)
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; pullG)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardWeakTree using (module FoldW; prOf)

cT : LG
cT = Lv.suc c₁

tcʷ : Tc cT
tcʷ = Tc-Ω₁

open FoldW cT wf₁ (Lv.s≈ sf₁) tcʷ
```

## §1 读位置的回答

`no-below`: $\lceil b\rceil$ 的严格下方的节点 $B+1$ 不可能有 $\lceil b\rceil\trianglelefteq B$. 由良基.

```agda
no-below : ∀ {b B} (Q : Cp (Lv.suc B) ⌜ b ⌝) → ⌜ b ⌝ ⊴ B → ⊥
no-below {b} Q h with pullG b (fromCpS Q)
... | a′ , refl , q with ⊴p h (fromCpS Q)
...   | viaᴸ d₁ s₁ _ with pullG a′ s₁
...     | a″ , refl , q′ = ≺ᴵ-irrefl (via (⌜≈⁻⌝ d₁) q′)

viewR : ∀ η e {k} (P : Cp (Lv.suc k) ⌜ η ⌝) → Σ _ λ x → (proj₁ tcʷ η e P ≡ x) × RdV ⌜_⌝ x
viewR η e P = proj₁ tcʷ η e P , refl , rdΩ₁ η e tt P
```

## §2 `nv`

```agda
one : Ordᴵ
one = suc zero

data NV {k} (r : k < cT) (j : Ordᴵ) : NR r → Set where
  nvF : ∀ {d rl} → j ≅ᴵ zero → NV r j (nr {rpR = Lv.zero} d (Lv.suc (Lv.fst Lv.self)) rl)
  nvB : ∀ {b} {e : one ⊑ᴵ suc b} {d rl} → b ≅ᴵ j → NV r j (nr {rpR = ⌜ b ⌝} d (Lv.suc (Lv.bra (suc b) e Lv.self)) rl)

nv : ∀ {k j} (r₁ : k < c₁) → k ≈ ⌜ j ⌝ → NV (Lv.suc r₁) j (nfR (Lv.suc r₁))
nv (Lv.fst Lv.zero) dk = nvF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} dk))
nv (Lv.fst (Lv.suc ())) dk
nv {j = j} (Lv.bra η e r₂) dk with viewR η e (toCpS r₂)
nv {j = j} (Lv.bra η e r₂) dk | rdF (inj₂ refl) Lv.self tr , eq , rvF rewrite eq = nvF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} dk))
nv {j = j} (Lv.bra η e r₂) dk | rdF (inj₁ (Lv.s≈ d)) Lv.self tr , eq , rvF rewrite eq = nvF (≅ᴵ-sym (⌜≈⁻⌝ {a = zero} (≈-trans (≈-sym d) dk)))
nv {j = j} (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₂ refl) Lv.self tr , eq , rvN .b w rewrite eq = nvB (⌜≈⁻⌝ dk)
nv {j = j} (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) Lv.self tr , eq , rvN .b w rewrite eq = nvB (⌜≈⁻⌝ (≈-trans (≈-sym d) dk))
nv (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr , eq , rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
nv (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₂ refl) (Lv.suc Q) tr , eq , rvN .b (inj₂ ())
nv (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr , eq , rvN .b (inj₁ h) = ⊥-elim (no-below Q h)
nv (Lv.bra η e r₂) dk | rdB (suc b) ea l (inj₁ (Lv.s≈ d)) (Lv.suc Q) tr , eq , rvN .b (inj₂ ())
```

## §3 弱证据给字面证据

```agda
prOf-suc : ∀ {b η ℓ} (lt : suc b ⊲ η) (σ : Simᴵ η ℓ) → Σ _ λ q → prOf lt σ ≡ just q
prOf-suc ⊲= σ = _ , refl
prOf-suc (⊲ˢ h) σ = _ , refl

belR-suc : ∀ {E ρ π} (st : St E ρ π) → (∀ {f} (m : Mem π f) → Σ _ λ d → ev (st m) ≡ just d) →
           ∀ {y b} (d : Dm π y (suc b)) → Σ _ λ B → Rd.belR st d ≡ just B
belR-suc st full (f , m , lk , lt) with ev (st m) | full m
... | just (evd _ _ _ (ℓ , b , σ)) | _ , refl with prOf lt σ | prOf-suc lt σ
...   | just q | _ , refl = _ , refl
```

## §4 极限的分支值

```agda
zeros : ℕ → Ordᴵ
zeros zero = zero
zeros (suc n) = natᴵ n

mono : ∀ n → zeros n ⊑ᴵ zeros (suc n)
mono zero = z⊑
mono (suc n) = Sim→⊑ᴵ suc

no-guard : (∀ (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) n → one ⊑ᴵ lim f s → one ⊑ᴵ f n) → ⊥
no-guard H with H zeros mono 0 (s⊑ z≅ (lim 2 zero))
... | s⊑ _ ()
```

**`stays`: 这个读法真的留在 $\lim f$.** $\eta=\omega\cdot2=\lim_n(\omega+n)$, 节点是 $f\,0=\omega$ (极限). 规范位置的第一个分支值还是 $\omega\cdot2$, 不是 $\omega$. `¬ω2⊑ω` 说这个帧不被 `flo ω` 盖住. **所以 "规范位置的帧 $\sqsubseteq$ 节点的层" 对极限节点是假的 (`cover-false`).** 判断: 这是过渡的: 极限层 $\dot\Omega$ 只有 `ol`, 里面下一个 `omk` 又下降, 其间没有内容, 所以与塔一致 (有限测试 `V` 探针). 但闭包的证书要的盖住关系不能写成对一切位置的不变量.

```agda
itO : Ordᴵ → ℕ → Ordᴵ
itO c zero = c
itO c (suc k) = suc (itO c k)

ω2 : Ordᴵ
ω2 = lim (itO ωᴵ) (λ k → Sim→⊑ᴵ suc)

e₂ : one ⊑ᴵ ω2
e₂ = s⊑ z≅ (lim 0 (lim 1 zero))

firstV : ∀ {a b} → Cp a b → Maybe Ordᴵ
firstV Lv.self = nothing
firstV (Lv.suc P) = firstV P
firstV (Lv.lim n P) = firstV P
firstV (Lv.fst P) = firstV P
firstV (Lv.bra η e P) = just η

pos₂ : Cp ⌜ ωᴵ ⌝ c₁
pos₂ = Lv.bra ω2 e₂ (Lv.lim 0 Lv.self)

stays : firstV (posN (nfC c₁ tcʷ pos₂)) ≡ just ω2
stays = refl

lim≠nat : ∀ n → ωᴵ ≅ᴵ natᴵ n → ⊥
lim≠nat zero ()
lim≠nat (suc n) ()

fin< : ∀ {r} n → r <ᴵ natᴵ n → ωᴵ ≅ᴵ r → ⊥
fin< (suc n) zero e = lim≠nat n e
fin< (suc n) (suc q) e = fin< n q e

¬s⊑ω : suc ωᴵ ⊑ᴵ ωᴵ → ⊥
¬s⊑ω (s⊑ e (lim n q)) = fin< n q e

¬ω2⊑ω : ω2 ⊑ᴵ ωᴵ → ⊥
¬ω2⊑ω (l⊑ h) = ¬s⊑ω (h 1)

cover-false : (∀ {k′ a} (P : Cp ⌜ k′ ⌝ c₁) → firstV (posN (nfC c₁ tcʷ P)) ≡ just a → a ⊑ᴵ k′) → ⊥
cover-false H = ¬ω2⊑ω (H pos₂ stays)
```
