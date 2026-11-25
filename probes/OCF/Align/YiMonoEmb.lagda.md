# YiMono：前驱嵌入与 `T₃ᵐ` 的 BTBO 下界的约化

**验收文件，档位：编译定理与条件定理。** `PEmb a b` (`BTBOFullEmb`，前驱的保序映射，`Ψ-emb` 给 ψ⁰(Ω_a) ≼ ψ⁰(Ω_b)) 对后继同余 (`PEmb-suc`)，而 `⊑ᴵ` 不是 (`ω-not`)；左极限在各项嵌入互相一致时可拼 (`PEmb-limˡ`)；实例 `ω-inst` 是上一路判断的断点 ω+1 对 (1+ω)+1。
条件定理：`btbo-dom : DomT → D.BTBOᴵ ≼ read T₃ᵐ`，`DomT` 是只谈参照族的命题 "参照第 n 项的 ψ⁰(Ω_·) 不超过某个链点层号上的 ψ⁰(Ω_·)"；`emb→dom`：链点层号的前驱嵌入 `EmbT` 推出 `DomT`。`EmbT` 在 n = 0 的实例 `emb₀` 是定理；n ≥ 1 未证 (n = 1 只做到 ω+1 嵌进 κ₁，见 `YiMonoOne`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiMonoEmb where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
import OCF.Align.Level as L
open L using (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiBtValBT using (module D; κ; T₃ᵐ-own)
```

## 1 `PEmb` 的演算

```agda
PEmb-⊑ : ∀ {a b} → a ⊑ᴵ b → PEmb a b
map (PEmb-⊑ k) {c} r = c
bnd (PEmb-⊑ k) (via e q) = L.≺ᴵ-respˡ e (L.sim k q)
mono (PEmb-⊑ k) r s lt = lt
coh (PEmb-⊑ k) r s e = e

PEmb-∘ : ∀ {a b c} → PEmb a b → PEmb b c → PEmb a c
map (PEmb-∘ P Q) r = map Q (bnd P r)
bnd (PEmb-∘ P Q) r = bnd Q (bnd P r)
mono (PEmb-∘ P Q) r s lt = mono Q (bnd P r) (bnd P s) (mono P r s lt)
coh (PEmb-∘ P Q) r s e = coh Q (bnd P r) (bnd P s) (coh P r s e)

PEmb-limʳ : ∀ {a f s} n → PEmb a (f n) → PEmb a (L.lim f s)
map (PEmb-limʳ n P) r = map P r
bnd (PEmb-limʳ n P) r = L.≺-lim n (bnd P r)
mono (PEmb-limʳ n P) = mono P
coh (PEmb-limʳ n P) = coh P
```

左边是极限时，各项的嵌入只要在公共前驱上互相 `≅ᴵ` 就能拼起来 (`PEmb-limˡ`)；不必比较下标的大小。

```agda
PEmb-limˡ : ∀ {f s b} (P : ∀ n → PEmb (f n) b) →
  (∀ n m {c} (r : c ≺ᴵ f n) (t : c ≺ᴵ f m) → map (P n) r ≅ᴵ map (P m) t) →
  PEmb (L.lim f s) b
map (PEmb-limˡ P k) (via e (L.lim n q)) = map (P n) (via e q)
bnd (PEmb-limˡ P k) (via e (L.lim n q)) = bnd (P n) (via e q)
mono (PEmb-limˡ P k) (via e (L.lim n q)) (via e′ (L.lim m q′)) lt =
  L.≺ᴵ-respˡ (k n m (via e q) (L.≺ᴵ-trans lt (via e′ q′)))
    (mono (P m) (L.≺ᴵ-trans lt (via e′ q′)) (via e′ q′) lt)
coh (PEmb-limˡ P k) (via e (L.lim n q)) (via e′ (L.lim m q′)) d =
  L.≅ᴵ-trans (k n m (via e q) (L.≺ᴵ-respˡ d (via e′ q′)))
    (coh (P m) (L.≺ᴵ-respˡ d (via e′ q′)) (via e′ q′) d)
```

后继同余：顶 `a` 映到 `b`，其余经 `P`。两个顶上的比较由 `≺ᴵ` 无自反排除。

```agda
PEmb-suc : ∀ {a b} → PEmb a b → PEmb (L.suc a) (L.suc b)
map (PEmb-suc {b = b} P) (via e L.zero) = b
map (PEmb-suc P) (via e (L.suc q)) = map P (via e q)
bnd (PEmb-suc {b = b} P) (via e L.zero) = via (L.≅ᴵ-refl b) L.zero
bnd (PEmb-suc P) (via e (L.suc q)) = L.≺-suc (bnd P (via e q))
mono (PEmb-suc P) (via e L.zero) (via e′ L.zero) lt =
  ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respʳ (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) lt) e′))
mono (PEmb-suc P) (via e L.zero) (via e′ (L.suc q′)) lt =
  ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-trans (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) lt) (via e′ q′)))
mono (PEmb-suc P) (via e (L.suc q)) (via e′ L.zero) lt = bnd P (via e q)
mono (PEmb-suc P) (via e (L.suc q)) (via e′ (L.suc q′)) lt = mono P (via e q) (via e′ q′) lt
coh (PEmb-suc {b = b} P) (via e L.zero) (via e′ L.zero) d = L.≅ᴵ-refl b
coh (PEmb-suc P) (via e L.zero) (via e′ (L.suc q′)) d =
  ⊥-elim (L.≺ᴵ-irrefl (via (L.≅ᴵ-trans (L.≅ᴵ-trans (L.≅ᴵ-sym e) d) e′) q′))
coh (PEmb-suc P) (via e (L.suc q)) (via e′ L.zero) d =
  ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (L.≅ᴵ-trans (L.≅ᴵ-sym e′) (L.≅ᴵ-sym d)) (via e q)))
coh (PEmb-suc P) (via e (L.suc q)) (via e′ (L.suc q′)) d = coh P (via e q) (via e′ q′) d
```

## 2 断点上的实例：ω+1 对 (1+ω)+1

```agda
ω⁺ᴵ : Ordᴵ
ω⁺ᴵ = L.lim (λ n → L.natᴵ (suc n)) (λ n → L.natᴵ-step (suc n))

ω⊑ω⁺ : L.ωᴵ ⊑ᴵ ω⁺ᴵ
ω⊑ω⁺ = L.l⊑ (λ n → L.Sim→⊑ᴵ (λ q → L.lim n (L.suc q)))

ω≇nat : ∀ m → ¬ (L.ωᴵ ≅ᴵ L.natᴵ m)
ω≇nat zero ()
ω≇nat (suc m) ()

ω≇<nat : ∀ m {c} → c <ᴵ L.natᴵ m → ¬ (L.ωᴵ ≅ᴵ c)
ω≇<nat (suc m) L.zero = ω≇nat m
ω≇<nat (suc m) (L.suc q) = ω≇<nat m q

ω-not : ¬ (L.suc L.ωᴵ ⊑ᴵ L.suc ω⁺ᴵ)
ω-not (L.s⊑ (L.l≅ h) L.zero) with h 0
... | ()
ω-not (L.s⊑ e (L.suc (L.lim n q))) = ω≇<nat (suc n) q e

ω-inst : L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ L.ψ⁰ (L.Ω (L.suc ω⁺ᴵ))
ω-inst = Ψ-emb (PEmb-suc (PEmb-⊑ ω⊑ω⁺))
```

## 3 约化

```agda
DomT : Set
DomT = ∀ n → Σ ℕ λ m → L.ψ⁰ (L.Ω (D.L n)) ≼ L.ψ⁰ (L.Ω (κ m))

btbo-dom : DomT → D.BTBOᴵ ≼ read T₃ᵐ
btbo-dom d = l≼ (λ n → ≼-trans (proj₂ (d n)) (T₃ᵐ-own (proj₁ (d n))))

EmbT : Set
EmbT = ∀ n → Σ ℕ λ m → PEmb (D.L n) (κ m)

emb→dom : EmbT → DomT
emb→dom e n = proj₁ (e n) , Ψ-emb (proj₂ (e n))

emb₀ : Σ ℕ λ m → PEmb (D.L 0) (κ m)
emb₀ = 0 , PEmb-⊑ L.⊑ᴵ-refl
```
