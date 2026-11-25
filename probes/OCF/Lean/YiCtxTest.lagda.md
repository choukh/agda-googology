# 同支证据的闸门: 跨支那一对对一切证据来源都不再保留, 卡住的那一对要证据

非验收文件. 编译定理, 无前提: 对一切派发 `D` 与证据来源 `E`, 两支下标字面不同的一对在 Ω 结点那一句只走 `D` (`gate-no`, `cross-fold`); `E` 在卡住的那一对 (`rN`, `pN`) 的支下标上给出证据时, 这一对保留在 `YiZipLost` 的槽位上 (`kept-if`).
有限测试 (`refl`): 实例 `evF` 下跨支那一对折叠 (`cross-inst`), 卡住的那一对也折叠 (`lost-evF`), 因为它的支下标是 `suc` 后接 ℕ 极限 (`ηN-form`, `evF-ηN`); 有限支里的同支一对 `D` 本来就保留 (`fin-D`). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCtxTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; R)
open import OCF.Lean.YiLamFold using (Lw; wΩ; nrmk)
open import OCF.Lean.YiDlInst using (V2; rN; ξa)
open import OCF.Lean.YiDlLost using (pN) renaming (s to sN)
open import OCF.Lean.YiZipWay
open import OCF.Lean.YiZipMove using (mv)
open import OCF.Lean.YiZipFold using (PT; viaM; orW; dl′)
open import OCF.Lean.YiCtxFold
```

## 1 闸门的两条律

```agda
gate-no : ∀ {A : Set} {m j} (u : Maybe A) → (A → ⊥) → (d s : Way′ m j) → gate u d s ≡ d
gate-no nothing n d s = refl
gate-no (just a) n d s = ⊥-elim (n a)

gate-yes : ∀ {A : Set} {m j} (u : Maybe A) (a : A) → u ≡ just a → (d s : Way′ m j) → gate u d s ≡ orW d s
gate-yes .(just a) a refl d s = refl

wΩ-no : ∀ D E {k g} (V : ∀ η → Lgl k η → Lw (g η)) w η l q η′ l′ r → (η ≡ η′ → ⊥) →
  FoldC.cmpc D E (wΩ V w) (η , l , q) (η′ , l′ , r) ≡ D (lev (g η) q) (lc k g) (η′ , l′ , r)
wΩ-no D E {k} V w η l q η′ l′ r n = gate-no (E k η η′) n _ _

wΩ-yes : ∀ D E {k g} (V : ∀ η → Lgl k η → Lw (g η)) w η l q l′ r (e : η ≡ η) → E k η η ≡ just e →
  FoldC.cmpc D E (wΩ V w) (η , l , q) (η , l′ , r) ≡
    orW (D (lev (g η) q) (lc k g) (η , l′ , r)) (viaM (g η) (g η) (FoldC.cmpc D E (V η l) q) r (PT (g η) (g η) r))
wΩ-yes D E {k} V w η l q l′ r e h = gate-yes (E k η η) e h _ _
```

## 2 跨支那一对: 对一切证据来源

`q₂`, `r₃` 同 [YiZipLost](YiZipLost.lagda.md) (第 2 支与第 3 支); 那里只按结构对齐时保留 (`cross-keep`).

```agda
q₂ r₃ : Pre (tw 2)
q₂ = G.suc (G.suc G.zero) , tt , inj₁ tt
r₃ = G.suc (G.suc (G.suc G.zero)) , tt , inj₂ (inj₁ tt)

cross-fold : ∀ D E → FoldC.cmpc D E V2 q₂ r₃ ≡ D (lev (tw 2) q₂) (tw 2) r₃
cross-fold D E = gate-no (E zero _ _) (λ ()) _ _

cross-inst : cmpc V2 q₂ r₃ ≡ fold′
cross-inst = refl
```

## 3 卡住的那一对

```agda
ηN : R
ηN = nrmk zero ξa

ηN-form : Σ (ℕ → R) λ f → ηN ≡ G.suc (G.lim f)
ηN-form = _ , refl

evF-ηN : evF zero ηN ηN ≡ nothing
evF-ηN = refl

lost-evF : cmpc V2 rN pN ≡ fold′
lost-evF = refl

L : LF
L = lev (tw 2) pN

kept-if : ∀ E (e : ηN ≡ ηN) → E zero ηN ηN ≡ just e →
  FoldC.cmpc dl′ E V2 rN pN ≡ keep′ sN (byEq refl ⨾ byMv L L)
kept-if E e h = wΩ-yes dl′ E _ _ ηN _ _ _ _ e h
```

## 4 有限支里的同支一对

```agda
q₂′ : Pre (tw 2)
q₂′ = G.suc (G.suc G.zero) , tt , inj₂ (inj₁ tt)

fin-D : dl′ (lev (tw 2) q₂) (tw 2) q₂′ ≡ keep′ (inj₁ tt) (byEq refl)
fin-D = refl

fin-same : cmpc V2 q₂ q₂′ ≡ keep′ (inj₁ tt) (byEq refl)
fin-same = refl
```
