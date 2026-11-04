# `HtS` 的字段, 对层号 `LG` 与路径: 清单

> 不含记号. 结论写在 [GuardCert](GuardCert.lagda.md). [LadderInfBase](LadderInfBase.lagda.md) 的 `HtS` 把 "高度" 抽象掉; `T₀ʷ` 没有外部高度, 最自然的候选是: 高度 = 层号 `LG`, 序 = 路径 `_<_`. 这里逐字段写定理. **只否定这个字面的实例 ($\mathrm{LG}$, `_<_`, 底 `zero`), 不否定弱化 (带界的比较, 去掉退化极限), 也不否定别的高度选法.**
>
> | 字段 | 状况 | 定理 |
> |---|---|---|
> | `tr<`, `tr-assoc` | 成立 | `tr<ᴸ`, `assocᴸ` |
> | `irr`, `no<` | 成立 | `irrᴸ`, `no<ᴸ` |
> | `Rec`, `Rec-β` | 成立 | `recᴸ`, `recᴸ-β` |
> | `tri` | **假** | `no-triᴸ` ($\lceil\omega\rceil$, $\lceil\omega'\rceil$ 不可比) |
> | `bot` | **假** | `no-botᴸ` (常值 0 的极限) |
> | `view` | **假** | `no-viewᴸ` (同一个例子) |
> | `view-step` | 依赖 `view`, 没有写 | |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertHt where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.LadderInfBase using (Tri; tlt; teq; tgt; View; base; clos; chain)
open import OCF.Align.GuardTightLv using (Dom₀; module Lv)
open Lv Dom₀ renaming (zero to Zr; suc to Sc; lim to Lm)
open import OCF.Align.GuardTightTab Dom₀ using (toCp; _⊙_)
open import OCF.Align.GuardTightTree using (_◁_)
open import OCF.Align.GuardWeakRel using (⌜_⌝; pullG)
open import OCF.Free.Level using (Ordᴵ; natᴵ; natᴵ-step; z⊑; ωᴵ; lim; _<ᴵ_)
import OCF.Free.Level as I
```

## §1 成立的字段

```agda
tr<ᴸ : ∀ {k a b} → k < a → a < b → k < b
tr<ᴸ r s = toCp s ◁ r

no<ᴸ : ∀ {i} → i < Zr → ⊥
no<ᴸ ()

data AccL (a : LG) : Set where
  acc : (∀ {k} → k < a → AccL k) → AccL a

accL : ∀ a → AccL a
goL : ∀ a {k} → k < a → AccL k
accL a = acc (goL a)
goL (Sc b) Lv.zero = accL b
goL (Sc b) (Lv.suc r) = goL b r
goL (Lm f) (Lv.lim n r) = goL (f n) r
goL (lc c t g) (Lv.fst r) = goL t r
goL (lc c t g) (Lv.bra η e r) = goL (g η e) r

irr-acc : ∀ {a} → AccL a → a < a → ⊥
irr-acc (acc h) r = irr-acc (h r) r

irrᴸ : ∀ {a} → a < a → ⊥
irrᴸ {a} = irr-acc (accL a)

recᴸ : ∀ {ℓ : Level} (X : LG → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ m {n} → n < m → X n
recᴸ X F (Sc m) Lv.zero = F m (recᴸ X F m)
recᴸ X F (Sc m) (Lv.suc q) = recᴸ X F m q
recᴸ X F (Lm f) (Lv.lim i q) = recᴸ X F (f i) q
recᴸ X F (lc c t g) (Lv.fst q) = recᴸ X F t q
recᴸ X F (lc c t g) (Lv.bra η e q) = recᴸ X F (g η e) q

recᴸ-β : ∀ {ℓ : Level} (X : LG → Set ℓ) (F : ∀ m → (∀ {n} → n < m → X n) → X m) → ∀ m {n} (q : n < m) → recᴸ X F m q ≡ F n (recᴸ X F n)
recᴸ-β X F (Sc m) Lv.zero = refl
recᴸ-β X F (Sc m) (Lv.suc q) = recᴸ-β X F m q
recᴸ-β X F (Lm f) (Lv.lim i q) = recᴸ-β X F (f i) q
recᴸ-β X F (lc c t g) (Lv.fst q) = recᴸ-β X F t q
recᴸ-β X F (lc c t g) (Lv.bra η e q) = recᴸ-β X F (g η e) q

-- 结合律
◁⊙ : ∀ {k a b d} (P : Cp b d) (Q : Cp a b) (r : k < a) → P ◁ (Q ◁ r) ≡ (P ⊙ Q) ◁ r
◁⊙ Lv.self Q r = refl
◁⊙ (Lv.suc P) Q r = cong Lv.suc (◁⊙ P Q r)
◁⊙ (Lv.lim n P) Q r = cong (Lv.lim n) (◁⊙ P Q r)
◁⊙ (Lv.fst P) Q r = cong Lv.fst (◁⊙ P Q r)
◁⊙ (Lv.bra η e P) Q r = cong (Lv.bra η e) (◁⊙ P Q r)

toCp◁ : ∀ {k a b} (P : Cp a b) (r : k < a) → toCp (P ◁ r) ≡ P ⊙ toCp r
toCp◁ Lv.self r = refl
toCp◁ (Lv.suc P) r = cong Lv.suc (toCp◁ P r)
toCp◁ (Lv.lim n P) r = cong (Lv.lim n) (toCp◁ P r)
toCp◁ (Lv.fst P) r = cong Lv.fst (toCp◁ P r)
toCp◁ (Lv.bra η e P) r = cong (Lv.bra η e) (toCp◁ P r)

assocᴸ : ∀ {a b c d} (x : a < b) (y : b < c) (z : c < d) → tr<ᴸ (tr<ᴸ x y) z ≡ tr<ᴸ x (tr<ᴸ y z)
assocᴸ x y z = trans (◁⊙ (toCp z) (toCp y) x) (cong (_◁ x) (sym′ (toCp◁ (toCp z) y)))
  where
  sym′ : ∀ {A : Set} {u v : A} → u ≡ v → v ≡ u
  sym′ refl = refl
```

## §2 假的字段

`no-triᴸ`: 同 [LadderInfOrd](LadderInfOrd.lagda.md) 的 `no-triᴼ`, 层号上. 这是 `¬tri` 在 `LG` 上的影子: 全局三歧不可得. **`cmpN` ([GuardWeakTree](GuardWeakTree.lagda.md)) 是这个字段的弱化: 只比较字面公共上界之下的 (表里有证据的) 值, 没有证据答 `cj`; `no-bra-cmp` 说没有证据的比较写不出.**

```agda
ω′ : Ordᴵ
ω′ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

head : LG → LG
head (Lm f) = f 0
head a = a

nl : ∀ m {f s} → I.lim f s <ᴵ natᴵ m → ⊥
nl zero ()
nl (suc zero) (I.suc ())
nl (suc (suc m)) (I.suc q) = nl (suc m) q

no-triᴸ : (∀ a b → Tri _<_ a b) → ⊥
no-triᴸ t with t ⌜ ωᴵ ⌝ ⌜ ω′ ⌝
... | tlt r with pullG ω′ r
...   | I.zero , () , q
...   | I.suc a′ , () , q
...   | I.lim f s , e , I.lim n q = nl (suc n) q
no-triᴸ t | tgt r with pullG ωᴵ r
...   | I.zero , () , q
...   | I.suc a′ , () , q
...   | I.lim f s , e , I.lim n q = nl n q
no-triᴸ t | teq e with cong head e
...   | ()

𝟎 : LG
𝟎 = Lm (λ _ → Zr)

none : ∀ {a} → a < 𝟎 → ⊥
none (Lv.lim n ())

no-botᴸ : (∀ i → (Zr ≡ i) ⊎ (Zr < i)) → ⊥
no-botᴸ b with b 𝟎
... | inj₁ ()
... | inj₂ q = none q

no-viewᴸ : (∀ m → View _<_ Zr m) → ⊥
no-viewᴸ v with v 𝟎
... | clos q = none q
... | chain F qs = none (qs 0)
```

## §3 下一步的第一个具体差别

`keep-Ω+2`: 层 $c_1+2$, 帧的位置 `suc (suc self)`, 节点 $c_1$ (路径 `suc zero`): `keepP` 答 `true`. 所以链保留这个帧 (`trim`), 证书里 $c_1+1$ 上的 `Emp ξ` (`trim-emp`) 到这里不再成立, `Rc` 的 `ci` 的前提要换成 `CvL ξ ξ̂`, 对应右边 `oΩ` 的地板 `ξ̂`. 这是定义的一个计算, 不是否定.

```agda
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁)
open import OCF.Align.GuardWeakTree using (module FoldW)
open import Data.Bool using (true)
open import Data.Unit using (tt)

keep-Ω+2 : ∀ {E} → FoldW.keepP (Sc (Sc c₁)) wf₁ (Lv.s≈ (Lv.s≈ sf₁)) Tc-Ω₁ {E = E} wf₁ (Lv.s≈ (Lv.s≈ sf₁)) (Lv.suc (Lv.suc Lv.self)) (Lv.suc Lv.zero) tt tt ≡ true
keep-Ω+2 = refl
```
