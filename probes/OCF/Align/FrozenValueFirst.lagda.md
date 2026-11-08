# 实际冻结 Tω 的首个地板分量下界

直接比较实际 `Fold1.TΩ1` 与 `SupCollapseClosed.Tω`，输入分支为 `up c`。
证明不依赖常值样本：坐标为任意可数树，回灌轨道的全部项同时比较。
第 1 分量还证明反方向，所以该分量同值于原 TΩ1；不声称更高分量或原 TΩω 与冻结 Tω 同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenValueFirst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; top; ΣT; mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (Wi; ≤-refl; ≤-trans; mul-≤; ⊞-≤ˡ; ⊞-≤ʳ)
import OCF.Lean.Fold1Fold as Old
import OCF.Lean.SupCollapseFrozen as New
import OCF.Lean.Fold1 as Original
import OCF.Lean.SupCollapseClosed as Frozen

add-mono : ∀ {a b c d : Cd} → a ≤ᵛ b → c ≤ᵛ d → (a ⊞ c) ≤ᵛ (b ⊞ d)
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)

-- 只用来证明实际两个纯坐标解释器的联合单调。
record Pure {D : Set} (F : D → Cd → Cd) : Set where
  field
    at0 : ∀ d → F d hz ≡ hs hz
    ats : ∀ d a → F d (hs a) ≡ hl (mul (F d a))
    atl : ∀ d f → F d (hl f) ≡ hl (λ n → F d (f n))
open Pure

module Compare {D E : Set} {F : D → Cd → Cd} {G : E → Cd → Cd}
               (pf : Pure F) (pg : Pure G) where
  positive : ∀ d c → hs hz ≤ᵛ G d c
  positive d hz rewrite at0 pg d = s≤s z≤
  positive d (hs c) rewrite ats pg d c = ≤l 0 (positive d c)
  positive d (hl f) rewrite atl pg d f = ≤l 0 (positive d (f 0))

  mono : ∀ d e {a b} → a ≤ᵛ b → F d a ≤ᵛ G e b
  mono d e {b = b} z≤ rewrite at0 pf d = positive e b
  mono d e {a = hs a} {hs b} (s≤s p) rewrite ats pf d a | ats pg e b =
    l≤ (λ n → ≤l n (mul-≤ (mono d e p) n))
  mono d e {b = hs b} (≤s p) rewrite ats pg e b = ≤l 0 (mono d e p)
  mono d e {a = hl f} (l≤ h) rewrite atl pf d f = l≤ (λ n → mono d e (h n))
  mono d e {b = hl f} (≤l n p) rewrite atl pg e f = ≤l n (mono d e p)

m₁ : Cd
m₁ = hs hz
p₁ : hz ⊲ m₁
p₁ = hsuc hself

encode : Cd → HB (Lv Frozen.ω)
encode c = hz ⊞ ι 1 (up c)

F : Wd (Lv m₁) → Cd → Cd
F W c = Old.Φ m₁ tt hz p₁ W (up c)

G : Wd (Lv Frozen.ω) → Cd → Cd
G W c = New.Φ Frozen.ω Frozen.legal-ω hz (z⊲ᴮ Frozen.ω) W (encode c)

Gx : Wd (Lv Frozen.ω) → Cd → Cd
Gx W c = New.Φ Frozen.ω Frozen.legal-ω hz (hlim 1 (hsuc hself)) W (encode c)

pure-Gx : Pure Gx
pure-Gx = record { at0 = λ W → refl ; ats = λ W c → refl ; atl = λ W f → refl }

pure-F : Pure F
pure-F = record { at0 = λ W → refl ; ats = λ W c → refl ; atl = λ W f → refl }

pure-G : Pure G
pure-G = record { at0 = λ W → refl ; ats = λ W c → refl ; atl = λ W f → refl }

module C = Compare pure-F pure-G
module Cx = Compare pure-F pure-Gx

module O = Old.Col _⊞_ _⊞_ (Wi m₁) hz (λ W e → proj₁ W , e) F F
module N = New.Col _⊞_ _⊞_ (Wi Frozen.ω) hz (λ W e → W) Gx G

coordinates : ∀ n → O.ce n ≤ᵛ N.ce n
coordinates zero = z≤
coordinates (suc n) = add-mono (coordinates n) (Cx.mono (O.cw n) (N.cw n) (coordinates n))

outputs : ∀ n → O.oo n ≤ᵛ N.oo n
outputs n = C.mono (O.cw n) (N.cw n) (coordinates n)

sums : ∀ n → O.oO n ≤ᵛ N.oO n
sums zero = outputs zero
sums (suc n) = add-mono (sums n) (outputs (suc n))

first-component : Original.TΩ1 ≤ᵛ New.Φ Frozen.ω Frozen.legal-ω hz
  (z⊲ᴮ Frozen.ω) (Wi Frozen.ω) (ΣT S⊥ hz Frozen.num 1)
first-component = l≤ (λ n → ≤l n (sums n))

module Back = Compare pure-G pure-F
module BackX = Compare pure-Gx pure-F

coordinates-back : ∀ n → N.ce n ≤ᵛ O.ce n
coordinates-back zero = z≤
coordinates-back (suc n) = add-mono (coordinates-back n)
  (BackX.mono (N.cw n) (O.cw n) (coordinates-back n))

outputs-back : ∀ n → N.oo n ≤ᵛ O.oo n
outputs-back n = Back.mono (N.cw n) (O.cw n) (coordinates-back n)

sums-back : ∀ n → N.oO n ≤ᵛ O.oO n
sums-back zero = outputs-back zero
sums-back (suc n) = add-mono (sums-back n) (outputs-back (suc n))

first-component-back : New.Φ Frozen.ω Frozen.legal-ω hz
  (z⊲ᴮ Frozen.ω) (Wi Frozen.ω) (ΣT S⊥ hz Frozen.num 1) ≤ᵛ Original.TΩ1
first-component-back = l≤ (λ n → ≤l n (sums-back n))

original-one≤frozen-omega : Original.TΩ1 ≤ᵛ Frozen.Tω
original-one≤frozen-omega = ≤l 1 first-component
```

关键实例是 `pure-G`：第 1 分量的坐标类型只有可数树，所以 `encode c`
没有 Ω 节点，解释器虽收到不同世界，输出值仍由同一纯构造子规则控制。
`coordinates` 在实际更新/冻结两条轨道间递归，并未假设它们字面相等。
较高分量坐标可能含 Ω，`Pure` 不再覆盖它，必须另证支持或世界关系。
翻译账：只增加实际值下界，不改任何定义或证书，不读取记号。
