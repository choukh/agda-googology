# 稳定分支与搬运的证据无关性

此文件给出 `WorldEvidence` 反例所缺的一个充分条件。
只在同一源世界、同一目标世界的路径之间陈述律。
接口从本次定稿起只增不改。它不是 ψ₀Λ 折叠接口，尚不含合法性与值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldStable where

open import OCF.Lean.Fab6Base using (Cd; hz; _⊲_; ⊲ᴮ-tr)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldCompose
open import OCF.Lean.WorldEvidence using (reader; left; right; no-evidence-independence)
open import Data.Empty using (⊥)

data Stable {B : Cd} : W B → Set where
  stz : Stable wz
  sts : ∀ {a} → Stable a → Stable (ws a)
  stl : ∀ {f} → (∀ n → Stable (f n)) → Stable (wl f)
  stn : ∀ {g} → (∀ e p → Stable (g e p)) →
    (∀ e (p q : B ⊲ e) → g e p ≈ g e q) → Stable (wn g)

stable-lift : ∀ {A B} (p : A ⊲ B) {a} → Stable a → Stable (lift p a)
stable-lift p stz = stz
stable-lift p (sts s) = sts (stable-lift p s)
stable-lift p (stl s) = stl (λ n → stable-lift p (s n))
stable-lift p (stn s u) = stn
  (λ e r → s e (⊲ᴮ-tr p r))
  (λ e r t → u e (⊲ᴮ-tr p r) (⊲ᴮ-tr p t))

independent : ∀ {A B} (p q : A ⊲ B) {a} → Stable a → lift p a ≈ lift q a
independent p q stz = z≈
independent p q (sts s) = s≈ (independent p q s)
independent p q (stl s) = l≈ (λ n → independent p q (s n))
independent p q (stn s u) = n≈ (λ e r → u e (⊲ᴮ-tr p r) (⊲ᴮ-tr q r))

-- 充分条件有 Ω 形节点实例，不只含可数构造子。
node-instance : ∀ {B} → Stable {B} (wn (λ e p → ws wz))
node-instance = stn (λ e p → sts stz) (λ e p q → s≈ z≈)

reader-not-stable : Stable reader → ⊥
reader-not-stable s = no-evidence-independence (independent left right s)
```

已交的构造是稳定性谓词、含节点的实例及搬运封闭；否定明确针对
读路径的旧反例。尚未证明加法与 `φW` 保稳定，也未给值语义。
翻译账：未改树、折叠、合法性定义；新增条件由显式证据依赖反例提出。
常值分支实例仅证明条件可满足，不证明它足够支持有强度的折叠。
