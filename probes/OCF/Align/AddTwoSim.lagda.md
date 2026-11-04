# 一格 $\cdot\omega$ 由后面高层节点的链模拟

> 不含记号, 不含旧树. 入口 [AddTwo](AddTwo.lagda.md). 折叠用 [TLRuleSum](TLRuleSum.lagda.md), 关系用 [AddCloRel](AddCloRel.lagda.md) 的 `Rel`.
>
> `simStep`: 世界 $W$ 里, 节点 $N_j=\sum_{z:j}1$ ($j\ll W$). 对 $j$ 以下的目标 $t$, 只要 $c\trianglelefteq\Omega_t+Y'_t$, 就有
>
>     ω⋅ c ⊴ Run (n1 ⨾ N_j) 从状态 Y′ 在 t 上的输出
>
> 对任何 "膨胀" 的 $S$ ($c\trianglelefteq c'\Rightarrow c\trianglelefteq S c'$), 特别是 $S=\cdot2$. 也就是: 一格 $\cdot\omega$ 被 "一格 $S$, 再一个高层节点" 盖住, 那个节点的链每一段都至少有一格. `simChain` 是只有节点的版本, 要状态在 $j$ 上有顶层的叶子 (`TL`).
>
> **它只管一层.** 链里的输入是状态 (`D j` 的树), 放不进 $\geq j$ 的节点, 所以链自己那一层上的 $\cdot\omega$ 没有东西模拟. 见 [AddTwo](AddTwo.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddTwoSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; Ωd; AccL; acc; accL; module Fold; ω⋅)
import OCF.Align.TLRuleSum as N
open import OCF.Align.AddCloRel using (Rel; r0; r1; r⨾; rf; rs; rp; rn; rt; ri)
open import OCF.Align.AddCloLeaf using (cmp-rise)
```

## §1 顶层的叶子

`TL x`: 不进任何节点, 沿 `⨾` 的某一边和 `nl` 的某一项, 能走到一个 `n1`.

```agda
data TL {k : A} : D k → Set where
  tl1 : TL n1
  tlL : ∀ {x y} → TL x → TL (x ⨾ y)
  tlR : ∀ {x y} → TL y → TL (x ⨾ y)
  tlN : ∀ {d} n → TL (d n) → TL (nl d)

-- 右边末尾再接东西, 关系不变
weakR : ∀ {k} {c a b : D k} (e : D k) → Rel k c (a ⨾ b) → Rel k c (a ⨾ (b ⨾ e))
weakR e r0 = r0
weakR e (r⨾ d₁ d₂) = r⨾ d₁ (rf d₂)
weakR e (rf d) = rf d
weakR e (rs d) = rs (rf d)
```

## §2 走到第一个顶层叶子

```agda
module First (W : A) (lW : Lg W) (S : ∀ {t} → D t → D t) where
  open Fold W lW S

  -- 原子在 t 上至少是 Ω_t + Z_t
  HA : ∀ {k} → (D k → St → St) → ∀ {t} → t ⊲ W → D t → Set
  HA {k} A₀ {t} τ c = ∀ w (Z : St) → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ Z τ) → Rel t c (A₀ w Z τ)

  first : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) {t} (τ : t ⊲ W) {c : D t} → HA A₀ τ c →
          ∀ w {x} (Z : St) → TL x → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ Z τ) → Rel t c (Run ac kp A₀ w x Z τ)
  firstR : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) {t} (τ : t ⊲ W) {c : D t} →
           ∀ w (d : ℕ → D k) (Z : St) → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ Z τ) → ∀ n → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ proj₂ (Rpt ac kp A₀ w d Z n) τ)

  first ac kp A₀ τ hA w Z tl1 h = hA w Z h
  first ac kp A₀ τ hA w Z (tlL {x} t) h = rf (first ac kp A₀ τ hA w Z t h)
  first ac kp A₀ τ hA w Z (tlR {x} t) h = rs (first ac kp A₀ τ hA (w ⨾ x) (Z ⊕ Run ac kp A₀ w x Z) t (weakR _ h))
  first ac kp A₀ τ hA w Z (tlN {d} n t) h = rn n (first ac kp A₀ τ hA _ (proj₂ (Rpt ac kp A₀ w d Z n)) t (firstR ac kp A₀ τ w d Z h n))

  firstR ac kp A₀ τ w d Z h zero = h
  firstR ac kp A₀ τ w d Z h (suc n) = weakR _ (firstR ac kp A₀ τ w d Z h n)

  -- 顶层叶子走过折叠还在
  tlRun : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) {t} (τ : t ⊲ W) → (∀ w (Z : St) → TL (A₀ w Z τ)) →
          ∀ w {x} (Z : St) → TL x → TL (Run ac kp A₀ w x Z τ)
  tlRun ac kp A₀ τ hT w Z tl1 = hT w Z
  tlRun ac kp A₀ τ hT w Z (tlL t) = tlL (tlRun ac kp A₀ τ hT w Z t)
  tlRun ac kp A₀ τ hT w Z (tlR {x} t) = tlR (tlRun ac kp A₀ τ hT (w ⨾ x) (Z ⊕ Run ac kp A₀ w x Z) t)
  tlRun ac kp A₀ τ hT w Z (tlN {d} n t) = tlN n (tlRun ac kp A₀ τ hT _ (proj₂ (Rpt ac kp A₀ w d Z n)) t)
```

## §3 链

```agda
module Sim (W : A) (lW : Lg W) (S : ∀ {t} → D t → D t)
           (hS : ∀ {t} {c c′ : D t} → Rel t c c′ → Rel t c (S c′))
           (tS : ∀ {t} {c : D t} → TL c → TL (S c)) {j : A} (r : j ≪ W) where
  open Fold W lW S
  open First W lW S

  ρ : j ⊲ W
  ρ = ≪⊲ r

  A₀ : D W → St → St
  A₀ _ Y = Step Y

  hStep : ∀ {k} {t} (τ : t ⊲ W) {c : D t} → HA {k} (λ _ Y → Step Y) τ c
  hStep τ w Z h = hS h

  tStep : ∀ {k} {t} (τ : t ⊲ W) → ∀ (w : D k) (Z : St) → TL (Step Z τ)
  tStep τ w Z = tS (tlL (tlL tl1))

  acj : AccL j
  acj = N.acc≪ W r

  A′ : ∀ w → D j → St → St
  A′ w = Ai (accL W) r C.self acj A₀ w (λ _ → n1)

  -- 链的状态在 t 上只会变长
  chnY : ∀ w (Y′ : St) {t} (τ : t ⊲ W) {c : D t} → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ Y′ τ) →
         ∀ n → Rel t c (Ωd t C.self (lg⊲ τ lW) ⨾ proj₂ (proj₂ (Chn acj ρ (A′ w) Y′ n)) τ)
  chnY w Y′ τ h zero = h
  chnY w Y′ τ h (suc n) = weakR _ (chnY w Y′ τ h n)

  chnT : ∀ w (Y′ : St) → TL (Y′ ρ) → ∀ n → TL (proj₁ (proj₂ (Chn acj ρ (A′ w) Y′ n)))
  chnT w Y′ t zero = t
  chnT w Y′ t (suc n) = tlRun acj ρ (A′ w) ρ (λ w′ Z → tStep ρ w′ Z) _ _ (chnT w Y′ t n)

  simChain : ∀ w (Y′ : St) {t} (τ : t ⊲ j) {c : D t} → Rel t c (Ωd t C.self (lg⊲ (⊲-tr τ ρ) lW) ⨾ Y′ (⊲-tr τ ρ)) → TL (Y′ ρ) →
             Rel t (ω⋅ c) (Run (accL W) C.self A₀ w (ni r (λ _ → n1)) Y′ (⊲-tr τ ρ))
  simChain w Y′ {t} τ {c} h tY =
    subst (λ c₀ → Rel t (ω⋅ c) (RunK (accL W) acj C.self A₀ w r (λ _ → n1) Y′ (⊲-tr τ ρ) c₀))
      (sym (cmp-rise r τ lW))
      (rp (λ n → first acj ρ (A′ w) (⊲-tr τ ρ) (λ w′ Z h′ → hStep (⊲-tr τ ρ) w′ Z h′) _ _ (chnT w Y′ tY n) (chnY w Y′ (⊲-tr τ ρ) h n)))

  -- 一格 S, 再一个节点: 盖住一格 ·ω. 不要另外的前提
  simStep : ∀ w (Y′ : St) {t} (τ : t ⊲ j) {c : D t} → Rel t c (Ωd t C.self (lg⊲ (⊲-tr τ ρ) lW) ⨾ Y′ (⊲-tr τ ρ)) →
            Rel t (ω⋅ c) (Run (accL W) C.self A₀ w (n1 ⨾ ni r (λ _ → n1)) Y′ (⊲-tr τ ρ))
  simStep w Y′ τ h = rs (simChain (w ⨾ n1) (Y′ ⊕ Step Y′) τ (weakR _ h) (tlR (tStep ρ w Y′)))

-- S = ·2 的实例
module Sim·2 (W : A) (lW : Lg W) {j : A} (r : j ≪ W) = Sim W lW (λ c → c) (λ h → h) (λ t → t) r
```

## §4 没有节点的输入: 模拟能一路走下去

`Lf`: 只有 $0$, $1$, 先后, $\omega$-极限的输入. 左边 $\cdot\omega$ 在世界 $j$ 里走 `emb₁ x`; 右边 $\cdot2$ 在世界 $W\rhd j$ 里走 `emb₂ x`, 每个 $1$ 后面接一个 $N_j$. 对 $j$ 以下的一切目标, 左 $\trianglelefteq$ 右 (`leafy`). 这说明 `simStep` 能沿 `⨾`, `nl` 和状态的累积传下去; 断的地方只在链 (见 [AddTwo](AddTwo.lagda.md)).

```agda
data Lf : Set where
  l0 l1 : Lf
  _l⨾_ : Lf → Lf → Lf
  lN : (ℕ → Lf) → Lf

emb₁ : ∀ {k} → Lf → D k
emb₁ l0 = n0
emb₁ l1 = n1
emb₁ (x l⨾ y) = emb₁ x ⨾ emb₁ y
emb₁ (lN d) = nl (λ n → emb₁ (d n))

open import OCF.Align.AddCloRel using (reflΩ; lg-tr)

module Leafy (W : A) (lW : Lg W) {j : A} (r : j ≪ W) where
  module R = Fold W lW (λ c → c)
  module L = Fold j (lg⊲ (≪⊲ r) lW) ω⋅
  open Sim·2 W lW r using (simStep; ρ)

  emb₂ : Lf → D W
  emb₂ l0 = n0
  emb₂ l1 = n1 ⨾ ni r (λ _ → n1)
  emb₂ (x l⨾ y) = emb₂ x ⨾ emb₂ y
  emb₂ (lN d) = nl (λ n → emb₂ (d n))

  RS : L.St → R.St → Set
  RS Y Y′ = ∀ {t} (τ : t ⊲ j) → Rel t (Y τ) (Y′ (⊲-tr τ ρ))

  leafy : ∀ {k} (ac : AccL k) (kp : k ⊲ j) (x : Lf) w w′ (Y : L.St) (Y′ : R.St) → RS Y Y′ →
          RS (L.Run ac kp (λ _ Z → L.Step Z) w (emb₁ x) Y) (R.Run (accL W) C.self (λ _ Z → R.Step Z) w′ (emb₂ x) Y′)
  leafyR : ∀ {k} (ac : AccL k) (kp : k ⊲ j) (d : ℕ → Lf) w w′ (Y : L.St) (Y′ : R.St) → RS Y Y′ → ∀ n →
           RS (proj₂ (L.Rpt ac kp (λ _ Z → L.Step Z) w (λ m → emb₁ (d m)) Y n)) (proj₂ (R.Rpt (accL W) C.self (λ _ Z → R.Step Z) w′ (λ m → emb₂ (d m)) Y′ n))

  leafy ac kp l0 w w′ Y Y′ h τ = r0
  leafy ac kp l1 w w′ Y Y′ h {t} τ =
    simStep w′ Y′ τ (r⨾ (subst (λ l → Rel t (Ωd t C.self (lg⊲ τ (lg⊲ (≪⊲ r) lW))) (Ωd t C.self l)) (sym (lg-tr τ (≪⊲ r) lW)) (reflΩ t C.self _)) (h τ))
  leafy ac kp (x l⨾ y) w w′ Y Y′ h τ =
    r⨾ (leafy ac kp x w w′ Y Y′ h τ)
       (leafy ac kp y _ _ _ _ (λ τ′ → r⨾ (h τ′) (leafy ac kp x w w′ Y Y′ h τ′)) τ)
  leafy ac kp (lN d) w w′ Y Y′ h τ = rp (λ n → leafy ac kp (d n) _ _ _ _ (leafyR ac kp d w w′ Y Y′ h n) τ)

  leafyR ac kp d w w′ Y Y′ h zero = h
  leafyR ac kp d w w′ Y Y′ h (suc n) τ = r⨾ (leafyR ac kp d w w′ Y Y′ h n τ) (leafy ac kp (d n) _ _ _ _ (leafyR ac kp d w w′ Y Y′ h n) τ)
```
