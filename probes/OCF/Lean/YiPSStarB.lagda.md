# 理想折叠 ψ★: 换基候选一份

> 验收文件, 不进成品. 编译定义: `YiBSFold.ψ` 的各行, 保留判定换成 `Keep★.kp★ cmpK` (修 K6), `seen` 的内部折叠换成 `Star cmpK cmp₀`; 模块参数 `ctx` 选 `seen` 的底: `false` 是默认底 `B₀` (同 `YiBSBase.seen`), `true` 是带上下文的底 `ctxBase` (地板 j 本身取当前的值 β, 低于 j 的层取外层对 x 的折叠, 偏移层仍取 `Ωt`).
> 经典实例 `IdealB lem ctx`, 闭项 `closed★`; 结论读作 "条件（排中律）". `ctxBase` 是对 MathAB "seen 的默认底是第二处损失" 的改法提案, 未经作者采纳, 本轮没有算它的值.
> 不否定什么; 主线一份在 [YiPSStar](YiPSStar.lagda.md), 转移引理的反例对两份同样适用的部分见 [YiPSNeg](YiPSNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPSStarB where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; node⁺; nodeLe)
open import OCF.Lean.YiRBSib using (rb; rb-ind; rb-ind₂)
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiPSStar using (Cmp; cmp₀; LEM; cmpᴵ; module Keep★; module Star)
```

## 带上下文的底

`split j off` 沿目标路径分出地板上下; 地板本身 (路径是 `self`) 取 β.

```agda
ctxPick : ∀ {j} → Tr⁺ j → ((i : L) → i ≤ j → Tr⁺ i) → ∀ {i} → (i ≤ j) ⊎ (j ≤ i) → Tr⁺ i
ctxPick βj low (inj₁ self)      = βj
ctxPick βj low (inj₁ (inc c v)) = low _ (inc c v)
ctxPick βj low (inj₁ (inu vs))  = low _ (inu vs)
ctxPick βj low (inj₁ (ink v))   = low _ (ink v)
ctxPick βj low (inj₂ _)         = Ωt _

ctxBase : (j off : L) → OkO j off → Tr⁺ j → ((i : L) → i ≤ j → Tr⁺ i) → Base (j ⊕ off)
ctxBase j off ob βj low i w = ctxPick βj low (split j off ob w)

pickB : ∀ {A : Set} → Bool → A → A → A
pickB true  a b = a
pickB false a b = b
```

## seen 与折叠

```agda
module StarB (cmpK : Cmp) (ctx : Bool) where
  open Keep★ cmpK using (kp★)
  module I = Star cmpK cmp₀

  okS : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → (c : Tr k) → Ok (j ⊕ offsets S c)
  okS S j oj u c = Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))

  seen★ : ∀ {k h} (S : Schema k h) (j : L) (oj : Ok j) (u : floor S ≤ j) (c : Tr k)
        → Base (j ⊕ offsets S c) → Tr⁺ j → Tr⁺ j
  seen★ S j oj u c Bs β =
    I.ψ★ (j ⊕ offsets S c) (okS S j oj u c) Bs j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))

  seen-step★ : ∀ {k h} (S : Schema k h) j oj u c Bs β → j ⊢ proj₁ β ◃ proj₁ (seen★ S j oj u c Bs β)
  seen-step★ S j oj u c Bs β =
    I.mono★ (j ⊕ offsets S c) (okS S j oj u c) Bs j (lift j (offsets S c)) β (proj₂ (Ωt (j ⊕ offsets S c)))

  mutual
    ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
    ψ ℓ o r B j w β zero      = β
    ψ ℓ o r B j w β (suc x)   = next⁺ (ψ ℓ o r B j w β x)
    ψ ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o r B j w β (f n)) (λ n → mono ℓ o r B j w β (a n))
    ψ ℓ o r B j w β (Ω p g)   = node⁺ (kp★ ℓ o p w) (λ z → ψ ℓ o r B j w β (g z))
      (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    ψ (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y
    ψ (nd s h) o r B j (inu ws) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
    ψ (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
    ψ (nd sS h) o r B j (inc c′ v) β (up x c y e) =
      ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
    ψ (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
      (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) y)
    ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = rb (proj₁ r)
      (λ S → cW (route S j c′ v)
        (λ u → ψ (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
        (λ u → seen★ S j (downOk (h c′) (proj₂ o c′) j v) u c
          (pickB ctx
            (ctxBase j (offsets S c) (raiseO (floor S) j (offsets S c) u (ok-offsets S c))
              (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x)
              (λ i w′ → ψ (nd (sΩ k) h) o r B i (inc c′ (w′ ∙ v)) (B i (inc c′ (w′ ∙ v))) x))
            (B₀ _))
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x)
          ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
      (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

    mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
         → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)
    mono ℓ o r B j w β ◃s           = ◃l zero
    mono ℓ o r B j w β (◃l n)       = ◃l n
    mono ℓ o r B j w β (◃w {p = p}) = nodeLe (kp★ ℓ o p w) _ _
    mono (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) e
    mono (nd s h) o r B j (inu ws) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) e
    mono (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) e
    mono (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) e
    mono (nd sL g) o r B j (inc n v) β (◃u x m y e) =
      cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o r B j (inc n v) β x) e)
    mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
      rb-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₁ r)
        (λ S → cW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (route S j c′ v)
          (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
            (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
            (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
          (λ u → ◃t (seen-step★ S j (downOk (h c′) (proj₂ o c′) j v) u c _ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x))
            (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))))
        (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))
    mono (nd s h) o r B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) d
    mono (nd s h) o r B j (inu ws) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) d
    mono (nd (sΩ k) h) o r B j (ink v) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ (nd (sΩ k) h) o r B j (ink v) β x) d
    mono (nd sS h) o r B j (inc c′ v) β (◃c x c d) =
      mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) d
    mono (nd sL g) o r B j (inc n v) β (◃c x m d) =
      cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
        (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
        (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ (nd sL g) o r B j (inc n v) β x) d)
    mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c d) =
      rb-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r)
        (λ S → cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (route S j c′ v)
          (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
            (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
            (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) d)
          (λ u → +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d))))
        (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
    mono ℓ o r B j w β (◃t d d′) = ◃t (mono ℓ o r B j w β d) (mono ℓ o r B j w β d′)

  ψ₀ : (ℓ : L) → Ok ℓ → Rb ℓ → Tr ℓ → Tr⁺ zero
  ψ₀ ℓ o r = ψ ℓ o r (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

  closed★ : (n : ℕ) → Tr⁺ zero
  closed★ n = ψ₀ (tw n) (Ok-tw n) (rb-tw n) (proj₁ (Ωt (tw n)))

module IdealB (lem : LEM) (ctx : Bool) = StarB (cmpᴵ lem) ctx
```

默认底时 `seen★` 与 `YiBSBase.seen` 逐字同形 (内部折叠换成 ψ★ 的同一组行); 带上下文时, 地板本身的底是 β.

```agda
seen-default : ∀ (cmpK : Cmp) {k h} (S : Schema k h) j oj u c β
  → StarB.seen★ cmpK false S j oj u c (B₀ _) β
  ≡ Star.ψ★ cmpK cmp₀ (j ⊕ offsets S c) (StarB.okS cmpK false S j oj u c) (B₀ _) j (lift j (offsets S c)) β
      (proj₁ (Ωt (j ⊕ offsets S c)))
seen-default cmpK S j oj u c β = refl

ctx-floor : ∀ j (βj : Tr⁺ j) (low : (i : L) → i ≤ j → Tr⁺ i) → ctxPick βj low (inj₁ (self {ℓ = j})) ≡ βj
ctx-floor j βj low = refl
```
