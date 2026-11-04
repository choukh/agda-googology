# 值判据 (五): 不动点行的抽象形式

> **判决: HOLDS.** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). `IsFix F T`: $T$ 是从 $F(1)$ 出发迭代 $x\mapsto F(\mathrm{lv}\,x)$ 的上确界. 这是对 $F$ 相对的值规格: 不提记号, 不提折叠, 只提 $F$. 这里证它确实决定值: 对 $F$ 封闭 (`fix-closed`), 最小 (`fix-least`), 唯一 (`fix-uniq`), 静态的替身过不了 (`fix-static`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeFix where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level
open import OCF.Align.ValueJudgeBase

record IsFix (F : Ordᴵ → Ordᶜ zero) (T : Ordᶜ zero) : Set where
  constructor isFix
  field
    ys    : ℕ → Ordᶜ zero
    hy    : ∀ k → HS (ys k)
    first : ys 0 ≅ F (suc zero)
    next  : ∀ k → ys (suc k) ≅ F (toLevel (ys k) (hy k))
    value : T ≅ lim ys
open IsFix public

-- 结构序的传递
≺-tr : ∀ {ℓ} {d : Ordᶜ ℓ} {c a : Ordᶜ zero} → d ≺ c → c ≺ a → d ≺ a
≺-tr h (≺z e)      = ≺s (≺-respʳ h e)
≺-tr h (≺s q)      = ≺s (≺-tr h q)
≺-tr h (≺l n q)    = ≺l n (≺-tr h q)
≺-tr h (≺i {p = ()} x ex q)
≺-tr h (≺u {r = ()} q)

≺→⊑ : ∀ {c a : Ordᶜ zero} → c ≺ a → c ⊑⁰ a
≺→⊑ q h = ≺-tr h q

module Row {F T} (R : IsFix F T) (Fm : ∀ {a b} → a ⊑ᴵ b → F a ⊑⁰ F b) where
  private
    Y = ys R
    H = hy R

  T⊑ : ∀ {x} → (∀ k → Y k ⊑⁰ x) → T ⊑⁰ x
  T⊑ k h with ≺-respʳ h (value R)
  ... | ≺l n q = k n q

  ⊑T : ∀ k → Y k ⊑⁰ T
  ⊑T k h = ≺-respʳ (≺l k h) (≅-sym (value R))

  -- 封闭: 严格在 T 以下的点, F 不会跳出 T
  fix-closed : ∀ {x} (hx : HS x) → x ≺ T → F (toLevel x hx) ⊑⁰ T
  fix-closed {x} hx q with ≺-respʳ q (value R)
  ... | ≺l n q′ = ⊑-trans (Fm (s⊑-to (toLevel-≺ hx (H n) q′))) (⊑-trans (≅→⊑ (≅-sym (next R n))) (⊑T (suc n)))
    where
    s⊑-to : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
    s⊑-to q₁ = ⊑ᴵ-trans (Sim→⊑ᴵ suc) (s⊑′ q₁)

  -- 最小: 任何 ≥1 且对 F 封闭的点都不低于 T
  fix-least : ∀ {x} (hx : HS x) → suc zero ⊑ᴵ toLevel x hx → F (toLevel x hx) ⊑⁰ x → T ⊑⁰ x
  fix-least {x} hx one Fx = T⊑ go
    where
    go : ∀ k → Y k ⊑⁰ x
    go zero    = ⊑-trans (≅→⊑ (first R)) (⊑-trans (Fm one) Fx)
    go (suc k) = ⊑-trans (≅→⊑ (next R k)) (⊑-trans (Fm (toLevel-⊑ (H k) hx (go k))) Fx)

-- 唯一: F 相同, T 的值相同. 不要 Fm
fix-uniq : ∀ {F T T′} → (∀ {a b} → a ≅ᴵ b → F a ≅ F b) → (R : IsFix F T) (R′ : IsFix F T′) → T ≅ T′
fix-uniq {F} Fc R R′ = ≅-trans (value R) (≅-trans (l≅ go) (≅-sym (value R′)))
  where
  go : ∀ k → ys R k ≅ ys R′ k
  go zero    = ≅-trans (first R) (≅-sym (first R′))
  go (suc k) = ≅-trans (next R k) (≅-trans (Fc (toLevel-≅ (hy R k) (hy R′ k) (go k))) (≅-sym (next R′ k)))
```

**`fix-static`: 静态的替身过不了.** $T\cong F(a)$, $F$ 严格, 链爬过了 $a$: 那么不是 `IsFix`. 这是 `static-rejected` 的机制: 把 $\Omega$-共尾的节点换成 $F$ 在固定点 $a$ 的值. 前提 `crossed` 是链真的爬过 $a$.

```agda
fix-static : ∀ {F T a} (R : IsFix F T) → (∀ {b c} → b ≺ᴵ c → F b ≺ᵛ F c) →
             T ≅ F a → (k : ℕ) → a ≺ᴵ toLevel (ys R k) (hy R k) → ⊥
fix-static {F} {T} {a} R Fs eT k cr =
  ≺ᵛ-irrefl T (≼-trans (s≼s (≅→≼ eT)) (≼-trans (Fs cr)
    (≼-trans (≅→≼ (≅-sym (next R k))) (≼-trans (≼l (suc k) (≼-refl _)) (≅→≼ (≅-sym (value R)))))))
```
