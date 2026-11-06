# Third (八): 值的定理: 固定世界里的高度序嵌入可数树; 损失的形状

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **这一篇回答 "闭项 `TΛ` 的值".** 没有下界定理. 有的是一条**上限性质的结构定理**: `rk-⊲`: 在任一站的固定世界里, 合法高度的第一位置序经 `rk` 保序地映进可数树 `Cd`. 折叠在一站里世界 $w$ 不动 (只有界 $B$ 动), 所以一站里看到的塔高度的序是可数树的序的像. 这是本路闭项读法低于 $\psi_0\Lambda$ 的主要依据 (判断, 见入口).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw
open import OCF.Lean.ThirdLeg
```

## §1 固定世界里高度的序是可数的

前提: 每个种类有代表坐标 `pk`, 在世界的界之下, 界之下的坐标都是它的第一位置. `rk` 在 $\Omega$-结点处取代表坐标的分支.

```agda
module Rk (U : KS) (w : Wd U) (lw : LgW U w) (pk : (κ : K U) → E U κ)
          (pkb : ∀ κ → Bd U κ (pk κ) w) (top : ∀ κ e → Bd U κ e w → Pr U κ w e (pk κ)) where
  rk : HB U → Cd
  rk hz = hz
  rk (hs x) = hs (rk x)
  rk (hl f) = hl (λ n → rk (f n))
  rk (hΩ κ g) = rk (g (pk κ))

  rk-⊲ : ∀ m {a} → _⊲[_]_ {U} a w m → LgB m → rk a ⊲ rk m
  rk-⊲ m hself l = hself
  rk-⊲ (hs b) (hsuc p) l = hsuc (rk-⊲ b p l)
  rk-⊲ (hl f) (hlim n p) (st , l) = hlim n (rk-⊲ (f n) p (l n))
  rk-⊲ (hΩ κ g) (hLim {c = c} b p) (mo , l) =
    ⊲ᴮ-tr {S⊥} (rk-⊲ (g c) p (l lw b)) (rk-⊲ (g (pk κ)) (mo lw b (pkb κ) (top κ c b)) (l lw (pkb κ)))

-- 每一站的世界都满足前提
module Stage (c₀ : Cd) (lc₀ : LgB c₀) (n : ℕ) where
  open W c₀ lc₀
  open Rk (Sb n) (wS n) (lwS n) (pkS n) (pk-bd n) (pk-top n) public
```

## §2 损失的形状

`er-drop`: 洗法把穿过 $\Omega$-分量的结点整个换成 $0$. `leg-const`: 合法化在分量种类的结点上是常值分支. `slot-zero`: 分量种类 (第 $c$ 个分量的顶新种类) 在世界里的界是 $0$: 只有坐标 $0$ 在界之下.

```agda
open import OCF.Lean.ThirdSan using (san)

er-drop : ∀ U w lw fb (κ₀ : K U) (g : E U κ₀ → HB U) (κ : Σ (E U κ₀) (λ e → K (Tw U (g e)))) (h : E (Tw U (hΩ κ₀ g)) κ → HB (Tw U (hΩ κ₀ g))) →
          san U w lw fb (hΩ κ₀ g) (hΩ κ h) ≡ hz
er-drop U w lw fb κ₀ g κ h = refl

leg-const : ∀ n c (κ : K (Tw (Sb n) (hs c))) (h : E (Tw (Sb n) (hs c)) κ → HB (XSof (Sb n))) →
            legS (suc n) (hΩ (inj₂ c , κ) h) ≡ hΩ (inj₂ c , κ) (λ _ → legS (suc n) (h (bot (XSof (Sb n)) (inj₂ c , κ))))
leg-const n c κ h = refl

slot-zero : ∀ c₀ lc₀ n c (e : HB (Tw (Sb n) c)) →
            _⊲[_]_ {Tw (Sb n) c} e (W.wS c₀ lc₀ (suc n) (inj₂ c) .proj₁) hz → e ≡ hz
slot-zero c₀ lc₀ n c .hz hself = refl
```
