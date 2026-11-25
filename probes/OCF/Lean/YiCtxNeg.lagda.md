# 同支证据从哪里来: 三处编译的反面

非验收文件. 编译定理, 无前提. (1) 证据来源是裸树上的函数时, 在卡住的那一对的支下标上给出证据就判定与它的字面相等 (`diag1→dec`, `kept→dec`, `kept→decα`). (2) 证据作为逐次出现的标注随折叠走 (`YiCtxAnn.Ψᴹ`), 标注不进第一位置关系时, 合法的输入折出不合法的输出 (`Ψᴹ-not-lgl`); 那份输入不满足带标注的合法性 (`in-not-lglA`).
(3) 块里唯一的作用域 `em` 在加法下打开成完整位置 (`em-flat`); 打开以后, 同支只剩第一坐标字面相同. 不否定: 标注进入合法性 (带标注的树有自己的第一位置关系) 的写法; 改块.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCtxNeg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; R; succ)
open import OCF.Lean.YiLamFold using (Lw)
open import OCF.Lean.YiDlInst using (V2)
open import OCF.Lean.YiZipWay
open import OCF.Lean.YiZipFold using (dl′)
open import OCF.Lean.YiCtxFold using (Ev; SB; evF; module FoldC)
open import OCF.Lean.YiCtxTest using (ηN)
open import OCF.Lean.YiCtxAnn using (Mk; noM; lcM; limM; Pv; noP; An; LglA; module Marked; cmpe₀; ηs; ls; qs; rs; M; ts; μs)
```

## 1 裸树上的证据来源

```agda
Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

IsJust : ∀ {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing = ⊥

diag1→dec : (E : Ev) (k : LF) (η₀ : Raw k) → IsJust (E k η₀ η₀) → ∀ η′ → Dec′ (η₀ ≡ η′)
diag1→dec E k η₀ j η′ = go (E k η₀ η′) refl
  where
  back : ∀ {y} → η₀ ≡ y → E k η₀ y ≡ nothing → ⊥
  back refl h = subst IsJust h j
  go : (u : Maybe (η₀ ≡ η′)) → E k η₀ η′ ≡ u → Dec′ (η₀ ≡ η′)
  go (just e) h = inj₁ e
  go nothing h = inj₂ (λ e → back e h)

kept→dec : ∀ E (e : ηN ≡ ηN) → E zero ηN ηN ≡ just e → ∀ η′ → Dec′ (ηN ≡ η′)
kept→dec E e h = diag1→dec E zero ηN (subst IsJust (sym h) tt)
```

`ηN` 是 `suc` 后接 ℕ 极限 (`YiCtxTest.ηN-form`); `ηα α` 在 `α n` 为真的分量上加一个 `suc`. 相等推出 `α` 处处为假; 反方向要函数外延, 不陈述.

```agda
comp : R → ℕ → R
comp (G.suc (G.lim f)) = f
comp _ = λ _ → G.zero

fN : ℕ → R
fN = comp ηN

ηα : (ℕ → Bool) → R
ηα α = G.suc (G.lim (λ n → if α n then G.suc (fN n) else fN n))

no-suc : ∀ {k} (t : Raw k) → G.suc t ≡ t → ⊥
no-suc (G.suc t) e = no-suc t (cong pd e)
  where
  pd : ∀ {k} → Raw k → Raw k
  pd (G.suc a) = a
  pd a = a
no-suc G.zero ()
no-suc (G.lim f) ()
no-suc (G.lc r g) ()
no-suc (G.em i a) ()
no-suc G.top ()

eq→allF : ∀ α → ηN ≡ ηα α → ∀ n → α n ≡ false
eq→allF α e n = go (α n) (cong (λ t → comp t n) e)
  where
  go : (b : Bool) → fN n ≡ (if b then G.suc (fN n) else fN n) → b ≡ false
  go true e′ = ⊥-elim′ (no-suc (fN n) (sym e′))
    where ⊥-elim′ : ⊥ → true ≡ false
          ⊥-elim′ ()
  go false e′ = refl

kept→decα : ∀ E (e : ηN ≡ ηN) → E zero ηN ηN ≡ just e →
  ∀ α → (∀ n → α n ≡ false) ⊎ (ηN ≡ ηα α → ⊥)
kept→decα E e h α with kept→dec E e h (ηα α)
... | inj₁ q = inj₁ (eq→allF α q)
... | inj₂ q = inj₂ q
```

## 2 逐次出现的证据

`Ψᴹ` 与输入 `ts`, `μs` 见 [YiCtxAnn](YiCtxAnn.lagda.md) §4: 常值序列 `ts, ts, …` (合法), 第 0 项的结点带证据, 第 1 项不带; 输出第 0 项是结点, 第 1 项是极限, 两者互不为第一位置. 这份输入不满足带标注的合法性 (`in-not-lglA`).

```agda
open Marked dl′ evF using (Ψᴹ)

in-legal : Lgl (tw 2) (G.lim (λ _ → ts))
in-legal = (λ n → inj₁ refl) , (λ n → (λ η l → tt) , (λ η η′ l e l′ → inj₁ refl))

out : Raw M
out = Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) (G.lim (λ _ → ts)) (limM μs) noP

out-0 : Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) ts (μs 0) noP ≡ G.lc (inj₁ tt) (λ _ → G.top)
out-0 = refl

out-1 : Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) ts (μs 1) noP ≡ G.lim (λ _ → G.top)
out-1 = refl

inc : Cp M (G.lc (inj₁ tt) (λ _ → G.top)) (G.lim (λ _ → G.top)) → ⊥
inc (inj₁ ())
inc (inj₂ (n , inj₁ ()))
inc (inj₂ (n , inj₂ ()))

out-illegal : Lgl M out → ⊥
out-illegal (st , _) = inc (st 0)

Ψᴹ-not-lgl : (∀ (t : Raw (tw 2)) μ π → Lgl (tw 2) t → Lgl M (Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) t μ π)) → ⊥
Ψᴹ-not-lgl h = out-illegal (h _ (limM μs) noP in-legal)

yes0 : An (SB (tw 2) qs) → Bool
yes0 (G.lc _ _ , lcM (just _) _ , _) = true
yes0 _ = false

in-not-lglA : LglA (SB (tw 2) qs) (G.lim (λ _ → ts)) (limM μs) noP → ⊥
in-not-lglA (st , _) with st 0
... | inj₁ e = tf (cong yes0 e)
  where tf : true ≡ false → ⊥
        tf ()
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
```

## 3 块里的作用域在加法下打开

```agda
em-flat : ∀ (z : Raw (tw 2)) (η : R) (l : Lgl zero η) (a : Raw (up zero η)) →
  plus (tw 2) z (G.em (η , l) a) ≡ add (up zero η) (λ r → G.lc (η , l , r)) z a
em-flat z η l a = refl
```
