# 原 κ₁ 首格后继内枝的迁回观察

先处理 κ₀ 保留回调的全部未来事件后缀，再应用到旧 Step.output。
不改原输出，不以零内枝代替，不使用函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedValueStep where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Align.CumReadCF using (Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCtxValueIf
open import OCF.Align.EventReturnCtxValueRun using (returned)
open import OCF.Align.EventReturnCtxValueActual using (floor₂)
open import OCF.Align.EventReturnHistory
open import OCF.Align.EventReturnHistoryCompose using (shape-reverse)
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventOneWalk using (length; counted; counted-related) renaming (length-pair to same-length)
import OCF.Align.EventOneWalk as One
import OCF.Align.EvFoldClosed as Closed
import OCF.Align.EventReturnValueCell as Base
import OCF.Align.EventReturnValueStep as Original
open Base.R
module Walk = One.At Closed.three tt (hsuc (hsuc hself)) (hsuc hself)

kp-count : ∀ {ly W₀ W W⁺ m} (ac : AccY ly) (q₀ : W₀ ≤ W)
  (ll : LW ly W) (w : D ly W) (Y : St W) (wu : W ≤ W⁺) (lW⁺ : LgWε W⁺)
  (T : Tg W⁺ (hs (hs hz)) m) →
  yc (Kpε ac (λ _ _ → n1) q₀ ll Act w Y wu lW⁺) T ≡
  counted (length (proj₂ (≤tr q₀ wu))) (yc (d Y) (tg↑ wu T))
kp-count ac q₀ ll w Y wu lW⁺ T =
  Walk.walk ac (proj₁ (≤tr q₀ wu)) here (proj₂ (≤tr q₀ wu)) here
    lW⁺ (⊲ᴮ↑ wu ll) (nw wu w) (cv wu Y) T

kb-count : ∀ {ly W₀ W W⁺ W′ m} (ac : AccY ly) (q₀ : W₀ ≤ W)
  (ll : LW ly W) (w : D ly W) (Y : St W) (wu : W ≤ W⁺) (lW⁺ : LgWε W⁺)
  (q : W⁺ ≤ W′) (lW′ : LgWε W′) (T : Tg W′ (hs (hs hz)) m) →
  yc (Kbε ac (λ _ _ → n1) q₀ ll Act w Y wu lW⁺ q lW′) T ≡
  nl (λ _ → Ωd (hs (hs hz)) ⨾
    ((yc (d Y) (tg↑ wu (tg↑ q T)) ⨾
      counted (length (proj₂ (≤tr q₀ wu))) (yc (d Y) (tg↑ wu (tg↑ q T)))) ⨾
      counted (length (proj₂ q))
        (yc (d Y) (tg↑ wu (tg↑ q T)) ⨾
         counted (length (proj₂ (≤tr q₀ wu))) (yc (d Y) (tg↑ wu (tg↑ q T))))))
kb-count ac q₀ ll w Y wu lW⁺ q lW′ T
  rewrite Walk.walk ac (proj₁ (≤tr (≤tr q₀ wu) q)) (proj₂ (≤tr q₀ wu))
    (proj₂ q) here lW′ (⊲ᴮ↑ (≤tr wu q) ll)
    (nw q (nw wu w ⨾ CutE (λ _ _ → n1) (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺)
      here (proj₂ (≤tr q₀ wu)) here))
    (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kpε ac (λ _ _ → n1) q₀ ll Act w Y wu lW⁺)) T
  rewrite kp-count ac q₀ ll w Y wu lW⁺ (tg↑ q T) = refl
```

原外层首格的前缀与状态包含真实的零段包装，以下逐字保留它们。

```agda
Wcell : Wε
Wcell = Closed.one , hc Original.cell

rise₀ : Closed.W₁ ≤ Wcell
rise₀ = C.self , wc Original.cell

prefix₀ : D Closed.three Wcell
prefix₀ = nw rise₀ n0 ⨾ n0

state₀ : St Wcell
state₀ = cv rise₀ Base.state ⊕⟨ (tt , tt) ⟩ zeroD

base : ∀ {W} → D₂ W
base = (n0 ⨾ nl (λ _ → Ωd (hs (hs hz)) ⨾ n0)) ⨾ n0

base-related : ∀ {a H H′} → R₂ a H H′ base base
base-related = ra (ra rz (rl (λ _ → ra floor₂ rz))) rz

callback : ∀ {W′} → Wcell ≤ W′ → LgWε W′ → D₂ W′
callback q l = yc (Kbε accᴸ (λ _ _ → n1) rise₀ hself Act prefix₀ state₀
  ≤rf (tt , tt) q l) (τ₂ l)

retained : D₂ Wcell
retained = yc (RunE accᴸ κ₀ (λ _ _ → n1) rise₀ (tt , tt) hself Act
  prefix₀ state₀) (τ₂ (tt , tt))

output-shape : Original.output ≡ n0 ⨾ retained
output-shape = refl

retained-shape : retained ≡ counted 1 base ⨾ nε κ₀ tt callback
retained-shape = refl

callback-shape : ∀ {W′} (q : Wcell ≤ W′) (l : LgWε W′) →
  callback q l ≡ nl (λ _ → Ωd (hs (hs hz)) ⨾
    ((base ⨾ counted 1 base) ⨾ counted (length (proj₂ q)) (base ⨾ counted 1 base)))
callback-shape q l = kb-count accᴸ rise₀ hself prefix₀ state₀ ≤rf (tt , tt) q l (τ₂ l)
```

回调的量词覆盖全部原未来后缀；只通过同步后缀的长度相等耦合
两次 counted。回调中的状态累计不是常数，也未略去新增事件。

```agda
prefix-related : ∀ {a H H′} →
  R₂ a H H′ (base ⨾ counted 1 base) (base ⨾ counted 1 base)
prefix-related = ra base-related (counted-related base-related 1)

callback-related : ∀ {b J J′} (p : Closed.one C.⊲ b)
  (s : Suf (hc Original.cell) J) (s′ : Suf (hc Original.cell) J′) → Suffix s s′ →
  (lb : Lg b) → R₂ b J J′ (callback (p , s) (lb , tt)) (callback (p , s′) (lb , tt))
callback-related {b} {J} {J′} p s s′ sr lb =
  subst₂ (R₂ b J J′) (sym (callback-shape (p , s) (lb , tt)))
    (sym (callback-shape (p , s′) (lb , tt)))
    (rl (λ _ → ra floor₂ (ra prefix-related counted-pair)))
  where
  counted-pair : R₂ b J J′
    (counted (length s) (base ⨾ counted 1 base))
    (counted (length s′) (base ⨾ counted 1 base))
  counted-pair = subst
    (λ n → R₂ b J J′ (counted (length s) (base ⨾ counted 1 base))
                     (counted n (base ⨾ counted 1 base)))
    (same-length sr) (counted-related prefix-related (length s))

retained-related : R₂ Closed.one (hc Original.cell) (hc Original.cell) retained retained
retained-related = ra (counted-related base-related 1) (re callback-related)

output-related : R₂ Closed.one (hc Original.cell) (hc Original.cell) Original.output Original.output
output-related = ra rz retained-related

output-returned : ∀ b →
  Shape (rd₂ (tt , tt) b Original.output)
        (rd₂ {Closed.W₁} (tt , tt) b (drp₂ Original.output))
output-returned b = shape-reverse (returned tt output-related b)
```

这补掉旧 Step 文件中 refl 退出 42 的悬案，结论是逐枝 Shape，
不是函数等式。范围是这一个原输出、经全部未来后缀的回调证明；
没有据此宣称任意 Run 或整个 κ₁ 反馈链已满足关系。
