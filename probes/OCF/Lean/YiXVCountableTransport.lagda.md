# YiXVCountableTransport
> 验收文件。档位：编译定理。沿原同构证明递归，字面端点相等时原 tr 与 tr⁻ 保持辅助合法性和比较。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableTransport where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.Level as L
import OCF.Lean.YiXVLiteralSim as M
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableMap as Map
import OCF.Lean.YiXVCountablePull as P
import OCF.Lean.YiXVCountableRep as R
import OCF.Lean.YiXVCountableTransportInput as Q

tc : ∀ {a b} (e : a L.≅ᴵ b) {X Y} → X L.≅ Y → L.tr e X L.≅ L.tr e Y
tc e h = L.≅-trans (L.tr-≅ e h) (L.≅-sym (L.tr-≅ e (L.≅-trans (L.≅-sym h) h)))
mc : ∀ {a b} (e : a L.≅ᴵ b) {X Y} → X L.≅ Y → L.tr⁻ e X L.≅ L.tr⁻ e Y
mc e h = L.≅-trans (L.tr⁻-≅ e h) (L.≅-sym (L.tr⁻-≅ e (L.≅-trans (L.≅-sym h) h)))

mutual
  ops : ∀ {a b} (e : a L.≅ᴵ b) (same : a ≡ b) → Q.Ops e same
  Q.Ops.good (ops e same) = Map.Map.good (L.tr e) (plus e same)
  Q.Ops.mono (ops e same) = Map.Map.mono (L.tr e) (plus e same)
  Q.Ops.minus-good (ops e same) = Map.Map.good (L.tr⁻ e) (minus e same)
  Q.Ops.minus-mono (ops e same) = Map.Map.mono (L.tr⁻ e) (minus e same)

  bp : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) → a ≡ b → P.Back (L.res q e)
  P.Back.good (bp L.zero (L.s≅ e) same) = Q.Ops.minus-good (ops e (cong M.pred same))
  P.Back.mono (bp L.zero (L.s≅ e) same) = Q.Ops.minus-mono (ops e (cong M.pred same))
  P.Back.good (bp (L.suc q) (L.s≅ e) same) = P.Back.good (bp q e (cong M.pred same))
  P.Back.mono (bp (L.suc q) (L.s≅ e) same) = P.Back.mono (bp q e (cong M.pred same))
  P.Back.good (bp (L.lim n q) (L.l≅ h) same) = P.Back.good (bp q (h n) (cong (λ a → M.at a n) same))
  P.Back.mono (bp (L.lim n q) (L.l≅ h) same) = P.Back.mono (bp q (h n) (cong (λ a → M.at a n) same))

  bm : ∀ {i a b} (q : i L.<ᴵ b) (e : a L.≅ᴵ b) → a ≡ b → P.Back (L.res⁻ q e)
  P.Back.good (bm L.zero (L.s≅ e) same) = Q.Ops.good (ops e (cong M.pred same))
  P.Back.mono (bm L.zero (L.s≅ e) same) = Q.Ops.mono (ops e (cong M.pred same))
  P.Back.good (bm (L.suc q) (L.s≅ e) same) = P.Back.good (bm q e (cong M.pred same))
  P.Back.mono (bm (L.suc q) (L.s≅ e) same) = P.Back.mono (bm q e (cong M.pred same))
  P.Back.good (bm (L.lim n q) (L.l≅ h) same) = P.Back.good (bm q (h n) (cong (λ a → M.at a n) same))
  P.Back.mono (bm (L.lim n q) (L.l≅ h) same) = P.Back.mono (bm q (h n) (cong (λ a → M.at a n) same))

  pp : ∀ {i a b} (q : i L.<ᴵ a) (e : a L.≅ᴵ b) → a ≡ b → V.Pull {a} {b} q
  pp q e same = P.make q (L.res q e) (R.plus q e same) (bp q e same)
    (R.plus-suc q e) (R.plus-Ω q e) (λ gx → L.back-≅ q e (A.self gx))
  pm : ∀ {i a b} (q : i L.<ᴵ b) (e : a L.≅ᴵ b) → a ≡ b → V.Pull {b} {a} q
  pm q e same = P.make q (L.res⁻ q e) (R.minus q e same) (bm q e same)
    (R.minus-suc q e) (R.minus-Ω q e) (λ gx → L.back⁻-≅ q e (A.self gx))

  cp : ∀ {i a b} (e : a L.≅ᴵ b) → a ≡ b → (r : i L.◃₁ a) → V.Child {a} {b} r (L.tr e L.zero)
  cp {b = L.suc b} (L.s≅ e) same L.zero = record
    { map = λ X → A.Up L.zero (L.tr e X)
    ; good = λ gx → A.Basics.up (L.suc b) L.zero (Q.Ops.good (ops e (cong M.pred same)) gx)
    ; mono = λ h → A.Basics.up-mono (L.suc b) L.zero (Q.Ops.mono (ops e (cong M.pred same)) h)
    ; right = λ gx → A.Basics.z≤ (L.suc b) (A.Basics.up (L.suc b) L.zero (Q.Ops.good (ops e (cong M.pred same)) gx)) }
  cp {b = L.lim g gt} (L.l≅ h) same (L.self n) = record
    { map = λ X → A.Up (L.self n) (L.tr (h n) X)
    ; good = λ gx → A.Basics.up (L.lim g gt) (L.self n) (Q.Ops.good (ops (h n) (cong (λ a → M.at a n) same)) gx)
    ; mono = λ t → A.Basics.up-mono (L.lim g gt) (L.self n) (Q.Ops.mono (ops (h n) (cong (λ a → M.at a n) same)) t)
    ; right = λ gx → A.Basics.z≤ (L.lim g gt) (A.Basics.up (L.lim g gt) (L.self n) (Q.Ops.good (ops (h n) (cong (λ a → M.at a n) same)) gx)) }

  cm : ∀ {i a b} (e : a L.≅ᴵ b) → a ≡ b → (r : i L.◃₁ b) → V.Child {b} {a} r (L.tr⁻ e L.zero)
  cm {a = L.suc a} (L.s≅ e) same L.zero = record
    { map = λ X → A.Up L.zero (L.tr⁻ e X)
    ; good = λ gx → A.Basics.up (L.suc a) L.zero (Q.Ops.minus-good (ops e (cong M.pred same)) gx)
    ; mono = λ h → A.Basics.up-mono (L.suc a) L.zero (Q.Ops.minus-mono (ops e (cong M.pred same)) h)
    ; right = λ gx → A.Basics.z≤ (L.suc a) (A.Basics.up (L.suc a) L.zero (Q.Ops.minus-good (ops e (cong M.pred same)) gx)) }
  cm {a = L.lim f s} (L.l≅ h) same (L.self n) = record
    { map = λ X → A.Up (L.self n) (L.tr⁻ (h n) X)
    ; good = λ gx → A.Basics.up (L.lim f s) (L.self n) (Q.Ops.minus-good (ops (h n) (cong (λ a → M.at a n) same)) gx)
    ; mono = λ t → A.Basics.up-mono (L.lim f s) (L.self n) (Q.Ops.minus-mono (ops (h n) (cong (λ a → M.at a n) same)) t)
    ; right = λ gx → A.Basics.z≤ (L.lim f s) (A.Basics.up (L.lim f s) (L.self n) (Q.Ops.minus-good (ops (h n) (cong (λ a → M.at a n) same)) gx)) }

  ups : ∀ {i a b} (e : a L.≅ᴵ b) (same : a ≡ b) (r : i L.◃₁ a) X →
    L.tr e (A.Up r X) ≡ V.Child.map (cp e same r) X
  ups (L.s≅ e) same L.zero X = refl
  ups (L.l≅ h) same (L.self n) X = refl
  ums : ∀ {i a b} (e : a L.≅ᴵ b) (same : a ≡ b) (r : i L.◃₁ b) X →
    L.tr⁻ e (A.Up r X) ≡ V.Child.map (cm e same r) X
  ums (L.s≅ e) same L.zero X = refl
  ums (L.l≅ h) same (L.self n) X = refl

  plus : ∀ {a b} (e : a L.≅ᴵ b) → a ≡ b → V.View a b (L.tr e)
  plus e same = record
    { zero = A.Layer.gz ; suc = λ X → refl ; lim = λ f → refl
    ; node = λ q → pp q e same ; node-shape = λ q f → refl
    ; up = cp e same ; up-shape = ups e same ; cong = tc e }
  minus : ∀ {a b} (e : a L.≅ᴵ b) → a ≡ b → V.View b a (L.tr⁻ e)
  minus e same = record
    { zero = A.Layer.gz ; suc = λ X → refl ; lim = λ f → refl
    ; node = λ q → pm q e same ; node-shape = λ q f → refl
    ; up = cm e same ; up-shape = ums e same ; cong = mc e }

actual : A.Gd (L.tr (L.s≅ L.z≅) (L.Ω (L.suc L.zero)))
actual = Q.Ops.good (ops (L.s≅ L.z≅) refl) A.oneΩ
```
