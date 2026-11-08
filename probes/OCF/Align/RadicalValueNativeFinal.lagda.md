# 完成到字面第一位置合法的最终树

保留 TotalOrbit 的整个 ω² 端行输入，不改其运行。其 Ordᴵ 输出先结构
忘到 Cd，再按原 CRw.leg 的相同方程完成。本次完成可能改变值；只证明原输出下界。
最终对象的极限步进是实际 ⊲，不把 Ordᴵ 的 ⊑ᴵ 当作字面第一位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RadicalValueNativeFinal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
import OCF.Free.LiteralCompletion as C
import OCF.Free.Level as L
import OCF.Free.TotalOrbitRun as Run
import OCF.Align.TotalOrbitSource as Producer
open import OCF.Align.LadderOrdPos using (end)

Object : Set
Object = Σ Cd LgB

zeroO : Object
zeroO = hz , tt

sucO : Object → Object
sucO (a , la) = hs a , la

limO : (f : ℕ → Object) →
  (∀ {w} n → proj₁ (f n) ⊲[ w ] proj₁ (f (suc n))) → Object
limO f step = hl (λ n → proj₁ (f n)) , step , (λ n → proj₂ (f n))

data View : Object → Set where
  vz : View zeroO
  vs : (a : Object) → View (sucO a)
  vl : (f : ℕ → Object)
    (step : ∀ {w} n → proj₁ (f n) ⊲[ w ] proj₁ (f (suc n))) → View (limO f step)

view : ∀ a → View a
view (hz , tt) = vz
view (hs a , la) = vs (a , la)
view (hl f , step , legal) = vl (λ n → f n , legal n) step
view (hΩ () g , legal)

FGH : Object → ℕ → ℕ
FGH a = C.FGH (proj₁ a)

fgh-zero : ∀ n → FGH zeroO n ≡ suc n
fgh-zero n = refl
fgh-suc : ∀ a n → FGH (sucO a) n ≡ C.iter (FGH a) n n
fgh-suc a n = refl
fgh-lim : ∀ f step n → FGH (limO f step) n ≡ FGH (f n) n
fgh-lim f step n = refl

forget : L.Ordᴵ → Cd
forget L.zero = hz
forget (L.suc a) = hs (forget a)
forget (L.lim f st) = hl (λ n → forget (f n))

raw : Cd
raw = forget (Run.run (Producer.High.raw end L.zero))

closed : Object
closed = C.leg raw , C.Lg-leg raw

closed-view : View closed
closed-view = view closed

fgh : ℕ → ℕ
fgh = FGH closed

```

View 的分支仍属 Object，极限保留字面第一位置证据；没有函数外延或证明
无关。值比较移至 RadicalValueNativeAccept，不进入本篇导入闭包。
