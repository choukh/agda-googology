# 单边迁回的低坐标合同实填

E₀ 允许单边 nw；原 drp 删除世界包装后仍可作为高阶分支的输入。
全部原 D₀ 数据均有自关系，基本列观察保逐形关系。没有假设函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCoordBuild where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import OCF.Align.CumReadCF using (azero; asuc; alim)
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (toD)
open import OCF.Align.EventReturnCoordIf
import OCF.Align.EventReturnValueZero as V

refl₀ : ∀ {W} (x : D₀ W) → E₀ x x
refl₀ n0 = ez
refl₀ n1 = eo
refl₀ (x ⨾ y) = ea (refl₀ x) (refl₀ y)
refl₀ (nl f) = el (λ n → refl₀ (f n))
refl₀ (ni () u)
refl₀ (nκ () u)
refl₀ (nε κ z u) = ⊥-elim (ze0 κ z)
refl₀ (nw p x) = ewL p (ewR p (refl₀ x))

drop-left : ∀ {U V W} {x : D₀ U} {y : D₀ V} → E₀ x y → E₀ (drp {W′ = W} x) y
drop-left ez = ez
drop-left eo = eo
drop-left (ea p q) = ea (drop-left p) (drop-left q)
drop-left (el p) = el (λ n → drop-left (p n))
drop-left (ewL {x = x} {y = y} p q) = drop-left {x = x} {y = y} q
drop-left (ewR p q) = ewR p (drop-left q)

drop-right : ∀ {U V W} {x : D₀ U} {y : D₀ V} → E₀ x y → E₀ x (drp {W′ = W} y)
drop-right ez = ez
drop-right eo = eo
drop-right (ea p q) = ea (drop-right p) (drop-right q)
drop-right (el p) = el (λ n → drop-right (p n))
drop-right (ewL p q) = ewL p (drop-right q)
drop-right (ewR {x = x} {y = y} p q) = drop-right {x = x} {y = y} q

sum-related : ∀ {W W′} {x : D₀ W} {y : D₀ W′} {a b} →
              E₀ x y → V.Same a b → V.Same (sum a x) (sum b y)
pt-related : ∀ {W W′} {f : ℕ → D₀ W} {g : ℕ → D₀ W′} {a b} →
             (∀ n → E₀ (f n) (g n)) → V.Same a b → ∀ n → V.Same (pt a f n) (pt b g n)
sum-related ez p = p
sum-related eo p = V.ss p
sum-related (ea {a = x} {b = y} {a′ = x′} {b′ = y′} r s) p =
  sum-related {x = y} {y = y′} s (sum-related {x = x} {y = x′} r p)
sum-related (el r) p = V.sl (pt-related r p)
sum-related (ewL {x = x} {y = y} q r) p = sum-related {x = x} {y = y} r p
sum-related (ewR {x = x} {y = y} q r) p = sum-related {x = x} {y = y} r p
pt-related r p zero = p
pt-related {f = f} {g = g} r p (suc n) =
  sum-related {x = f n} {y = g n} (r n) (pt-related r p n)

encoded₀ : ∀ {W W′} a → E₀ (toD {W} a) (toD {W′} a)
encoded₀ azero = ez
encoded₀ (asuc a) = ea (encoded₀ a) eo
encoded₀ (alim f) = el (λ n → encoded₀ (f n))
```
