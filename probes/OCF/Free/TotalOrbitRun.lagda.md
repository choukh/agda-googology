# 累积解释器的纯运行核心

从本轮 TotalOrbitBuild 原样搬出 add、部分和与 run。算法和递归方程
不变；表示转换及其证明不再进入只需要 run 的生产模块。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.TotalOrbitRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)

-- 只递归右参数。单调律用已经给出的 ⊑ᴵ，不比较裸层号。
add : Ordᴵ → Ordᴵ → Ordᴵ
add-mono : ∀ a {b c} → b ⊑ᴵ c → add a b ⊑ᴵ add a c

add a zero = a
add a (suc b) = suc (add a b)
add a (lim f st) = lim (λ n → add a (f n)) (λ n → add-mono a (st n))

add-cong : ∀ a {b c} → b ≅ᴵ c → add a b ≅ᴵ add a c
add-cong a z≅ = ≅ᴵ-refl a
add-cong a (s≅ e) = s≅ (add-cong a e)
add-cong a (l≅ h) = l≅ (λ n → add-cong a (h n))

add-path : ∀ a {b c} → b <ᴵ c → add a b <ᴵ add a c
add-path a zero = zero
add-path a (suc q) = suc (add-path a q)
add-path a (lim n q) = lim n (add-path a q)

prefix-path : ∀ a b {x} → x <ᴵ a → x <ᴵ add a b
prefix-path a zero q = q
prefix-path a (suc b) q = suc (prefix-path a b q)
prefix-path a (lim f st) q = lim 0 (prefix-path a (f 0) q)

prefix : ∀ a b → a ⊑ᴵ add a b
prefix a b = Sim→⊑ᴵ (prefix-path a b)

add-mono a z⊑ = prefix a _
add-mono a (s⊑ e q) = s⊑ (add-cong a e) (add-path a q)
add-mono a (l⊑ h) = l⊑ (λ n → add-mono a (h n))

sum : (ℕ → Ordᴵ) → ℕ → Ordᴵ
sum f zero = f 0
sum f (suc n) = add (sum f n) (f (suc n))

complete : (ℕ → Ordᴵ) → Ordᴵ
complete f = lim (sum f) (λ n → prefix (sum f n) (f (suc n)))

run : Z → Ordᴵ
run Z.zero = zero
run (Z.suc x) = suc (run x)
run (Z.lim f) = complete (λ n → run (f n))
run (ĉᴸ c t g o₀ o) = complete outputs
  where
  coord : ℕ → Ordᴵ
  coord-bound : ∀ n → c ⊑ᴵ coord n
  coord zero = add c (run t)
  coord (suc n) = add c (run (g (coord n) (coord-bound n)))
  coord-bound zero = prefix c (run t)
  coord-bound (suc n) = prefix c (run (g (coord n) (coord-bound n)))

  outputs : ℕ → Ordᴵ
  outputs zero = run o₀
  outputs (suc n) = run (o (coord n) (coord-bound n))

```
