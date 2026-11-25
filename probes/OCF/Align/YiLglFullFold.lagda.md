# 四处严格下的 ψ 各行条件接口

在 FullCore／FullVal 上只取 JiaExactFold 的 copies、逐点极限、保留与 gt 输出形状作检验。
不实现 ψ 或 γ；go／out／step 是参数，严格性和合法性的前提逐项显式给出。
这些规则形状来自照 EBO 基本列写的甲模板，不称树侧独立推出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.YiLglFullCore as F
open import OCF.Align.YiLglFullVal using (CP)
import OCF.Align.YiLglFullVal as V
open import OCF.Align.YiLglFullVal
  using (Properˢ; Legal; weak; under-suc; under-lim; under-first; Ω-proper; Legal-Ω̂)

iter : ∀ {A : Set} → (A → A) → A → ℕ → A
iter step start zero = start
iter step start (suc n) = step (iter step start n)

copies : F.LF → ℕ → F.LF
copies x = iter (V._+ᴸ_ x) F.zero

Nonzero : F.LF → Set
Nonzero F.zero = ⊥
Nonzero (F.suc x) = ⊤
Nonzero (F.lim f) = ⊤
Nonzero (F.lc k c t g) = ⊤

Ω-nonzero : ∀ x → Nonzero (V.Ω̂ x)
Ω-nonzero F.zero = tt
Ω-nonzero (F.suc x) = tt
Ω-nonzero (F.lim f) = tt
Ω-nonzero (F.lc k c t g) = tt

zero-CP : ∀ x → CP F.zero x
zero-CP F.zero = V.self
zero-CP (F.suc x) = V.suc (zero-CP x)
zero-CP (F.lim f) = V.lim zero (zero-CP (f zero))
zero-CP (F.lc k c t g) = V.fst (zero-CP t)

zero-proper : ∀ x → Nonzero x → Properˢ F.zero x
zero-proper (F.suc x) p = under-suc (zero-CP x)
zero-proper (F.lim f) p = under-lim zero (zero-CP (f zero))
zero-proper (F.lc k c t g) p = under-first (zero-CP t)

add-proper : ∀ x {a b} → Properˢ a b → Properˢ (V._+ᴸ_ x a) (V._+ᴸ_ x b)
add-proper x (under-suc p) = under-suc (V.add-CP x p)
add-proper x (under-lim n p) = under-lim n (V.add-CP x p)
add-proper x (under-first p) = under-first (V.add-CP x p)

add-legal : ∀ x a → Legal x → Legal a → Legal (V._+ᴸ_ x a)
add-legal x F.zero lx la = lx
add-legal x (F.suc a) lx la = add-legal x a lx la
add-legal x (F.lim f) lx (step , lawful) =
  (λ n → add-proper x (step n)) , (λ n → add-legal x (f n) lx (lawful n))
add-legal x (F.lc k c t g) lx (lk , first , mono , same , lt , lg) =
  lk , (λ η e → V.add-CP x (first η e)) ,
  (λ η e η′ e′ d → V.add-proper x (mono η e η′ e′ d)) ,
  (λ η e e′ → cong (V._+ᴸ_ x) (same η e e′)) ,
  add-legal x t lx lt , (λ η e → add-legal x (g η e) lx (lg η e))

copies-step : ∀ x → Nonzero x → ∀ n → Properˢ (copies x n) (copies x (suc n))
copies-step x nonzero zero = zero-proper x nonzero
copies-step x nonzero (suc n) = add-proper x (copies-step x nonzero n)

copies-legal : ∀ x → Legal x → ∀ n → Legal (copies x n)
copies-legal x lawful zero = tt
copies-legal x lawful (suc n) = add-legal x (copies x n) lawful (copies-legal x lawful n)

successor : F.LF → F.LF
successor x = F.lim (copies x)

successor-legal : ∀ x → Legal x → Nonzero x → Legal (successor x)
successor-legal x lawful nonzero = copies-step x nonzero , copies-legal x lawful

record StrictMap (go : F.LF → F.LF) : Set where
  field
    legal-map : ∀ x → Legal x → Legal (go x)
    proper-map : ∀ {a b} → Properˢ a b → Properˢ (go a) (go b)
open StrictMap public

cp-map : ∀ {go} → StrictMap go → ∀ {a b} → CP a b → CP (go a) (go b)
cp-map m V.self = V.self
cp-map m (V.suc p) = weak (proper-map m (under-suc p))
cp-map m (V.lim n p) = weak (proper-map m (under-lim n p))
cp-map m (V.fst p) = weak (proper-map m (under-first p))

omega-map : StrictMap V.Ω̂
legal-map omega-map = Legal-Ω̂
proper-map omega-map = Ω-proper

limit-legal : ∀ {go} → StrictMap go → ∀ f → Legal (F.lim f) →
  Legal (F.lim (λ n → go (f n)))
limit-legal m f (step , lawful) =
  (λ n → proper-map m (step n)) , (λ n → legal-map m (f n) (lawful n))

keep-legal : ∀ {go} → StrictMap go → ∀ k c t g → Legal (F.lc k c t g) →
  Legal (F.lc k c (go t) (λ η e → go (g η e)))
keep-legal {go} m k c t g (lk , first , mono , same , lt , lg) =
  lk , (λ η e → cp-map m (first η e)) ,
  (λ η e η′ e′ d → proper-map m (mono η e η′ e′ d)) ,
  (λ η e e′ → cong go (same η e e′)) ,
  legal-map m t lt , (λ η e → legal-map m (g η e) (lg η e))

-- 三种 Proper 构造子的输出位置义务。collapse 的 p 要由源第一支和递归 CP 保持给出。
successor-position : ∀ {a b} → CP a b → Properˢ a (successor b)
successor-position p = under-lim 1 p

limit-position : ∀ {a f} n → CP a (f n) → Properˢ a (F.lim f)
limit-position = under-lim

keep-position : ∀ {a k c t g} → CP a t → Properˢ a (F.lc k c t g)
keep-position = under-first

collapse-position : ∀ {A : Set} (out : A → F.LF) step start {a} →
  CP a (out start) → Properˢ a (F.lim (λ n → out (iter step start n)))
collapse-position out step start p = under-lim zero p

-- 链的严格性与 out 的严格性分开。R 可以实例化为链点的 Properˢ。
chain-output-legal : ∀ {A : Set} (R : A → A → Set)
  (step : A → A) (start : A) (out : A → F.LF) →
  (∀ a → R a (step a)) →
  (∀ {a b} → R a b → Properˢ (out a) (out b)) →
  (∀ a → Legal (out a)) →
  Legal (F.lim (λ n → out (iter step start n)))
chain-output-legal R step start out next monotone lawful =
  (λ n → monotone (next (iter step start n))) , (λ n → lawful (iter step start n))

nat-legal : ∀ n → Legal (V.natF n)
nat-legal zero = tt
nat-legal (suc n) = nat-legal n

-- 所有条件合同都有实例；这里只为链合同给自然数结构路径，不作 ψ 或 γ 的实例。
chain-instance : Legal (F.lim (λ n → V.natF (iter suc zero n)))
chain-instance = chain-output-legal (λ n m → Properˢ (V.natF n) (V.natF m))
  suc zero V.natF (λ n → under-suc V.self) (λ p → p) nat-legal
```

加法在右参数递归；copies x (n+1)=x+copies x n。
不能直接把“追加后含原左前缀”错当成所需步进：本篇以 zero→x 为基步，
再用固定左参数的 add-proper 归纳。Nonzero 只排除语法零，不作值上的正性判定。
Ω 种子由 Ω-nonzero 给此前提；其它输出行根构造子也不是零。

StrictMap 的非空实例是 omega-map，链合同的实例是 chain-instance；
它们并不证明满足 ψ 规则的 go 已获得这些合同。
Proper 的后继／极限／第一支三行可由上面的 position 引理归纳给出；
gt 的列严格性还需要 next 与 out 的 monotone；新的源严格分支可以提供后者的一部分，仍不能自动给 γ 的增长。
