# YiLvFold 底座一：对层号一般的加法

**档位：定义与编译定理，没有折叠。** 一个加法 `add`，对加数所在的层号 `k` 与加数递归，值域是任意带结点构造的类型 (`Alg k`)；
取 `Alg` 为 `Raw m` 自己就是第 `m` 层的加法 `plus`，对一切 `Plain` 的层号 (零、后继、ℕ 极限)。引理：保持第一位置、弱增长、
严格增长、合法性、嵌套证据。不否定任何路线；入口 [YiLvFold](YiLvFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFoldAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiLvIf using (Plain)
```

## 1 值域的接口

加数 `em a` 是低一层的值，`top` 展开成低一层槽位的结点；递归到低层时，输出仍在原来的层里，只是槽位换成
`inj₂ r` 或 `(n , r)`。`Low (suc k) (inj₂ r)` 与 `Low k r` 是定义性相等的，所以把 "在槽位 `r` 上造结点" 作为参数传下去，
不需要搬运。`Alg k` 就是这份参数，连同证明要用的第一位置、合法性、嵌套证据、头的正性。

```agda
record Alg (k : LF) : Set₁ where
  field
    T : Set
    sT : T → T
    lT : (ℕ → T) → T
    nT : (r : Pre k) (c : Low k r) → T →
         ((η : Low k r) → .(GdL k r c η) → T) → T
    Dnᵀ : T → T → Set
    Lgᵀ Nsᵀ Psᵀ : T → Set
  Cpᵀ : T → T → Set
  Cpᵀ a d = (a ≡ d) ⊎ Dnᵀ a d
  field
    dnS : ∀ {a d} → Cpᵀ a d → Dnᵀ a (sT d)
    dnL : ∀ {a f} n → Cpᵀ a (f n) → Dnᵀ a (lT f)
    dnN : ∀ {a} r c t g → Cpᵀ a t → Dnᵀ a (nT r c t g)
    lgS : ∀ {a} → Lgᵀ a → Lgᵀ (sT a)
    lgL : ∀ {f} → (∀ n → Cpᵀ (f n) (f (suc n))) → (∀ n → Lgᵀ (f n)) → Lgᵀ (lT f)
    lgN : ∀ r c t g →
      (∀ η (e : GdL k r c η) → Cpᵀ t (g η e)) →
      (∀ η (e : GdL k r c η) η′ (e′ : GdL k r c η′) → GdL k r η η′ →
        Cpᵀ (g η e) (g η′ e′)) →
      Lgᵀ t → (∀ η (e : GdL k r c η) → Lgᵀ (g η e)) → Lgᵀ (nT r c t g)
    nsS : ∀ {a} → Nsᵀ a → Nsᵀ (sT a)
    nsL : ∀ {f} → (∀ n → Nsᵀ (f n)) → Nsᵀ (lT f)
    nsN : ∀ r c t g → LglLow k r c → NestedLow k r c → Nsᵀ t →
      (∀ η (e : GdL k r c η) → Nsᵀ (g η e)) → Nsᵀ (nT r c t g)
    psS : ∀ {a} → Psᵀ (sT a)
    psL : ∀ {f} → Psᵀ (lT f)
    psN : ∀ r c t g → Psᵀ (nT r c t g)

shS : ∀ {k} → Alg (suc k) → Alg k
shS A = record
  { T = T; sT = sT; lT = lT; nT = λ r → nT (inj₂ r)
  ; Dnᵀ = Dnᵀ; Lgᵀ = Lgᵀ; Nsᵀ = Nsᵀ; Psᵀ = Psᵀ
  ; dnS = dnS; dnL = dnL; dnN = λ r → dnN (inj₂ r)
  ; lgS = lgS; lgL = lgL; lgN = λ r → lgN (inj₂ r)
  ; nsS = nsS; nsL = nsL; nsN = λ r → nsN (inj₂ r)
  ; psS = psS; psL = psL; psN = λ r → psN (inj₂ r) }
  where open Alg A

shL : ∀ {f} → Alg (lim f) → ∀ n → Alg (f n)
shL A n = record
  { T = T; sT = sT; lT = lT; nT = λ r → nT (n , r)
  ; Dnᵀ = Dnᵀ; Lgᵀ = Lgᵀ; Nsᵀ = Nsᵀ; Psᵀ = Psᵀ
  ; dnS = dnS; dnL = dnL; dnN = λ r → dnN (n , r)
  ; lgS = lgS; lgL = lgL; lgN = λ r → lgN (n , r)
  ; nsS = nsS; nsL = nsL; nsN = λ r → nsN (n , r)
  ; psS = psS; psL = psL; psN = λ r → psN (n , r) }
  where open Alg A

-- 头不是 zero, 不是嵌入.
Pos : ∀ k → Raw k → Set
Pos k G.zero = ⊥
Pos k (G.suc y) = ⊤
Pos k (G.lim f) = ⊤
Pos k (G.lc r c t g) = ⊤
Pos k (G.em i a) = ⊥
Pos k G.top = ⊤

rawAlg : ∀ m → Alg m
rawAlg m = record
  { T = Raw m; sT = G.suc; lT = G.lim; nT = G.lc
  ; Dnᵀ = Dn m; Lgᵀ = Lgl m; Nsᵀ = Nested m; Psᵀ = Pos m
  ; dnS = λ p → p; dnL = λ n p → n , p; dnN = λ r c t g p → p
  ; lgS = λ l → l; lgL = λ st lf → st , lf
  ; lgN = λ r c t g tg dir lt lg → tg , dir , (λ η e e′ → refl) , lt , lg
  ; nsS = λ n → n; nsL = λ n → n
  ; nsN = λ r c t g l nl nt ng → l , nl , nt , ng
  ; psS = tt; psL = tt; psN = λ r c t g → tt }
```

## 2 加法

`x + top`：层号 `suc k` 上展开成层 `k` 槽位的结点 (下界 `cO k`，第一支是下界那一支，分支 `η ↦ x + η`)。
层号 `lim f` 上 `top` 之下没有第一位置 (块里的 `DnT (lim f) a = ⊥`)，不同分支的嵌入之间也没有 (`DnK (lim f) n m` 要 `n ≡ m`)，
所以 `λ n → x + top_{f n}` 不是合法的 ℕ 极限；这里取逐项累加 `x + top_{f 0} + … + top_{f n}`，相邻项由弱增长是第一位置。
这是块在极限层号上的第一位置逼出的写法。层号是 Ω 结点时不在片段里，给固定的值。

```agda
cum : ∀ {T : Set} → (ℕ → T → T) → T → ℕ → T
cum step x zero = step zero x
cum step x (suc n) = step (suc n) (cum step x n)

cum-ind : ∀ {T : Set} (P : T → Set) (step : ℕ → T → T) →
  (∀ n y → P y → P (step n y)) → ∀ x → P x → ∀ n → P (cum step x n)
cum-ind P step h x px zero = h zero x px
cum-ind P step h x px (suc n) = h (suc n) _ (cum-ind P step h x px n)

add : ∀ k (A : Alg k) → Alg.T A → Raw k → Alg.T A
add k A x G.zero = x
add k A x (G.suc a) = Alg.sT A (add k A x a)
add k A x (G.lim f) = Alg.lT A (λ n → add k A x (f n))
add k A x (G.lc r c t g) =
  Alg.nT A r c (add k A x t) (λ η e → add k A x (g η e))
add zero A x (G.em () a)
add (suc k) A x (G.em _ a) = add k (shS A) x a
add (lim f) A x (G.em n a) = add (f n) (shL A n) x a
add (lc k c w b t g) A x (G.em i a) = x
add zero A x G.top = Alg.sT A x
add (suc k) A x G.top =
  Alg.nT A (inj₁ tt) (cO k) (add k (shS A) x (cO k))
    (λ η e → add k (shS A) x η)
add (lim f) A x G.top =
  Alg.lT A (cum (λ n y → add (f n) (shL A n) y G.top) x)
add (lc k c w b t g) A x G.top = Alg.sT A x

plus : ∀ m → Raw m → Raw m → Raw m
plus m = add m (rawAlg m)
```

## 3 引理

```agda
add-cp : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) {a b : Raw k} →
  Cp k a b → Alg.Cpᵀ A (add k A x a) (add k A x b)
add-dn : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) {a : Raw k} (b : Raw k) →
  Dn k a b → Alg.Dnᵀ A (add k A x a) (add k A x b)
add-top : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) {a : Raw k} →
  Cp k a G.top → Alg.Cpᵀ A (add k A x a) (add k A x (cO k))

add-cp k pl A x (inj₁ refl) = inj₁ refl
add-cp k pl A x {b = b} (inj₂ p) = inj₂ (add-dn k pl A x b p)

add-dn k pl A x (G.suc b) p = Alg.dnS A (add-cp k pl A x p)
add-dn k pl A x (G.lim f) (n , p) = Alg.dnL A n (add-cp k pl A x p)
add-dn k pl A x (G.lc r c t g) p = Alg.dnN A r c _ _ (add-cp k pl A x p)
add-dn (suc k) pl A x {G.em _ a} (G.em _ T) p = add-dn k pl (shS A) x T p
add-dn (lim f) pl A x {G.em n a} (G.em .n T) (refl , p) =
  add-dn (f n) (pl n) (shL A n) x T p
add-dn (suc k) pl A x {G.em _ a} G.top p =
  Alg.dnN A (inj₁ tt) (cO k) _ _ (add-top k pl (shS A) x p)

add-top zero pl A x (inj₁ refl) = inj₁ refl
add-top (suc k) pl A x p = add-cp (suc k) pl A x p
add-top (lim f) pl A x p = add-cp (lim f) pl A x p

add-weak : ∀ k (A : Alg k) (x : Alg.T A) (a : Raw k) →
  Alg.Cpᵀ A x (add k A x a)
add-weak k A x G.zero = inj₁ refl
add-weak k A x (G.suc a) = inj₂ (Alg.dnS A (add-weak k A x a))
add-weak k A x (G.lim f) = inj₂ (Alg.dnL A zero (add-weak k A x (f zero)))
add-weak k A x (G.lc r c t g) = inj₂ (Alg.dnN A r c _ _ (add-weak k A x t))
add-weak zero A x (G.em () a)
add-weak (suc k) A x (G.em _ a) = add-weak k (shS A) x a
add-weak (lim f) A x (G.em n a) = add-weak (f n) (shL A n) x a
add-weak (lc k c w b t g) A x (G.em i a) = inj₁ refl
add-weak zero A x G.top = inj₂ (Alg.dnS A (inj₁ refl))
add-weak (suc k) A x G.top =
  inj₂ (Alg.dnN A (inj₁ tt) (cO k) _ _ (add-weak k (shS A) x (cO k)))
add-weak (lim f) A x G.top =
  inj₂ (Alg.dnL A zero (add-weak (f zero) (shL A zero) x G.top))
add-weak (lc k c w b t g) A x G.top = inj₂ (Alg.dnS A (inj₁ refl))

grow : ∀ k (A : Alg k) (x : Alg.T A) (y : Raw k) → Pos k y →
  Alg.Dnᵀ A x (add k A x y)
grow k A x (G.suc y) p = Alg.dnS A (add-weak k A x y)
grow k A x (G.lim f) p = Alg.dnL A zero (add-weak k A x (f zero))
grow k A x (G.lc r c t g) p = Alg.dnN A r c _ _ (add-weak k A x t)
grow zero A x G.top p = Alg.dnS A (inj₁ refl)
grow (suc k) A x G.top p =
  Alg.dnN A (inj₁ tt) (cO k) _ _ (add-weak k (shS A) x (cO k))
grow (lim f) A x G.top p =
  Alg.dnL A zero (add-weak (f zero) (shL A zero) x G.top)
grow (lc k c w b t g) A x G.top p = Alg.dnS A (inj₁ refl)

add-lgl : ∀ k → Plain k → (A : Alg k) (x : Alg.T A) (a : Raw k) →
  Alg.Lgᵀ A x → Lgl k a → Alg.Lgᵀ A (add k A x a)
add-lgl k pl A x G.zero lx la = lx
add-lgl k pl A x (G.suc a) lx la = Alg.lgS A (add-lgl k pl A x a lx la)
add-lgl k pl A x (G.lim f) lx (st , lf) =
  Alg.lgL A (λ n → add-cp k pl A x (st n))
    (λ n → add-lgl k pl A x (f n) lx (lf n))
add-lgl k pl A x (G.lc r c t g) lx (tg , dir , irr , lt , lg) =
  Alg.lgN A r c _ _
    (λ η e → add-cp k pl A x (tg η e))
    (λ η e η′ e′ q → add-cp k pl A x (dir η e η′ e′ q))
    (add-lgl k pl A x t lx lt)
    (λ η e → add-lgl k pl A x (g η e) lx (lg η e))
add-lgl (suc k) pl A x (G.em _ a) lx la = add-lgl k pl (shS A) x a lx la
add-lgl (lim f) pl A x (G.em n a) lx la =
  add-lgl (f n) (pl n) (shL A n) x a lx la
add-lgl zero pl A x G.top lx la = Alg.lgS A lx
add-lgl (suc k) pl A x G.top lx la =
  Alg.lgN A (inj₁ tt) (cO k) _ _
    (λ η e → add-cp k pl (shS A) x (proj₁ e))
    (λ η e η′ e′ q → add-cp k pl (shS A) x (proj₁ q))
    (add-lgl k pl (shS A) x (cO k) lx (cO-Lgl k))
    (λ η e → add-lgl k pl (shS A) x η lx (proj₁ (proj₂ e)))
add-lgl (lim f) pl A x G.top lx la =
  Alg.lgL A
    (λ n → add-weak (f (suc n)) (shL A (suc n)) _ G.top)
    (cum-ind (Alg.Lgᵀ A) _
      (λ n y ly → add-lgl (f n) (pl n) (shL A n) y G.top ly tt) x lx)

add-ns : ∀ k (A : Alg k) (x : Alg.T A) (a : Raw k) →
  Alg.Nsᵀ A x → Nested k a → Alg.Nsᵀ A (add k A x a)
add-ns k A x G.zero nx na = nx
add-ns k A x (G.suc a) nx na = Alg.nsS A (add-ns k A x a nx na)
add-ns k A x (G.lim f) nx na = Alg.nsL A (λ n → add-ns k A x (f n) nx (na n))
add-ns k A x (G.lc r c t g) nx (l , nl , nt , ng) =
  Alg.nsN A r c _ _ l nl (add-ns k A x t nx nt)
    (λ η e → add-ns k A x (g η e) nx (ng η e))
add-ns zero A x (G.em () a)
add-ns (suc k) A x (G.em _ a) nx na = add-ns k (shS A) x a nx na
add-ns (lim f) A x (G.em n a) nx na = add-ns (f n) (shL A n) x a nx na
add-ns (lc k c w b t g) A x (G.em i a) nx na = nx
add-ns zero A x G.top nx na = Alg.nsS A nx
add-ns (suc k) A x G.top nx na =
  Alg.nsN A (inj₁ tt) (cO k) _ _ (cO-Lgl k) (cO-Nested k)
    (add-ns k (shS A) x (cO k) nx (cO-Nested k))
    (λ η e → add-ns k (shS A) x η nx (proj₂ (proj₂ e)))
add-ns (lim f) A x G.top nx na =
  Alg.nsL A (cum-ind (Alg.Nsᵀ A) _
    (λ n y ny → add-ns (f n) (shL A n) y G.top ny tt) x nx)
add-ns (lc k c w b t g) A x G.top nx na = Alg.nsS A nx
```

## 4 ω 倍

第 0 项取一份 (`copies m y 0 = y`)，对一切层号同一个写法；第 0 层上它是 `YiIrrIf.copies` 去掉第 0 项。

```agda
copies : ∀ m → Raw m → ℕ → Raw m
copies m y zero = y
copies m y (suc n) = plus m y (copies m y n)

successor : ∀ m → Raw m → Raw m
successor m y = G.lim (copies m y)

copies-step : ∀ m → Plain m → ∀ y n → Cp m (copies m y n) (copies m y (suc n))
copies-step m pl y zero = add-weak m (rawAlg m) y y
copies-step m pl y (suc n) = add-cp m pl (rawAlg m) y (copies-step m pl y n)

copies-legal : ∀ m → Plain m → ∀ y → Lgl m y → ∀ n → Lgl m (copies m y n)
copies-legal m pl y ly zero = ly
copies-legal m pl y ly (suc n) =
  add-lgl m pl (rawAlg m) y (copies m y n) ly (copies-legal m pl y ly n)

copies-nested : ∀ m y → Nested m y → ∀ n → Nested m (copies m y n)
copies-nested m y ny zero = ny
copies-nested m y ny (suc n) =
  add-ns m (rawAlg m) y (copies m y n) ny (copies-nested m y ny n)
```
