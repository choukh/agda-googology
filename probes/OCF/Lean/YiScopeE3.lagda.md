# 实验 E3: 规范树 `Tw 2` 的折叠里的链点

验收文件. 判决: **测到的范围内不出现, 范围很小; 其余没定.** 测到的是 `Tw 2` 的顶层链的第 1 点 `θ₁` 与孩子 1 上那个结点的全部内层链点 `δ n m`: 都合法 (`θ₁-legal`, `δ-legal`, 编译定理, 无前提), 它们全在零层 (可数树), 没有结点, 所以没有 "保留的一份与折掉的一份" 那种配置.
`Tw 2` 的第 2 个链点起, `Tw 3`, `TΛ`: **没定** (要用作用域里 `sucS` 的合法性, 缺 `wrap-below`; 见回报). 这是有限范围的结果, 不是 "不出现" 的证明.
顺带的编译事实: Ω 结点层号的 `top` 的分支在 ℕ 极限下标上不碰那个下标的孩子 (`Br-lim`), `Tw 2` 的第 0, 1 项只用到孩子 0 与 1.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeE3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiScopeCore
open import OCF.Lean.YiScopeFold
open import OCF.Lean.YiScopeLegal
```

## 1 `Tw 2` 的形状

`Br θ` 是 `top (tw 2)` 的根结点在下标 `θ` 上的分支; 顶层链 `θ` 在零层. `Br` 在后继下标 1 上是各孩子的 `top` 的累加 `cs`.

```agda
R0 : Set
R0 = Raw zero

g2 : R0 → Level
g2 = rb zero root

K2 : Level
K2 = sup (raw zero) g2

b0 i1 : R0
b0 = top zero G.zero
i1 = G.suc G.zero

Br : R0 → Raw K2
Br = Kf zero (ct (raw zero) g2) G.zero

θ : ℕ → R0
θ = chain zero (λ γ → F ⊥-elim K2 zero col b0 (Br γ))

Tw2-form : Tw 2 ≡ G.lim (λ n → F ⊥-elim K2 zero col b0 (Br (θ n)))
Tw2-form = refl

Br-lim : ∀ f → Br (G.lim f) ≡ G.lim (λ n → Br (f n))
Br-lim f = refl

cs : ℕ → Raw K2
cs = acc (λ _ z → ct (raw zero) g2 i1 z) (ct (raw zero) g2 G.zero G.zero)

Br-one : Br (θ 0) ≡ G.lim cs
Br-one = refl

θ₁-form : θ 1 ≡ plus b0 (F ⊥-elim K2 zero col b0 (G.lim cs))
θ₁-form = refl
```

孩子 0 是零层 (它的 `top` 是后继), 孩子 1 是层号 1 (它的 `top` 是根结点, 下标是可数树 `η`). `P n η` 是那个结点的分支在孩子作用域里的部分;
`Gf` 是它的全折, `Ef` 是链步 (折到下标层), `δ` 是内层链.

```agda
L1 : Level
L1 = sucᴸ zero

q2 : Path K2
q2 = down i1 (down tt root)

P : ℕ → R0 → Tr ⊥ K2 q2
P n η = plus (cs n) (un (raw zero) g2 i1 ⊥-elim (down tt root)
  (plus {K = L1} {s = down tt root} G.zero (un one (λ _ → zero) tt ⊥-elim root η)))

Gf : ℕ → R0 → R0 → R0
Gf n b η = F (λ v → v) zero zero col b (dn (λ v → v) L1 (down tt root) (dn ⊥-elim K2 q2 (P n η)))

Ef : ℕ → R0 → R0
Ef n η = In (λ v → v) L1 (down tt root) b0 (dn ⊥-elim K2 q2 (P n η))

δ : ℕ → ℕ → R0
δ n = chain zero (Ef n)

fold-c0 : ∀ b → F ⊥-elim K2 zero col b (cs 0) ≡ succ b
fold-c0 b = refl

fold-cs : ∀ n b → F ⊥-elim K2 zero col b (cs (suc n)) ≡ G.lim (λ m → Gf n b (δ n m))
fold-cs n b = refl
```

## 2 零层上的指数族

`Gf n b` 与 `Ef n` 都是: 零的像是外层那一项的折叠, 后继乘 ω, ℕ 极限逐项. 对这样的族, 底在像之下, 像对第一位置单调, 保持合法.

```agda
module Exp (X : R0 → R0) (β : R0) (e0 : X G.zero ≡ β) (es : ∀ a → X (G.suc a) ≡ succ (X a))
           (el : ∀ f → X (G.lim f) ≡ G.lim (λ k → X (f k))) (lβ : Legal zero root β) where

  weak : ∀ η → Cp β (X η)
  weak G.zero = inj₁ (sym e0)
  weak (G.suc a) = subst (Cp β) (sym (es a)) (inj₂ (0 , weak a))
  weak (G.lim f) = subst (Cp β) (sym (el f)) (inj₂ (0 , weak (f 0)))
  weak (G.nd () h)
  weak (G.into () t)
  weak (G.up () e y)
  weak (G.hole ())

  dn′ : ∀ a b → Dn a b → Dn (X a) (X b)
  cp′ : ∀ a b → Cp a b → Cp (X a) (X b)
  cp′ a b (inj₁ refl) = inj₁ refl
  cp′ a b (inj₂ p) = inj₂ (dn′ a b p)
  dn′ a (G.suc b) p = subst (Dn (X a)) (sym (es b)) (0 , cp′ a b p)
  dn′ a (G.lim f) (n , p) = subst (Dn (X a)) (sym (el f)) (n , cp′ a (f n) p)
  dn′ a (G.nd () h) p
  dn′ a (G.into () t) p
  dn′ a (G.up () e y) p
  dn′ a (G.hole ()) p

  lgl : ∀ η → Legal zero root η → Legal zero root (X η)
  lgl G.zero l = subst (Legal zero root) (sym e0) lβ
  lgl (G.suc a) l = subst (Legal zero root) (sym (es a)) (succ-lgl zero (X a) (lgl a l))
  lgl (G.lim f) (st , lf) = subst (Legal zero root) (sym (el f))
    ((λ n → cp′ _ _ (st n)) , (λ n → lgl (f n) (lf n)))
  lgl (G.nd () h) l
  lgl (G.into () t) l
  lgl (G.up () e y) l
  lgl (G.hole ()) l
```

## 3 链点合法

```agda
βc : ℕ → R0 → R0
βc n b = F ⊥-elim K2 zero col b (cs n)

βc-legal : ∀ n b → Legal zero root b → Legal zero root (βc n b)
δ-legal : ∀ n m → Legal zero root (δ n m)

module E (n : ℕ) = Exp (Ef n) (βc n b0) refl (λ a → refl) (λ f → refl) (βc-legal n b0 tt)
module Gm (n : ℕ) (b : R0) (lb : Legal zero root b) =
  Exp (Gf n b) (βc n b) refl (λ a → refl) (λ f → refl) (βc-legal n b lb)

βc-legal zero b lb = succ-lgl zero b lb
βc-legal (suc n) b lb =
  (λ m → Gm.cp′ n b lb _ _ (plus-weak (δ n m) (Ef n (δ n m)) (inj₁ refl))) ,
  (λ m → Gm.lgl n b lb (δ n m) (δ-legal n m))

δ-legal n zero = tt
δ-legal n (suc m) = plus-lgl (δ n m) (Ef n (δ n m)) (δ-legal n m) (E.lgl n (δ n m) (δ-legal n m))

-- 顶层链步: 分支在下标 1 上的全折.
step-legal : ∀ b → Legal zero root b → Legal zero root (F ⊥-elim K2 zero col b (G.lim cs))
step-legal b lb = (λ n → inj₂ (0 , Gm.weak n b lb (δ n 0))) , (λ n → βc-legal n b lb)

θ₁-legal : Legal zero root (θ 1)
θ₁-legal = plus-lgl b0 (F ⊥-elim K2 zero col b0 (G.lim cs)) tt (step-legal b0 tt)

-- Tw 2 的第 0 项合法.
obs0-legal : Legal zero root (F ⊥-elim K2 zero col b0 (Br (θ 0)))
obs0-legal = step-legal b0 tt
```
