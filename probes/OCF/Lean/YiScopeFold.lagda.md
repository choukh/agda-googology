# 作用域块上的折叠: 没有派发, 没有 `top` 行

非验收文件, 成品候选. 判决: 定义 (第 2 层) 与闭项, 没有定理. 折叠 `F` 只看树的构造子与方式 `Mode` (全折 `col`, 或折到后继层根结点的下标层 `kp`); 不比较层号, 不比较孩子的下标.
`top` 是树 ([YiScopeCore](YiScopeCore.lagda.md) §3), 所以没有单独的 `top` 行: 它们是结点行与 `into` 行的推论 ([YiScopeSame](YiScopeSame.lagda.md)).
不说明合法性与值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiScopeCore
```

## 1 部件

`succ y` 是 `y · ω` (根作用域). 结点的链在它的分支下标层里, 从那一层的 `top` 起, 每步加上分支折到下标层的结果.
`Res` 是洞里的东西: 外层那棵树对任意目标层的折叠.

```agda
iter : ∀ {V : Set} → (V → V) → V → ℕ → V
iter h x zero = x
iter h x (suc n) = h (iter h x n)

succ : ∀ {K} → Raw K → Raw K
succ {K} = sucS K root

chain : ∀ j → (Raw j → Raw j) → ℕ → Raw j
chain j h = iter (λ γ → plus γ (h γ)) (top j G.zero)

chainD : ∀ K → Root K root → (Dom K root → Dom K root) → ℕ → Dom K root
chainD K r = domE (λ D → (D → D) → ℕ → D) K root r chain

no-up : ∀ K s c → sub K s c ≡ root → ⊥
no-up zero s ()
no-up (sup S g) root c ()
no-up (sup S g) (down d p) c ()

Res : Set
Res = (J : Level) → Raw J → Raw J

data Mode : Level → Level → Set where
  col : ∀ {K J} → Mode K J
  kp  : ∀ {g} → Mode (sup one g) (g tt)

DnR : (K : Level) → Path K → Set
DnR K root = ⊤
DnR zero (inj₂ ())
DnR (sup S g) (down c p) = Tr Res (g c) p

InB : Level → Set
InB zero = ⊤
InB (sup one g) = Raw (g tt)
InB (sup nat g) = ⊤
InB (sup (raw k) g) = ⊤

InR : (K : Level) → Path K → Set
InR K root = ⊤
InR zero (inj₂ ())
InR (sup one g) (down c p) = Tr ⊥ (g c) p
InR (sup nat g) (down c p) = ⊤
InR (sup (raw k) g) (down c p) = ⊤
```

## 2 折叠

`F ρ K J m b t`: 把 `K` 层根作用域的树 `t` 折到 `J` 层, `b` 是零的像, `ρ` 解释洞.
结点一律经自己下标层的链折叠 (链步 `RlD`: 后继层的根结点用 `kp`, Ω 结点层号的根结点用 `col`).
`into`: 全折时换成孩子层的树 (`dn`: 越过孩子根的 `up` 变成洞), 再折; `kp` 时孩子就是目标层, 里面的东西留在原来的作用域上 (`In`:
结点, `into`, 孩子内部的 `up` 保留, 后继在所在的作用域里乘 ω), 只有越过孩子根的 `up` 回到 `F`. 进孩子时下标 `c` 只是被传过去.
`In` 的算术必须留在孩子的作用域里: 若把分支先算成根作用域的树再经 `up` 送回, 以后相对这个结点折叠时, 里面的结点是 "越出又进来" 的, 会被折叠.

```agda
F : ∀ {X} → (X → Res) → (K J : Level) → Mode K J → Raw J → Tr X K root → Raw J
RlD : ∀ {X} → (X → Res) → (K : Level) → Root K root → Dom K root → Tr X K root → Dom K root
In : ∀ {X} → (X → Res) → (K : Level) (q : Path K) → InB K → Tr X K q → InR K q
dn : ∀ {X} → (X → Res) → (K : Level) (q : Path K) → Tr X K q → DnR K q

F ρ K J m b G.zero = b
F ρ K J m b (G.suc a) = succ (F ρ K J m b a)
F ρ K J m b (G.lim f) = G.lim (λ n → F ρ K J m b (f n))
F ρ K J m b (G.nd r h) = G.lim (λ n → F ρ K J m b
  (h (chainD K r (λ γ → RlD ρ K r (tpD K root r) (h γ)) n)))
F ρ zero J m b (G.into () t)
F ρ (sup S g) J col b (G.into c t) = F (λ v → v) (g c) J col b (dn ρ (sup S g) (down c root) t)
F ρ (sup one g) .(g tt) kp b (G.into c t) = In ρ (sup one g) (down c root) b t
F ρ K J m b (G.up {s} c e y) = ⊥-elim (no-up K s c e)
F ρ K J m b (G.hole v) = ρ v J b

RlD ρ zero () b t
RlD ρ (sup one g) r b t = F ρ (sup one g) (g tt) kp b t
RlD ρ (sup nat g) () b t
RlD ρ (sup (raw k) g) r b t = F ρ (sup (raw k) g) k col b t

In ρ K root b t = tt
In ρ zero (inj₂ ()) b t
In ρ (sup nat g) (down c p) b t = tt
In ρ (sup (raw k) g) (down c p) b t = tt
In ρ (sup one g) (down c p) b G.zero = lift (g c) p b
In ρ (sup one g) (down c p) b (G.suc a) = sucS (g c) p (In ρ (sup one g) (down c p) b a)
In ρ (sup one g) (down c p) b (G.lim f) = G.lim (λ n → In ρ (sup one g) (down c p) b (f n))
In ρ (sup one g) (down c p) b (G.nd r h) = G.nd r (λ η → In ρ (sup one g) (down c p) b (h η))
In ρ (sup one g) (down c p) b (G.into d t) = G.into d (In ρ (sup one g) (down c (sub (g c) p d)) b t)
In ρ (sup one g) (down c p) b (G.up {s = root} c′ refl y) = F ρ (sup one g) (g tt) kp b y
In ρ (sup one g) (down c p) b (G.up {s = down c′ p′} d refl y) =
  G.up d refl (In ρ (sup one g) (down c′ p′) b y)

dn ρ K root t = tt
dn ρ zero (inj₂ ()) t
dn ρ (sup S g) (down c p) G.zero = G.zero
dn ρ (sup S g) (down c p) (G.suc a) = G.suc (dn ρ (sup S g) (down c p) a)
dn ρ (sup S g) (down c p) (G.lim f) = G.lim (λ n → dn ρ (sup S g) (down c p) (f n))
dn ρ (sup S g) (down c p) (G.nd r h) = G.nd r (λ η → dn ρ (sup S g) (down c p) (h η))
dn ρ (sup S g) (down c p) (G.into d t) = G.into d (dn ρ (sup S g) (down c (sub (g c) p d)) t)
dn ρ (sup S g) (down c p) (G.up {s = root} c′ refl y) =
  G.hole (λ J b → F ρ (sup S g) J col b y)
dn ρ (sup S g) (down c p) (G.up {s = down c′ p′} d refl y) =
  G.up d refl (dn ρ (sup S g) (down c′ p′) y)
```

## 3 闭项

`Ψ₀ K` 是 `K` 层的 `top` 折到零层 (零的像是零层的 `top`). 判断: 读法是 ψ₀(Ω_K).

```agda
Ψ₀ : Level → Raw zero
Ψ₀ K = F ⊥-elim K zero col (top zero G.zero) (top K G.zero)

Tw : ℕ → Raw zero
Tw n = Ψ₀ (tw n)

TΛ : Raw zero
TΛ = Ψ₀ Λ

T⁺ʷ : Raw zero
T⁺ʷ = Ψ₀ (sucᴸ (tw 2))
```
