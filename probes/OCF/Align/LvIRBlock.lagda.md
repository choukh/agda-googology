# 归纳-递归块: 层号、好输入、折叠、闭包定理写在同一个互递归块里

> 不含记号. 结论写在 [LvIR](LvIR.lagda.md). 块里**没有** `ev`: 链的下一点的证据由闭包定理 `cloT` 给出, `cloT` 与折叠、`Good`、`Lv` 在同一个块里, 块过了正性与停机检查. **但这个块只有目标 0, 节点层必须字面是 0** (`NodeG`), 所以它只走到 $x_1$ (`hs-x₀`, `hs-x₁`); $\Omega_\Omega$ 上不 `Good` (`¬Good-L₂`).

第 0 层的树就是 `O₀` (`Ord zero = O₀`). 第一版让第 0 层也是 `Tree`, 停机检查失败, 见 [LvIRPos](LvIRPos.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvIRBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.LvIRBase
```

## §1 块

`Inp k` 是第 $k$ 层的好输入, `Good` 是唯一的谓词. `Good zero y` 是 `HS y`: **内在的**, 只读这棵树 (为什么只能这样, 见 [LvIRPos](LvIRPos.lagda.md)). `GoodT` 的极限带相邻步进, 节点带基点与沿链的步进, 它们读折叠的输出, 所以 `Good → GoodT → ψT → cloT → Good` 是真的循环.

```agda
data Tree (P : Set) (Br : P → Set) (D : Set) (Dr : D → Set) : Set where
  zero : Tree P Br D Dr
  suc  : Tree P Br D Dr → Tree P Br D Dr
  lim  : (ℕ → Tree P Br D Dr) → Tree P Br D Dr
  limᵢ : (r : P) → (Br r → Tree P Br D Dr) → Tree P Br D Dr
  up   : (d : D) → Dr d → Tree P Br D Dr

Inp₀ : Set
Inp₀ = Σ O₀ HS

one₀ : Inp₀
one₀ = O₀.suc O₀.zero , hs hz

data Lv : Set
Pre   : Lv → Set
Low   : (ℓ : Lv) → Pre ℓ → Set
Dn    : Lv → Set
DnT   : (ℓ : Lv) → Dn ℓ → Set
Trk   : Lv → Set
Ord   : Lv → Set
Good  : (k : Lv) → Ord k → Set

data Lv where
  zero : Lv
  suc  : Lv → Lv
  lim  : (ℕ → Lv) → Lv
  limᴼ : (k : Lv) → (Σ (Ord k) (Good k) → Lv) → Lv

GoodT : (K : Lv) → Trk K → Set
GoodU : (K : Lv) (d : Dn K) → DnT K d → Set
NodeG : (K k : Lv) (r : Pre k) → (Low k r → Trk K) → Set
ZN    : (K : Lv) → (Inp₀ → Trk K) → Set
ψ₀    : (k : Lv) (t : Ord k) → Good k t → O₀
ψT    : (K : Lv) (t : Trk K) → GoodT K t → O₀
ψU    : (K : Lv) (d : Dn K) (x : DnT K d) → GoodU K d x → O₀
node  : (K k : Lv) (r : Pre k) (f : Low k r → Trk K) → NodeG K k r f → O₀
zn    : (K : Lv) (f : Inp₀ → Trk K) → ZN K f → O₀
chn   : (K : Lv) (f : Inp₀ → Trk K) (hf : ∀ x → GoodT K (f x)) → ℕ → Inp₀
clo   : (k : Lv) (t : Ord k) (g : Good k t) → HS (ψ₀ k t g)
cloT  : (K : Lv) (t : Trk K) (g : GoodT K t) → HS (ψT K t g)
cloU  : (K : Lv) (d : Dn K) (x : DnT K d) (g : GoodU K d x) → HS (ψU K d x g)
cloN  : (K k : Lv) (r : Pre k) (f : Low k r → Trk K) (g : NodeG K k r f) → HS (node K k r f g)
cloZ  : (K : Lv) (f : Inp₀ → Trk K) (g : ZN K f) → HS (zn K f g)

Pre zero       = ⊥
Pre (suc k)    = ⊤ ⊎ Pre k
Pre (lim f)    = Σ ℕ λ n → Pre (f n)
Pre (limᴼ k g) = (⊤ ⊎ Pre k) ⊎ Σ (Σ (Ord k) (Good k)) λ x → Pre (g x)

Low (suc k)    (inj₁ _)        = Σ (Ord k) (Good k)
Low (suc k)    (inj₂ r)        = Low k r
Low (lim f)    (n , r)         = Low (f n) r
Low (limᴼ k g) (inj₁ (inj₁ _)) = Σ (Ord k) (Good k)
Low (limᴼ k g) (inj₁ (inj₂ r)) = Low k r
Low (limᴼ k g) (inj₂ (x , r))  = Low (g x) r

Dn zero       = ⊥
Dn (suc k)    = ⊤
Dn (lim f)    = ℕ
Dn (limᴼ k g) = Σ (Ord k) (Good k)

DnT (suc k)    _ = Ord k
DnT (lim f)    n = Ord (f n)
DnT (limᴼ k g) x = Ord (g x)

Trk K = Tree (Pre K) (Low K) (Dn K) (DnT K)

Ord zero       = O₀
Ord (suc k)    = Trk (suc k)
Ord (lim f)    = Trk (lim f)
Ord (limᴼ k g) = Trk (limᴼ k g)

Good zero       y = HS y
Good (suc k)    t = GoodT (suc k) t
Good (lim f)    t = GoodT (lim f) t
Good (limᴼ k g) t = GoodT (limᴼ k g) t

GoodU (suc k)    _ x = Good k x
GoodU (lim f)    n x = Good (f n) x
GoodU (limᴼ k g) d x = Good (g d) x

GoodT K zero       = ⊤
GoodT K (suc a)    = GoodT K a
GoodT K (lim f)    = Σ (∀ n → GoodT K (f n)) λ hg → ∀ n → ψT K (f n) (hg n) ⊑⁰ ψT K (f (suc n)) (hg (suc n))
GoodT K (limᵢ r f) = NodeG K K r f
GoodT K (up d x)   = GoodU K d x

-- 只有字面是第 0 层的节点才有好的形式
NodeG K (suc k)             (inj₂ r)        f = NodeG K k r f
NodeG K (lim h)             (n , r)         f = NodeG K (h n) r f
NodeG K (limᴼ k h)          (inj₁ (inj₂ r)) f = NodeG K k r f
NodeG K (limᴼ k h)          (inj₂ (x , r))  f = NodeG K (h x) r f
NodeG K (suc zero)          (inj₁ _)        f = ZN K f
NodeG K (suc (suc _))       (inj₁ _)        f = ⊥
NodeG K (suc (lim _))       (inj₁ _)        f = ⊥
NodeG K (suc (limᴼ _ _))    (inj₁ _)        f = ⊥
NodeG K (limᴼ zero h)       (inj₁ (inj₁ _)) f = ZN K f
NodeG K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) f = ⊥
NodeG K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) f = ⊥
NodeG K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) f = ⊥

-- 分支好, 基点, 步进. 步进只沿自己的链, 读折叠的输出
ZN K f =
  Σ (∀ x → GoodT K (f x)) λ hf →
    (proj₁ one₀ ⊑⁰ ψT K (f one₀) (hf one₀))
  × (∀ x → proj₁ x ⊑⁰ ψT K (f x) (hf x) →
       ψT K (f x) (hf x) ⊑⁰ ψT K (f (ψT K (f x) (hf x) , cloT K (f x) (hf x))) (hf (ψT K (f x) (hf x) , cloT K (f x) (hf x))))

ψ₀ zero       y g = P₀ y
ψ₀ (suc k)    t g = ψT (suc k) t g
ψ₀ (lim f)    t g = ψT (lim f) t g
ψ₀ (limᴼ k h) t g = ψT (limᴼ k h) t g

ψU (suc k)    _ x g = ψ₀ k x g
ψU (lim f)    n x g = ψ₀ (f n) x g
ψU (limᴼ k h) d x g = ψ₀ (h d) x g

ψT K zero       g = O₀.suc O₀.zero
ψT K (suc a)    g = O₀.lim (iterᴼ (ψT K a g ⊕_))
ψT K (lim f)    (hg , _) = O₀.lim (λ n → ψT K (f n) (hg n))
ψT K (limᵢ r f) g = node K K r f g
ψT K (up d x)   g = ψU K d x g

node K (suc k)             (inj₂ r)        f g = node K k r f g
node K (lim h)             (n , r)         f g = node K (h n) r f g
node K (limᴼ k h)          (inj₁ (inj₂ r)) f g = node K k r f g
node K (limᴼ k h)          (inj₂ (x , r))  f g = node K (h x) r f g
node K (suc zero)          (inj₁ _)        f g = zn K f g
node K (suc (suc _))       (inj₁ _)        f ()
node K (suc (lim _))       (inj₁ _)        f ()
node K (suc (limᴼ _ _))    (inj₁ _)        f ()
node K (limᴼ zero h)       (inj₁ (inj₁ _)) f g = zn K f g
node K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) f ()
node K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) f ()
node K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) f ()

chn K f hf zero    = one₀
chn K f hf (suc n) = ψT K (f (chn K f hf n)) (hf (chn K f hf n)) , cloT K (f (chn K f hf n)) (hf (chn K f hf n))

zn K f (hf , _) = O₀.lim (λ n → ψT K (f (chn K f hf n)) (hf (chn K f hf n)))
```

**闭包定理.** 对树递归. 第 $n$ 个步进由链上上一个步进给出: 下一点就是这一项的输出, 所以 `st` 的前提就是上一步的结论. 第 0 层就是 `P₀-HS`.

```agda
clo zero       y g = P₀-HS g
clo (suc k)    t g = cloT (suc k) t g
clo (lim f)    t g = cloT (lim f) t g
clo (limᴼ k h) t g = cloT (limᴼ k h) t g

cloU (suc k)    _ x g = clo k x g
cloU (lim f)    n x g = clo (f n) x g
cloU (limᴼ k h) d x g = clo (h d) x g

cloT K zero       g = hs hz
cloT K (suc a)    g = hl (iter-HS (cloT K a g)) (iter-step _)
cloT K (lim f)    (hg , st) = hl (λ n → cloT K (f n) (hg n)) st
cloT K (limᵢ r f) g = cloN K K r f g
cloT K (up d x)   g = cloU K d x g

cloN K (suc k)             (inj₂ r)        f g = cloN K k r f g
cloN K (lim h)             (n , r)         f g = cloN K (h n) r f g
cloN K (limᴼ k h)          (inj₁ (inj₂ r)) f g = cloN K k r f g
cloN K (limᴼ k h)          (inj₂ (x , r))  f g = cloN K (h x) r f g
cloN K (suc zero)          (inj₁ _)        f g = cloZ K f g
cloN K (suc (suc _))       (inj₁ _)        f ()
cloN K (suc (lim _))       (inj₁ _)        f ()
cloN K (suc (limᴼ _ _))    (inj₁ _)        f ()
cloN K (limᴼ zero h)       (inj₁ (inj₁ _)) f g = cloZ K f g
cloN K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) f ()
cloN K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) f ()
cloN K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) f ()

cloZ K f (hf , b , st) = hl (λ n → cloT K (f (chn K f hf n)) (hf (chn K f hf n))) stp where
  pre : ∀ n → proj₁ (chn K f hf n) ⊑⁰ ψT K (f (chn K f hf n)) (hf (chn K f hf n))
  stp : ∀ n → ψT K (f (chn K f hf n)) (hf (chn K f hf n)) ⊑⁰ ψT K (f (chn K f hf (suc n))) (hf (chn K f hf (suc n)))
  pre zero    = b
  pre (suc n) = stp n
  stp n = st (chn K f hf n) (pre n)
```

## §2 $\Omega$ 与层号化

不要证据. 树的分支直接忘掉输入上的证据 (`up tt (proj₁ x)`).

```agda
natL : ℕ → Lv
natL zero    = zero
natL (suc n) = suc (natL n)

Ω : (ℓ : Lv) → Ord ℓ
Ω zero       = O₀.suc O₀.zero
Ω (suc k)    = limᵢ (inj₁ tt) (λ x → up tt (proj₁ x))
Ω (lim f)    = lim (λ n → up n (Ω (f n)))
Ω (limᴼ k g) = limᵢ (inj₁ (inj₁ tt)) (λ x → up x (Ω (g x)))

toLv₀ : O₀ → Lv
toLv₀ O₀.zero    = zero
toLv₀ (O₀.suc a) = suc (toLv₀ a)
toLv₀ (O₀.lim f) = lim (λ n → toLv₀ (f n))

-- 第 2 项的层号: 第 0 层上的对角线
L₂ : Lv
L₂ = limᴼ zero (λ x → toLv₀ (proj₁ x))
```

## §3 头两项, 无 `ev`, 无条件

```agda
P₀-1 : proj₁ one₀ ⊑⁰ P₀ (proj₁ one₀)
P₀-1 q with q
... | ≺z z≅ = ≺l 1 (≺z z≅)
... | ≺s ()

good-Ω₀ : Good zero (Ω zero)
good-Ω₀ = hs hz

good-Ω₁ : Good (suc zero) (Ω (suc zero))
good-Ω₁ = (λ x → proj₂ x) , P₀-1 , (λ x p → P₀-mono (proj₁ x) p)

x₀ x₁ : O₀
x₀ = ψ₀ zero (Ω zero) good-Ω₀
x₁ = ψ₀ (suc zero) (Ω (suc zero)) good-Ω₁

hs-x₀ : HS x₀
hs-x₀ = clo zero (Ω zero) good-Ω₀

hs-x₁ : HS x₁
hs-x₁ = clo (suc zero) (Ω (suc zero)) good-Ω₁
```

## §4 这个块走不到 $x_2$: 节点层 $1$ 不 `Good`

$\Omega_\Omega$ 的分支 $y=2$ 是 $\Omega_2$, 它的节点层是 1. 这一版的 `NodeG` 对它是 $\bot$. 所以 `Good` 在 $L_2$ 上是假的, 这是块的范围, 不是证明的缺口: 目标 1 的折叠与闭包都没有写.

```agda
two₀ : Σ O₀ HS
two₀ = O₀.suc (O₀.suc O₀.zero) , hs (hs hz)

¬Good-L₂ : Good L₂ (Ω L₂) → ⊥
¬Good-L₂ (hf , _) = hf two₀
```
