# 块内的下界守卫: 形状测试

> 2026-11-03 Fable 5.1 审核 `LvIR` 时写的实验, 原样搬进来 (只改模块名). **这只是形状测试: 定义编译过, 不是强度结果.** 问题: 归纳-递归块里的节点带下界 `c` 与第一支, 分支只在 `c ⊑⁰ v` 的好输入上, 检查器收不收. 收, `Lv : Set`, 平凡守卫重得 `hs-x₁`. 目标 ≥ 1 的折叠与第 1 层的步进没有写. 它说明 [LvIR](LvIR.lagda.md) 里 "节点谓词要 `Set₁`" 只对任意 `Set` 值的谓词成立, 不对界数据成立.

```agda
{-# OPTIONS --safe --without-K #-}
-- 审核用实验 (不进仓库): 归纳-递归块 + 下界守卫的节点 (ŝ c t₀ g 的形状).
-- 问题: 块内的节点带 "下界 c 与第一支 t₀", 分支只在 c ⊑⁰ v 的好输入上,
-- 闭包定理仍在块内, 过不过正性与停机? Lv 是否仍在 Set (不用 P7 的 Set₁)?
module OCF.Align.LvIRGuardProbe where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.LvIRBase

-- Bd r: 节点可带的界的类型; Gd r c x: 分支 x 受界 c 支配的证据
data Tree (P : Set) (Br : P → Set) (Bd : P → Set) (Gd : (r : P) → Bd r → Br r → Set)
          (D : Set) (Dr : D → Set) : Set where
  zero : Tree P Br Bd Gd D Dr
  suc  : Tree P Br Bd Gd D Dr → Tree P Br Bd Gd D Dr
  lim  : (ℕ → Tree P Br Bd Gd D Dr) → Tree P Br Bd Gd D Dr
  limᵢ : (r : P) (c : Bd r) (t₀ : Tree P Br Bd Gd D Dr)
       → (Σ (Br r) (Gd r c) → Tree P Br Bd Gd D Dr) → Tree P Br Bd Gd D Dr
  up   : (d : D) → Dr d → Tree P Br Bd Gd D Dr

Inp₀ : Set
Inp₀ = Σ O₀ HS

data Lv : Set
Pre   : Lv → Set
Low   : (ℓ : Lv) → Pre ℓ → Set
Bdp   : (ℓ : Lv) → Pre ℓ → Set
Gdp   : (ℓ : Lv) (r : Pre ℓ) → Bdp ℓ r → Low ℓ r → Set
Dn    : Lv → Set
DnT   : (ℓ : Lv) → Dn ℓ → Set
Trk   : Lv → Set
Ord   : Lv → Set
Good  : (k : Lv) → Ord k → Set
Bd0   : Lv → Set
Gd0   : (k : Lv) → Bd0 k → Σ (Ord k) (Good k) → Set

data Lv where
  zero : Lv
  suc  : Lv → Lv
  lim  : (ℕ → Lv) → Lv
  limᴼ : (k : Lv) → (Σ (Ord k) (Good k) → Lv) → Lv

GoodT : (K : Lv) → Trk K → Set
GoodU : (K : Lv) (d : Dn K) → DnT K d → Set
NodeG : (K k : Lv) (r : Pre k) (c : Bdp k r) (t₀ : Trk K) → (Σ (Low k r) (Gdp k r c) → Trk K) → Set
ZN    : (K : Lv) (c : O₀) (t₀ : Trk K) → (Σ Inp₀ (λ x → c ⊑⁰ proj₁ x) → Trk K) → Set
ψ₀    : (k : Lv) (t : Ord k) → Good k t → O₀
ψT    : (K : Lv) (t : Trk K) → GoodT K t → O₀
ψU    : (K : Lv) (d : Dn K) (x : DnT K d) → GoodU K d x → O₀
node  : (K k : Lv) (r : Pre k) (c : Bdp k r) (t₀ : Trk K) (f : Σ (Low k r) (Gdp k r c) → Trk K) → NodeG K k r c t₀ f → O₀
zn    : (K : Lv) (c : O₀) (t₀ : Trk K) (f : Σ Inp₀ (λ x → c ⊑⁰ proj₁ x) → Trk K) → ZN K c t₀ f → O₀
chn   : (K : Lv) (c : O₀) (t₀ : Trk K) (f : Σ Inp₀ (λ x → c ⊑⁰ proj₁ x) → Trk K)
        (h₀ : GoodT K t₀) (hf : ∀ x → GoodT K (f x))
        (g₀ : c ⊑⁰ ψT K t₀ h₀) (g : ∀ x → c ⊑⁰ ψT K (f x) (hf x)) → ℕ → Σ Inp₀ (λ x → c ⊑⁰ proj₁ x)
clo   : (k : Lv) (t : Ord k) (g : Good k t) → HS (ψ₀ k t g)
cloT  : (K : Lv) (t : Trk K) (g : GoodT K t) → HS (ψT K t g)
cloU  : (K : Lv) (d : Dn K) (x : DnT K d) (g : GoodU K d x) → HS (ψU K d x g)
cloN  : (K k : Lv) (r : Pre k) (c : Bdp k r) (t₀ : Trk K) (f : Σ (Low k r) (Gdp k r c) → Trk K) (g : NodeG K k r c t₀ f) → HS (node K k r c t₀ f g)
cloZ  : (K : Lv) (c : O₀) (t₀ : Trk K) (f : Σ Inp₀ (λ x → c ⊑⁰ proj₁ x) → Trk K) (g : ZN K c t₀ f) → HS (zn K c t₀ f g)

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

Trk K = Tree (Pre K) (Low K) (Bdp K) (Gdp K) (Dn K) (DnT K)

Ord zero       = O₀
Ord (suc k)    = Trk (suc k)
Ord (lim f)    = Trk (lim f)
Ord (limᴼ k g) = Trk (limᴼ k g)

Good zero       y = HS y
Good (suc k)    t = GoodT (suc k) t
Good (lim f)    t = GoodT (lim f) t
Good (limᴼ k g) t = GoodT (limᴼ k g) t

-- 界: 第 0 层位置的界是 O₀, 其余位置没有界 (⊤), 守卫平凡
Bd0 zero       = O₀
Bd0 (suc _)    = ⊤
Bd0 (lim _)    = ⊤
Bd0 (limᴼ _ _) = ⊤

Gd0 zero       c x = c ⊑⁰ proj₁ x
Gd0 (suc _)    c x = ⊤
Gd0 (lim _)    c x = ⊤
Gd0 (limᴼ _ _) c x = ⊤

Bdp (suc k)    (inj₁ _)        = Bd0 k
Bdp (suc k)    (inj₂ r)        = Bdp k r
Bdp (lim f)    (n , r)         = Bdp (f n) r
Bdp (limᴼ k h) (inj₁ (inj₁ _)) = Bd0 k
Bdp (limᴼ k h) (inj₁ (inj₂ r)) = Bdp k r
Bdp (limᴼ k h) (inj₂ (x , r))  = Bdp (h x) r

Gdp (suc k)    (inj₁ _)        c x = Gd0 k c x
Gdp (suc k)    (inj₂ r)        c x = Gdp k r c x
Gdp (lim f)    (n , r)         c x = Gdp (f n) r c x
Gdp (limᴼ k h) (inj₁ (inj₁ _)) c x = Gd0 k c x
Gdp (limᴼ k h) (inj₁ (inj₂ r)) c x = Gdp k r c x
Gdp (limᴼ k h) (inj₂ (x′ , r)) c x = Gdp (h x′) r c x

GoodU (suc k)    _ x = Good k x
GoodU (lim f)    n x = Good (f n) x
GoodU (limᴼ k g) d x = Good (g d) x

GoodT K zero            = ⊤
GoodT K (suc a)         = GoodT K a
GoodT K (lim f)         = Σ (∀ n → GoodT K (f n)) λ hg → ∀ n → ψT K (f n) (hg n) ⊑⁰ ψT K (f (suc n)) (hg (suc n))
GoodT K (limᵢ r c t₀ f) = NodeG K K r c t₀ f
GoodT K (up d x)        = GoodU K d x

NodeG K (suc k)             (inj₂ r)        c t₀ f = NodeG K k r c t₀ f
NodeG K (lim h)             (n , r)         c t₀ f = NodeG K (h n) r c t₀ f
NodeG K (limᴼ k h)          (inj₁ (inj₂ r)) c t₀ f = NodeG K k r c t₀ f
NodeG K (limᴼ k h)          (inj₂ (x , r))  c t₀ f = NodeG K (h x) r c t₀ f
NodeG K (suc zero)          (inj₁ _)        c t₀ f = ZN K c t₀ f
NodeG K (suc (suc _))       (inj₁ _)        c t₀ f = ⊥
NodeG K (suc (lim _))       (inj₁ _)        c t₀ f = ⊥
NodeG K (suc (limᴼ _ _))    (inj₁ _)        c t₀ f = ⊥
NodeG K (limᴼ zero h)       (inj₁ (inj₁ _)) c t₀ f = ZN K c t₀ f
NodeG K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) c t₀ f = ⊥
NodeG K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) c t₀ f = ⊥
NodeG K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) c t₀ f = ⊥

-- 好的守卫节点: 第一支好, 分支好, 第一支的输出与每个分支的输出都在守卫之上 (所以链点是合法输入),
-- 第 0 步步进, 沿链步进
ZN K c t₀ f =
  Σ (GoodT K t₀) λ h₀ →
  Σ (∀ x → GoodT K (f x)) λ hf →
  Σ (c ⊑⁰ ψT K t₀ h₀) λ g₀ →
  Σ (∀ x → c ⊑⁰ ψT K (f x) (hf x)) λ g →
    (ψT K t₀ h₀ ⊑⁰ ψT K (f ((ψT K t₀ h₀ , cloT K t₀ h₀) , g₀)) (hf ((ψT K t₀ h₀ , cloT K t₀ h₀) , g₀)))
  × (∀ x → proj₁ (proj₁ x) ⊑⁰ ψT K (f x) (hf x) →
       ψT K (f x) (hf x) ⊑⁰ ψT K (f ((ψT K (f x) (hf x) , cloT K (f x) (hf x)) , g x)) (hf ((ψT K (f x) (hf x) , cloT K (f x) (hf x)) , g x)))

ψ₀ zero       y g = P₀ y
ψ₀ (suc k)    t g = ψT (suc k) t g
ψ₀ (lim f)    t g = ψT (lim f) t g
ψ₀ (limᴼ k h) t g = ψT (limᴼ k h) t g

ψU (suc k)    _ x g = ψ₀ k x g
ψU (lim f)    n x g = ψ₀ (f n) x g
ψU (limᴼ k h) d x g = ψ₀ (h d) x g

ψT K zero            g = O₀.suc O₀.zero
ψT K (suc a)         g = O₀.lim (iterᴼ (ψT K a g ⊕_))
ψT K (lim f)         (hg , _) = O₀.lim (λ n → ψT K (f n) (hg n))
ψT K (limᵢ r c t₀ f) g = node K K r c t₀ f g
ψT K (up d x)        g = ψU K d x g

node K (suc k)             (inj₂ r)        c t₀ f g = node K k r c t₀ f g
node K (lim h)             (n , r)         c t₀ f g = node K (h n) r c t₀ f g
node K (limᴼ k h)          (inj₁ (inj₂ r)) c t₀ f g = node K k r c t₀ f g
node K (limᴼ k h)          (inj₂ (x , r))  c t₀ f g = node K (h x) r c t₀ f g
node K (suc zero)          (inj₁ _)        c t₀ f g = zn K c t₀ f g
node K (suc (suc _))       (inj₁ _)        c t₀ f ()
node K (suc (lim _))       (inj₁ _)        c t₀ f ()
node K (suc (limᴼ _ _))    (inj₁ _)        c t₀ f ()
node K (limᴼ zero h)       (inj₁ (inj₁ _)) c t₀ f g = zn K c t₀ f g
node K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) c t₀ f ()
node K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) c t₀ f ()
node K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) c t₀ f ()

chn K c t₀ f h₀ hf g₀ g zero    = (ψT K t₀ h₀ , cloT K t₀ h₀) , g₀
chn K c t₀ f h₀ hf g₀ g (suc n) =
  (ψT K (f (chn K c t₀ f h₀ hf g₀ g n)) (hf (chn K c t₀ f h₀ hf g₀ g n))
   , cloT K (f (chn K c t₀ f h₀ hf g₀ g n)) (hf (chn K c t₀ f h₀ hf g₀ g n)))
  , g (chn K c t₀ f h₀ hf g₀ g n)

zn K c t₀ f (h₀ , hf , g₀ , g , _) = O₀.lim (λ n → proj₁ (proj₁ (chn K c t₀ f h₀ hf g₀ g n)))

clo zero       y g = P₀-HS g
clo (suc k)    t g = cloT (suc k) t g
clo (lim f)    t g = cloT (lim f) t g
clo (limᴼ k h) t g = cloT (limᴼ k h) t g

cloU (suc k)    _ x g = clo k x g
cloU (lim f)    n x g = clo (f n) x g
cloU (limᴼ k h) d x g = clo (h d) x g

cloT K zero            g = hs hz
cloT K (suc a)         g = hl (iter-HS (cloT K a g)) (iter-step _)
cloT K (lim f)         (hg , st) = hl (λ n → cloT K (f n) (hg n)) st
cloT K (limᵢ r c t₀ f) g = cloN K K r c t₀ f g
cloT K (up d x)        g = cloU K d x g

cloN K (suc k)             (inj₂ r)        c t₀ f g = cloN K k r c t₀ f g
cloN K (lim h)             (n , r)         c t₀ f g = cloN K (h n) r c t₀ f g
cloN K (limᴼ k h)          (inj₁ (inj₂ r)) c t₀ f g = cloN K k r c t₀ f g
cloN K (limᴼ k h)          (inj₂ (x , r))  c t₀ f g = cloN K (h x) r c t₀ f g
cloN K (suc zero)          (inj₁ _)        c t₀ f g = cloZ K c t₀ f g
cloN K (suc (suc _))       (inj₁ _)        c t₀ f ()
cloN K (suc (lim _))       (inj₁ _)        c t₀ f ()
cloN K (suc (limᴼ _ _))    (inj₁ _)        c t₀ f ()
cloN K (limᴼ zero h)       (inj₁ (inj₁ _)) c t₀ f g = cloZ K c t₀ f g
cloN K (limᴼ (suc _) h)    (inj₁ (inj₁ _)) c t₀ f ()
cloN K (limᴼ (lim _) h)    (inj₁ (inj₁ _)) c t₀ f ()
cloN K (limᴼ (limᴼ _ _) h) (inj₁ (inj₁ _)) c t₀ f ()

cloZ K c t₀ f (h₀ , hf , g₀ , g , s₀ , st) = hl (λ n → proj₂ (proj₁ (ch n))) stp where
  ch : ℕ → Σ Inp₀ (λ x → c ⊑⁰ proj₁ x)
  ch = chn K c t₀ f h₀ hf g₀ g
  stp : ∀ n → proj₁ (proj₁ (ch n)) ⊑⁰ proj₁ (proj₁ (ch (suc n)))
  stp zero    = s₀
  stp (suc n) = st (ch n) (stp n)

-- 实例: 守卫平凡 (c = 0) 时就是 LvIRBlock 的 Ω₁, x₁ = ψ₀(Ω₁) 的 HS 无条件
⊑-zero : ∀ b → O₀.zero ⊑⁰ b
⊑-zero b ()

P₀-1 : O₀.suc O₀.zero ⊑⁰ P₀ (O₀.suc O₀.zero)
P₀-1 (≺z z≅) = ≺l 1 (≺z z≅)
P₀-1 (≺s ())

Ω₁ : Ord (suc zero)
Ω₁ = limᵢ (inj₁ tt) O₀.zero (up tt (O₀.suc O₀.zero)) (λ x → up tt (proj₁ (proj₁ x)))

good-Ω₁ : Good (suc zero) Ω₁
good-Ω₁ = hs hz , (λ x → proj₂ (proj₁ x)) , ⊑-zero _ , (λ x → ⊑-zero _)
        , P₀-mono _ P₀-1 , (λ x p → P₀-mono _ p)

x₁ : O₀
x₁ = ψ₀ (suc zero) Ω₁ good-Ω₁

hs-x₁ : HS x₁
hs-x₁ = clo (suc zero) Ω₁ good-Ω₁

-- 非平凡守卫的节点能写下来 (不证它 Good): 分支只在 c ⊑⁰ v 的好输入上
guarded : (c : O₀) → Ord (suc zero)
guarded c = limᵢ (inj₁ tt) c (up tt c) (λ x → up tt (proj₁ (proj₁ x)))
```
