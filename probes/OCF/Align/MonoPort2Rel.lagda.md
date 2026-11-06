# 第 1 层的值关系 (一): 定义

> 不含记号. 入口 [MonoPort2](MonoPort2.lagda.md). 实例 $\Lambda=2$ (`hs (hs hz)`, $S=\cdot\omega$) 里, 世界 $W$ 固定 (模块参数), 一切折叠都从路径 `self` 进, 目标只有两个: 第 0 层 $T_0$ 与第 1 层 $T_1$, 都在世界 $W$ 里. 这够用: 共同目标 `ChainLe (hs hz)` 的计算里, 节点的分支只在 `self`, `lW` 上被取 (见 [MonoPort2Sound](MonoPort2Sound.lagda.md) 的讲解).
>
> - `_⊑_`: 世界 $W$ 里第 1 层差树之间的关系. 与 `DValTree` 同形 (和的结构, `ni` 逐分支、坐标按第 0 层的值对齐, 两条判据), 改了两处: **分支只在 `self`, `lW` 上比**; **凡是语义里要 "把一段的输出加进状态" 的构造子, 都带这一段的自比** (`⨾⊑` 的左边两段, `nl⊑` 的各项, `as*` 的三段, `pre⊑`, `lim⊑`). 这些自比是语义证明里状态一致 (`Good`) 要的, 作为子推导带着, 递归才是结构的.
> - `SRel`: 状态在 $T_0$ 上的值 $\le$, 在 $T_1$ 上的差 $\sqsubseteq$. `Good`: 状态在 $T_1$ 上的差自比.
> - `Obs`: 一对输出的两个读数: 第 0 层加底后 $\le$, 第 1 层 $\sqsubseteq$.
> - `HA₁`: 第 1 层输入用的动作 (只在 `self` 上取) 满足 `Obs`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort2Rel {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (H; D; Ωd; hz; hs; hsuc; hself; ss; _⊲[_]_; AccY; n0; n1; _⨾_; nl; ni; nw; sum)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.MonoPortBridge using (val)

Λ₂ : H
Λ₂ = hs (hs hz)

module P = At Λ₂ tt

k1 : hs hz ⊲[ W ] Λ₂
k1 = hsuc hself

k0 : hz ⊲[ W ] Λ₂
k0 = hsuc (hsuc hself)

T₀ : P.Tg W hz W
T₀ = P.tg C.self k0 lW

T₁ : P.Tg W (hs hz) W
T₁ = P.tg C.self k1 lW

D₁ : Set
D₁ = D (hs hz) W

o₀ : P.Df W → D hz W
o₀ Δ = P.yc Δ T₀

o₁ : P.Df W → D₁
o₁ Δ = P.yc Δ T₁

infixl 6 _⊕_
_⊕_ : P.St W → P.Df W → P.St W
Y ⊕ Δ = P._⊕⟨_⟩_ Y lW Δ

vY : P.St W → A
vY Y = sum azero (o₀ (P.d Y))

d₁ : P.St W → D₁
d₁ Y = o₁ (P.d Y)

-- 第 1 层节点的分支 (坐标是第 0 层的树)
Br : Set
Br = ∀ {W′} → W ⊲ W′ → Lg W′ → D hz W′ → D (hs hz) W′

ap : Br → D hz W → D₁
ap u z = u C.self lW z

preL : ∀ {ly V} → (ℕ → D ly V) → ℕ → D ly V
preL d zero = n0
preL d (suc k) = preL d k ⨾ d k
```

## §1 关系

```agda
infix 4 _⊑_
data _⊑_ : D₁ → D₁ → Set where
  n0⊑ : ∀ {x} → n0 ⊑ x
  n1⊑ : n1 ⊑ n1
  ⨾⊑  : ∀ {x y x′ y′} → x ⊑ x → x′ ⊑ x′ → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)
  nl⊑ : ∀ {d d′ : ℕ → D₁} → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
  ni⊑ : ∀ {u u′ : Br} →
        (∀ z z′ → val z ≤ val z′ → ap u z ⊑ ap u z′) →
        (∀ z z′ → val z ≤ val z′ → ap u′ z ⊑ ap u′ z′) →
        (∀ z z′ → val z ≤ val z′ → ap u z ⊑ ap u′ z′) →
        ni (ss hself) u ⊑ ni (ss hself) u′
  tr  : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  u0ˡ : ∀ {x x′} → x ⊑ x′ → (n0 ⨾ x) ⊑ x′
  u0ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (n0 ⨾ x′)
  u1ˡ : ∀ {x x′} → x ⊑ x′ → (x ⨾ n0) ⊑ x′
  u1ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (x′ ⨾ n0)
  asˡ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → (x ⨾ (y ⨾ z)) ⊑ t → ((x ⨾ y) ⨾ z) ⊑ t
  asˡ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → ((x ⨾ y) ⨾ z) ⊑ t → (x ⨾ (y ⨾ z)) ⊑ t
  asʳ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ ((x ⨾ y) ⨾ z) → t ⊑ (x ⨾ (y ⨾ z))
  asʳ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ (x ⨾ (y ⨾ z)) → t ⊑ ((x ⨾ y) ⨾ z)
  pre⊑ : ∀ {x x′} {d d′ : ℕ → D₁} → x ⊑ x → x′ ⊑ x′ → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) →
         x ⊑ x′ → (∀ n → d n ⊑ d′ n) → ∀ k → (x ⨾ preL d k) ⊑ (x′ ⨾ nl d′)
  lim⊑ : ∀ {x t} {d : ℕ → D₁} → x ⊑ x → (∀ n → d n ⊑ d n) → (∀ k → (x ⨾ preL d k) ⊑ t) → (x ⨾ nl d) ⊑ t

Rf : D₁ → Set
Rf x = x ⊑ x
```

## §2 状态与读数

```agda
SRel : P.St W → P.St W → Set
SRel Y Y′ = (vY Y ≤ vY Y′) × (d₁ Y ⊑ d₁ Y′)

Good : P.St W → Set
Good Y = Rf (d₁ Y)

sr : ∀ {Y} → Good Y → SRel Y Y
sr g = ≤-refl _ , g

Obs : A → A → P.Df W → P.Df W → Set
Obs c c′ Δ Δ′ = (sum c (o₀ Δ) ≤ sum c′ (o₀ Δ′)) × (o₁ Δ ⊑ o₁ Δ′)

-- 加一段之后的状态
G⊕ : ∀ {Y Δ} → Good Y → Rf (o₁ Δ) → Good (Y ⊕ Δ)
G⊕ g r = ⨾⊑ g g g r

S⊕ : ∀ {Y Y′ Δ Δ′} → Good Y → Good Y′ → SRel Y Y′ → Obs (vY Y) (vY Y′) Δ Δ′ → SRel (Y ⊕ Δ) (Y′ ⊕ Δ′)
S⊕ g g′ s o = proj₁ o , ⨾⊑ g g′ (proj₂ s) (proj₂ o)

-- 加 0
G⊕0 : ∀ {Y} → Good Y → Good (Y ⊕ P.zeroD)
G⊕0 g = ⨾⊑ g g g n0⊑

S0ˡ : ∀ {Y Y′} → SRel Y Y′ → SRel (Y ⊕ P.zeroD) Y′
S0ˡ s = proj₁ s , u1ˡ (proj₂ s)

S0ʳ : ∀ {Y Y′} → SRel Y Y′ → SRel Y (Y′ ⊕ P.zeroD)
S0ʳ s = proj₁ s , u1ʳ (proj₂ s)

-- 两段一起加与分开加: 值字面相同, 差由结合律对上
asS : ∀ {Y Δ₁ Δ₂} → Good Y → Rf (o₁ Δ₁) → Rf (o₁ Δ₂) →
      SRel (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂)) ((Y ⊕ Δ₁) ⊕ Δ₂) × SRel ((Y ⊕ Δ₁) ⊕ Δ₂) (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂))
asS g r₁ r₂ = (≤-refl _ , asʳ′ g r₁ r₂ (⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂))) ,
              (≤-refl _ , asˡ g r₁ r₂ (⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂)))

G⨾ᴰ : ∀ {Y Δ₁ Δ₂} → Good Y → Rf (o₁ Δ₁) → Rf (o₁ Δ₂) → Good (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂))
G⨾ᴰ g r₁ r₂ = ⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂)

-- Ω₁ 自比
rfΩ : Rf (Ωd (hs hz) {W})
rfΩ = ⨾⊑ n1⊑ n1⊑ n1⊑ (ni⊑ m m m)
  where
  m : ∀ (z z′ : D hz W) → val z ≤ val z′ → n1 ⊑ n1
  m _ _ _ = n1⊑
```

## §3 动作, 部分和的输出

```agda
Act₁ : Set
Act₁ = P.Ig (hs hz) W

HA₁ : Act₁ → Set
HA₁ A₀ = ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ C.self lW w Y) (A₀ C.self lW w′ Y′)

-- 走部分和 preL d k 在 T₁ 上的输出字面就是各段输出的部分和
module PreOut {ly V} (ac : AccY ly) (ll : ly ⊲[ W ] Λ₂) (A₀ : P.Ig ly W) (d : ℕ → D ly V) (q : V ⊲ W) (w : D ly W) (Z : P.St W) where
  Rp : ℕ → P.Df W
  Rp k = P.Run ac (preL d k) q lW ll A₀ w Z

  Ek : ℕ → P.Df W
  Ek k = P.Run ac (d k) q lW ll A₀ (w ⨾ nw q (preL d k)) (Z ⊕ Rp k)

  O≡ : ∀ k → o₁ (Rp k) ≡ preL (λ n → o₁ (Ek n)) k
  O≡ zero = refl
  O≡ (suc k) = cong (λ t → t ⨾ o₁ (Ek k)) (O≡ k)
```
