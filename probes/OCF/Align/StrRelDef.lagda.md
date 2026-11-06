# 结构关系 (一): 两层的关系, 状态, 读数

> 不含记号. 入口 [StrRel](StrRel.lagda.md). 范围同 [MonoPort2](MonoPort2.lagda.md): 实例 $\Lambda=2$, 世界 $W$ 固定 (模块参数), 一切折叠从路径 `self` 进, 只读两个目标 $T_0$, $T_1$ (都在世界 $W$ 里). 实例、目标、读数、状态更新照用 [MonoPort2Rel](MonoPort2Rel.lagda.md) 的定义, 只换关系.
>
> - **`_⊑₀_`: 第 0 层的结构关系.** 构造子正是 `KNest2` §3 列出的那一组: `n0 ⊑ z`, `n1 ⊑ n1`, `⨾`, `nl` 逐项, `nw` 两边透明, 部分和 `pr` ($x⨾\mathrm{pre}\,d\,k\sqsubseteq x'⨾\mathrm{nl}\,d'$), 传递, 单位, 结合. **没有左边极限截断** (没有 `lim-leP`/`lim⊑` 那一条: 由一切前缀 $\sqsubseteq t$ 推出极限 $\sqsubseteq t$). 两边世界可以不同 (第 0 层没有节点, 世界不起作用).
> - **`_⊑₁_`: 第 1 层的结构关系.** `MonoPort2Rel` 的关系去掉 `lim⊑`, 节点 `ni⊑` 的分支**按第 0 层的结构关系对齐** ($z\sqsubseteq_0 z'$ ⇒ $u\,z\sqsubseteq_1 u'\,z'$), 不按值. 自比仍作为子推导带着 (理由同 `MonoPort2`: 第 1 层不是一切树自比).
> - `SRel`: 状态在 $T_0$ 上的差 $\sqsubseteq_0$, 在 $T_1$ 上的差 $\sqsubseteq_1$. `Obs`: 一对输出在两个目标上的读数分别 $\sqsubseteq_0$, $\sqsubseteq_1$. **两个读数都是结构的**, 没有值.
> - `val₀`: 结构关系推出值的单调 (对一切底 $b\le b'$, $b+x\le b'+x'$). 这是 "第 0 层读数单调" 的来源.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.StrRelDef {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; Ωd; hz; hs; hself; ss; AccY; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
open import OCF.Align.HtFeedTree using (H; _⊲[_]_; hsuc)
open import OCF.Align.HtFeedClosed using (module At)
open import Data.Unit using (tt)
```

**实例与读数.** 与 [MonoPort2Rel](MonoPort2Rel.lagda.md) 的同名定义逐字相同. 这里重抄一遍 (约 40 行), 不导入它: 那个模块经 `MonoPortBridge` 导入 `DValCanon` (`Gen`), 重抄之后本组的 `Def`, `Zero`, `Sound`, `Head`, `Neg` 的导入闭包里没有 `Gen`, "不经规范形" 由编译器保证.

```agda
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

Act₁ : Set
Act₁ = P.Ig (hs hz) W
```

## §1 第 0 层

```agda
infix 4 _⊑₀_
data _⊑₀_ : ∀ {V V′} → D hz V → D hz V′ → Set where
  z0  : ∀ {V V′} {x : D hz V′} → n0 {W = V} ⊑₀ x
  o1  : ∀ {V V′} → n1 {W = V} ⊑₀ n1 {W = V′}
  sq  : ∀ {V V′} {x y : D hz V} {x′ y′ : D hz V′} → x ⊑₀ x′ → y ⊑₀ y′ → (x ⨾ y) ⊑₀ (x′ ⨾ y′)
  lm  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → nl d ⊑₀ nl d′
  wl  : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D hz V₀} {x′ : D hz V′} → x ⊑₀ x′ → nw p x ⊑₀ x′
  wr  : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D hz V} {x′ : D hz V₀} → x ⊑₀ x′ → x ⊑₀ nw p x′
  pr  : ∀ {V V′} {x : D hz V} {x′ : D hz V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} →
        x ⊑₀ x′ → (∀ n → d n ⊑₀ d′ n) → ∀ k → (x ⨾ preL d k) ⊑₀ (x′ ⨾ nl d′)
  tr  : ∀ {V V′} {x y : D hz V} {z : D hz V′} → x ⊑₀ y → y ⊑₀ z → x ⊑₀ z
  u0l : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → (n0 ⨾ x) ⊑₀ x′
  u0r : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → x ⊑₀ (n0 ⨾ x′)
  u1l : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → (x ⨾ n0) ⊑₀ x′
  u1r : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → x ⊑₀ (x′ ⨾ n0)
  al  : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → (x ⨾ (y ⨾ z)) ⊑₀ t → ((x ⨾ y) ⨾ z) ⊑₀ t
  al′ : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → ((x ⨾ y) ⨾ z) ⊑₀ t → (x ⨾ (y ⨾ z)) ⊑₀ t
  ar  : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → t ⊑₀ ((x ⨾ y) ⨾ z) → t ⊑₀ (x ⨾ (y ⨾ z))
  ar′ : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → t ⊑₀ (x ⨾ (y ⨾ z)) → t ⊑₀ ((x ⨾ y) ⨾ z)

-- 第 0 层一切树自比
refl₀ : ∀ {V} (x : D hz V) → x ⊑₀ x
refl₀ n0 = z0
refl₀ n1 = o1
refl₀ (x ⨾ y) = sq (refl₀ x) (refl₀ y)
refl₀ (nl d) = lm (λ n → refl₀ (d n))
refl₀ (ni () u)
refl₀ (nκ () u)
refl₀ (nw p x) = wl (wr (refl₀ x))

-- nw 对 ⨾ 的分配 (两个方向)
nwd : ∀ {V₀ V} {q : V₀ ⊲ V} (x y : D hz V₀) → nw q (x ⨾ y) ⊑₀ (nw q x ⨾ nw q y)
nwd x y = wl (sq (wr (refl₀ x)) (wr (refl₀ y)))

nwd′ : ∀ {V₀ V} {q : V₀ ⊲ V} (x y : D hz V₀) → (nw q x ⨾ nw q y) ⊑₀ nw q (x ⨾ y)
nwd′ x y = wr (sq (wl (refl₀ x)) (wl (refl₀ y)))

preL₀ : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ k → preL d k ⊑₀ preL d′ k
preL₀ h zero = z0
preL₀ h (suc k) = sq (preL₀ h k) (h k)
```

**值的单调.** 对推导归纳, 底一起变大. 单位律与结合律在 `sum` 下定义性成立, `nw` 透明.

```agda
val₀ : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ {b b′} → b ≤ b′ → sum b x ≤ sum b′ x′
ptv  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ {b b′} → b ≤ b′ → ∀ n → pt b d n ≤ pt b′ d′ n
prv  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ {b b′} → b ≤ b′ → ∀ k → sum b (preL d k) ≤ pt b′ d′ k
val₀ (z0 {x = x}) {b′ = b′} h = ≤-trans h (⊲→≤ (sum-fst b′ x))
val₀ o1 h = s≤ h
val₀ (sq hx hy) h = val₀ hy (val₀ hx h)
val₀ (lm hd) h = l≤ (λ n → ≤l n (ptv hd h n))
val₀ (wl hx) h = val₀ hx h
val₀ (wr hx) h = val₀ hx h
val₀ (pr hx hd k) h = ≤l k (prv hd (val₀ hx h) k)
val₀ (tr hx hy) {b′ = b′} h = ≤-trans (val₀ hx h) (val₀ hy (≤-refl b′))
val₀ (u0l hx) h = val₀ hx h
val₀ (u0r hx) h = val₀ hx h
val₀ (u1l hx) h = val₀ hx h
val₀ (u1r hx) h = val₀ hx h
val₀ (al hx) h = val₀ hx h
val₀ (al′ hx) h = val₀ hx h
val₀ (ar hx) h = val₀ hx h
val₀ (ar′ hx) h = val₀ hx h
ptv hd h zero = h
ptv hd h (suc n) = val₀ (hd n) (ptv hd h n)
prv hd h zero = h
prv hd h (suc k) = val₀ (hd k) (prv hd h k)
```

## §2 第 1 层

```agda
infix 4 _⊑₁_
data _⊑₁_ : D₁ → D₁ → Set where
  n0⊑ : ∀ {x} → n0 ⊑₁ x
  n1⊑ : n1 ⊑₁ n1
  ⨾⊑  : ∀ {x y x′ y′} → x ⊑₁ x → x′ ⊑₁ x′ → x ⊑₁ x′ → y ⊑₁ y′ → (x ⨾ y) ⊑₁ (x′ ⨾ y′)
  nl⊑ : ∀ {d d′ : ℕ → D₁} → (∀ n → d n ⊑₁ d n) → (∀ n → d′ n ⊑₁ d′ n) → (∀ n → d n ⊑₁ d′ n) → nl d ⊑₁ nl d′
  ni⊑ : ∀ {u u′ : Br} →
        (∀ (z z′ : D hz W) → z ⊑₀ z′ → ap u z ⊑₁ ap u z′) →
        (∀ (z z′ : D hz W) → z ⊑₀ z′ → ap u′ z ⊑₁ ap u′ z′) →
        (∀ (z z′ : D hz W) → z ⊑₀ z′ → ap u z ⊑₁ ap u′ z′) →
        ni (ss hself) u ⊑₁ ni (ss hself) u′
  tr  : ∀ {x y z} → x ⊑₁ y → y ⊑₁ z → x ⊑₁ z
  u0ˡ : ∀ {x x′} → x ⊑₁ x′ → (n0 ⨾ x) ⊑₁ x′
  u0ʳ : ∀ {x x′} → x ⊑₁ x′ → x ⊑₁ (n0 ⨾ x′)
  u1ˡ : ∀ {x x′} → x ⊑₁ x′ → (x ⨾ n0) ⊑₁ x′
  u1ʳ : ∀ {x x′} → x ⊑₁ x′ → x ⊑₁ (x′ ⨾ n0)
  asˡ  : ∀ {x y z t} → x ⊑₁ x → y ⊑₁ y → z ⊑₁ z → (x ⨾ (y ⨾ z)) ⊑₁ t → ((x ⨾ y) ⨾ z) ⊑₁ t
  asˡ′ : ∀ {x y z t} → x ⊑₁ x → y ⊑₁ y → z ⊑₁ z → ((x ⨾ y) ⨾ z) ⊑₁ t → (x ⨾ (y ⨾ z)) ⊑₁ t
  asʳ  : ∀ {x y z t} → x ⊑₁ x → y ⊑₁ y → z ⊑₁ z → t ⊑₁ ((x ⨾ y) ⨾ z) → t ⊑₁ (x ⨾ (y ⨾ z))
  asʳ′ : ∀ {x y z t} → x ⊑₁ x → y ⊑₁ y → z ⊑₁ z → t ⊑₁ (x ⨾ (y ⨾ z)) → t ⊑₁ ((x ⨾ y) ⨾ z)
  pre⊑ : ∀ {x x′} {d d′ : ℕ → D₁} → x ⊑₁ x → x′ ⊑₁ x′ → (∀ n → d n ⊑₁ d n) → (∀ n → d′ n ⊑₁ d′ n) →
         x ⊑₁ x′ → (∀ n → d n ⊑₁ d′ n) → ∀ k → (x ⨾ preL d k) ⊑₁ (x′ ⨾ nl d′)

Rf : D₁ → Set
Rf x = x ⊑₁ x

rPre : ∀ {e : ℕ → D₁} → (∀ n → Rf (e n)) → ∀ k → Rf (preL e k)
rPre r zero = n0⊑
rPre r (suc k) = ⨾⊑ (rPre r k) (rPre r k) (rPre r k) (r k)
```

## §3 状态与读数

```agda
SRel : P.St W → P.St W → Set
SRel Y Y′ = (o₀ (P.d Y) ⊑₀ o₀ (P.d Y′)) × (d₁ Y ⊑₁ d₁ Y′)

Good : P.St W → Set
Good Y = Rf (d₁ Y)

sr : ∀ {Y} → Good Y → SRel Y Y
sr {Y} g = refl₀ (o₀ (P.d Y)) , g

Obs : P.Df W → P.Df W → Set
Obs Δ Δ′ = (o₀ Δ ⊑₀ o₀ Δ′) × (o₁ Δ ⊑₁ o₁ Δ′)

G⊕ : ∀ {Y Δ} → Good Y → Rf (o₁ Δ) → Good (Y ⊕ Δ)
G⊕ g r = ⨾⊑ g g g r

S⊕ : ∀ {Y Y′ Δ Δ′} → Good Y → Good Y′ → SRel Y Y′ → Obs Δ Δ′ → SRel (Y ⊕ Δ) (Y′ ⊕ Δ′)
S⊕ g g′ s o = sq (proj₁ s) (proj₁ o) , ⨾⊑ g g′ (proj₂ s) (proj₂ o)

G⊕0 : ∀ {Y} → Good Y → Good (Y ⊕ P.zeroD)
G⊕0 g = ⨾⊑ g g g n0⊑

S0ˡ : ∀ {Y Y′} → SRel Y Y′ → SRel (Y ⊕ P.zeroD) Y′
S0ˡ s = u1l (proj₁ s) , u1ˡ (proj₂ s)

S0ʳ : ∀ {Y Y′} → SRel Y Y′ → SRel Y (Y′ ⊕ P.zeroD)
S0ʳ s = u1r (proj₁ s) , u1ʳ (proj₂ s)

G⨾ᴰ : ∀ {Y Δ₁ Δ₂} → Good Y → Rf (o₁ Δ₁) → Rf (o₁ Δ₂) → Good (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂))
G⨾ᴰ g r₁ r₂ = ⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂)

-- 两段一起加与分开加: 两层都由结合律对上
asS : ∀ {Y Δ₁ Δ₂} → Good Y → Rf (o₁ Δ₁) → Rf (o₁ Δ₂) →
      SRel (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂)) ((Y ⊕ Δ₁) ⊕ Δ₂) × SRel ((Y ⊕ Δ₁) ⊕ Δ₂) (Y ⊕ (Δ₁ P.⨾ᴰ Δ₂))
asS {Y} {Δ₁} {Δ₂} g r₁ r₂ =
  (ar′ (refl₀ (o₀ (P.d Y) ⨾ (o₀ Δ₁ ⨾ o₀ Δ₂))) , asʳ′ g r₁ r₂ (⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂))) ,
  (al (refl₀ (o₀ (P.d Y) ⨾ (o₀ Δ₁ ⨾ o₀ Δ₂))) , asˡ g r₁ r₂ (⨾⊑ g g g (⨾⊑ r₁ r₁ r₁ r₂)))

rfΩ : Rf (Ωd (hs hz) {W})
rfΩ = ⨾⊑ n1⊑ n1⊑ n1⊑ (ni⊑ m m m)
  where
  m : ∀ (z z′ : D hz W) → z ⊑₀ z′ → n1 ⊑₁ n1
  m _ _ _ = n1⊑
```

## §4 动作, 部分和的输出

```agda
HA₁ : Act₁ → Set
HA₁ A₀ = ∀ (w w′ : D₁) Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (A₀ C.self lW w Y) (A₀ C.self lW w′ Y′)

-- 走部分和 preL d k 在两个目标上的输出字面就是各段输出的部分和
module PreOut {ly V} (ac : AccY ly) (ll : P.LW ly W) (A₀ : P.Ig ly W) (d : ℕ → D ly V) (q : V ⊲ W) (w : D ly W) (Z : P.St W) where
  Rp : ℕ → P.Df W
  Rp k = P.Run ac (preL d k) q lW ll A₀ w Z

  Ek : ℕ → P.Df W
  Ek k = P.Run ac (d k) q lW ll A₀ (w ⨾ nw q (preL d k)) (Z ⊕ Rp k)

  O≡ : ∀ k → o₁ (Rp k) ≡ preL (λ n → o₁ (Ek n)) k
  O≡ zero = refl
  O≡ (suc k) = cong (λ t → t ⨾ o₁ (Ek k)) (O≡ k)

  O≡₀ : ∀ k → o₀ (Rp k) ≡ preL (λ n → o₀ (Ek n)) k
  O≡₀ zero = refl
  O≡₀ (suc k) = cong (λ t → t ⨾ o₀ (Ek k)) (O≡₀ k)
```
