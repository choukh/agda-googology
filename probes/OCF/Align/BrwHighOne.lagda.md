# 高层的布劳威尔树 (一): 数类第 1 层的正规节点

> 不含记号. 入口 [BrwHigh](BrwHigh.lagda.md).
>
> - `B₁`: 数类第 1 层的布劳威尔树. $\Omega$-极限节点 `bN g` 的分支 $g$ 以第 0 层的树 $z$ 为参数. 第 0 层的树用差的写法 (`D₀`, 与 `Σ A Lg` 互译到值, [BrwMidZero](BrwMidZero.lagda.md)). 回灌的节点 `bK b g` 同形, 分支以世界 $b$ 之上的层为参数, 层写成 $b$ 加一段差.
> - `Lg₁`: 字面合法: 极限的相邻项是第一位置, 节点的分支沿坐标的前缀单调: $g(z)\lhd_1 g(z\,⨾\,y)$.
> - `Ig Δ`: **正规的分支**, 对坐标 $z$ 的结构递归: $g(0)=0$, $g(z+1)=g(z)\boxplus\Delta(z)$, $g(\lim)$ = 部分和的极限. `Ig-pre`: 沿前缀单调, 无前提, 来自 `⊞₁-fst`.
> - `N₁`, `br`: 正规的树与它的布劳威尔读法. `Lg-br`: **一切正规的树读出来都字面合法, 无前提.**
> - `incr-blind`: 只沿前缀单调 (合法) 的节点不被增量决定: 分支 `gL` 与正规的 `Ig (const 0)` 起点相同, 每个后继增量相同, 都合法, 在 $\omega$ 处一个是 $1$ 一个是 $0$. 所以读回增量要节点本身正规, 合法性不够.
> - `nrm`, `out-legal`: 第 1 层的差树 (`SumOne`, `BrwMid` 的第 1 层状态都是) 读成正规的树, 合法, 无前提. 增量就是差树节点的分支, 折叠直接算出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwHighOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; drp; sum; sum-fst; Lg-sum)
```

## §1 树, 加法, 第一位置

```agda
D₀ : Set
D₀ = D azero azero

data B₁ : Set where
  bz : B₁
  bs : B₁ → B₁
  bl : (ℕ → B₁) → B₁
  bN : (D₀ → B₁) → B₁
  bK : A → (D₀ → B₁) → B₁

infixl 6 _⊞₁_
_⊞₁_ : B₁ → B₁ → B₁
a ⊞₁ bz = a
a ⊞₁ bs b = bs (a ⊞₁ b)
a ⊞₁ bl f = bl (λ n → a ⊞₁ f n)
a ⊞₁ bN g = bN (λ z → a ⊞₁ g z)
a ⊞₁ bK c g = bK c (λ z → a ⊞₁ g z)

infix 4 _⊲₁_
data _⊲₁_ : B₁ → B₁ → Set where
  self : ∀ {a} → a ⊲₁ a
  s    : ∀ {a b} → a ⊲₁ b → a ⊲₁ bs b
  l    : ∀ {a f} n → a ⊲₁ f n → a ⊲₁ bl f
  N    : ∀ {a g} z → a ⊲₁ g z → a ⊲₁ bN g
  K    : ∀ {a c g} z → a ⊲₁ g z → a ⊲₁ bK c g

⊲₁-tr : ∀ {a b c} → a ⊲₁ b → b ⊲₁ c → a ⊲₁ c
⊲₁-tr p self = p
⊲₁-tr p (s q) = s (⊲₁-tr p q)
⊲₁-tr p (l n q) = l n (⊲₁-tr p q)
⊲₁-tr p (N z q) = N z (⊲₁-tr p q)
⊲₁-tr p (K z q) = K z (⊲₁-tr p q)

⊞₁-fst : ∀ a b → a ⊲₁ a ⊞₁ b
⊞₁-fst a bz = self
⊞₁-fst a (bs b) = s (⊞₁-fst a b)
⊞₁-fst a (bl f) = l 0 (⊞₁-fst a (f 0))
⊞₁-fst a (bN g) = N n0 (⊞₁-fst a (g n0))
⊞₁-fst a (bK c g) = K n0 (⊞₁-fst a (g n0))

⊞₁-⊲ : ∀ a {x y} → x ⊲₁ y → a ⊞₁ x ⊲₁ a ⊞₁ y
⊞₁-⊲ a self = self
⊞₁-⊲ a (s q) = s (⊞₁-⊲ a q)
⊞₁-⊲ a (l n q) = l n (⊞₁-⊲ a q)
⊞₁-⊲ a (N z q) = N z (⊞₁-⊲ a q)
⊞₁-⊲ a (K z q) = K z (⊞₁-⊲ a q)
```

## §2 字面合法

```agda
Lg₁ : B₁ → Set
Lg₁ bz = ⊤
Lg₁ (bs a) = Lg₁ a
Lg₁ (bl f) = (∀ n → f n ⊲₁ f (suc n)) × (∀ n → Lg₁ (f n))
Lg₁ (bN g) = (∀ z y → g z ⊲₁ g (z ⨾ y)) × (∀ z → Lg₁ (g z))
Lg₁ (bK c g) = (∀ z y → g z ⊲₁ g (z ⨾ y)) × (∀ z → Lg₁ (g z))

Lg-⊞₁ : ∀ a b → Lg₁ a → Lg₁ b → Lg₁ (a ⊞₁ b)
Lg-⊞₁ a bz u v = u
Lg-⊞₁ a (bs b) u v = Lg-⊞₁ a b u v
Lg-⊞₁ a (bl f) u (st , v) = (λ n → ⊞₁-⊲ a (st n)) , (λ n → Lg-⊞₁ a (f n) u (v n))
Lg-⊞₁ a (bN g) u (st , v) = (λ z y → ⊞₁-⊲ a (st z y)) , (λ z → Lg-⊞₁ a (g z) u (v z))
Lg-⊞₁ a (bK c g) u (st , v) = (λ z y → ⊞₁-⊲ a (st z y)) , (λ z → Lg-⊞₁ a (g z) u (v z))
```

## §3 正规的分支

`Ig Δ w δ`: 坐标从 $w$ 再走 $\delta$, 分支长了多少. 分支是 `Ig Δ n0`. 对 $\delta$ 的结构递归; 极限是部分和.

```agda
Ig  : ∀ {V} → (D₀ → B₁) → D₀ → D azero V → B₁
Ips : ∀ {V} → (D₀ → B₁) → D₀ → (ℕ → D azero V) → ℕ → B₁ × D₀
Ig Δ w n0 = bz
Ig Δ w n1 = Δ w
Ig Δ w (x ⨾ y) = Ig Δ w x ⊞₁ Ig Δ (w ⨾ drp x) y
Ig Δ w (nl d) = bl (λ n → proj₁ (Ips Δ w d n))
Ig Δ w (ni () u)
Ig Δ w (nκ () u)
Ig Δ w (nw p x) = Ig Δ w x
Ips Δ w d zero = bz , w
Ips Δ w d (suc n) = (proj₁ (Ips Δ w d n) ⊞₁ Ig Δ (proj₂ (Ips Δ w d n)) (d n)) , (proj₂ (Ips Δ w d n) ⨾ drp (d n))

-- 沿前缀单调, 无前提
Ig-pre : (Δ : D₀ → B₁) (z y : D₀) → Ig Δ n0 z ⊲₁ Ig Δ n0 (z ⨾ y)
Ig-pre Δ z y = ⊞₁-fst (Ig Δ n0 z) (Ig Δ (n0 ⨾ drp z) y)

Lg-Ig  : ∀ {V} (Δ : D₀ → B₁) → (∀ w → Lg₁ (Δ w)) → ∀ w (δ : D azero V) → Lg₁ (Ig Δ w δ)
Lg-Ips : ∀ {V} (Δ : D₀ → B₁) → (∀ w → Lg₁ (Δ w)) → ∀ w (d : ℕ → D azero V) n → Lg₁ (proj₁ (Ips Δ w d n))
Lg-Ig Δ h w n0 = tt
Lg-Ig Δ h w n1 = h w
Lg-Ig Δ h w (x ⨾ y) = Lg-⊞₁ _ _ (Lg-Ig Δ h w x) (Lg-Ig Δ h (w ⨾ drp x) y)
Lg-Ig Δ h w (nl d) = (λ n → ⊞₁-fst _ _) , Lg-Ips Δ h w d
Lg-Ig Δ h w (ni () u)
Lg-Ig Δ h w (nκ () u)
Lg-Ig Δ h w (nw p x) = Lg-Ig Δ h w x
Lg-Ips Δ h w d zero = tt
Lg-Ips Δ h w d (suc n) = Lg-⊞₁ _ _ (Lg-Ips Δ h w d n) (Lg-Ig Δ h _ (d n))

-- 正规节点: 合法, 前提只在增量上
Lg-node : (Δ : D₀ → B₁) → (∀ w → Lg₁ (Δ w)) → Lg₁ (bN (Ig Δ n0))
Lg-node Δ h = Ig-pre Δ , Lg-Ig Δ h n0
```

## §4 正规的树

```agda
data N₁ : Set where
  mz : N₁
  m1 : N₁
  _∔_ : N₁ → N₁ → N₁
  ml : (ℕ → N₁) → N₁
  mN : (D₀ → N₁) → N₁
  mK : A → (D₀ → N₁) → N₁

br : N₁ → B₁
br mz = bz
br m1 = bs bz
br (x ∔ y) = br x ⊞₁ br y
br (ml d) = bl (λ n → pl n)
  where
  pl : ℕ → B₁
  pl zero = bz
  pl (suc n) = pl n ⊞₁ br (d n)
br (mN Δ) = bN (Ig (λ w → br (Δ w)) n0)
br (mK c Δ) = bK c (Ig (λ w → br (Δ w)) n0)

Lg-br : ∀ x → Lg₁ (br x)
Lg-br mz = tt
Lg-br m1 = tt
Lg-br (x ∔ y) = Lg-⊞₁ _ _ (Lg-br x) (Lg-br y)
Lg-br (ml d) = (λ n → ⊞₁-fst _ _) , pl
  where
  pl : ∀ n → Lg₁ _
  pl zero = tt
  pl (suc n) = Lg-⊞₁ _ _ (pl n) (Lg-br (d n))
Lg-br (mN Δ) = Lg-node (λ w → br (Δ w)) (λ w → Lg-br (Δ w))
Lg-br (mK c Δ) = Ig-pre (λ w → br (Δ w)) , Lg-Ig (λ w → br (Δ w)) (λ w → Lg-br (Δ w)) n0
```

## §5 合法不等于正规

```agda
hasL : ∀ {V} → D azero V → Bool
hasL n0 = false
hasL n1 = false
hasL (x ⨾ y) = hasL y ∨ hasL x
hasL (nl d) = true
hasL (ni () u)
hasL (nκ () u)
hasL (nw p x) = hasL x

gL : D₀ → B₁
gL z with hasL z
... | true = bs bz
... | false = bz

∨-l : ∀ a b → a ≡ true → (b ∨ a) ≡ true
∨-l a true e = refl
∨-l a false e = e

gT : Bool → B₁
gT true = bs bz
gT false = bz

gL≡ : ∀ z → gL z ≡ gT (hasL z)
gL≡ z with hasL z
... | true = refl
... | false = refl

gT-∨ : ∀ a b → gT a ⊲₁ gT (b ∨ a)
gT-∨ true true = self
gT-∨ true false = self
gT-∨ false true = s self
gT-∨ false false = self

gL-pre : ∀ z y → gL z ⊲₁ gL (z ⨾ y)
gL-pre z y rewrite gL≡ z | gL≡ (z ⨾ y) = gT-∨ (hasL z) (hasL y)

Lg-gL : Lg₁ (bN gL)
Lg-gL = gL-pre , lg
  where
  lg : ∀ z → Lg₁ (gL z)
  lg z with hasL z
  ... | true = tt
  ... | false = tt

-- 值为 0
data Z₁ : B₁ → Set where
  zz : Z₁ bz
  zl : ∀ {f} → (∀ n → Z₁ (f n)) → Z₁ (bl f)

Z-⊞ : ∀ {a b} → Z₁ a → Z₁ b → Z₁ (a ⊞₁ b)
Z-⊞ za zz = za
Z-⊞ za (zl h) = zl (λ n → Z-⊞ za (h n))

Z-Ig  : ∀ {V} w (δ : D azero V) → Z₁ (Ig (λ _ → bz) w δ)
Z-Ips : ∀ {V} w (d : ℕ → D azero V) n → Z₁ (proj₁ (Ips (λ _ → bz) w d n))
Z-Ig w n0 = zz
Z-Ig w n1 = zz
Z-Ig w (x ⨾ y) = Z-⊞ (Z-Ig w x) (Z-Ig (w ⨾ drp x) y)
Z-Ig w (nl d) = zl (Z-Ips w d)
Z-Ig w (ni () u)
Z-Ig w (nκ () u)
Z-Ig w (nw p x) = Z-Ig w x
Z-Ips w d zero = zz
Z-Ips w d (suc n) = Z-⊞ (Z-Ips w d n) (Z-Ig (proj₂ (Ips (λ _ → bz) w d n)) (d n))

ωz : D₀
ωz = nl (λ _ → n1)

-- 同一个起点, 同样的后继增量, 都合法; 在 ω 处值不同
incr-blind :
  (gL n0 ≡ Ig {azero} (λ _ → bz) n0 n0) ×
  (∀ (w : D₀) → gL (w ⨾ n1) ≡ gL w ⊞₁ bz) ×
  (∀ (w : D₀) → Ig {azero} (λ _ → bz) n0 (w ⨾ n1) ≡ Ig {azero} (λ _ → bz) n0 w ⊞₁ bz) ×
  Lg₁ (bN gL) × Lg₁ (bN (Ig (λ _ → bz) n0)) ×
  (gL ωz ≡ bs bz) × Z₁ (Ig (λ _ → bz) n0 ωz) × ¬ Z₁ (bs bz)
incr-blind = refl , gL1 , (λ w → refl) , Lg-gL , Lg-node (λ _ → bz) (λ _ → tt) , refl , Z-Ig n0 ωz , (λ ())
  where
  gL1 : ∀ w → gL (w ⨾ n1) ≡ gL w ⊞₁ bz
  gL1 w with hasL w
  ... | true = refl
  ... | false = refl
```

## §6 第 1 层的差树读成正规的树

`nrm`: 节点 `ni` 的分支就是增量; `nκ` 的分支在层 $W\boxplus$ 一段差上取. 世界只用 $W$ 本身.

```agda
nrm : ∀ {W} → Lg W → D (asuc azero) W → N₁
nrm lW n0 = mz
nrm lW n1 = m1
nrm lW (x ⨾ y) = nrm lW x ∔ nrm lW y
nrm lW (nl d) = ml (λ n → nrm lW (d n))
nrm {W} lW (ni (ss C.self) u) = mN (λ z → nrm lW (u C.self lW (drp z)))
nrm {W} lW (nκ _ u) = mK W (λ z → nrm (Lg-sum W z lW) (u (sum-fst W z) (Lg-sum W z lW)))
nrm lW (nw p x) = nrm (lg⊲ p lW) x

out-legal : ∀ {W} (lW : Lg W) (x : D (asuc azero) W) → Lg₁ (br (nrm lW x))
out-legal lW x = Lg-br (nrm lW x)
```
