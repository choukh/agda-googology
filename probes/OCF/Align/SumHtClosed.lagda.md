# 和形式, 高度取 $A$ (三): 闭项

> 不含记号. 入口 [SumHt](SumHt.lagda.md). $S=\cdot\omega$ 的实例 (同 `SumOneClosed`). 两族闭项, 都没有证书参数, 合法性都只是 `Lg-sum` 的一次调用:
>
> - `TΩ p a`: 层 $(p,a)$ 自己的 $\Omega_{\Omega\cdot p+a}$ (`Ωd`) 的折叠, 对一切合法的 $p,a$.
> - **站** `T n a`, `Tω`, `T²`: 顶层在世界 $\omega$ 上的输入的折叠, 各站的输入用同一组积木 (`nd`, `B`, `κH`) 拼出, 所以相邻两站字面相接, 严格增长在 [SumHtGrow](SumHtGrow.lagda.md) 里证. 读法 (判断): `T n a` 读 $\psi_0(\Omega_{\Omega\cdot n+a})$, `Tω` 读 $\psi_0(\Omega_{\Omega\cdot\omega})$, `T²` 读 $\psi_0(\Omega_{\Omega^2})$.
>
> 积木的读法: `nd n m` 是 $\sum_{z:(n,m)}1$; `B n` 是 $\sum_{m<\omega}\sum_{z:(n,m)}1+\sum_{d\ge\omega}\sum_{z:(n,d)}1$, 即高度 $n\to n+1$ 的那一段; `κH` 是 $\sum_{c\ge\omega}\sum_{z:(c,0)}1$. 闭包节点放在运行的世界 $\omega$ 上, 世界之前的部分 ($m<\omega$) 显式写成 ℕ-和. 这是一个选择 (判断: 值不变, 见 [SumHt](SumHt.lagda.md) 的翻译账), 它让 `T 1 2` 字面是 `T 2 0` 的前缀的前缀.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumHtClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.SumHtTree

ω⋅ : ∀ {Kd : A → A → A → Set} {V′ : ∀ {W h k} → Kd W h k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W
ω⋅ c = nl (λ _ → c)

open import OCF.Align.SumHtFold ω⋅ public
```

## §1 世界 $\omega$ 与一格

```agda
natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ω : A
ω = alim natA

lgN : ∀ n → Lg (natA n)
lgN zero = tt
lgN (suc n) = lgN n

lω : Lg ω
lω = (λ n → C.suc C.self) , lgN

nω : ∀ n → natA n ⊲ ω
nω n = C.lim n C.self

-- 顶上的一格: 每个位置做一次 Step
Act : ∀ {ly W} → Ig ly W
Act p lW′ _ Y = Step Y

Y₀ : ∀ {W} → St W
Y₀ = st zeroD n0
```

## §2 每一层自己的 $\Omega$

```agda
ΔΩ : ∀ p a {m} → Lg m → p ⊲ m → a ⊲ m → Df m
ΔΩ p a lm pm am = Run (accY p a) (Ωd p a (lg⊲ pm lm) (lg⊲ am lm)) C.self lm (pm , am) Act n0 Y₀

TΩ : ∀ p a {m} → Lg m → p ⊲ m → a ⊲ m → A
TΩ p a lm pm am = sum azero (n1 ⨾ yc (ΔΩ p a lm pm am) (τ₀ lm))

Lg-TΩ : ∀ p a {m} (lm : Lg m) (pm : p ⊲ m) (am : a ⊲ m) → Lg (TΩ p a lm pm am)
Lg-TΩ p a lm pm am = Lg-sum azero (n1 ⨾ yc (ΔΩ p a lm pm am) (τ₀ lm)) tt
```

## §3 站

```agda
Δ : D̂ ω → Df ω
Δ x = Run accTop x C.self lω tt Act n0 Y₀

Tψ : D̂ ω → A
Tψ x = sum azero (n1 ⨾ yc (Δ x) (τ₀ lω))

Lg-Tψ : ∀ x → Lg (Tψ x)
Lg-Tψ x = Lg-sum azero (n1 ⨾ yc (Δ x) (τ₀ lω)) tt

-- Σ_{z:(n,m)} 1
nd : ℕ → ℕ → D̂ ω
nd n m = ni (nω n , nω m) (λ _ _ _ → n1)

-- Σ_{d≥ω} Σ_{z:(n,d)} 1: 闭包节点在世界 ω 上
κB : ℕ → D̂ ω
κB n = nκ tt (λ {d} ωd _ → ni (⊲-tr (nω n) ωd , C.self) (λ _ _ _ → n1))

-- 高度 n → n+1 的一段
B : ℕ → D̂ ω
B n = nl (nd n) ⨾ κB n

-- Σ_{c≥ω} Σ_{z:(c,0)} 1: 高度上的闭包
κH : D̂ ω
κH = nκ tt (λ {c} _ _ → ni (C.self , z⊲ c) (λ _ _ _ → n1))

-- 右结合的前 n 项, 后面接 tl: 与 Run 走 nl 的部分和字面相同 (SumHtGrow 的 L1)
Pfx : (ℕ → D̂ ω) → ℕ → ℕ → D̂ ω → D̂ ω
Pfx F k zero tl = tl
Pfx F k (suc n) tl = F k ⨾ Pfx F (suc k) n tl

Xna : ℕ → ℕ → D̂ ω
Xna n a = n1 ⨾ Pfx B 0 n (Pfx (nd n) 0 a n0)

Xnω : ℕ → D̂ ω
Xnω n = n1 ⨾ Pfx B 0 n (nl (nd n))

Xω : D̂ ω
Xω = n1 ⨾ nl B

X² : D̂ ω
X² = n1 ⨾ (nl B ⨾ κH)

T : ℕ → ℕ → A
T n a = Tψ (Xna n a)

Tnω : ℕ → A
Tnω n = Tψ (Xnω n)

Tω T² : A
Tω = Tψ Xω
T² = Tψ X²

-- 要求的各站
TΩ+1 TΩ+2 TΩ·2 TΩ·ω TΩ² : A
TΩ+1 = T 1 1
TΩ+2 = T 1 2
TΩ·2 = T 2 0
TΩ·ω = Tω
TΩ² = T²

Lg-T : ∀ n a → Lg (T n a)
Lg-T n a = Lg-Tψ (Xna n a)

Lg-Tω : Lg Tω
Lg-Tω = Lg-Tψ Xω

Lg-T² : Lg T²
Lg-T² = Lg-Tψ X²
```

## §4 到第 0 层的树

```agda
ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

G : ℕ → A → ℕ
G n azero = 0
G n (asuc a) = suc (G n a)
G n (alim f) = G n (f n)

fgh : ℕ → ℕ
fgh = FL.FGH (ord T²)
```
