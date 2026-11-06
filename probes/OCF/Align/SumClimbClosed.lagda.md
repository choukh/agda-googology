# 和形式, 层取三位 (三): 闭项

> 不含记号. 入口 [SumClimb](SumClimb.lagda.md). 同 [SumHtClosed](SumHtClosed.lagda.md) 的做法, 多一级. $S=\cdot\omega$ 的实例.
>
> - `TΩ r p a`: 层 $(r,p,a)$ 自己的 $\Omega$ 的折叠, 对一切合法的 $r,p,a$.
> - 站: 顶层在世界 $\omega$ 上的输入的折叠. 积木: `nd r n m` $=\sum_{z:(r,n,m)}1$; `B r n` $=\sum_{m<\omega}$`nd r n m` $+\sum_{d\ge\omega}\sum_{z:(r,n,d)}1$ (第二位 $n\to n+1$); `BR r` $=\sum_{n<\omega}$`B r n` $+\sum_{c\ge\omega}\sum_{z:(r,c,0)}1$ (第一位 $r\to r+1$); `κ3` $=\sum_{c\ge\omega}\sum_{z:(c,0,0)}1$. 闭包节点都由同一个 `κN` 造出, 节点的层由函数 `ρ` 给.
>
> 读法 (判断): `T r n a` 读 $\psi_0(\Omega_{\Omega^2\cdot r+\Omega\cdot n+a})$, `TNω r n` 读 $\psi_0(\Omega_{\Omega^2\cdot r+\Omega\cdot n+\omega})$, `TRω r` 读 $\psi_0(\Omega_{\Omega^2\cdot r+\Omega\cdot\omega})$, `Tω` 读 $\psi_0(\Omega_{\Omega^2\cdot\omega})$, `T³` 读 $\psi_0(\Omega_{\Omega^3})$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumClimbClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.SumClimbTree

ω⋅ : ∀ {Kd : A → A → A → A → Set} {V′ : ∀ {W g h k} → Kd W g h k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W
ω⋅ c = nl (λ _ → c)

open import OCF.Align.SumClimbFold ω⋅ public
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

Act : ∀ {ly W} → Ig ly W
Act p lW′ _ Y = Step Y

Y₀ : ∀ {W} → St W
Y₀ = st zeroD n0
```

## §2 每一层自己的 $\Omega$

```agda
ΔΩ : ∀ r p a {m} → Lg m → r ⊲ m → p ⊲ m → a ⊲ m → Df m
ΔΩ r p a lm rm pm am = Run (accY r p a) (Ωd r p a (lg⊲ rm lm) (lg⊲ pm lm) (lg⊲ am lm)) C.self lm (rm , (pm , am)) Act n0 Y₀

TΩ : ∀ r p a {m} → Lg m → r ⊲ m → p ⊲ m → a ⊲ m → A
TΩ r p a lm rm pm am = sum azero (n1 ⨾ yc (ΔΩ r p a lm rm pm am) (τ₀ lm))

Lg-TΩ : ∀ r p a {m} (lm : Lg m) (rm : r ⊲ m) (pm : p ⊲ m) (am : a ⊲ m) → Lg (TΩ r p a lm rm pm am)
Lg-TΩ r p a lm rm pm am = Lg-sum azero (n1 ⨾ yc (ΔΩ r p a lm rm pm am) (τ₀ lm)) tt
```

## §3 站

```agda
Δ : D̂ ω → Df ω
Δ x = Run accTop x C.self lω tt Act n0 Y₀

Tψ : D̂ ω → A
Tψ x = sum azero (n1 ⨾ yc (Δ x) (τ₀ lω))

Lg-Tψ : ∀ x → Lg (Tψ x)
Lg-Tψ x = Lg-sum azero (n1 ⨾ yc (Δ x) (τ₀ lω)) tt

c1 : ∀ {ly W₀ g h k} (x : K ly W₀ g h k) → ∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly x W′ → Dl ly W′
c1 x _ _ _ = n1

-- 闭包 Σ_{c≥ω} Σ_{z:ρ c} 1, 闭包节点在世界 ω 上
κN : (G′ H′ K′ : A → A) → (∀ {c} → ω ⊲ c → KT c (G′ c) (H′ c) (K′ c)) → D̂ ω
κN G′ H′ K′ ρ = nκ tt (λ {c} p _ → ni (ρ p) (c1 (ρ p)))

nd : ℕ → ℕ → ℕ → D̂ ω
nd r n m = ni (nω r , (nω n , nω m)) (c1 (nω r , (nω n , nω m)))

ρB : ∀ r n {c} → ω ⊲ c → KT c (natA r) (natA n) c
ρB r n p = ⊲-tr (nω r) p , (⊲-tr (nω n) p , C.self)

ρR : ∀ r {c} → ω ⊲ c → KT c (natA r) c azero
ρR r {c} p = ⊲-tr (nω r) p , (C.self , z⊲ c)

ρ3 : ∀ {c} → ω ⊲ c → KT c c azero azero
ρ3 {c} p = C.self , (z⊲ c , z⊲ c)

κB : ℕ → ℕ → D̂ ω
κB r n = κN (λ _ → natA r) (λ _ → natA n) (λ c → c) (ρB r n)

κR : ℕ → D̂ ω
κR r = κN (λ _ → natA r) (λ c → c) (λ _ → azero) (ρR r)

κ3 : D̂ ω
κ3 = κN (λ c → c) (λ _ → azero) (λ _ → azero) ρ3

-- 第二位 n → n+1 的一段
B : ℕ → ℕ → D̂ ω
B r n = nl (nd r n) ⨾ κB r n

-- 第一位 r → r+1 的一段
BR : ℕ → D̂ ω
BR r = nl (B r) ⨾ κR r

Pfx : (ℕ → D̂ ω) → ℕ → ℕ → D̂ ω → D̂ ω
Pfx F k zero tl = tl
Pfx F k (suc n) tl = F k ⨾ Pfx F (suc k) n tl

X : ℕ → ℕ → ℕ → D̂ ω
X r n a = n1 ⨾ Pfx BR 0 r (Pfx (B r) 0 n (Pfx (nd r n) 0 a n0))

XNω : ℕ → ℕ → D̂ ω
XNω r n = n1 ⨾ Pfx BR 0 r (Pfx (B r) 0 n (nl (nd r n)))

XRω : ℕ → D̂ ω
XRω r = n1 ⨾ Pfx BR 0 r (nl (B r))

Xω : D̂ ω
Xω = n1 ⨾ nl BR

X³ : D̂ ω
X³ = n1 ⨾ (nl BR ⨾ κ3)

T : ℕ → ℕ → ℕ → A
T r n a = Tψ (X r n a)

TNω : ℕ → ℕ → A
TNω r n = Tψ (XNω r n)

TRω : ℕ → A
TRω r = Tψ (XRω r)

Tω : A
Tω = Tψ Xω

T³ : A
T³ = Tψ X³

-- 要求的各站
TΩ²+1 TΩ²·2 TΩ²·ω TΩ³ : A
TΩ²+1 = T 1 0 1
TΩ²·2 = T 2 0 0
TΩ²·ω = Tω
TΩ³ = T³

Lg-T : ∀ r n a → Lg (T r n a)
Lg-T r n a = Lg-Tψ (X r n a)

Lg-Tω : Lg Tω
Lg-Tω = Lg-Tψ Xω

Lg-T³ : Lg T³
Lg-T³ = Lg-Tψ X³
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
fgh = FL.FGH (ord T³)
```
