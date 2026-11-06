# 和形式, 层取可变位数 (三): 闭项

> 不含记号. 入口 [SumVar](SumVar.lagda.md). 同 [SumClimbClosed](SumClimbClosed.lagda.md) 的做法, 但**积木对一切深度一个定义**. $S=\cdot\omega$ 的实例.
>
> - `TΩ L`: 一切合法层 $L$ (任意位数) 自己的 $\Omega$ 的折叠.
> - 积木: `nd ns` $=\sum_{z:ns}1$ (层 `ns`, 各位是自然数); `κ j ns` $=\sum_{c\ge\omega}\sum_{z:(0,\dots,0,c,ns)}1$ (低 $j$ 位为零); `Blk j ns`: 深度 $j$ 的一段, `Blk 0 ns = nd ns`, `Blk (j+1) ns = ` $\sum_{n<\omega}$ `Blk j (n ∷ ns)` `⨾ κ j ns`. 三位时的 `nd r n m`, `B r n`, `BR r` 分别是 `Blk 0 [m,n,r]`, `Blk 1 [n,r]`, `Blk 2 [r]`, `κ3` 是 `κ 2 []`.
> - `Rj j` $=\sum_{n<\omega}$ `Blk j [n+1]` `⨾ κ j []`: 从 $\Omega^j$ 到 $\Omega^{j+1}$ 的一段, 层有 $j+1$ 位. 低于 $\Omega^j$ 的部分已由更短的层给出, 所以从 `[1]` 起.
> - 站: `X⁰ j` $=1$ `⨾ nd [] ⨾ Rj 0 ⨾ … ⨾ Rj (j-1)`; `Xs j d ds` 再接 `Blk j [1] ⨾ … ⨾ Blk j [d]` 与 `ds` 给的前缀 (`Pr`); `Xω` $=1$ `⨾ nd [] ⨾` $\sum_j$ `Rj j`.
>
> 读法 (判断): `T⁰ j` 读 $\psi_0(\Omega_{\Omega^j})$, `Ts j d ds` 读 $\psi_0(\Omega_{\Omega^j\cdot(d+1)+\Omega^{j-1}ds_0+\dots+ds_{j-1}})$, `Tω` 读 $\psi_0(\Omega_{\Omega^\omega})$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumVarClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.SumVarTree

ω⋅ : ∀ {Kd : A → Lay → Set} {V′ : ∀ {W L} → Kd W L → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W
ω⋅ c = nl (λ _ → c)

open import OCF.Align.SumVarFold ω⋅ public
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

对一切位数的合法层.

```agda
ΔΩ : ∀ L {m} → Lg m → AllB L m → Df m
ΔΩ L lm Lm = Run (accY L) (Ωd L (allLg Lm lm)) C.self lm Lm Act n0 Y₀

TΩ : ∀ L {m} → Lg m → AllB L m → A
TΩ L lm Lm = sum azero (n1 ⨾ yc (ΔΩ L lm Lm) (τ₀ lm))

Lg-TΩ : ∀ L {m} (lm : Lg m) (Lm : AllB L m) → Lg (TΩ L lm Lm)
Lg-TΩ L lm Lm = Lg-sum azero (n1 ⨾ yc (ΔΩ L lm Lm) (τ₀ lm)) tt
```

## §3 积木与站

```agda
Δ : D̂ ω → Df ω
Δ x = Run accTop x C.self lω tt Act n0 Y₀

Tψ : D̂ ω → A
Tψ x = sum azero (n1 ⨾ yc (Δ x) (τ₀ lω))

Lg-Tψ : ∀ x → Lg (Tψ x)
Lg-Tψ x = Lg-sum azero (n1 ⨾ yc (Δ x) (τ₀ lω)) tt

c1 : ∀ {ly W₀ L′} (x : K ly W₀ L′) → ∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly x W′ → Dl ly W′
c1 x _ _ _ = n1

lyN : List ℕ → Lay
lyN [] = []
lyN (n ∷ ns) = natA n ∷ lyN ns

allN : ∀ ns → AllB (lyN ns) ω
allN [] = tt
allN (n ∷ ns) = nω n , allN ns

zs : ℕ → Lay → Lay
zs zero L = L
zs (suc j) L = azero ∷ zs j L

-- 闭包 Σ_{c≥ω} Σ_{z:G c} 1, 闭包节点在世界 ω 上
κN : (G : A → Lay) → (∀ {c} → ω ⊲ c → AllB (G c) c) → D̂ ω
κN G ρ = nκ tt (λ {c} p _ → ni (ρ p) (c1 (ρ p)))

nd : List ℕ → D̂ ω
nd ns = ni (allN ns) (c1 (allN ns))

ρκ : ∀ j ns {c} → ω ⊲ c → AllB (zs j (c ∷ lyN ns)) c
ρκ zero ns p = C.self , hk↑ (allN ns) p
ρκ (suc j) ns {c} p = z⊲ c , ρκ j ns p

κ : ℕ → List ℕ → D̂ ω
κ j ns = κN (λ c → zs j (c ∷ lyN ns)) (ρκ j ns)

-- 深度 j 的一段: 层的高位是 ns, 低 j 位走遍
Blk : ℕ → List ℕ → D̂ ω
Blk zero ns = nd ns
Blk (suc j) ns = nl (λ n → Blk j (n ∷ ns)) ⨾ κ j ns

-- 从 Ω^j 到 Ω^{j+1}
Rj : ℕ → D̂ ω
Rj j = nl (λ n → Blk j (suc n ∷ [])) ⨾ κ j []

Pfx : (ℕ → D̂ ω) → ℕ → ℕ → D̂ ω → D̂ ω
Pfx F k zero rest = rest
Pfx F k (suc n) rest = F k ⨾ Pfx F (suc k) n rest

-- 高位 ns 之下, 各位 es (高位在前) 给的前缀
Pr : ∀ {k} → List ℕ → Vec ℕ k → D̂ ω → D̂ ω
Pr ns [] rest = rest
Pr {suc k} ns (e ∷ es) rest = Pfx (λ c → Blk k (c ∷ ns)) 0 e (Pr (e ∷ ns) es rest)

X⁰ : ℕ → D̂ ω
X⁰ j = n1 ⨾ (nd [] ⨾ Pfx Rj 0 j n0)

Xs : ∀ j → ℕ → Vec ℕ j → D̂ ω
Xs j d ds = n1 ⨾ (nd [] ⨾ Pfx Rj 0 j (Pfx (λ n → Blk j (suc n ∷ [])) 0 d (Pr (suc d ∷ []) ds n0)))

Xω : D̂ ω
Xω = n1 ⨾ (nd [] ⨾ nl Rj)

T⁰ : ℕ → A
T⁰ j = Tψ (X⁰ j)

Ts : ∀ j → ℕ → Vec ℕ j → A
Ts j d ds = Tψ (Xs j d ds)

Tω : A
Tω = Tψ Xω

Lg-T⁰ : ∀ j → Lg (T⁰ j)
Lg-T⁰ j = Lg-Tψ (X⁰ j)

Lg-Ts : ∀ j d ds → Lg (Ts j d ds)
Lg-Ts j d ds = Lg-Tψ (Xs j d ds)

Lg-Tω : Lg Tω
Lg-Tω = Lg-Tψ Xω

-- 几个具体的站 (读法是判断)
TΩ²+1 TΩ²·2 TΩ³ TΩ⁴ TΩ^ω : A
TΩ²+1 = Ts 2 0 (0 ∷ 1 ∷ [])
TΩ²·2 = Ts 2 1 (0 ∷ 0 ∷ [])
TΩ³ = T⁰ 3
TΩ⁴ = T⁰ 4
TΩ^ω = Tω
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
fgh = FL.FGH (ord Tω)
```
