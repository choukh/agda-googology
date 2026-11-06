# 事件世界上的真折叠 (四): 闭项

> 不含记号. 入口 [EvFold](EvFold.lagda.md). $S=\cdot\omega$ 的实例 (同 `HtTowerFClosed`). `TΛ Λ lΛ o₁ o₂`: 层 $\Lambda$ 的 $\Omega_\Lambda$ 折叠到第 0 层的输出, 世界从 $(1, [])$ 起. `T⁺ h = TΛ (3 ⊞ h)`: 第 1, 2 层字面地是第一位置.
>
> **层的高度用到 κ₁** (坐标是 `HB S₁` 的事件种类): `Ω₃ᴱ = hΩ κ₁ (x ↦ x 的嵌入)`, 分支 `nbᴱ` 对 `HB S₁` 坐标递归 (`σA ↦ κa`, `σH ↦ κ₀`), 连续是定义性的. 合法 (`Lg-Ω₃ᴱ`): 单调对坐标的路径归纳, 坐标的界按 `evKS₀` 的内层世界 (全 0) 搬到 `T` 的世界 (`NbE.mono`). 由它: 后继, 两倍, ℕ-倍的极限, κ₁ 上的 $x\mapsto\Omega_3^{\mathcal E}\cdot x$. 对照: `Ω₂ᴱ = hΩ κ₀ (x ↦ x 的嵌入)`.
>
> 读法 $\psi_0(\Omega_\Lambda)$ 是判断 (入口 §读法). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
import OCF.Align.EvFoldFold as Fold
```

## §1 一个定义对一切合法的层

```agda
ω⋅ : ∀ {Kd : Wε → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wε → Set} {Z₀ : Set} {Zε : Kᵉ → Set} {W} → D₊ Kd V′ Z₀ Zε W → D₊ Kd V′ Z₀ Zε W
ω⋅ c = nl (λ _ → c)

one : A
one = asuc azero

W₁ : Wε
W₁ = one , []

module At (Λ : Ht) (lΛ : LgB Λ) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where
  open Fold ω⋅ Λ lΛ o₁ o₂ public

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0 n0

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ {azero , []}) (z⊲ one , here) (tt , tt) hself Act n0 Y₀

  ΨΩ : D₀ W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ (tt , tt))

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

TΛ : ∀ Λ → LgB Λ → (∀ {w} → hs hz ⊲[ w ] Λ) → (∀ {w} → hs (hs hz) ⊲[ w ] Λ) → A
TΛ Λ lΛ o₁ o₂ = At.Tψ Λ lΛ o₁ o₂

Lg-TΛ : ∀ Λ (lΛ : LgB Λ) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) → Lg (TΛ Λ lΛ o₁ o₂)
Lg-TΛ Λ lΛ o₁ o₂ = At.Lg-Tψ Λ lΛ o₁ o₂

three : Ht
three = hs (hs (hs hz))

top₃ : Ht → Ht
top₃ h = three ⊞ h

Lg-top₃ : ∀ h → LgB h → LgB (top₃ h)
Lg-top₃ h lh = Lg-⊞ three h tt lh

o₁⁺ : ∀ h {w} → hs hz ⊲[ w ] top₃ h
o₁⁺ h = ⊲ᴮ-tr (hsuc (hsuc hself)) (⊞-fst three h)

o₂⁺ : ∀ h {w} → hs (hs hz) ⊲[ w ] top₃ h
o₂⁺ h = ⊲ᴮ-tr (hsuc hself) (⊞-fst three h)

T⁺ : ∀ h → LgB h → A
T⁺ h lh = TΛ (top₃ h) (Lg-top₃ h lh) (o₁⁺ h) (o₂⁺ h)

Lg-T⁺ : ∀ h (lh : LgB h) → Lg (T⁺ h lh)
Lg-T⁺ h lh = Lg-TΛ (top₃ h) (Lg-top₃ h lh) (o₁⁺ h) (o₂⁺ h)
```

## §2 κ₁ 上对坐标递归的分支

坐标是 `HB S₁` 的高度 (`S₁ = step S₀`, 种类 `inj₁ tt` 坐标 `A`, `inj₂ tt` 坐标 $H_0$). `nbᴱ` 把坐标里 `inj₁ tt` 的结点换成 `κa`, `inj₂ tt` 的结点换成事件种类 κ₀. 单调: `S₁` 世界 $w$ 里的路径, 只要 $w$ 的两种界能搬进 `T` 的世界 $W$ (`mA`, `mH`), 就是 $W$ 里的路径.

```agda
nbᴱ : Ht → (H₁ → Ht → Ht) → H₁ → Ht
nbᴱ b s hz = b
nbᴱ b s (hs x) = s x (nbᴱ b s x)
nbᴱ b s (hl f) = hl (λ n → nbᴱ b s (f n))
nbᴱ b s (hΩ (inj₁ tt) h) = hΩ κa (λ c → nbᴱ b s (h c))
nbᴱ b s (hΩ (inj₂ tt) h) = hΩ (inj₂ κ₀) (λ c → nbᴱ b s (h c))

-- κ₀ 的界: 在 T 的世界 W 里
β₀ : Wε → H₀
β₀ W = rp (proj₂ W) hz (hsuc hself)

lβ₀ : ∀ W → LgB (β₀ W)
lβ₀ W = EK.Lg-rp (proj₂ W) hz (hsuc hself)

-- S₁ 的世界 (0, 0) 与 (a, 0): 界搬进 T 的世界
m₀A : ∀ {c} {W : Wε} → c ⊲ azero → c ⊲ proj₁ W
m₀A {W = W} e = ⊲-tr e (z⊲ (proj₁ W))

mHz : ∀ {a c} {W : Wε} → c ⊲[ a ] hz → Bd T (inj₂ κ₀) c W
mHz {W = W} hself = z⊲ᴮ (β₀ W)

module NbE (b : Ht) (s : H₁ → Ht → Ht) (fs : ∀ x h {W} → h ⊲[ W ] s x h) where
  mono : ∀ {w : Wd (step S₀)} {W : Wε} → (∀ {c} → c ⊲ proj₁ w → c ⊲ proj₁ W) →
         (∀ {c} → c ⊲[ proj₁ w ] proj₂ w → Bd T (inj₂ κ₀) c W) →
         ∀ {x y} → x ⊲[ w ] y → nbᴱ b s x ⊲[ W ] nbᴱ b s y
  mono mA mH hself = hself
  mono mA mH (hsuc p) = ⊲ᴮ-tr (mono mA mH p) (fs _ _)
  mono mA mH (hlim n p) = hlim n (mono mA mH p)
  mono mA mH (hLim {κ = inj₁ tt} e p) = hLim (mA e) (mono mA mH p)
  mono mA mH (hLim {κ = inj₂ tt} e p) = hLim (mH e) (mono mA mH p)

  mono₀ : ∀ {x y} {W : Wε} → x ⊲[ (azero , hz) ] y → nbᴱ b s x ⊲[ W ] nbᴱ b s y
  mono₀ {W = W} = mono {W = W} (m₀A {W = W}) (mHz {W = W})

  Lg-nbᴱ : LgB b → (∀ x h → LgB h → LgB (s x h)) → ∀ x → LgB {step S₀} x → LgB {T} (nbᴱ b s x)
  Lg-nbᴱ lb ls hz _ = lb
  Lg-nbᴱ lb ls (hs x) l = ls x _ (Lg-nbᴱ lb ls x l)
  Lg-nbᴱ lb ls (hl f) (st , l) = (λ {W} n → mono₀ {W = W} (st {azero , hz} n)) , (λ n → Lg-nbᴱ lb ls (f n) (l n))
  Lg-nbᴱ lb ls (hΩ (inj₁ tt) h) (mo , l) =
    (λ {W} lW e e′ pr → mono {w = proj₁ W , hz} {W = W} (λ e₁ → e₁) (mHz {W = W}) (mo {proj₁ W , hz} (proj₁ lW , tt) e e′ pr)) ,
    (λ c lc → Lg-nbᴱ lb ls (h c) (l c lc))
  Lg-nbᴱ lb ls (hΩ (inj₂ tt) h) (mo , l) =
    (λ {W} lW e e′ pr → mono {w = azero , β₀ W} {W = W} (m₀A {W = W}) (λ e₁ → e₁) (mo {azero , β₀ W} (tt , lβ₀ W) e e′ pr)) ,
    (λ c lc → Lg-nbᴱ lb ls (h c) (l c lc))

  -- κ₁ 的 Ω-结点: 单调在 κ₁ 的内层世界 (0, 0) 里
  Lg-topᴱ : LgB b → (∀ x h → LgB h → LgB (s x h)) → LgB {T} (hΩ (inj₂ κ₁) (nbᴱ b s))
  Lg-topᴱ lb ls = (λ {W} lW e e′ pr → mono₀ {W = W} pr) , (λ x lx → Lg-nbᴱ lb ls x lx)
```

## §3 对照: κ₀ 上的嵌入

```agda
nb₀ : H₀ → Ht
nb₀ hz = hz
nb₀ (hs x) = hs (nb₀ x)
nb₀ (hl f) = hl (λ n → nb₀ (f n))
nb₀ (hΩ tt h) = hΩ κa (λ c → nb₀ (h c))

nb₀-mono : ∀ {a x y} {W : Wε} → (∀ {c} → c ⊲ a → c ⊲ proj₁ W) → x ⊲[ a ] y → nb₀ x ⊲[ W ] nb₀ y
nb₀-mono mA hself = hself
nb₀-mono mA (hsuc p) = hsuc (nb₀-mono mA p)
nb₀-mono mA (hlim n p) = hlim n (nb₀-mono mA p)
nb₀-mono mA (hLim e p) = hLim (mA e) (nb₀-mono mA p)

Lg-nb₀ : ∀ x → LgB {S₀} x → LgB {T} (nb₀ x)
Lg-nb₀ hz _ = tt
Lg-nb₀ (hs x) l = Lg-nb₀ x l
Lg-nb₀ (hl f) (st , l) = (λ {W} n → nb₀-mono {W = W} (m₀A {W = W}) (st {azero} n)) , (λ n → Lg-nb₀ (f n) (l n))
Lg-nb₀ (hΩ tt h) (mo , l) =
  (λ {W} lW e e′ pr → nb₀-mono {W = W} (λ e₁ → e₁) (mo {proj₁ W} (proj₁ lW) e e′ pr)) , (λ c lc → Lg-nb₀ (h c) (l c lc))

Ω₂ᴱ : Ht
Ω₂ᴱ = hΩ (inj₂ κ₀) nb₀

Lg-Ω₂ᴱ : LgB Ω₂ᴱ
Lg-Ω₂ᴱ = (λ {W} lW e e′ pr → nb₀-mono {W = W} (m₀A {W = W}) pr) , (λ x lx → Lg-nb₀ x lx)
```

## §4 闭项

```agda
module E₁ = NbE hz (λ _ h → hs h) (λ _ h → hsuc hself)

Ω₃ᴱ : Ht
Ω₃ᴱ = hΩ (inj₂ κ₁) (nbᴱ hz (λ _ h → hs h))

Lg-Ω₃ᴱ : LgB Ω₃ᴱ
Lg-Ω₃ᴱ = E₁.Lg-topᴱ tt (λ _ h lh → lh)

-- Ω₃ · n
mul : ℕ → Ht
mul zero = hz
mul (suc n) = mul n ⊞ Ω₃ᴱ

Lg-mul : ∀ n → LgB (mul n)
Lg-mul zero = tt
Lg-mul (suc n) = Lg-⊞ (mul n) Ω₃ᴱ (Lg-mul n) Lg-Ω₃ᴱ

Ω₃ω : Ht
Ω₃ω = hl mul

Lg-Ω₃ω : LgB Ω₃ω
Lg-Ω₃ω = (λ n → ⊞-fst (mul n) Ω₃ᴱ) , Lg-mul

-- κ₁ 上 x ↦ Ω₃ · x
module E₂ = NbE hz (λ _ h → h ⊞ Ω₃ᴱ) (λ _ h → ⊞-fst h Ω₃ᴱ)

Ω₃² : Ht
Ω₃² = hΩ (inj₂ κ₁) (nbᴱ hz (λ _ h → h ⊞ Ω₃ᴱ))

Lg-Ω₃² : LgB Ω₃²
Lg-Ω₃² = E₂.Lg-topᴱ tt (λ _ h lh → Lg-⊞ h Ω₃ᴱ lh Lg-Ω₃ᴱ)

T-Ω₂ T-Ω₃ T-Ω₃+1 T-Ω₃·2 T-Ω₃ω T-Ω₃² : A
T-Ω₂ = T⁺ Ω₂ᴱ Lg-Ω₂ᴱ
T-Ω₃ = T⁺ Ω₃ᴱ Lg-Ω₃ᴱ
T-Ω₃+1 = T⁺ (hs Ω₃ᴱ) Lg-Ω₃ᴱ
T-Ω₃·2 = T⁺ (mul 2) (Lg-mul 2)
T-Ω₃ω = T⁺ Ω₃ω Lg-Ω₃ω
T-Ω₃² = T⁺ Ω₃² Lg-Ω₃²

Lg-T-Ω₃² : Lg T-Ω₃²
Lg-T-Ω₃² = Lg-T⁺ Ω₃² Lg-Ω₃²

ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-Ω₃²)

fgh₃ : ℕ → ℕ
fgh₃ = FL.FGH (ord T-Ω₃)
```
