# 差树按层互译 (四): $\Omega_1$ 的差树

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md). 对照: 分支不读坐标时往返没有问题.
>
> - `Ωx = Ωd one self tt`: $\Omega_1$ 的差树 $1+\sum_{z}1$ ([SumOneTree](SumOneTree.lagda.md) §3).
> - `Ω≈`: `toB Ωx` 与标准树 `Ωᴮ` (分支就是坐标) 互相 $\preccurlyeq$.
> - `Ω-round`: 差 → 树 → 差 → 树, 树字面不变 (`refl`).
> - `Ω-dif`: 读回的差树字面是 `nw self (n0 ⨾ n1) ⨾ ni _ (λ _ _ _ → n0 ⨾ n1)`, 与 `Ωx` 字面不同 (第 0 层 `dif-not-id` 的同类).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; _⊞_; ⊞-mono)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; Ωd)
import OCF.Align.BrwMidZero as Z
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne
```

## §1 积 1 就是和

```agda
lim≈ : ∀ {W W′} {f : ℕ → B₁ W} {g : ℕ → B₁ W′} → (∀ n → f n ≈ g n) → bl f ≈ bl g
lim≈ h = l≼ (λ n → ≼l n (proj₁ (h n))) , l≼ (λ n → ≼l n (proj₂ (h n)))

Iv  : ∀ {W₀ W} (z : D azero W₀) (q : W₀ ⊲ W) w (b : B₁ W) a → b ≈ emb {W} a → I (λ _ b → bs b) z q w b ≈ emb {W} (sum a z)
Ivp : ∀ {W₀ W} (d : ℕ → D azero W₀) (q : W₀ ⊲ W) w (b : B₁ W) a → b ≈ emb {W} a → ∀ n → Ip (λ _ b → bs b) d q w b n ≈ emb {W} (pt a d n)
Iv n0 q w b a h = h
Iv n1 q w b a h = s≼s (proj₁ h) , s≼s (proj₂ h)
Iv (x ⨾ y) q w b a h = Iv y q _ _ (sum a x) (Iv x q w b a h)
Iv (nl d) q w b a h = lim≈ (Ivp d q w b a h)
Iv (ni () u) q w b a h
Iv (nκ () u) q w b a h
Iv (nw p x) q w b a h = Iv x (⊲-tr p q) w b a h
Ivp d q w b a h zero = h
Ivp d q w b a h (suc n) = Iv (d n) q _ _ (pt a d n) (Ivp d q w b a h n)
```

## §2 第 0 层的两条不等式

```agda
⊞-right : ∀ a b → b ≤ a ⊞ b
⊞-right a azero = z≤
⊞-right a (asuc b) = s≤ (⊞-right a b)
⊞-right a (alim f) = l≤ (λ n → ≤l n (⊞-right a (f n)))

1⊞≤ : ∀ c → (asuc azero ⊞ c) ≤ asuc c
1⊞≤ azero = s≤ z≤
1⊞≤ (asuc c) = s≤ (1⊞≤ c)
1⊞≤ (alim f) = l≤ (λ n → ≤-trans (1⊞≤ (f n)) (s≤ (≤l n (≤-refl (f n)))))

-- 1 + dif y 的和夹在 y 与 y+1 之间
lower : ∀ {W} y (ly : Lg y) → y ≤ sum {W} (asuc azero) (Z.dif y (z⊲ y) ly)
lower {W} y ly =
  ≤-trans (proj₂ (Z.round₁ {W} y ly))
  (≤-trans (⊞-right (asuc azero) _) (proj₂ (Z.sum-toA (asuc azero) (Z.dif {W} y (z⊲ y) ly))))

upper : ∀ {W} y (ly : Lg y) → sum {W} (asuc azero) (Z.dif y (z⊲ y) ly) ≤ asuc y
upper {W} y ly =
  ≤-trans (proj₁ (Z.sum-toA (asuc azero) (Z.dif {W} y (z⊲ y) ly)))
  (≤-trans (⊞-mono (≤-refl (asuc azero)) (proj₁ (Z.round₁ {W} y ly))) (1⊞≤ y))
```

## §3 $\Omega_1$

```agda
Ωx : D one azero
Ωx = Ωd one C.self tt

okΩ : Ok no Ωx
okΩ = tt , (tt , λ p l w → tt)

branch≈ : ∀ {W′} (p : azero ⊲ W′) (l : Lg W′) y (ly : Lg y) →
          I (λ _ b → bs b) (Z.dif {W′} y (z⊲ y) ly) C.self n0 (bw p (bs bz)) ≈ emb {W′} (sum {W′} (asuc azero) (Z.dif y (z⊲ y) ly))
branch≈ p l y ly = Iv (Z.dif y (z⊲ y) ly) C.self n0 (bw p (bs bz)) (asuc azero) (w≼ (s≼s z≼) , ≼w (s≼s z≼))

Ω≈ : toB tt Ωx ≈ Ωᴮ {azero}
Ω≈ = i≼ (λ p l y ly → ≼i p l (asuc y) ly (≼-trans (proj₁ (branch≈ p l y ly)) (emb-mono (upper y ly)))) ,
     i≼ (λ p l y ly → ≼i p l y ly (≼-trans (emb-mono (lower y ly)) (proj₂ (branch≈ p l y ly))))

Ω-dif : difT tt Ωx okΩ ≡ (nw C.self (n0 ⨾ n1) ⨾ ni (ss C.self) (λ _ _ _ → n0 ⨾ n1))
Ω-dif = refl

Ω-round : toB tt (difT tt Ωx okΩ) ≡ toB tt Ωx
Ω-round = refl
```
