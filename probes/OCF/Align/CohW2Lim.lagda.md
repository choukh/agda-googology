# 单一并上的折叠要什么 (二): 极限层号的种类确在 `Λ` 之下

> 不含记号. 入口 [CohW2](CohW2.lagda.md). [CohW2Need](CohW2Need.lagda.md) 的定理用到层号 `Lc c` ($c$ 是可数坐标). 这一篇说它们是 `Λ` 上的折叠必然碰到的层号:
>
> - **`lim-layer`**: 对一切可数坐标 $c$, 世界 `wc (c+1)` (第 `lz` 层的界取 $c+1$, 其余取 $0$) 里, 最外是层号 `Lc c` 的新种类 `ν (Lc c)` 的层是 `Λ` 的第一位置. 若 $c$ 合法, 这个世界合法 (`Lg-wc`), 层也合法 (`Lg-lim-layer`).
> - **`Lg-hα`**: `CohW2Need` 用的那族坐标 `l⁰ (hα α)` 对一切 $\alpha$ 都合法 (严格上升).
>
> 合起来: 一个对 `Λ` 的一切合法层、一切合法世界都工作的 `HtFeed` 族折叠, 要在每个 `ν (Lc c)` 上有闭包 (判断: 照 `HtTowerFTree.Ωd`, 层的每个 $\Omega$-节点给一个闭包), 闭包的回灌要 `RaiseAt (Lc c)` (判断, 见 `CohW2Need`); 而 `RaiseAt` 在这族层号上推出 WLPO (定理, 前提 `FE`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohW2Lim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.CohWGl using (LH; lz; ls; ll; lΩ; Lv; H⁰; z⁰; s⁰; l⁰; Ω⁰; GW; cv; ιS; ofHB; SL⋆; LgW⋆; ν; Ω̂; tw; Λ; Lg-Λ)
open import OCF.Align.CohW2Need using (Lc; nat; ω⁰; sn; sw; pickH; hα)
```

## §1 世界

```agda
wc : H⁰ (Lv lz) → GW
wc b lz = b
wc b (ls y) = z⁰
wc b (ll f) = z⁰
wc b (lΩ k g) = z⁰

module _ (b : H⁰ (Lv lz)) (lb : LgB (cv lz b)) where
  lgb : ∀ x → LgB (cv x (wc b x))
  lgb lz = lb
  lgb (ls x) = tt
  lgb (ll f) = tt
  lgb (lΩ k g) = tt

  lgW : ∀ y → LgW⋆ y (wc b)
  lgW lz = tt
  lgW (ls x) = lgW x , lgb x
  lgW (ll f) = λ n → lgW (f n)
  lgW (lΩ k g) = (lgW k , lgb k) , (λ d → lgW (g d))

  Lg-wc : LgW SL⋆ (wc b)
  Lg-wc y = lgW y , lgb y
```

## §2 层

`tw 3 = hΩ (ν lz) G`, `G c = Ω̂ (1 ⊞ c)`; `G (c+1) = hΩ (ν (Lc c)) (d ↦ Ω̂ (1 ⊞ c) ⊞ …)`, 都是定义相等.

```agda
brL : (c : H⁰ (Lv lz)) → H⁰ (Lv (Lc c)) → HB SL⋆
brL c d = Ω̂ (hs hz ⊞ ιS lz (cv lz c)) ⊞ ιS (Lc c) (cv (Lc c) d)

lim-layer : ∀ c → hΩ (ν (Lc c)) (brL c) ⊲[ wc (s⁰ c) ] Λ
lim-layer c = hlim 3 (hLim {c = s⁰ c} hself hself)

Lg-lim-layer : ∀ c → LgB (cv lz c) → LgB (hΩ (ν (Lc c)) (brL c))
Lg-lim-layer c lc = lgB⊲ (lim-layer c) (Lg-wc (s⁰ c) lc) Lg-Λ
```

## §3 那族坐标合法

```agda
⊲ω : ∀ {w} n → cv lz (nat n) ⊲[ w ] cv lz ω⁰
⊲ω n = hlim n hself

⊲sn : ∀ {w} n k → cv lz (nat n) ⊲[ w ] cv lz (sn k (s⁰ ω⁰))
⊲sn n zero = hsuc (⊲ω n)
⊲sn n (suc k) = hsuc (⊲sn n k)

Lg-nat : ∀ n → LgB (cv lz (nat n))
Lg-nat zero = tt
Lg-nat (suc n) = Lg-nat n

Lg-ω : LgB (cv lz ω⁰)
Lg-ω = (λ n → hsuc hself) , Lg-nat

Lg-sn : ∀ k → LgB (cv lz (sn k (s⁰ ω⁰)))
Lg-sn zero = Lg-ω
Lg-sn (suc k) = Lg-sn k

Lg-pick : ∀ b n → LgB (cv lz (pickH b n))
Lg-pick true n = Lg-sn n
Lg-pick false n = Lg-nat n

step-pick : ∀ {w} b b′ n → (b ≡ true → b′ ≡ true) → cv lz (pickH b n) ⊲[ w ] cv lz (pickH b′ (suc n))
step-pick false false n m = hsuc hself
step-pick false true n m = ⊲sn n (suc n)
step-pick true true n m = hsuc hself
step-pick true false n m with m refl
... | ()

sw-mono : ∀ α n → sw α n ≡ true → sw α (suc n) ≡ true
sw-mono α n e = cong (λ b → b ∨ α (suc n)) e

Lg-hα : ∀ α → LgB (cv lz (l⁰ (hα α)))
Lg-hα α = (λ n → step-pick (sw α n) (sw α (suc n)) n (sw-mono α n)) , (λ n → Lg-pick (sw α n) n)
```
