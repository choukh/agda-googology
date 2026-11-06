# LeanT (二): 一次封闭的层号 `LH`, 种类结构 `SL`, 塔与对角 Λ

> 不含记号. 入口 [LeanT](LeanT.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 重写 `LFReTy` 的 `LH`, `Lv`, `FL`, `SL`, `νL`, `node`, `ofHB` 与 `LFReTower` 的 `Ω̂`, `tw`, `Λ`. 定义与原来逐条相同 (同一个归纳-递归块, 同一个 `Ω̂`); 差: `Lv lz` 是 [LeanTBase](LeanTBase.lagda.md) 的 `S⊥ = sup ⊥ (λ ())`, 不是手写的空记录; 不带 `lvl`, `rbl`, `toHB`, `upL`, `E-rbl` (闭项用不到).
>
> `LH` 与 `Lv` 互相定义: 层号 `lΩ k g` 的分支以第 `k` 层的高度 `HB (Lv k)` 为下标. 一切层的种类都在 `SL = sup LH (step ∘ Lv)` 里; 第 `k` 层的新种类 `νL k` 的坐标就是 `HB (Lv k)`. [判断] `Lv` 的形状受下标塔的直觉启发, 记为记号引导的形状 (同 `LFReTy` 自述).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanTLv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.LeanTBase
```

## §1 层号

```agda
data LH : Set
Lv : LH → KS

data LH where
  lz : LH
  ls : LH → LH
  ll : (ℕ → LH) → LH
  lΩ : (k : LH) → (HB (Lv k) → LH) → LH

Lv lz = S⊥
Lv (ls x) = step (Lv x)
Lv (ll f) = sup ℕ (λ n → Lv (f n))
Lv (lΩ k g) = sup (⊤ ⊎ HB (Lv k)) [ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′

FL : LH → KS
FL k = step (Lv k)

SL : KS
SL = sup LH FL

νL : LH → K SL
νL k = k , inj₂ tt
```

**高度读成层号.** `SL` 的高度读成 `LH`: 新种类 `νL k` 的 $\Omega$-结点读成 `lΩ k`, 旧种类的结点沿种类下降到它所在层的 `lΩ` (`node`).

```agda
node : (k : LH) (κ : K (Lv k)) → (E (Lv k) κ → LH) → LH
node lz (() , _) h
node (ls x) (inj₁ κ) h = node x κ h
node (ls x) (inj₂ _) h = lΩ x h
node (ll f) (n , κ) h = node (f n) κ h
node (lΩ k g) (inj₁ _ , inj₁ κ) h = node k κ h
node (lΩ k g) (inj₁ _ , inj₂ _) h = lΩ k h
node (lΩ k g) (inj₂ c , κ) h = node (g c) κ h

ofHB : HB SL → LH
ofHB hz = lz
ofHB (hs h) = ls (ofHB h)
ofHB (hl f) = ll (λ n → ofHB (f n))
ofHB (hΩ (k , inj₂ _) g) = lΩ k (λ c → ofHB (g c))
ofHB (hΩ (k , inj₁ κ) g) = node k κ (λ c → ofHB (g c))
```

## §2 塔与对角

`Ω̂ (h+1) = Ω_{h}` 的分支在新种类 `νL (ofHB h)` 上, 第 $c$ 支是 $\hat\Omega\,h \boxplus c$. `tw n = Ω̂ⁿ 0`, `Λ = hl tw`.

```agda
Ω̂ : HB SL → HB SL
Ω̂ hz = hs hz
Ω̂ (hs h) = hΩ (νL (ofHB h)) (λ c → Ω̂ h ⊞ ι (ofHB h) (up c))
Ω̂ (hl f) = hl (λ n → Ω̂ (f n))
Ω̂ (hΩ κ g) = hΩ κ (λ c → Ω̂ (g c))

Ω̂-⊲ : ∀ {x y W} → x ⊲[ W ] y → Ω̂ x ⊲[ W ] Ω̂ y
Ω̂-⊲ hself = hself
Ω̂-⊲ {W = W} (hsuc {b = b} p) = ⊲ᴮ-tr (Ω̂-⊲ p) (hLim (botBd SL (νL (ofHB b)) W) (⊞-fst (Ω̂ b) hz))
Ω̂-⊲ (hlim n p) = hlim n (Ω̂-⊲ p)
Ω̂-⊲ (hLim e p) = hLim e (Ω̂-⊲ p)

Lg-Ω̂ : ∀ h → LgB h → LgB (Ω̂ h)
Lg-Ω̂ hz l = tt
Lg-Ω̂ (hs h) l =
  (λ {W} lw e e′ p → ⊞-⊲ (Ω̂ h) (ι-⊲ {LH} {FL} {ofHB h} {w = W} (up-⊲ p))) ,
  (λ {W} {c} lw e → Lg-⊞ (Ω̂ h) (ι (ofHB h) (up c)) (Lg-Ω̂ h l)
     (Lg-ι (ofHB h) (up c) (Lg-up c (lgB⊲ e (proj₁ (lw (ofHB h))) (proj₂ (lw (ofHB h)))))))
Lg-Ω̂ (hl f) (st , l) = (λ n → Ω̂-⊲ (st n)) , (λ n → Lg-Ω̂ (f n) (l n))
Lg-Ω̂ (hΩ κ g) (mo , l) = (λ lw e e′ p → Ω̂-⊲ (mo lw e e′ p)) , (λ {c = c} lw e → Lg-Ω̂ (g c) (l lw e))

tw : ℕ → HB SL
tw zero = hz
tw (suc n) = Ω̂ (tw n)

tw-st : ∀ {W} n → tw n ⊲[ W ] tw (suc n)
tw-st zero = z⊲ᴮ (hs hz)
tw-st (suc n) = Ω̂-⊲ (tw-st n)

Lg-tw : ∀ n → LgB (tw n)
Lg-tw zero = tt
Lg-tw (suc n) = Lg-Ω̂ (tw n) (Lg-tw n)

Λ : HB SL
Λ = hl tw

Lg-Λ : LgB Λ
Lg-Λ = (λ n → tw-st n) , Lg-tw
```
