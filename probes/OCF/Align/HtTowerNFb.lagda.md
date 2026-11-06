# 种类结构的对应 (三): 新种类上的回灌算子

> 不含记号. 入口 [HtTowerN](HtTowerN.lagda.md). `HtOut.Fb` 的对应物, 高一级:
>
> - `out₂ h`: 以 $2\boxplus h$ 为最高层, 用两种种类的折叠 ([HtTowerFFold](HtTowerFFold.lagda.md), 闭项定义 `HtTowerFClosed.At`, 不改) 折叠 $\Omega_{2\boxplus h}$, 取**第 2 层目标**上的输出 (`D₂`).
> - **`Fb₂ h = rd₂ (h+1) (out₂ h)`**: 读回成 `HB S₁` 的高度 ([HtTowerNRead](HtTowerNRead.lagda.md)). 第 1 层节点与新种类闭包读成新种类的 $\Omega$-分支. 合法性是 `Lg-rd₂` 的一次调用; $h+1$ 是第一位置 (`fb₂-fst`).
> - `Λs₂ n = Fb₂ⁿ 0`, `Λω₂ = hl Λs₂`: **从 $0$ 出发, 只用新种类的回灌与 ℕ-对角**; 不用 `Ωtop`, `up`, `Ω₂ᴴ`. `Λ₁-ΩH`: `Λs₂ 1` 的最外是新种类的 $\Omega$-极限 (`refl`, 对具体项的计算).
> - 闭项 `T-fb₂ n`, **`T-fb₂ω`**, `fgh`; 增长 `Supμ-fb`, `Sup-fb` (在 $1\boxplus\Lambda\omega_2$ 上, `HtTowerFGrow` 的 `Stμ`, `Sta` 的实例).
>
> 读法 (判断, 纸面): 按 `HtOut` 的读法高一级, $x_{n+1}=\psi_2(\Omega_{x_n})$ 一类的迭代, $x_\omega=\sup_n x_n$; `T-fb₂ω` 读 $\psi_0(\Omega_{x_\omega})$, 按 Buchholz 读法即 $\psi_0(\Omega_{\Omega_3})$ (同 `HtTower` 对 `T-fbω` 读 $\psi_0(\Omega_{\Omega_2})$ 的判断). 没有定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerNFb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FL
open import OCF.Align.TLRuleSpec renaming (_≤_ to _≤ᴬ_) using ()
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (module At; W₁; T⁺; Lg-T⁺; ord)
open import OCF.Align.HtTowerFGrow using (module G)
open import OCF.Align.HtTowerNRead using (D₂; rd₂; rd₂-fst; Lg-rd₂)
```

## §1 第 2 层目标上的输出

```agda
top₂ : Ht → Ht
top₂ h = hs (hs hz) ⊞ h

Lg-top₂ : ∀ h → LgB h → LgB (top₂ h)
Lg-top₂ h lh = Lg-⊞ (hs (hs hz)) h tt lh

o₂ : ∀ h {w} → hs hz ⊲[ w ] top₂ h
o₂ h = ⊲ᴮ-tr (hsuc hself) (⊞-fst (hs (hs hz)) h)

module O (h : Ht) (lh : LgB h) where
  open At (top₂ h) (Lg-top₂ h lh) (o₂ h) public

  τ₂ : Tg W₁ (hs (hs hz)) W₁
  τ₂ = tg ≤rf (⊞-fst (hs (hs hz)) h) (tt , tt)

  out₂ : D₂ W₁
  out₂ = yc ΔΩ τ₂
```

## §2 回灌算子与回灌高度

```agda
HL₂ : Set
HL₂ = Σ Ht LgB

Fb₂ : HL₂ → HL₂
Fb₂ (h , lh) = rd₂ (tt , tt) (hs h) (O.out₂ h lh) , Lg-rd₂ (tt , tt) (hs h) (O.out₂ h lh) lh

fb₂-fst : ∀ (x : HL₂) {w} → hs (proj₁ x) ⊲[ w ] proj₁ (Fb₂ x)
fb₂-fst (h , lh) = rd₂-fst (tt , tt) (hs h) (O.out₂ h lh)

fb₂-st : ∀ (x : HL₂) {w} → proj₁ x ⊲[ w ] proj₁ (Fb₂ x)
fb₂-st x = ⊲ᴮ-tr (hsuc hself) (fb₂-fst x)

Λs₂ : ℕ → HL₂
Λs₂ zero = hz , tt
Λs₂ (suc n) = Fb₂ (Λs₂ n)

Λω₂ : Ht
Λω₂ = hl (λ n → proj₁ (Λs₂ n))

lΛω₂ : LgB Λω₂
lΛω₂ = (λ n → fb₂-st (Λs₂ n)) , (λ n → proj₂ (Λs₂ n))

isΩH : Ht → Bool
isΩH (hΩ (inj₂ tt) _) = true
isΩH _ = false

-- 新种类的 Ω-极限是输出读出来的 (起点是 0)
Λ₁-ΩH : isΩH (proj₁ (Λs₂ 1)) ≡ true
Λ₁-ΩH = refl
```

## §3 闭项

```agda
T-fb₂ : ℕ → A
T-fb₂ n = T⁺ (proj₁ (Λs₂ n)) (proj₂ (Λs₂ n))

T-fb₂ω : A
T-fb₂ω = T⁺ Λω₂ lΛω₂

Lg-T-fb₂ω : Lg T-fb₂ω
Lg-T-fb₂ω = Lg-T⁺ Λω₂ lΛω₂

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-fb₂ω)
```

## §4 增长: 在 $1\boxplus\Lambda\omega_2$ 上

`T-fb₂ω` 的折叠实例的最高层是 $1\boxplus\Lambda\omega_2=\mathrm{hl}\,(n\mapsto 1\boxplus\Lambda_n)$. 前缀站的第 $j$ 段过层 $1\boxplus\Lambda_j$; 闭包的节点族取层 $1$. 新种类闭包的站 (`Supμ-fb`) 与旧种类闭包的站 (`Sup-fb`) 都严格高于前缀站的任意可数子族.

```agda
Λ⁺ : Ht
Λ⁺ = hs hz ⊞ Λω₂

lΛ⁺ : LgB Λ⁺
lΛ⁺ = Lg-⊞ (hs hz) Λω₂ tt lΛω₂

o⁺ : ∀ {w} → hs hz ⊲[ w ] Λ⁺
o⁺ = hlim 0 hself

module ωSt₂ where
  open G Λ⁺ lΛ⁺ o⁺ public
  open Stμ (λ j → hs hz ⊞ proj₁ (Λs₂ j) , sl j hself) (λ {c} _ _ → hs hz , sl 0 hself) (λ {W′} _ _ → hs hz , sl 0 hself) tt tt public

  Supμ-fb : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xμ
  Supμ-fb = Supμ

  Sup-fb : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xκ
  Sup-fb = Sup
```
