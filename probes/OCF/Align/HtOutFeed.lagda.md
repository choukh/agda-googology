# 高度来自折叠的输出 (二): 回灌算子与闭项

> 不含记号. 入口 [HtOut](HtOut.lagda.md). 折叠与闭项定义 `TΛ` 用 [HtFeedClosed](HtFeedClosed.lagda.md) 的, 不改.
>
> - `out₁ h`: 以 $1\boxplus h$ 为最高层折叠 $\Omega_{1\boxplus h}$ (`Ωd`), 取**第 1 层目标**上的输出 (`D (hs hz) one`). 闭项 `TΛ` 取的是第 0 层目标, 这里只换目标, 折叠不变.
> - `Fb`: **回灌算子** $h\mapsto \mathrm{rd}(h+1,\ \mathrm{out}_1\,h)$. 定义在合法高度上 (折叠要最高层合法). 合法性是 `Lg-rd` 的一次调用; $h+1$ 是新高度的第一位置 (`fb-fst`, 世界 $0$).
> - `Λs n = Fb^n 0`, `Λω = hl Λs`: **从 $0$ 出发, 只用回灌与 ℕ-对角**. 没有 `emb`, 没有 `Ωᴴ`, 没有 [HtFeedHt](HtFeedHt.lagda.md) 的生成规则. $\Omega$-极限的节点都是折叠输出里的 `ni`, `nκ` 读出来的 (`Λ₁-Ω`, 计算).
> - 闭项 `T-fb n`, `T-fbω`, `T-ψΩΩ` (从 `Ωᴴ` 回灌一次, 对照), `fgh`.
>
> 读法都是判断, 见入口.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOutFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (module At; TΛ; Lg-TΛ; one; ord)
open import OCF.Align.HtOutRead
```

## §1 第 1 层目标上的输出

$1\boxplus h$: 让第 1 层字面地是最高层的第一位置 (在一切世界里, `⊞ᴴ-fst`). 折叠的目标要 $t\lhd_{[m]}\Lambda$, 这是比较要字面公共上界逼出的 (同 `HtFeedFold` 的 `Tg`).

```agda
top⁺ : H → H
top⁺ h = hs hz ⊞ᴴ h

Lg-top⁺ : ∀ h → LgH h → LgH (top⁺ h)
Lg-top⁺ h lh = Lg-⊞ᴴ (hs hz) h tt lh

module O (h : H) (lh : LgH h) where
  open At (top⁺ h) (Lg-top⁺ h lh) public

  τ₁ : Tg one (hs hz) one
  τ₁ = tg C.self (⊞ᴴ-fst (hs hz) h) tt

  out₁ : D (hs hz) one
  out₁ = yc ΔΩ τ₁

out₁ : (h : H) → LgH h → D (hs hz) one
out₁ h lh = O.out₁ h lh
```

## §2 回灌算子

```agda
HL : Set
HL = Σ H LgH

Fb : HL → HL
Fb (h , lh) = rd tt (hs h) (out₁ h lh) , Lg-rd tt (hs h) (out₁ h lh) lh

-- h + 1 是 Fb h 的第一位置, 在世界 0 里
fb-fst : ∀ (x : HL) → hs (proj₁ x) ⊲[ azero ] proj₁ (Fb x)
fb-fst (h , lh) = rd-fst tt (hs h) (out₁ h lh)

fb-st : ∀ (x : HL) → proj₁ x ⊲[ azero ] proj₁ (Fb x)
fb-st x = ⊲ᴴ-tr (hsuc hself) (fb-fst x)
```

## §3 从 $0$ 出发的高度

```agda
Λs : ℕ → HL
Λs zero = hz , tt
Λs (suc n) = Fb (Λs n)

Λω : H
Λω = hl (λ n → proj₁ (Λs n))

lΛω : LgH Λω
lΛω = (λ n → fb-st (Λs n)) , (λ n → proj₂ (Λs n))

-- 对照: 从 HtFeedHt 的 Ω 回灌一次
Λψ : HL
Λψ = Fb (Ωᴴ , Lg-Ωᴴ)
```

## §4 闭项

```agda
T-fb : ℕ → A
T-fb n = TΛ (proj₁ (Λs n)) (proj₂ (Λs n))

T-fbω : A
T-fbω = TΛ Λω lΛω

T-ψΩΩ : A
T-ψΩΩ = TΛ (proj₁ Λψ) (proj₂ Λψ)

Lg-T-fbω : Lg T-fbω
Lg-T-fbω = Lg-TΛ Λω lΛω

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-fbω)
```

## §5 $\Omega$ 是输出读出来的

`Λs 1` 的最外构造子是 `hΩ`: 由检查器归约 (`refl`), 是对一个具体项的计算. 起点是 $0$, 所以这个 $\Omega$-极限不是给定的, 是折叠在第 1 层的输出里的节点读出来的.

```agda
isΩ : H → Bool
isΩ (hΩ _) = true
isΩ _ = false

Λ₁-Ω : isΩ (proj₁ (Λs 1)) ≡ true
Λ₁-Ω = refl
```
