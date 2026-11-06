# 新塔, 否定一路 (五): 用到构造一路的无条件闭项 `NewTwrK.N₀`

> 不含记号. 入口 [NegNewTwr](NegNewTwr.lagda.md). 本篇导入构造一路的 [NewTwrK](NewTwrK.lagda.md) (只读, 不改; 对着的是 2026-11-05 17:44 的版本), 把 [NegNewTwrShape](NegNewTwrShape.lagda.md) 对一切 `NewTw` 的定理用到构造一路的 `N₀` 上. 构造文件若改动, 本篇可能需要重编译; 主结论不依赖本篇. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> - `B≡`, `Bᴧ≡`: 构造一路的塔 `NewTwrK.Twr N₀` 与本路照接口写的 `Sh N₀` 逐站相等.
> - **`N₀-lossy`**: `N₀` 的层号对角 `NT.ΛB` (即闭项 `TN = col collΛ (up (hl NT.Bᴧ)) _` 的层的内容, `NewTwrK.TN-def`) 的每个 $\Omega$-结点都在 `GΛ` 下有损; **`N₀-kinds`**: 最终层 `1 ⊞ up NT.ΛB` (`collG` 在层前接 1) 里没有 `step KΛc` 的新种类.
> - **`N₀-inc-not-below`**: 第 $s+2$ 站的增量 (含 $\Omega$-结点, 头是求值 `evN` 的新种类结点) 不是 `NT.ΛB` 的字面第一位置.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwrBridge where

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; sym)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc; emb; injL; ιΛ)
open import OCF.Align.GenFoldIf using (fbA)
open import OCF.Align.NegLvKtTrap using (OmFree; module TΛ)
open import OCF.Align.NewTwrIf
open import OCF.Align.NewTwrEv using (ρ′)
open import OCF.Align.NewTwrK using (N₀; module NT)
open import OCF.Align.NegNewTwrFeed using (genΛ⁺)
open import OCF.Align.NegNewTwrShape

module S₀ = Sh N₀

B≡ : ∀ s → NT.B s ≡ S₀.B s
B≡ zero = refl
B≡ (suc s) = cong (λ b → emb b ⊞ injL b (hs (ρ′ b))) (B≡ s)

Bᴧ≡ : ∀ s → NT.Bᴧ s ≡ S₀.Bᴧ s
Bᴧ≡ zero = refl
Bᴧ≡ (suc s) = trans (cong (λ y → y ⊞ ιΛ (suc s) (NT.inc s)) (Bᴧ≡ s))
                    (cong (λ b → S₀.Bᴧ s ⊞ ιΛ (suc s) (injL b (hs (ρ′ b)))) (B≡ s))

-- 起点 2 无 Ω-结点
fr₀ : OmFree (b₀ N₀)
fr₀ = tt

N₀-lossy : AllK Lossy NT.ΛB
N₀-lossy n = subst (AllK Lossy) (sym (Bᴧ≡ n)) (Fin.cumL N₀ fr₀ n)

N₀-kinds : AllK OK⁺ (hs hz ⊞ up NT.ΛB)
N₀-kinds = all⊞ (hs hz) (up NT.ΛB) tt
  (allUp {S = KΛc} {P = OK⁺} NT.ΛB (λ n → subst (AllK OKΛ) (sym (Bᴧ≡ n)) (Fin.cumOK N₀ n)))

N₀-inc-not-below : ∀ (w : Wd KΛc) s → ¬ (ιΛ (suc (suc s)) (NT.inc (suc s)) ⊲[ w ] NT.ΛB)
N₀-inc-not-below w s (hlim n q) =
  NB.tw-not-below N₀ (λ ()) w (suc (suc s)) (s≤s (s≤s z≤n))
    (hlim n (subst (λ y → ιΛ (suc (suc s)) (NT.inc (suc s)) ⊲[ w ] y) (Bᴧ≡ n) q))
    (TΛ.pure-ι (suc (suc s)) (NT.inc (suc s))) (λ ())
```

## 结论 (按档)

- **[定理]** `B≡`, `Bᴧ≡` (构造一路的塔与照接口写的塔逐站相等); **`N₀-lossy`**, **`N₀-kinds`**, **`N₀-inc-not-below`**.
- 这三条对着构造一路的无条件闭项 `NewTwrK.TN`. 它们是形状定理, 不说 `ord TN` 的大小.
