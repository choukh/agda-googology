# 世界内的构造有没有封顶 (一): 类与封顶定理

> 入口 [TLEnd](TLEnd.lagda.md). **判决: HOLDS (编译过, 无条件), 封顶是相对于一个读法算子 $\rho$ 与一个起点 $M_0$ 的.** 不读记号.
>
> **类, 一句话.** 从 $M_0$ 起走一条 `⊂`-链: 每一步按 $\rho$ 读当前世界的一行, 把层号接到码上, 再把新世界第 0 行的层号接到码上. 类 `𝓦` 是这条链上一切世界的第 0 行, 被读的行, 对后继和下方封闭的最小集.
>
> **为什么这样选 (判断, 理由都有编译的依据).**
> - **`⊂`-链, 不是一族码.** `⊂-linear`: `⊂`-有向的一族码就是一条链. 跨链比较要 "码的值单调", 这里没有 (见入口的 `Mono`).
> - **没有任意的 ℕ-极限.** 有了就是全体 (`gen-all`, [TLEndNeg](TLEndNeg.lagda.md)). 没有任意的外部输入: 有了就没有上界 (`cofinal`, 同上).
> - **$\rho$ 是算子.** 这样 $\alpha$ 槽和高度槽都在类里, 不必一个一个列: `Ω̇ (suc lv)` 这种读法就是 `ra`.
>
> | 定理 | 陈述 |
> | --- | --- |
> | `cap` | `𝓦` 里一切层号 $x$: `suc x ≼ lvβ`, 对一切 $\rho$, $M_0$ |
> | `lub` | `lvβ` 是链上第 0 行的最小上界 |
> | `lim-closed` | `lvβ` 下面对后继封闭 |
> | `cof` | `lvβ` 下面的一切都被某个世界的值盖住 |
> | `dn` | 世界的值不超过它第 0 行的层号 |
> | `Cl W β′` | 树侧的闭包点: 对 `W` 里的世界, 读行和回灌都不出 $\beta'$ (定义, 不提记号) |
> | `closed-self` | `lvβ` 对链上的世界是闭包点, 所以闭包点的定义有实例 |
> | `closed-min` | 最小性: 对任何闭包点 $\beta'$ (`W` 含 $M_0$ 且对 `next` 封闭, $M_0$ 在 $\beta'$ 下面), `lvβ ≼ β′` |
> | `mono→row` | **条件定理:** 码的值单调 (`Mono`) 推出 `lvβ` 对一切世界的第 0 行封闭 |
> | `rel-cap` | 相对封顶: `𝓦` 的一切 $x$ 都 `suc x ≼ β′`, 对任何这样的闭包点 |
> | `no-worldᵇ` | 没有一个码含整条链 |
> | `⊂-linear` | `⊂` 下一个码以下是线序, 所以有向族都是链 |
> | `above` | 起点把 $x$ 喂给高度, 闭包点就严格高于 $x$ |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEndCap where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; gl; forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; _ᶜ+_; _≼_; z≼; s≼; s≼ʳ; l≼; l≼ʳ; ≼-trans; ≼-refl; dom₀)
open import OCF.Align.LadderOrdStr using (≺→s≼; ≺→≼)
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el; ⊂+; ⊂-trans; up)
open import OCF.Align.CrossMUpTree using (up≺; step≺)
open import OCF.Align.CrossMNode using (≺-trans; ≺→⊑; val-next)
open import OCF.Align.CrossMInst using (val≼T)
```

## §1 抽象的分支

`b`, `G`, `next` 都是抽象的. 这不是风格: 检查器比较闭合世界上 `forceᴺ` 的不同写法要化简证书 ([CrossMInst](CrossMInst.lagda.md) 的提示), 这个文件第一版在 10G 堆内耗尽 (退出码 251), 所以这一节不看它们是什么, 下一节只代入.

```agda
hgtᶜ : Code → ℕ
hgtᶜ cz = 0
hgtᶜ (cs c) = suc (hgtᶜ c)
hgtᶜ (cl g) = suc (hgtᶜ (g 0))

⊂-hgt : ∀ {A B} → A ⊂ B → hgtᶜ A ≤ hgtᶜ B
⊂-hgt ⊂r = ≤-refl
⊂-hgt (es e) = ≤-trans (⊂-hgt e) (n≤1+n _)
⊂-hgt (el e) = ≤-trans (⊂-hgt e) (n≤1+n _)

step-hgt : ∀ A N → suc (hgtᶜ A) ≤ hgtᶜ (A ᶜ+ cs N)
step-hgt A N = s≤s (⊂-hgt (⊂+ A N))

≺lv : ∀ {x y} (G₁ : Goodᴺ x) (G₂ : Goodᴺ y) → forceᴺ _ G₁ ≺ forceᴺ _ G₂ → lvG G₁ ≺ᴵ lvG G₂
≺lv G₁ G₂ r = toLevel-≺ (forceᴺ-HS _ G₁) (forceᴺ-HS _ G₂) r

module AB (b : Code → Z) (G : ∀ M → Goodᴺ (b M)) (next : Code → Code)
  (u≺ : ∀ M → forceᴺ _ (G M) ≺ forceᴺ _ (G (next M)))
  (grow : ∀ M → suc (hgtᶜ M) ≤ hgtᶜ (next M))
  (M₀ : Code) where

  Cb : ℕ → Code
  Cb zero = M₀
  Cb (suc n) = next (Cb n)

  Ẑ : Z
  Ẑ = Z.lim (λ n → b (Cb n))

  Ĝ : Goodᴺ Ẑ
  Ĝ = gl (λ n → G (Cb n)) (λ n → ≺→⊑ (u≺ (Cb n)))

  Tβ : Ordᶜ zero
  Tβ = forceᴺ _ Ĝ

  HSβ : HS Tβ
  HSβ = forceᴺ-HS _ Ĝ

  lvβ : Ordᴵ
  lvβ = lvG Ĝ

  at : ∀ n → lvG (G (Cb n)) ≼ lvβ
  at n = l≼ʳ n (≼-refl _)

  first : ∀ {y} → y ≼ lvG (G M₀) → y ≼ lvβ
  first h = l≼ʳ 0 h

  at′ : ∀ {y} n → y ≼ lvG (G (next (Cb n))) → y ≼ lvβ
  at′ n h = l≼ʳ (suc n) h

  strict : ∀ M → suc (lvG (G M)) ≼ lvG (G (next M))
  strict M = ≺→s≼ (toLevel-≺ (forceᴺ-HS _ (G M)) (forceᴺ-HS _ (G (next M))) (u≺ M))

  -- 下面对后继封闭: 严格链的极限
  lim-closed : ∀ {x} → suc x ≼ lvβ → suc (suc x) ≼ lvβ
  lim-closed (l≼ʳ n h) = ≼-trans (s≼ h) (at′ n (strict (Cb n)))

  -- 最小上界
  lub : ∀ {y} → (∀ n → lvG (G (Cb n)) ≼ y) → lvβ ≼ y
  lub h = l≼ h

  -- 链上的第 0 行严格低于闭包点
  below : ∀ n → suc (lvG (G (Cb n))) ≼ lvβ
  below n = at′ n (strict (Cb n))

  below′ : ∀ n → suc (lvG (G (next (Cb n)))) ≼ lvβ
  below′ n = at′ (suc n) (strict (next (Cb n)))

  -- 同上, 对 ≼ 形式
  inv′ : ∀ {x} → suc x ≼ lvβ → Σ ℕ λ n → suc x ≼ lvG (G (Cb n))
  inv′ (l≼ʳ n h) = n , h

  -- 闭包点下面的东西都低于链上某一行
  inv : ∀ {x} → x ≺ᴵ lvβ → Σ ℕ λ n → x ≼ lvG (G (Cb n))
  inv (via e (lim n q)) = n , ≺→≼ (via e q)

  module Cls (Seed : Ordᴵ → Set) (seed : ∀ {x} → Seed x → Σ ℕ λ n → x ≼ lvG (G (next (Cb n)))) where
    data 𝓦 : Ordᴵ → Set where
      w-seed : ∀ {x} → Seed x → 𝓦 x
      w-suc  : ∀ {x} → 𝓦 x → 𝓦 (suc x)
      w-dn   : ∀ {x y} → y ≼ x → 𝓦 x → 𝓦 y

    cap : ∀ {x} → 𝓦 x → suc x ≼ lvβ
    cap (w-seed s) with seed s
    ... | n , h = ≼-trans (s≼ h) (at′ (suc n) (strict (Cb (suc n))))
    cap (w-suc w) = lim-closed (cap w)
    cap (w-dn d w) = ≼-trans (s≼ d) (cap w)

  -- 没有一个码含整条链
  C-hgt : ∀ n → n ≤ hgtᶜ (Cb n)
  C-hgt zero = z≤n
  C-hgt (suc n) = ≤-trans (s≤s (C-hgt n)) (grow (Cb n))

  no-worldᵇ : ∀ M → (∀ n → Cb n ⊂ M) → ⊥
  no-worldᵇ M f = absurd (≤-trans (C-hgt (suc (hgtᶜ M))) (⊂-hgt (f (suc (hgtᶜ M)))))
    where
    absurd : ∀ {n} → suc n ≤ n → ⊥
    absurd {suc n} (s≤s h) = absurd h
```

## §2 世界内的类: 对读法算子 $\rho$

`rp`, `ra`: 在世界 $M$ 里读哪一行. 闭合的 $\rho$ 就是不依赖外部输入的构造, 比如 `ra M = suc (lvG (Gᵖ M end zero))`. 全部对变量 $M$ 证.

```agda
module Req (rp : ∀ M → Pos (cs M)) (ra : Code → Ordᴵ) where
  R₀ : Code → Ordᴵ
  R₀ M = lvG (Gᵖ M (rp M) (ra M))

  M′ : Code → Code
  M′ M = M ᶜ+ cs ⌈ R₀ M ⌉

  next : Code → Code
  next M = M′ M ᶜ+ cs ⌈ lvG (Gᵖ (M′ M) end zero) ⌉

  st₁ : ∀ M → forceᴺ _ (Gᵖ M end zero) ≺ forceᴺ _ (Gᵖ (M′ M) end zero)
  st₁ M = up≺ {M′ = M′ M} (⊂+ M (cs ⌈ R₀ M ⌉)) end end tt

  st₂ : ∀ M → forceᴺ _ (Gᵖ (M′ M) end zero) ≺ forceᴺ _ (Gᵖ (next M) end zero)
  st₂ M = up≺ {M′ = next M} (⊂+ (M′ M) (cs ⌈ lvG (Gᵖ (M′ M) end zero) ⌉)) end end tt

  u≺ : ∀ M → forceᴺ _ (Gᵖ M end zero) ≺ forceᴺ _ (Gᵖ (next M) end zero)
  u≺ M = ≺-trans (st₁ M) (st₂ M)

  grow : ∀ M → suc (hgtᶜ M) ≤ hgtᶜ (next M)
  grow M = ≤-trans (s≤s (⊂-hgt (⊂+ M (cs ⌈ R₀ M ⌉)))) (step-hgt (M′ M) ⌈ lvG (Gᵖ (M′ M) end zero) ⌉)

  -- 读到的行不超过下一个世界的第 0 行
  req≼ : ∀ M → R₀ M ≼ lvG (Gᵖ (next M) end zero)
  req≼ M = ≼-trans (val-next M (R₀ M)) (≼-trans (val≼T (M′ M)) (≼-trans (val-next (M′ M) _) (val≼T (next M))))

  pre≼ : ∀ {a b} → suc a ≼ b → a ≼ b
  pre≼ {a} h = ≼-trans (s≼ʳ (≼-refl a)) h

  -- 世界里任何位置的第 0 行低于下一个世界的第 0 行
  pth : ∀ M → M ⊂ next M
  pth M = ⊂-trans (⊂+ M (cs ⌈ R₀ M ⌉)) (⊂+ (M′ M) (cs ⌈ lvG (Gᵖ (M′ M) end zero) ⌉))

  pth< : ∀ M (p : Pos (cs M)) → up (pth M) p <ᴾ end
  pth< M p = tt

  low≺ : ∀ M (p : Pos (cs M)) → forceᴺ _ (Gᵖ M p zero) ≺ forceᴺ _ (Gᵖ (next M) end zero)
  low≺ M p = up≺ {M′ = next M} (pth M) p end (pth< M p)

  low≼ : ∀ M (p : Pos (cs M)) → lvG (Gᵖ M p zero) ≼ lvG (Gᵖ (next M) end zero)
  low≼ M p = ≺→≼ (≺lv (Gᵖ M p zero) (Gᵖ (next M) end zero) (low≺ M p))

  -- 第 0 行的层号被下一个世界的值盖住
  ly≼val : ∀ M → lvG (Gᵖ M end zero) ≼ val (next M)
  ly≼val M = ≼-trans (≺→≼ (≺lv (Gᵖ M end zero) (Gᵖ (M′ M) end zero) (st₁ M))) (val-next (M′ M) _)

  Mono : Set
  Mono = ∀ M M₁ → val M ≼ val M₁ → lvG (Gᵖ M end zero) ≼ lvG (Gᵖ M₁ end zero)

  -- 树侧的闭包点: 对世界谓词 W 里的世界, 读行与回灌都不出 β′
  Cl : (Code → Set) → Ordᴵ → Set
  Cl W β′ = (∀ M → W M → ∀ p → suc (val M) ≼ β′ → suc (lvG (Gᵖ M p zero)) ≼ β′)
          × (∀ M → W M → suc (val M) ≼ β′ → suc (R₀ M) ≼ β′)
          × (∀ M → W M → suc (val M) ≼ β′ → suc (val (next M)) ≼ β′)

  module At (M₀ : Code) where
    open AB (λ M → toZ (Tᵖ M end zero ev₀ zero)) (λ M → Gᵖ M end zero) next u≺ grow M₀ public

    -- 普通定义, 不是 data: data 的构造子类型里有 lvG (Gᵖ …) 时, 检查器 (判断是正性分析, 没有查) 要范式化它, 展开证书
    Seed : Ordᴵ → Set
    Seed x = (Σ ℕ λ n → Σ (Pos (cs (Cb n))) λ p → x ≼ lvG (Gᵖ (Cb n) p zero)) ⊎ (Σ ℕ λ n → x ≼ R₀ (Cb n))

    seed : ∀ {x} → Seed x → Σ ℕ λ n → x ≼ lvG (Gᵖ (next (Cb n)) end zero)
    seed (inj₁ (n , p , h)) = n , ≼-trans h (low≼ (Cb n) p)
    seed (inj₂ (n , h)) = n , ≼-trans h (req≼ (Cb n))

    open Cls Seed seed public

    -- 回灌: 闭包点下面的一切都被某个世界的值盖住
    cof : ∀ {x} → x ≺ᴵ lvβ → Σ ℕ λ n → x ≼ val (next (Cb n))
    cof r = proj₁ (inv r) , ≼-trans (proj₂ (inv r)) (ly≼val (Cb (proj₁ (inv r))))

    -- 世界的值不超过它第 0 行的层号
    dn : ∀ n → val (Cb n) ≼ lvG (Gᵖ (Cb n) end zero)
    dn n = val≼T (Cb n)

    -- 闭包点对链上的世界封闭
    InCh : Code → Set
    InCh M = Σ ℕ λ n → M ≡ Cb n

    closed-self : Cl InCh lvβ
    closed-self = c₁ , c₂ , c₃
      where
      c₁ : ∀ M → InCh M → ∀ p → suc (val M) ≼ lvβ → suc (lvG (Gᵖ M p zero)) ≼ lvβ
      c₁ M (n , refl) p _ = cap (w-seed (inj₁ (n , p , ≼-refl _)))
      c₂ : ∀ M → InCh M → suc (val M) ≼ lvβ → suc (R₀ M) ≼ lvβ
      c₂ M (n , refl) _ = cap (w-seed (inj₂ (n , ≼-refl _)))
      c₃ : ∀ M → InCh M → suc (val M) ≼ lvβ → suc (val (next M)) ≼ lvβ
      c₃ M (n , refl) _ = ≼-trans (s≼ (val≼T (next (Cb n)))) (below′ n)

    InCh₀ : InCh M₀
    InCh₀ = 0 , refl

    InCh-s : ∀ M → InCh M → InCh (next M)
    InCh-s M (n , refl) = suc n , refl

    -- 闭包点是最小的: 对任何封闭于这些操作的 β′
    closed-min : ∀ {W : Code → Set} {β′} → Cl W β′ → W M₀ → (∀ M → W M → W (next M)) → suc (val M₀) ≼ β′ → lvβ ≼ β′
    closed-min {W} {β′} (c₁ , c₂ , c₃) w₀ wn h₀ = lub (λ n → pre≼ (c₁ (Cb n) (proj₁ (go n)) end (proj₂ (go n))))
      where
      go : ∀ n → W (Cb n) × (suc (val (Cb n)) ≼ β′)
      go zero = w₀ , h₀
      go (suc n) = wn (Cb n) (proj₁ (go n)) , c₃ (Cb n) (proj₁ (go n)) (proj₂ (go n))

    -- 条件定理: 码的值单调推出对一切世界的第 0 行封闭. Mono 没有证明, 也没有否定
    mono→row : Mono → ∀ M → suc (val M) ≼ lvβ → suc (lvG (Gᵖ M end zero)) ≼ lvβ
    mono→row m M h = ≼-trans (s≼ (m M (next (Cb n)) (≼-trans (pre≼ (proj₂ (inv′ h))) (ly≼val (Cb n))))) (below′ n)
      where
      n = proj₁ (inv′ h)

    -- 封闭的 β′ 上面的类封顶: 世界内的构造从下面到不了 β′
    rel-cap : ∀ {W : Code → Set} {β′ x} → Cl W β′ → W M₀ → (∀ M → W M → W (next M)) → suc (val M₀) ≼ β′ → 𝓦 x → suc x ≼ β′
    rel-cap c w₀ wn h₀ w = ≼-trans (cap w) (closed-min c w₀ wn h₀)

  -- 起点把 x 喂给高度, 闭包点严格高于 x
  above : ∀ x → suc x ≼ At.lvβ (cs ⌈ x ⌉)
  above x = At.first (cs ⌈ x ⌉) (≼-trans (s≼ (dom₀ x)) (val≼T (cs ⌈ x ⌉)))
```

## §3 有向族都是链

```agda
⊂-linear : ∀ {A B D} → A ⊂ D → B ⊂ D → (A ⊂ B) ⊎ (B ⊂ A)
⊂-linear ⊂r b = inj₂ b
⊂-linear (es a) ⊂r = inj₁ (es a)
⊂-linear (el a) ⊂r = inj₁ (el a)
⊂-linear (es a) (es b) = ⊂-linear a b
⊂-linear (el a) (el b) = ⊂-linear a b
```
