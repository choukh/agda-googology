# Ω-极限坐标上的读回包 (三): 外层界沿 W1 长高时的单调

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 依赖 [LvOmLev](LvOmLev.lagda.md), [LvOmRd](LvOmRd.lagda.md); 推论一节只读导入 `LvRd` 的 [LvRdWk](LvRdWk.lagda.md) (`St`, `Sδ`, `σ₀`) 与 [LvRdFold](LvRdFold.lagda.md) (`Hn`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **一步定理 `tr-emb`.** 外层界沿外层世界 $a$ 里的路径 $p : c\lhd_{[a]} c'$ 长高 (W1 的部分和: $B_s\lhd B_s\boxplus\sigma_s$). 层结构沿 $p$ 嵌入 (`LvOmLev.embP`). 对 $c$ 的任一种类 $\kappa$: 在 $c'$ 的包里翻译嵌入后的种类, **等于** 在 $c$ 的包里翻译 $\kappa$, 层证据沿 $p$ 逐步加长 (`TrP p`). 证明对 $p$ 归纳, 每步 `refl`. 这一站新用到的字段: 路径 `hLim e p` 的证据 $e : x\lhd a$ 原样当作种类下标 $(x,e)$ 的证据 (`embP` 的 `hLim` 行), 不判定, 不搬运.
>
> **推论 `embδ`, `trδ`.** `LvRdWk.lvShapeδ` 的外层界 $B_{s+1}=B_s\boxplus\sigma_0(H_s)$ (外层世界 $0$): 第 $s$ 站的层结构嵌进第 $s+1$ 站, 翻译相容.
>
> **不成立的部分 (判断, 未写成定理).** 读回不沿 $p$ 相容: $c$ 与 $c'$ 的读回层的树是不同类型 (`D (Ly c)`, `D (Ly c′)`), 要比较须先把树沿层路径搬运. 外层世界 $a$ 本身长高 ($a\lhd a'$) 时没有 `Emb (Lv a c) (Lv a′ c)` 的构造: `Emb` 要求坐标往返 `cv ∘ vc = id`, 而反方向要对 $a'$ 里的种类重新判定 $x\lhd a$, 判定给出的证据不必是原来的那一条 (拷贝).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmW1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; ⊲-tr)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀; Ht; Wd₂; D; κA)
open import OCF.Align.LvRdEmb using (Emb; lk; vc)
open import OCF.Align.LvOmLev
open import OCF.Align.LvOmRd
```

## §1 层证据沿路径加长, 翻译与嵌入相容

```agda
module W1 (a : A) where
  open Rd a

  TrP : ∀ {c c′ L″} → c ⊲[ a ] c′ → (∀ {W} → a ⊲ proj₁ W → Ly c′ ⊲[ W ] L″) → ∀ {W} → a ⊲ proj₁ W → Ly c ⊲[ W ] L″
  TrP hself Pv = Pv
  TrP (hsuc p) Pv = TrP p (λ i′ → ⊲ᴮ-tr (hsuc hself) (Pv i′))
  TrP (hlim n p) Pv = TrP p (λ i′ → ⊲ᴮ-tr (hlim n hself) (Pv i′))
  TrP (hLim {c = x} e p) Pv = TrP p (λ i′ → ⊲ᴮ-tr (hLim {κ = κA} {c = x} (⊲-tr e i′) hself) (Pv i′))

  tr-emb : ∀ {c c′} (p : c ⊲[ a ] c′) (κ : K (Lv c)) {L″} (Pv : ∀ {W} → a ⊲ proj₁ W → Ly c′ ⊲[ W ] L″)
           (g : E (Lv c′) (lk (embP p) κ) → (W : Wd₂) → a ⊲ proj₁ W → D L″ W) W i →
           trK (pk c′) (lk (embP p) κ) Pv g W i ≡ trK (pk c) κ (TrP p Pv) (λ e → g (vc (embP p) e)) W i
  tr-emb hself κ Pv g W i = refl
  tr-emb (hsuc p) κ Pv g W i = tr-emb p κ _ g W i
  tr-emb (hlim n p) κ Pv g W i = tr-emb p κ _ g W i
  tr-emb (hLim e p) κ Pv g W i = tr-emb p κ _ g W i
```

## §2 推论: `lvShapeδ` 的部分和外层界

```agda
open import OCF.Align.LvRdWk using (σ₀; module Sδ)
open import OCF.Align.LvRdFold using (Hn)

module Wδ where
  open Rd azero
  open W1 azero

  embδ : ∀ s → Emb (Lv (Sδ.B s)) (Lv (Sδ.B (suc s)))
  embδ s = embP (⊞-fst {w = azero} (Sδ.B s) (σ₀ (Hn s)))

  trδ : ∀ s (κ : K (Lv (Sδ.B s))) {L″} (Pv : ∀ {W} → azero ⊲ proj₁ W → Ly (Sδ.B (suc s)) ⊲[ W ] L″) g W i →
        trK (pk (Sδ.B (suc s))) (lk (embδ s) κ) Pv g W i ≡
        trK (pk (Sδ.B s)) κ (TrP (⊞-fst {w = azero} (Sδ.B s) (σ₀ (Hn s))) Pv) (λ e → g (vc (embδ s) e)) W i
  trδ s κ Pv g W i = tr-emb (⊞-fst {w = azero} (Sδ.B s) (σ₀ (Hn s))) κ Pv g W i
```

## §3 在 `lvShapeδ` 的每个坐标上折叠

`LvRd` 的第一个障碍是 "在 `lvShapeδ` 给出的坐标上折叠". 外层世界 $0$ (`lvShapeδ` 的世界) 时, `LvOmFold.F1` 对每个 $B_s$ 都给出一级回灌; 级顶的读回合法. 代价同 `LvOmNeg.only0`: $B_s$ 里的 Ω-结点只取第 0 支.

```agda
open import OCF.Align.LvOmFold using (module F1)

module Fδ (s : ℕ) = F1 azero tt (Sδ.B s)

topδ : ∀ s → HB (LvM.Lv azero (Sδ.B s))
topδ s = Fδ.top s

Lg-topδ : ∀ s → LgB (topδ s)
Lg-topδ s = Fδ.Lg-top s
```
