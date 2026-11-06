# TK 的值 (二): 第 0 层的值, $\kappa_1$ 结点的比较, 整体的条件比较

> 不含记号. 入口 [ValTK](ValTK.lagda.md). 第 4 层: 只新增关系与定理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提.
>
> 值的序是 `TLRuleSpec._≤_` (布劳威尔树上通常的前序; `KindLvTw.ordK` 按构造子把 `A` 搬到 `Ordᶜ`, 所以这就是 `ord` 的比较), 下面记作 `≤ᴬ`.
>
> - **§1 第 0 层数据的加法支配 `x ⊑ y`**: 对一切底 $b$, $\mathrm{sum}\,b\,x\le\mathrm{sum}\,b\,y$ (两边的世界可以不同). 它对 `⨾`, `nl` 封闭, `drp` 不改它, 并且 $(\forall n.\ c\sqsubseteq e_n)\Rightarrow \omega\cdot c\sqsubseteq \mathrm{nl}\,e$ (`ω⊑nl`) [定理].
> - **§2 $\kappa_1$ 结点 [条件定理].** `node≤`: 若有损一边的分支输出 $c$ 被按级回灌一边**每一格**的分支输出 $\Delta_n$ 支配 (前提 `BrMono`), 则结点的输出 (有损: $\omega\cdot c$; 按级: $\sum_n\Delta_n$) 同样被支配. 前提比较的是**两份折叠, 两个世界** (结点所在的世界 $W$, 与第 $n$ 格升高的世界 $w_{n+1}$; 两者有字面的 $W\le w_{n+1}$, `ValTKBase.up-w`) 与两个状态 (`cv` 搬过的状态加上前面各格的输出).
> - **§3 整体 [条件定理].** `Dom l₁ l₂`: 两份折叠在**同一个世界, 同一组输入**上, 第 0 层输出被支配. `TK₀≤TK : Dom lv₀ lvΛ → TK₀ ≤ᴬ TK`. `Dom` 的形状可满足 (`Dom-refl`, 同一个级回灌). `Dom lv₀ lvΛ` 本身没有证: 对数据结构归纳时, $\kappa_1$ 结点那一行要的是 `BrMono` (换了世界与状态), 不是 `Dom` 的实例 (入口 "第一个障碍").

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValTKVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (AccY; tpK; module FoldTy; n0; n1; _⨾_; nl; ni; nc; nw)
open import OCF.Align.GenFoldTree using (module Tree; accᴸ; topStepG)
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.NewTwrColl using (GΛ; LdΛ; flΛ)
open import OCF.Align.KindLvIf using (LvFb)
open import OCF.Align.KindLvTw using (module ColL; module CK; Λ; lΛ; one⊲; lvΛ; κ₁; K1; TK)
open import OCF.Align.ValTKBase using (lv₀; module C0; TK₀; module NK; module N0; module Node)
import OCF.Align.KindLvRun as KR

open Tree KΛc using (L₀; D; D₀; drp; sum; pt; ≤rf; module Om)
open FoldTy KΛc Λ using (LW; Tg; Ig; St; Df; module Df)
open Df using (yc)
```

## §1 第 0 层数据的加法支配

```agda
sum-mono : ∀ {W} (x : D₀ W) {b b′} → b ≤ᴬ b′ → sum b x ≤ᴬ sum b′ x
pt-mono  : ∀ {W} (d : ℕ → D₀ W) {b b′} → b ≤ᴬ b′ → ∀ n → pt b d n ≤ᴬ pt b′ d n
sum-mono n0 p = p
sum-mono n1 p = s≤ p
sum-mono (x ⨾ y) p = sum-mono y (sum-mono x p)
sum-mono (nl d) p = l≤ (λ n → ≤l n (pt-mono d p n))
sum-mono (ni () u) p
sum-mono (nc (inj₁ _) () u) p
sum-mono (nc (inj₂ _) () u) p
sum-mono (nw q x) p = sum-mono x p
pt-mono d p zero = p
pt-mono d p (suc n) = sum-mono (d n) (pt-mono d p n)

infix 4 _⊑_
_⊑_ : ∀ {W W′} → D₀ W → D₀ W′ → Set
x ⊑ y = ∀ b → sum b x ≤ᴬ sum b y

⊑-rf : ∀ {W} (x : D₀ W) → x ⊑ x
⊑-rf x b = ≤-refl (sum b x)

⊑-tr : ∀ {U V W} {x : D₀ U} {y : D₀ V} {z : D₀ W} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-tr p q b = ≤-trans (p b) (q b)

⨾⊑ : ∀ {U V} {x x′ : D₀ U} {y y′ : D₀ V} → x ⊑ y → x′ ⊑ y′ → (x ⨾ x′) ⊑ (y ⨾ y′)
⨾⊑ {x = x} {x′} {y} {y′} p q b = ≤-trans (sum-mono x′ (p b)) (q (sum b y))

module _ {U V} {d : ℕ → D₀ U} {e : ℕ → D₀ V} (h : ∀ n → d n ⊑ e n) where
  pt⊑ : ∀ b n → pt b d n ≤ᴬ pt b e n
  pt⊑ b zero = ≤-refl b
  pt⊑ b (suc n) = ≤-trans (sum-mono (d n) (pt⊑ b n)) (h n (pt b e n))

  nl⊑ : nl d ⊑ nl e
  nl⊑ b = l≤ (λ n → ≤l n (pt⊑ b n))

-- ω 份同一个 c, 被一列每项都支配 c 的格的和支配
ω⊑nl : ∀ {U V} {c : D₀ U} {e : ℕ → D₀ V} → (∀ n → c ⊑ e n) → nl (λ _ → c) ⊑ nl e
ω⊑nl h = nl⊑ h

drp⊑ : ∀ {W W′} (x : D₀ W) → drp {W} {W′} x ⊑ x
⊑drp : ∀ {W W′} (x : D₀ W) → x ⊑ drp {W} {W′} x
drp⊑ n0 = ⊑-rf {W = _} n0
drp⊑ n1 = ⊑-rf {W = _} n1
drp⊑ (x ⨾ y) = ⨾⊑ (drp⊑ x) (drp⊑ y)
drp⊑ (nl d) = nl⊑ (λ n → drp⊑ (d n))
drp⊑ (ni () u)
drp⊑ (nc (inj₁ _) () u)
drp⊑ (nc (inj₂ _) () u)
drp⊑ (nw p x) = drp⊑ x
⊑drp n0 = ⊑-rf {W = _} n0
⊑drp n1 = ⊑-rf {W = _} n1
⊑drp (x ⨾ y) = ⨾⊑ (⊑drp x) (⊑drp y)
⊑drp (nl d) = nl⊑ (λ n → ⊑drp (d n))
⊑drp (ni () u)
⊑drp (nc (inj₁ _) () u)
⊑drp (nc (inj₂ _) () u)
⊑drp (nw p x) = ⊑drp x
```

## §2 $\kappa_1$ 结点: 条件比较

前提 `BrMono`: 有损一边 (折叠 `N0`, 世界 $W$, 状态 $Y$, 前缀 $w$) 的分支输出, 被按级回灌一边 (折叠 `NK`, 第 $n$ 格的世界 `wA (c n)`, 状态 `SA (c n)`, 前缀 `coA (c n)`) 的分支输出支配, 对每一格.

```agda
module NodeCmp {ly W₀ W} (ac : AccY ly) (u : NK.Bu ly W₀) (q₀ : _≤w_ L₀ W₀ W) (lW : LgW L₀ W)
               (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
  open Node ac u q₀ lW ll A₀ w Y

  BrMono : Set
  BrMono = ∀ n → yc (N0.Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (N0.τ₀ lW)
                   ⊑ yc (NK.κΔA ac u q₀ lW ll A₀ (c n)) (NK.τ₀ (NK.lwA (c n) , proj₂ lW))

  node≤ : BrMono → ∀ {m} (Tq : Tg W hz m) →
          N0.RKc ac (inj₁ κ₁) u q₀ lW ll A₀ w Y hz Tq ⊑ NK.RKc ac (inj₁ κ₁) u q₀ lW ll A₀ w Y hz Tq
  node≤ h Tq = ω⊑nl (λ n → ⊑-tr (drp⊑ _) (⊑-tr (h n) (⊑drp _)))
```

前提可满足 (形状): 取 $\Delta_n$ 就是 $c$ 时 `⊑-rf`; 对实际的两份折叠, `BrMono` 没有实例 (见入口).

## §3 整体: 条件比较

```agda
Dom : LvFb KΛc (tpK GΛ) Λ → LvFb KΛc (tpK GΛ) Λ → Set
Dom l₁ l₂ = ∀ {ly W₀ W} (ac : AccY ly) (x : D ly W₀) (q₀ : _≤w_ L₀ W₀ W) (lW : LgW L₀ W)
              (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
              yc (KR.Run KΛc GΛ LdΛ flΛ Λ lΛ one⊲ l₁ ac x q₀ lW ll A₀ w Y) (KR.τ₀ KΛc GΛ LdΛ flΛ Λ lΛ one⊲ l₁ lW)
                ⊑ yc (KR.Run KΛc GΛ LdΛ flΛ Λ lΛ one⊲ l₂ ac x q₀ lW ll A₀ w Y) (KR.τ₀ KΛc GΛ LdΛ flΛ Λ lΛ one⊲ l₁ lW)

-- 形状可满足: 同一个级回灌
Dom-refl : ∀ l → Dom l l
Dom-refl l ac x q₀ lW ll A₀ w Y b = ≤-refl _

-- 条件定理: TK₀ ≤ TK
TK₀≤TK : Dom lv₀ lvΛ → TK₀ ≤ᴬ TK
TK₀≤TK h = h accᴸ (Om.Ωd (topStepG (tpK GΛ)) Λ) ≤rf CK.lW₁ hself CK.Act n0 CK.Y₀ (asuc azero)
```
