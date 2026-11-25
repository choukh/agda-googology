# 跨层模拟 `Simʰ` 的接口: 关系, 前提 `Compat`, `KeepRow`, 陈述 `MonoH`

验收文件, 接口 (定稿后只增不改). 只有定义, 没有定理: 两层 `K`, `K′` 的树之间的模拟 `Simʰ` (对层号对双重递归, 不经参照框架, 不读记号), 派发的前提 `Compat` (一族配置对及其封闭律), Ω 结点层号的根保留时分支族的前提 `KeepRow`, 以及要证的陈述 `MonoH`.
结点的比较不看位置本身: 两个位置任意, 证据是它们的层号字面相等, 且那一层的顶相关 (律里的每一对位置都带这两条证据). 证明在 [YiCrossMono](YiCrossMono.lagda.md), 配对的否定建在本文件上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossIface where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; self)
open import OCF.Lean.YiLamFold using (Kfk; nrmk; nrmk-lgl; Wit; Lw; w0; ws; wl; wΩ; rootW; Pk)
import OCF.Lean.YiDlFold as W
open Pk
```

## 1 关系

一层对 `(K , K′)` 上的规则. `Pr r r′` 是两个位置上那两层之间的关系, `KL`, `KR` 是进左边, 右边的孩子之后的关系.
`nN` 的两个位置任意, 证据 `Ps` 是两个位置的层号相等, 另带顶相关 (只要顶相关时, 层号 2 上结构派发 `cmpw` 就会左保留右折叠); `eL`, `eR` 使嵌入透明; `cR`: 落在允许的孩子的顶之下就在本层的顶之下;
`t0`: 第 0 层的顶读作 1 (`add zero B x top = suc x`).

```agda
module H (K K′ : LF)
  (Ps : Pre K → Pre K′ → Set)
  (Pr : (r : Pre K) (r′ : Pre K′) → Lay.A (Lo K r) → Lay.A (Lo K′ r′) → Set)
  (KL : (i : Kid K) → Lay.A (KS K i) → Raw K′ → Set)
  (KR : (i′ : Kid K′) → Raw K → Lay.A (KS K′ i′) → Set)
  (Tp Zr : Set) (Ct : Kid K′ → Set) where
  infix 4 _⊑_
  data _⊑_ : Raw K → Raw K′ → Set where
    zS : ∀ {b} → G.zero ⊑ b
    sS : ∀ {a b} → a ⊑ b → G.suc a ⊑ G.suc b
    wS : ∀ {a b} → a ⊑ b → a ⊑ G.suc b
    lR : ∀ {a} {F : ℕ → Raw K′} n → a ⊑ F n → a ⊑ G.lim F
    lL : ∀ {F : ℕ → Raw K} {b} → (∀ n → F n ⊑ b) → G.lim F ⊑ b
    bR : ∀ {a r′ g′} → a ⊑ g′ (Lay.tp (Lo K′ r′)) → a ⊑ G.lc r′ g′
    nN : ∀ {r r′ g g′} → Ps r r′ → Pr r r′ (Lay.tp (Lo K r)) (Lay.tp (Lo K′ r′)) →
      (∀ η η′ → Pr r r′ η η′ → g η ⊑ g′ η′) → G.lc r g ⊑ G.lc r′ g′
    eL : ∀ {i a b} → KL i a b → G.em i a ⊑ b
    eR : ∀ {i′ a b′} → KR i′ a b′ → a ⊑ G.em i′ b′
    tT : Tp → G.top ⊑ G.top
    cR : ∀ {i′ a} → Ct i′ → KR i′ a (Lay.tp (KS K′ i′)) → a ⊑ G.top
    t0 : ∀ {b} → Zr → G.top ⊑ G.suc b

open H public using (zS; sS; wS; lR; lL; bR; nN; eL; eR; tT; cR; t0)
```

对层号对的递归: 位置先沿左边走到叶 (`SimP`), 再沿右边 (`SimQ`). 顶对顶 `TopR`: 左边是第 0 层时总成立; 后继对后继要前驱层相等且顶相关 (折叠后是根位置的一对结点);
ℕ 极限对 ℕ 极限逐项; Ω 结点层号对 Ω 结点层号只要下标层相等且顶相关 (分支层的顶在链点上相关是 `Compat` 的律 `c-obs`: 链点由公共上界与派发决定, 不是关系内部的量;
对一切相关的下标要求分支层的顶相关时, `tw 2` 的顶不自相关). 允许的孩子 `Ct`: 后继层号的孩子, ℕ 极限层号的第 0 个孩子
(第 `n` 个孩子的顶在折叠后是部分和的一项, 要目标层上的左加; Ω 结点层号的孩子不允许, 那里 `x + top = suc x`).

```agda
Simʰ : (K K′ : LF) → Raw K → Raw K′ → Set
SimP : (K K′ : LF) (r : Pre K) (r′ : Pre K′) → Lay.A (Lo K r) → Lay.A (Lo K′ r′) → Set
SimQ : (j K′ : LF) (r′ : Pre K′) → Raw j → Lay.A (Lo K′ r′) → Set
SimL : (K K′ : LF) (i : Kid K) → Lay.A (KS K i) → Raw K′ → Set
SimR : (K K′ : LF) (i′ : Kid K′) → Raw K → Lay.A (KS K′ i′) → Set
TopR : LF → LF → Set
IsZero : LF → Set
Ct : (K′ : LF) → Kid K′ → Set

Simʰ K K′ = H._⊑_ K K′ (λ r r′ → lev K r ≡ lev K′ r′) (SimP K K′) (SimL K K′) (SimR K K′) (TopR K K′) (IsZero K) (Ct K′)

SimP zero K′ ()
SimP (suc k) K′ (inj₁ _) r′ = SimQ k K′ r′
SimP (suc k) K′ (inj₂ r) r′ = SimP k K′ r r′
SimP (lim f) K′ (n , r) r′ = SimP (f n) K′ r r′
SimP (lc k g) K′ (η , _ , r) r′ = SimP (g η) K′ r r′

SimQ j zero ()
SimQ j (suc k′) (inj₁ _) = Simʰ j k′
SimQ j (suc k′) (inj₂ r′) = SimQ j k′ r′
SimQ j (lim f′) (n , r′) = SimQ j (f′ n) r′
SimQ j (lc k′ g′) (η′ , _ , r′) = SimQ j (g′ η′) r′

SimL zero K′ ()
SimL (suc k) K′ _ = Simʰ k K′
SimL (lim f) K′ n = Simʰ (f n) K′
SimL (lc k g) K′ (η , _) = Simʰ (g η) K′

SimR K zero ()
SimR K (suc k′) _ = Simʰ K k′
SimR K (lim f′) n = Simʰ K (f′ n)
SimR K (lc k′ g′) (η′ , _) = Simʰ K (g′ η′)

TopR zero K′ = ⊤
TopR (suc k) (suc k′) = (k ≡ k′) × Simʰ k k′ G.top G.top
TopR (lim f) (lim f′) = ∀ n → Simʰ (f n) (f′ n) G.top G.top
TopR (lc k g) (lc k′ g′) = (k ≡ k′) × Simʰ k k′ G.top G.top
TopR _ _ = ⊥

IsZero zero = ⊤
IsZero _ = ⊥

Ct zero ()
Ct (suc k′) _ = ⊤
Ct (lim f′) n = n ≡ 0
Ct (lc k′ g′) _ = ⊥
```

## 2 前提与陈述

`WayR`: 两个派发同为保留或同为折叠. 左保留右折叠时折叠后不相关; 左折叠右保留时要把链点那一支上移, 上移任一支作为输入规则对右折叠的行不成立, 所以也不收.
`Compat`: 一族配置对 `C` (配置 = 公共上界与外部派发), 对目标层的顶, 位置对上的派发, 位置上的内层派发 `cmpw`, 后继层号的 `self`, 两边的孩子,
Ω 结点层号的根的派发 (`c-root`) 封闭, 并且两边第 `n` 个链点那一支的顶相关 (`c-obs`). 每条律里的位置对都带层号相等与顶相关的证据.
`KeepRow`: Ω 结点层号对 Ω 结点层号, 两边的根都保留时, 保留行的分支族 (`Kfk` 套归一 `nrmk`) 对相关的下标单调; 这一条不由结构归纳给出, 单列. `Rec` 是交给它用的归纳假设 (各支的 `top` 一行).

```agda
data WayR {m j m′ j′ : LF} : Way m j → Way m′ j′ → Set where
  kk : ∀ {p e p′ e′} → WayR (keep p e) (keep p′ e′)
  ff : WayR fold fold

module _ (D : ∀ k K → Ext k K) where
  open W.Fold D

  record Compat : Set₁ where
    field
      C : ∀ {m k m′ k′} → Lw k → Ext m k → Lw k′ → Ext m′ k′ → Set
      c-top : ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} →
        C V x V′ x′ → Simʰ m m′ G.top G.top
      c-way : ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} →
        C V x V′ x′ → ∀ r r′ → lev k r ≡ lev k′ r′ →
        SimP k k′ r r′ (Lay.tp (Lo k r)) (Lay.tp (Lo k′ r′)) → WayR (x r) (x′ r′)
      c-cmp : ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} →
        C V x V′ x′ → ∀ r r′ → lev k r ≡ lev k′ r′ →
        SimP k k′ r r′ (Lay.tp (Lo k r)) (Lay.tp (Lo k′ r′)) → C V (cmpw V r) V′ (cmpw V′ r′)
      c-self : ∀ {m k m′ k′} {V : Lw k} {x : Ext m (suc k)} {V′ : Lw k′} {x′ : Ext m′ (suc k′)} →
        C (ws V) x (ws V′) x′ → k ≡ k′ → Simʰ k k′ G.top G.top → C V (self k) V′ (self k′)
      c-Ls : ∀ {m k m′ k′} {V : Lw k} {x : Ext m (suc k)} {V′ : Lw k′} {x′ : Ext m′ k′} →
        C (ws V) x V′ x′ → C V (λ r → x (inj₂ r)) V′ x′
      c-Ll : ∀ {m f m′ k′} {V : ∀ n → Lw (f n)} {st} {x : Ext m (lim f)} {V′ : Lw k′} {x′ : Ext m′ k′} →
        C (wl V st) x V′ x′ → ∀ n → C (V n) (λ r → x (n , r)) V′ x′
      c-LΩ : ∀ {m k g m′ k′} {V : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} {x : Ext m (lc k g)}
        {V′ : Lw k′} {x′ : Ext m′ k′} →
        C (wΩ V w) x V′ x′ → ∀ η l → C (V η l) (λ r → x (η , l , r)) V′ x′
      c-Rs : ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ (suc k′)} →
        C V x (ws V′) x′ → C V x V′ (λ r → x′ (inj₂ r))
      c-Rl : ∀ {m k m′ f′} {V : Lw k} {x : Ext m k} {V′ : ∀ n → Lw (f′ n)} {st′} {x′ : Ext m′ (lim f′)} →
        C V x (wl V′ st′) x′ → ∀ n → C V x (V′ n) (λ r → x′ (n , r))
      c-RΩ : ∀ {m k m′ k′ g′} {V : Lw k} {x : Ext m k} {V′ : ∀ η → Lgl k′ η → Lw (g′ η)} {w′ : Wit k′ g′}
        {x′ : Ext m′ (lc k′ g′)} →
        C V x (wΩ V′ w′) x′ → ∀ η l → C V x (V′ η l) (λ r → x′ (η , l , r))
      c-root : ∀ {m k g m′ k′ g′} {V : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} {x : Ext m (lc k g)}
        {V′ : ∀ η → Lgl k′ η → Lw (g′ η)} {w′ : Wit k′ g′} {x′ : Ext m′ (lc k′ g′)} →
        C (wΩ V w) x (wΩ V′ w′) x′ → k ≡ k′ → Simʰ k k′ G.top G.top →
        WayR (rootW m k g w x) (rootW m′ k′ g′ w′ x′)
      c-obs : ∀ {m k g m′ k′ g′} {V : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} {x : Ext m (lc k g)}
        {V′ : ∀ η → Lgl k′ η → Lw (g′ η)} {w′ : Wit k′ g′} {x′ : Ext m′ (lc k′ g′)} →
        C (wΩ V w) x (wΩ V′ w′) x′ → ∀ n →
        Simʰ (g (co (ptsΩ k g V n))) (g′ (co (ptsΩ k′ g′ V′ n))) G.top G.top

  Rec : (S : Compat) (k : LF) (g : Raw k → LF) (k′ : LF) (g′ : Raw k′ → LF) →
    (∀ η → Lgl k η → Lw (g η)) → (∀ η → Lgl k′ η → Lw (g′ η)) → Set
  Rec S k g k′ g′ V V′ = ∀ η l η′ l′ {m₁ m₁′} (y : Ext m₁ (g η)) (y′ : Ext m₁′ (g′ η′)) →
    Compat.C S (V η l) y (V′ η′ l′) y′ → Simʰ (g η) (g′ η′) G.top G.top →
    Simʰ m₁ m₁′ (Ψ m₁ (V η l) y G.top) (Ψ m₁′ (V′ η′ l′) y′ G.top)

  record KeepRow (S : Compat) : Set where
    open Compat S
    field
      c-keep : ∀ {m k g m′ k′ g′} {V : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} {x : Ext m (lc k g)}
        {V′ : ∀ η → Lgl k′ η → Lw (g′ η)} {w′ : Wit k′ g′} {x′ : Ext m′ (lc k′ g′)} →
        C (wΩ V w) x (wΩ V′ w′) x′ → TopR (lc k g) (lc k′ g′) →
        ∀ {p q p′ q′} → rootW m k g w x ≡ keep p q → rootW m′ k′ g′ w′ x′ ≡ keep p′ q′ → Rec S k g k′ g′ V V′ →
        ∀ η η′ → Simʰ k k′ η η′ →
        Simʰ m m′
          (Kfk k (λ θ → Ψ m (V (nrmk k θ) (nrmk-lgl k θ)) (λ r → x (nrmk k θ , nrmk-lgl k θ , r)) G.top) η)
          (Kfk k′ (λ θ → Ψ m′ (V′ (nrmk k′ θ) (nrmk-lgl k′ θ)) (λ r → x′ (nrmk k′ θ , nrmk-lgl k′ θ , r)) G.top) η′)

  MonoH : Set₁
  MonoH = (S : Compat) → KeepRow S → ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} →
    Compat.C S V x V′ x′ → ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)
```
