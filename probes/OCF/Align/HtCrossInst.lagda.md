# 跨高度 (三): 换实例

> 不含记号. 入口 [HtCross](HtCross.lagda.md). [HtCrossRun](HtCrossRun.lagda.md) 的 `Run-R` 在第 0 层上的推论, 前提都是 `Funext`.
>
> 1. **`inst0`**: 任一层 $ly$ 的输入 (与自己相关), 在两个实例里折叠 (层到最高层的路径两边任取), 第 0 层的输出相等.
> 2. **`change`**: 闭项 `TΛ Λ l` 等于在**任何**以 $\Lambda$ 为世界 $1$ 中第一位置的实例 $\Lambda'$ 里折叠 $\Omega_\Lambda$ 的读数. 特例 `hs-in`, `hl-in`, `hΩ-in`. **`lg-irr`**: 闭项与合法性证明无关.
> 3. **`hs-unfold`** (不用 `Funext`): `TΛ (hs Λ)` 不低于它的链的第 $0$ 项里的一次折叠 $\Omega_\Lambda$. **`hs-reduce`**: 若实例 $\Lambda$ 内的一条单调 (`MonoStep`) 成立, 则 `TΛ Λ ≤ TΛ (hs Λ)`. 跨高度由此归结为一个实例之内的单调. `mono-hz`: $\Lambda = 0$ 时 `MonoStep` 成立. §4 对 ℕ-极限同样归结 (`hl-unfold`, `hl-reduce`).
> 4. §5 **严格**: 链里再走一格, 输出非零, 所以 `hs-strict`, `hl-strict` (无前提) 与 `hs-reduce<`, `hl-reduce<` (前提同上) 都是严格的; `hz<1`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; s≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedGrow using (nz≤; nz-Ωd; nzL; module G)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅; module At; TΛ; one)
import OCF.Align.HtFeedFold as Fold
open import OCF.Align.HtCrossSim
open import OCF.Align.HtCrossRun using (module Two)
```

## §1 第 0 层的换实例

```agda
module Cross (fe : Funext) (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) where
  open Two fe Λ₁ l₁ Λ₂ l₂
  module P₁ = At Λ₁ l₁
  module P₂ = At Λ₂ l₂

  Act-R : ∀ {ly W} → IgR (P₁.Act {ly} {W}) (P₂.Act {ly} {W})
  Act-R = igr (λ p lW′ hw hY → Step-R hY)

  Y₀-R : ∀ {W} → StR (P₁.Y₀ {W}) (P₂.Y₀ {W})
  Y₀-R = str zero-R refl

  -- 任一层的输入, 两个实例, 第 0 层输出相等
  inst0 : ∀ {ly W₀ W} (x : D ly W₀) → Rl ly x x → (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : ly ⊲[ W ] Λ₁) (ll₂ : ly ⊲[ W ] Λ₂) →
          P₁.yc (P₁.Run accᴸ x q₀ lW ll₁ P₁.Act n0 P₁.Y₀) (P₁.τ₀ lW) ≡ P₂.yc (P₂.Run accᴸ x q₀ lW ll₂ P₂.Act n0 P₂.Y₀) (P₂.τ₀ lW)
  inst0 x hx q₀ lW ll₁ ll₂ =
    eq0 fe accᴸ (at (Run-R accᴸ accᴸ hx q₀ lW ll₁ ll₂ Act-R s0 Y₀-R) C.self (z⊲ᴴ Λ₁) (z⊲ᴴ Λ₂) lW)
```

## §2 闭项换实例

`TΛ-in Λ′ l′ Λ e`: 在实例 $\Lambda'$ 里折叠 $\Omega_\Lambda$, 层的路径是 $e:\Lambda\lhd_{[1]}\Lambda'$, 其余同 `TΛ`. `e = hself` 时就是 `TΛ Λ′ l′` (字面).

```agda
TΛ-in : ∀ (Λ′ : H) → LgH Λ′ → ∀ Λ → Λ ⊲[ one ] Λ′ → A
TΛ-in Λ′ l′ Λ e = sum azero (n1 ⨾ P.yc (P.Run accᴸ (Ωd Λ {azero}) (z⊲ one) tt e P.Act n0 P.Y₀) (P.τ₀ tt))
  where module P = At Λ′ l′

TΛ-in-self : ∀ Λ (l : LgH Λ) → TΛ-in Λ l Λ hself ≡ TΛ Λ l
TΛ-in-self Λ l = refl

change : Funext → ∀ Λ (l : LgH Λ) Λ′ (l′ : LgH Λ′) (e : Λ ⊲[ one ] Λ′) → TΛ Λ l ≡ TΛ-in Λ′ l′ Λ e
change fe Λ l Λ′ l′ e = cong (λ x → sum azero (n1 ⨾ x)) (Cross.inst0 fe Λ l Λ′ l′ (Ωd Λ) (Ωd-R Λ accᴸ) (z⊲ one) tt hself e)

-- 闭项与合法性证明无关
lg-irr : Funext → ∀ Λ (l l′ : LgH Λ) → TΛ Λ l ≡ TΛ Λ l′
lg-irr fe Λ l l′ = change fe Λ l Λ l′ hself

-- 三种一步
hs-in : Funext → ∀ Λ (l : LgH Λ) → TΛ Λ l ≡ TΛ-in (hs Λ) l Λ (hsuc hself)
hs-in fe Λ l = change fe Λ l (hs Λ) l (hsuc hself)

hl-in : Funext → ∀ (f : ℕ → H) (l : LgH (hl f)) n → TΛ (f n) (proj₂ l n) ≡ TΛ-in (hl f) l (f n) (hlim n hself)
hl-in fe f l n = change fe (f n) (proj₂ l n) (hl f) l (hlim n hself)

-- Ω-极限: 只有坐标在世界 1 之下的分支 (c = 0, 1) 可以这样换
hΩ-in : Funext → ∀ (g : A → H) (l : LgH (hΩ g)) c (e : c ⊲ one) → TΛ (g c) (proj₂ l c (C.lg⊲ e tt)) ≡ TΛ-in (hΩ g) l (g c) (hLim e hself)
hΩ-in fe g l c e = change fe (g c) (proj₂ l c (C.lg⊲ e tt)) (hΩ g) l (hLim e hself)
```

## §3 一步 $\Lambda\mapsto\Lambda+1$: 归结为一个实例之内的单调

在实例 `hs Λ` 里, $\Omega_{\Lambda+1} = 1 ⨾ (\text{层 }\Lambda\text{ 的节点})$. 节点对第 0 层的目标上升, 链的第 $0$ 项是状态在层 $\Lambda$ 上的差 $0 ⨾ \omega\cdot(\Omega_\Lambda ⨾ 0)$, 再走一次. 所以 `TΛ (hs Λ)` 不低于在那个上下文、那个状态里折叠一次 $\Omega_\Lambda$ (`hs-unfold`, 都是计算, 再加两次 $\le$ 极限). 用 `Run-R` 把这一次搬回实例 $\Lambda$ (`X≡`).

```agda
b₀ : A
b₀ = sum {one} one (nl (λ _ → n1 ⨾ n0))

module Hs (Λ : H) (l : LgH Λ) where
  module P = At (hs Λ) l
  module Q = At Λ l

  A² : P.Ig Λ one
  A² = P.Ai accᴸ (accK {azero} (ss hself)) (ss hself) (λ _ _ _ → n1) (z⊲ one) (hsuc hself) hself P.Act (n0 ⨾ nw (z⊲ one) n1)

  -- 实例 hs Λ 里, 链的第 0 项的第 0 项
  X : D₀ one
  X = P.yc (P.Run (accK {azero} (ss hself)) (Ωd Λ {one}) C.self tt (hsuc hself) A² (n0 ⨾ nw C.self n0)
             (P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)) tt P.zeroD)) (P.τ₀ tt)

  -- 实例 Λ 里的同一次折叠
  X′ : D₀ one
  X′ = Q.yc (Q.Run accᴸ (Ωd Λ {one}) C.self tt hself Q.Act (n0 ⨾ nw C.self n0)
             (Q._⊕⟨_⟩_ (Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)) tt Q.zeroD)) (Q.τ₀ tt)

  hs-unfold : sum b₀ X ≤ TΛ (hs Λ) l
  hs-unfold = ≤l 1 (≤l 1 (≤-refl _))

  X≡ : Funext → X ≡ X′
  X≡ fe = eq0 fe accᴸ (at (Run-R (accK {azero} (ss hself)) accᴸ (Ωd-R Λ accᴸ) C.self tt (hsuc hself) hself A²-R (s⨾ s0 (sw s0))
                             (⊕-R tt (⊕-R tt y0 (Step-R y0)) zero-R))
                         C.self (z⊲ᴴ (hs Λ)) (z⊲ᴴ Λ) tt)
    where
    open Two fe (hs Λ) l Λ l
    A²-R : IgR A² Q.Act
    A²-R = igr (λ p lW′ hw hY → Step-R hY)
    y0 : StR (P.Y₀ {one}) (Q.Y₀ {one})
    y0 = str zero-R refl

  -- 实例 Λ 之内的一条单调: 输入世界 0→1, 底 1→1+ω, 上下文与状态各多一段
  MonoStep : Set
  MonoStep = sum one (Q.yc Q.ΔΩ (Q.τ₀ tt)) ≤ sum b₀ X′

  hs-reduce : Funext → MonoStep → TΛ Λ l ≤ TΛ (hs Λ) l
  hs-reduce fe m = ≤-trans m (subst (λ x → sum b₀ x ≤ TΛ (hs Λ) l) (X≡ fe) hs-unfold)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ sum b x
sum≥ b x = ⊲→≤ (sum-fst b x)

-- Λ = 0: MonoStep 成立, 所以 TΛ 0 ≤ TΛ 1
mono-hz : Hs.MonoStep hz tt
mono-hz = sum≥ b₀ (Hs.X′ hz tt)

hz≤1 : Funext → TΛ hz tt ≤ TΛ (hs hz) tt
hz≤1 fe = Hs.hs-reduce hz tt fe mono-hz
```

## §4 ℕ-极限 $\Lambda=\lim_n f(n)$: 同样归结

`Ωd (hl f) = 1 ⨾ nl (n ↦ 层 f n 的节点)`. 第 $n$ 个节点对第 0 层的目标上升 (`rk0`: 第 0 层的目标上不可能保留, 对变量 $n$ 不能计算, 所以用相等搬). 链的第 0 项是状态在层 $f(n)$ 上的差, 它是左结合的 $(\dots((0 ⨾ \omega\cdot(\Omega_{f(n)} ⨾ 0)) ⨾ \Delta_0) \dots) ⨾ \Delta_{n-1}$, 折叠的读数不低于最左一段 (`nest`). 所以 `TΛ (hl f)` 不低于在第 $n$ 段的上下文与状态里折叠一次 $\Omega_{f(n)}$ (`hl-unfold`). `MonoL n` 是实例 `hl f` 之内的单调 (空状态对第 $n$ 段的状态).

```agda
module Hl (f : ℕ → H) (l : LgH (hl f)) where
  module P = At (hl f) l
  open import Data.Product using (_×_)

  Fi : ℕ → D (hl f) azero
  Fi j = ni (sl j hself) (λ _ _ _ → n1)

  Rp : ℕ → D (hl f) one × P.St one
  Rp = P.Rpt accᴸ Fi (z⊲ one) tt hself P.Act (n0 ⨾ nw (z⊲ one) n1) (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))

  d : ℕ → D₀ one
  d j = P.yc (P.Run accᴸ (Fi j) (z⊲ one) tt hself P.Act (proj₁ (Rp j)) (proj₂ (Rp j))) (P.τ₀ tt)

  TΛ≡ : TΛ (hl f) l ≡ alim (pt b₀ d)
  TΛ≡ = refl

  rk0 : ∀ {k m} (x : P.Rk k hz m) → x ≡ P.rise
  rk0 (P.keep ())
  rk0 P.rise = refl

  module N (n : ℕ) where
    r : StH azero (f n) (hl f)
    r = sl n hself

    hk : f n ⊲[ one ] hl f
    hk = hlim n hself

    A² : P.Ig (f n) one
    A² = P.Ai accᴸ (accK r) r (λ _ _ _ → n1) (z⊲ one) hk hself P.Act (proj₁ (Rp n))

    β : A
    β = pt b₀ d n

    RK : P.Rk (f n) hz one → D₀ one
    RK x = P.RKi accᴸ (accK r) r (λ _ _ _ → n1) (z⊲ one) tt hself P.Act (proj₁ (Rp n)) (proj₂ (Rp n)) (P.τ₀ tt) x

    dn≡ : d n ≡ RK P.rise
    dn≡ = cong RK (rk0 _)

    T : P.Tg one (f n) one
    T = P.tg C.self hk tt

    -- 第 n 段的状态在层 f n 上的差: 读数不低于最左一段
    nest : ∀ m (A₀ : P.Ig (f n) one) (w : D (f n) one) (Y : P.St one) b →
           sum b (P.yc (P.Run (accK r) (P.yc (P.d (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))) T) C.self tt hk A₀ w Y) (P.τ₀ tt)) ≤
           sum b (P.yc (P.Run (accK r) (P.yc (P.d (proj₂ (Rp m))) T) C.self tt hk A₀ w Y) (P.τ₀ tt))
    nest zero A₀ w Y b = ≤-refl _
    nest (suc m) A₀ w Y b = ≤-trans (nest m A₀ w Y b) (sum≥ _ _)

    X : D₀ one
    X = P.yc (P.Run (accK r) (Ωd (f n) {one}) C.self tt hk A² (n0 ⨾ nw C.self n0) (P._⊕⟨_⟩_ (proj₂ (Rp n)) tt P.zeroD)) (P.τ₀ tt)

    hl-unfold : sum β X ≤ TΛ (hl f) l
    hl-unfold = ≤l (suc n) (subst (λ y → sum β X ≤ sum β y) (sym dn≡)
                  (≤l 1 (≤-trans (≤l 1 (≤-refl _)) (nest n A² n0 (proj₂ (Rp n)) β))))

    -- 实例 hl f 之内: 空状态折叠 Ω_{f n} 不高于第 n 段的状态里折叠
    MonoL : Set
    MonoL = TΛ-in (hl f) l (f n) hk ≤ sum β X

    hl-reduce : Funext → MonoL → TΛ (f n) (proj₂ l n) ≤ TΛ (hl f) l
    hl-reduce fe m = ≤-trans (subst (λ y → y ≤ sum β X) (sym (hl-in fe f l n)) m) hl-unfold
```

## §5 严格: 链里再走一格

`hs-unfold`, `hl-unfold` 取的是链第 0 项里的第 0 格. 第 1 格又折叠一次 $\Omega_\Lambda ⨾ 0$, 动作是 `Step`, 所以第 0 层的输出非零 (`HtFeedGrow.L3`). 于是不等式是严格的 (`hs-strict`, `hl-strict`, 无前提), 归结也给出严格的跨高度增长 (`hs-reduce<`, `hl-reduce<`, 前提同上).

```agda
module HsS (Λ : H) (l : LgH Λ) where
  open Hs Λ l
  module GG = G (hs Λ) l

  hs-strict : asuc (sum b₀ X) ≤ TΛ (hs Λ) l
  hs-strict = ≤l 1 (≤l 2 (nz≤ (sum b₀ X)
    (GG.L3 (accK {azero} (ss hself)) {x = Ωd Λ {one} ⨾ n0} C.self tt (hsuc hself) A² (P.τ₀ tt) (GG.na (λ w Y → GG.nz-Step Y (P.τ₀ tt))) (nzL (nz-Ωd Λ))
       (proj₁ Rq) (proj₂ Rq))))
    where
    Rq = P.Rpt (accK {azero} (ss hself)) (λ _ → Ωd Λ {one} ⨾ n0) C.self tt (hsuc hself) A² (n0 ⨾ nw C.self n0)
               (P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)) tt P.zeroD) 1

  hs-reduce< : Funext → MonoStep → asuc (TΛ Λ l) ≤ TΛ (hs Λ) l
  hs-reduce< fe m = ≤-trans (s≤ m) (subst (λ x → asuc (sum b₀ x) ≤ TΛ (hs Λ) l) (X≡ fe) hs-strict)

hz<1 : Funext → asuc (TΛ hz tt) ≤ TΛ (hs hz) tt
hz<1 fe = HsS.hs-reduce< hz tt fe mono-hz

module HlS (f : ℕ → H) (l : LgH (hl f)) (n : ℕ) where
  open Hl f l
  open N n
  module GG = G (hl f) l

  hl-strict : asuc (sum β X) ≤ TΛ (hl f) l
  hl-strict = ≤l (suc n) (subst (λ y → asuc (sum β X) ≤ sum β y) (sym dn≡)
                (≤l 1 (≤-trans (≤l 2 (nz≤ (sum β X)
                          (GG.L3 (accK r) {x = Ωd (f n) {one} ⨾ n0} C.self tt hk A² (P.τ₀ tt) (GG.na (λ w Y → GG.nz-Step Y (P.τ₀ tt))) (nzL (nz-Ωd (f n)))
                             (proj₁ Rq) (proj₂ Rq))))
                        (nest n A² n0 (proj₂ (Rp n)) β))))
    where
    Rq = P.Rpt (accK r) (λ _ → Ωd (f n) {one} ⨾ n0) C.self tt hk A² (n0 ⨾ nw C.self n0) (P._⊕⟨_⟩_ (proj₂ (Rp n)) tt P.zeroD) 1

  hl-reduce< : Funext → MonoL → asuc (TΛ (f n) (proj₂ l n)) ≤ TΛ (hl f) l
  hl-reduce< fe m = ≤-trans (s≤ (subst (λ y → y ≤ sum β X) (sym (hl-in fe f l n)) m)) hl-strict
```
