# 跨高度, 不用外延性 (三): 换实例, 在值上

> 不含记号. 入口 [HtCrossV](HtCrossV.lagda.md). [HtCrossVRun](HtCrossVRun.lagda.md) 在第 0 层上的推论. 与 [HtCrossInst](HtCrossInst.lagda.md) 一一对应, 差两处: 结论是值上的 ($\le$ 两个方向, `TLRuleSpec._≤_`), 不是树的相等; **小的那个实例**的最高层不含 $\Omega$-极限 (`Free`). 大的那个实例任意.
>
> 1. **`inst0′`**: 任一层的输入 (与自己相关), 两个实例, 第 0 层的输出相关 (`Rl hz`), 所以和在值上相等.
> 2. **`change′`**: `Free Λ` ⇒ `TΛ Λ l` 与 `TΛ-in Λ′ l′ Λ e` 互相 $\le$, 一切 $\Lambda'$, $e : \Lambda\lhd_{[1]}\Lambda'$. **`lg-irr′`**. 特例 `hs-in′`, `hl-in′`, `hΩ-in′` (后者要 `Free (g c)`, $\Omega$-极限本身任意).
> 3. **`hs-reduce′`, `hs-reduce<′`**: `Free Λ` 且 `MonoStep` ⇒ `TΛ Λ ≤ TΛ (hs Λ)`, 严格. **`hl-reduce′`, `hl-reduce<′`**: `Free (f n)` 且 `MonoL n` ⇒ `TΛ (f n) ≤ TΛ (hl f)`, 严格. `MonoStep`, `MonoL` 与 `HtCrossInst` 的逐字相同 (`HtCrossVBridge` 用 `refl` 核对).
> 4. 不用外延性的展开与严格 (`hs-unfold`, `hl-unfold`, `hs-strict`, `hl-strict`) 照抄 `HtCrossInst`, 免得导入它.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossVInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; s≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedGrow using (nz≤; nz-Ωd; nzL; module G)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅; module At; TΛ; one)
import OCF.Align.HtFeedFold as Fold
open import OCF.Align.HtCrossVSim
open import OCF.Align.HtCrossVRun using (module Two)

-- 值上相等
infix 4 _≈_
_≈_ : A → A → Set
a ≈ b = (a ≤ b) × (b ≤ a)
```

## §1 第 0 层的换实例

```agda
module Cross (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) (fr : ∀ {t m} → t ⊲[ m ] Λ₁ → t ⊲[ m ] Λ₂ → Free t) where
  open Two Λ₁ l₁ Λ₂ l₂ fr
  module P₁ = At Λ₁ l₁
  module P₂ = At Λ₂ l₂

  Act-R : ∀ {ly W} → IgR (P₁.Act {ly} {W}) (P₂.Act {ly} {W})
  Act-R = igr (λ p lW′ hw hY → Step-R hY)

  Y₀-R : ∀ {W} → StR (P₁.Y₀ {W}) (P₂.Y₀ {W})
  Y₀-R = str zero-R

  inst0′ : ∀ {ly W₀ W} (x : D ly W₀) → Rl ly x x → (q₀ : W₀ ⊲ W) (lW : Lg W) (ll₁ : ly ⊲[ W ] Λ₁) (ll₂ : ly ⊲[ W ] Λ₂) →
           Rl hz (P₁.yc (P₁.Run accᴸ x q₀ lW ll₁ P₁.Act n0 P₁.Y₀) (P₁.τ₀ lW)) (P₂.yc (P₂.Run accᴸ x q₀ lW ll₂ P₂.Act n0 P₂.Y₀) (P₂.τ₀ lW))
  inst0′ x hx q₀ lW ll₁ ll₂ = at (Run-R accᴸ accᴸ hx q₀ lW ll₁ ll₂ Act-R s0 Y₀-R) C.self (z⊲ᴴ Λ₁) (z⊲ᴴ Λ₂) lW

-- 关系在值上: 和互相 ≤
Rl→≈ : ∀ {W} {x y : D₀ W} → Rl hz x y → ∀ b → sum b x ≈ sum b y
Rl→≈ r b = sum-R accᴸ r (≤-refl b) , sum-R′ accᴸ r (≤-refl b)
```

## §2 闭项换实例

`TΛ-in` 与 `HtCrossInst.TΛ-in` 逐字相同.

```agda
TΛ-in : ∀ (Λ′ : H) → LgH Λ′ → ∀ Λ → Λ ⊲[ one ] Λ′ → A
TΛ-in Λ′ l′ Λ e = sum azero (n1 ⨾ P.yc (P.Run accᴸ (Ωd Λ {azero}) (z⊲ one) tt e P.Act n0 P.Y₀) (P.τ₀ tt))
  where module P = At Λ′ l′

change′ : ∀ Λ (l : LgH Λ) → Free Λ → ∀ Λ′ (l′ : LgH Λ′) (e : Λ ⊲[ one ] Λ′) → TΛ Λ l ≈ TΛ-in Λ′ l′ Λ e
change′ Λ l fΛ Λ′ l′ e =
  Rl→≈ (Cross.inst0′ Λ l Λ′ l′ (λ p _ → free⊲ p fΛ) (Ωd Λ) (Ωd-R Λ fΛ accᴸ) (z⊲ one) tt hself e) one

-- 闭项的值与合法性证明无关
lg-irr′ : ∀ Λ (l l′ : LgH Λ) → Free Λ → TΛ Λ l ≈ TΛ Λ l′
lg-irr′ Λ l l′ fΛ = change′ Λ l fΛ Λ l′ hself

hs-in′ : ∀ Λ (l : LgH Λ) → Free Λ → TΛ Λ l ≈ TΛ-in (hs Λ) l Λ (hsuc hself)
hs-in′ Λ l fΛ = change′ Λ l fΛ (hs Λ) l (hsuc hself)

hl-in′ : ∀ (f : ℕ → H) (l : LgH (hl f)) n → Free (f n) → TΛ (f n) (proj₂ l n) ≈ TΛ-in (hl f) l (f n) (hlim n hself)
hl-in′ f l n fn = change′ (f n) (proj₂ l n) fn (hl f) l (hlim n hself)

-- Ω-极限: 分支 g c 不含 Ω-极限就行, hΩ g 本身任意
hΩ-in′ : ∀ (g : A → H) (l : LgH (hΩ g)) c (e : c ⊲ one) → Free (g c) → TΛ (g c) (proj₂ l c (C.lg⊲ e tt)) ≈ TΛ-in (hΩ g) l (g c) (hLim e hself)
hΩ-in′ g l c e fc = change′ (g c) (proj₂ l c (C.lg⊲ e tt)) fc (hΩ g) l (hLim e hself)
```

## §3 一步 $\Lambda\mapsto\Lambda+1$

`b₀`, `X`, `X′`, `hs-unfold`, `MonoStep` 照抄 `HtCrossInst.Hs`. 原文的 `X≡ : X ≡ X′` (要外延性) 换成 `X≈ : sum b₀ X ≈ sum b₀ X′`.

```agda
b₀ : A
b₀ = sum {one} one (nl (λ _ → n1 ⨾ n0))

module Hs (Λ : H) (l : LgH Λ) where
  module P = At (hs Λ) l
  module Q = At Λ l

  A² : P.Ig Λ one
  A² = P.Ai accᴸ (accK {azero} (ss hself)) (ss hself) (λ _ _ _ → n1) (z⊲ one) (hsuc hself) hself P.Act (n0 ⨾ nw (z⊲ one) n1)

  X : D₀ one
  X = P.yc (P.Run (accK {azero} (ss hself)) (Ωd Λ {one}) C.self tt (hsuc hself) A² (n0 ⨾ nw C.self n0)
             (P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)) tt P.zeroD)) (P.τ₀ tt)

  X′ : D₀ one
  X′ = Q.yc (Q.Run accᴸ (Ωd Λ {one}) C.self tt hself Q.Act (n0 ⨾ nw C.self n0)
             (Q._⊕⟨_⟩_ (Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)) tt Q.zeroD)) (Q.τ₀ tt)

  hs-unfold : sum b₀ X ≤ TΛ (hs Λ) l
  hs-unfold = ≤l 1 (≤l 1 (≤-refl _))

  XR : Free Λ → Rl hz X X′
  XR fΛ = at (Run-R (accK {azero} (ss hself)) accᴸ (Ωd-R Λ fΛ accᴸ) C.self tt (hsuc hself) hself A²-R (s⨾ s0 (sw s0))
                (⊕-R tt (⊕-R tt y0 (Step-R y0)) zero-R))
             C.self (z⊲ᴴ (hs Λ)) (z⊲ᴴ Λ) tt
    where
    open Two (hs Λ) l Λ l (λ _ q → free⊲ q fΛ)
    A²-R : IgR A² Q.Act
    A²-R = igr (λ p lW′ hw hY → Step-R hY)
    y0 : StR (P.Y₀ {one}) (Q.Y₀ {one})
    y0 = str zero-R

  X≈ : Free Λ → sum b₀ X ≈ sum b₀ X′
  X≈ fΛ = Rl→≈ (XR fΛ) b₀

  MonoStep : Set
  MonoStep = sum one (Q.yc Q.ΔΩ (Q.τ₀ tt)) ≤ sum b₀ X′

  hs-reduce′ : Free Λ → MonoStep → TΛ Λ l ≤ TΛ (hs Λ) l
  hs-reduce′ fΛ m = ≤-trans m (≤-trans (proj₂ (X≈ fΛ)) hs-unfold)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ sum b x
sum≥ b x = ⊲→≤ (sum-fst b x)

mono-hz : Hs.MonoStep hz tt
mono-hz = sum≥ b₀ (Hs.X′ hz tt)

hz≤1′ : TΛ hz tt ≤ TΛ (hs hz) tt
hz≤1′ = Hs.hs-reduce′ hz tt tt mono-hz
```

## §4 ℕ-极限

照抄 `HtCrossInst.Hl`; 原文 `hl-reduce` 用 `hl-in` (相等), 这里用 `hl-in′` 的一个方向.

```agda
module Hl (f : ℕ → H) (l : LgH (hl f)) where
  module P = At (hl f) l

  Fi : ℕ → D (hl f) azero
  Fi j = ni (sl j hself) (λ _ _ _ → n1)

  Rp : ℕ → D (hl f) one × P.St one
  Rp = P.Rpt accᴸ Fi (z⊲ one) tt hself P.Act (n0 ⨾ nw (z⊲ one) n1) (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))

  d : ℕ → D₀ one
  d j = P.yc (P.Run accᴸ (Fi j) (z⊲ one) tt hself P.Act (proj₁ (Rp j)) (proj₂ (Rp j))) (P.τ₀ tt)

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

    MonoL : Set
    MonoL = TΛ-in (hl f) l (f n) hk ≤ sum β X

    hl-reduce′ : Free (f n) → MonoL → TΛ (f n) (proj₂ l n) ≤ TΛ (hl f) l
    hl-reduce′ fn m = ≤-trans (≤-trans (proj₁ (hl-in′ f l n fn)) m) hl-unfold
```

## §5 严格

照抄 `HtCrossInst` §5 的无前提部分 (`hs-strict`, `hl-strict`); 归结换成值上的.

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

  hs-reduce<′ : Free Λ → MonoStep → asuc (TΛ Λ l) ≤ TΛ (hs Λ) l
  hs-reduce<′ fΛ m = ≤-trans (s≤ (≤-trans m (proj₂ (X≈ fΛ)))) hs-strict

hz<1′ : asuc (TΛ hz tt) ≤ TΛ (hs hz) tt
hz<1′ = HsS.hs-reduce<′ hz tt tt mono-hz

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

  hl-reduce<′ : Free (f n) → MonoL → asuc (TΛ (f n) (proj₂ l n)) ≤ TΛ (hl f) l
  hl-reduce<′ fn m = ≤-trans (s≤ (≤-trans (proj₁ (hl-in′ f l n fn)) m)) hl-strict
```

## §6 可数的高度都在内

`emb` 把 `A` 的树换成高度 (`HtFeedHt`), 不含 $\Omega$-极限, 所以本文的结论对一切可数高度成立; $\Omega$ 本身 (`Ωᴴ = hΩ emb`) 不在内, 但它在世界 $1$ 里的两个分支在内 (`Ω-in′`).

```agda
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ)

free-emb : ∀ a → Free (emb a)
free-emb azero = tt
free-emb (asuc a) = free-emb a
free-emb (alim f) = λ n → free-emb (f n)

lg-irr-emb : ∀ a (l l′ : LgH (emb a)) → TΛ (emb a) l ≈ TΛ (emb a) l′
lg-irr-emb a l l′ = lg-irr′ (emb a) l l′ (free-emb a)

Ω-in′ : ∀ c (e : c ⊲ one) → TΛ (emb c) (proj₂ Lg-Ωᴴ c (C.lg⊲ e tt)) ≈ TΛ-in Ωᴴ Lg-Ωᴴ (emb c) (hLim e hself)
Ω-in′ c e = hΩ-in′ emb Lg-Ωᴴ c e (free-emb c)

hs-reduce<-emb : ∀ a (l : LgH (emb a)) → Hs.MonoStep (emb a) l → asuc (TΛ (emb a) l) ≤ TΛ (hs (emb a)) l
hs-reduce<-emb a l = HsS.hs-reduce<′ (emb a) l (free-emb a)
```
