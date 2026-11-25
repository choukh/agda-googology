# 主线派发 `dl` 的 `Compat` 不含塔与 Λ 的配置对

验收文件. 编译定理, 无前提: 任何 `S : Compat dl` 都不含 `(Lw-tw (2+n), x, Lw-tw (2+j), x′)` (`no-tw`, 任意 `n j` 与外部派发, 含相邻项与自身), `(Lw-tw (2+n), x, VΛ, x′)` (`no-Λ`), `(VΛ, x, VΛ, x′)` (`no-ΛΛ`).
办法: 左边沿 `c-LΩ` 进 `tw 2` 型的支 `ω+2` (公共上界是 `ws (ws _)`), `c-cmp` 取层号 `ω+1` 的一对位置, `c-way` 取层号 `ω` 的一对: 左边结构派发保留, 右边 `dl` 折叠 (`dl-lim`), 与 `WayR` 矛盾 (`core`). 位置都是合法树, 不用退化结点.
不否定 `Compat` 本身可满足 (`S∅`); 对一切派发的形式 (推出 LPO) 在 [YiCompatDlLPO](YiCompatDlLPO.lagda.md), 错位处的 `Simʰ` 在 [YiCompatDlLoss](YiCompatDlLoss.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCompatDlNeg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; ⌜_⌝)
open import OCF.Lean.YiLamFold using (Wit; Lw; w0; ws; wl; wΩ; Lw-tw; VΛ; Lw-Ω̂; lgl→Lw)
import OCF.Lean.YiNextTower as T
open import OCF.Lean.YiDlFold using (dl; cmpw)
open import OCF.Lean.YiDlLost using (LimL; dl-lim)
open import OCF.Lean.YiCrossIface
```

## 1 部件

`ʰ→P`: 位置对的顶相关只看两个位置的层号 (`YiCrossInst` 的 `P→ʰ` 的逆).

```agda
noKF : ∀ {m j m′ j′} {p : Pre m} {e : lev m p ≡ j} {w : Way m′ j′} → w ≡ fold → WayR (keep p e) w → ⊥
noKF refl ()

trR : ∀ {j L L′} → L ≡ L′ → Simʰ j L G.top G.top → Simʰ j L′ G.top G.top
trR refl d = d

trL : ∀ {L L′ j} → L ≡ L′ → Simʰ L j G.top G.top → Simʰ L′ j G.top G.top
trL refl d = d

ʰ→Q : ∀ j K′ (r′ : Pre K′) → Simʰ j (lev K′ r′) G.top G.top → SimQ j K′ r′ G.top (Lay.tp (Lo K′ r′))
ʰ→Q j zero () d
ʰ→Q j (suc k′) (inj₁ _) d = d
ʰ→Q j (suc k′) (inj₂ r′) d = ʰ→Q j k′ r′ d
ʰ→Q j (lim f′) (n , r′) d = ʰ→Q j (f′ n) r′ d
ʰ→Q j (lc k′ g′) (η′ , _ , r′) d = ʰ→Q j (g′ η′) r′ d

ʰ→P : ∀ K (r : Pre K) K′ (r′ : Pre K′) → Simʰ (lev K r) (lev K′ r′) G.top G.top →
  SimP K K′ r r′ (Lay.tp (Lo K r)) (Lay.tp (Lo K′ r′))
ʰ→P zero () K′ r′ d
ʰ→P (suc k) (inj₁ _) K′ r′ d = ʰ→Q k K′ r′ d
ʰ→P (suc k) (inj₂ r) K′ r′ d = ʰ→P k r K′ r′ d
ʰ→P (lim f) (n , r) K′ r′ d = ʰ→P (f n) r K′ r′ d
ʰ→P (lc k g) (η , _ , r) K′ r′ d = ʰ→P (g η) r K′ r′ d

-- 第 0 层的树的读回, 顶自相关
reflR : ∀ (a : R) → Simʰ ⌜ a ⌝ ⌜ a ⌝ G.top G.top
reflR G.zero = tT tt
reflR (G.suc a) = tT (refl , reflR a)
reflR (G.lim f) = tT (λ n → reflR (f n))
reflR (G.lc () g)
reflR (G.em () a)
reflR G.top = tT (refl , tT tt)
```

## 2 到 `tw 2` 型的路径

`PR V`: 从 `V` 沿 Ω 结点层号的支走到 `Lw-tw 2` (塔的第 `2+n` 项沿第 1 支走 `n` 步, `lift`). 右边是 `wΩ` 时, 内层派发就是派发本身 (`IsWΩ`).

```agda
data IsWΩ : ∀ {K} → Lw K → Set where
  isΩ : ∀ {k g} {W : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} → IsWΩ (wΩ W w)

isΩ-up : ∀ {K} {V : Lw K} → IsWΩ V → (L : T.Legal K) → IsWΩ (Lw-Ω̂ K L V)
isΩ-up isΩ L = isΩ

isΩ-tw : ∀ n → IsWΩ (Lw-tw (suc (suc n)))
isΩ-tw zero = isΩ
isΩ-tw (suc n) = isΩ-up (isΩ-tw n) (T.Legal-tw (suc (suc n)))

data PR : ∀ {K} → Lw K → Set where
  pre : PR (Lw-tw 2)
  viaΩ : ∀ {k g} {W : ∀ η → Lgl k η → Lw (g η)} {w : Wit k g} η l → PR (W η l) → PR (wΩ W w)

ιP : ∀ {K} {V : Lw K} → PR V → Pre (tw 2) → Pre K
ιP pre r = r
ιP (viaΩ η l p) r = η , l , ιP p r

ιP-lev : ∀ {K} {V : Lw K} (p : PR V) r → lev K (ιP p r) ≡ lev (tw 2) r
ιP-lev pre r = refl
ιP-lev (viaΩ η l p) r = ιP-lev p r

η₁ : R
η₁ = G.suc G.zero

lift : ∀ {K} {V : Lw K} → PR V → (L : T.Legal K) → PR (Lw-Ω̂ K L V)
lift pre L = viaΩ η₁ tt pre
lift (viaΩ η l p) L = viaΩ η l (lift p (proj₁ (proj₂ L) η l))

pr-tw : ∀ n → PR (Lw-tw (suc (suc n)))
pr-tw zero = pre
pr-tw (suc n) = lift (pr-tw n) (T.Legal-tw (suc (suc n)))
```

## 3 `tw 2` 里层号 `ω+1`, `ω` 的位置

```agda
sucs : ℕ → R
sucs zero = G.zero
sucs (suc n) = G.suc (sucs n)

sucs-lgl : ∀ n → Lgl zero (sucs n)
sucs-lgl zero = tt
sucs-lgl (suc n) = sucs-lgl n

ωR : R
ωR = G.lim sucs

ωR-lgl : Lgl zero ωR
ωR-lgl = (λ n → inj₂ (inj₁ refl)) , sucs-lgl

ω2 : R
ω2 = G.suc (G.suc ωR)

Ωω : LF
Ωω = ⌜ ωR ⌝

p₁ p₀ : Pre (tw 2)
p₁ = ω2 , ωR-lgl , inj₁ tt
p₀ = ω2 , ωR-lgl , inj₂ (inj₁ tt)

dl-limΩ : ∀ {K} {V : Lw K} → IsWΩ V → ∀ r q → LimL (lev K q) → cmpw V r q ≡ fold
dl-limΩ {K} isΩ r q e = dl-lim (lev K r) K q e
```

## 4 否定

```agda
module _ (S : Compat dl) where
  open Compat S

  descend : ∀ {K} {V : Lw K} → PR V → ∀ {m} {x : Ext m K} {m′ K′} {V′ : Lw K′} {x′ : Ext m′ K′} →
    C V x V′ x′ → Σ (Ext m (tw 2)) λ y → C (Lw-tw 2) y V′ x′
  descend pre c = _ , c
  descend (viaΩ η l p) c = descend p (c-LΩ c η l)

  core : ∀ {m} {y : Ext m (tw 2)} {K′} {V′ : Lw K′} {m′} {x′ : Ext m′ K′} → IsWΩ V′ →
    (r′ q′ : Pre K′) → lev K′ r′ ≡ suc Ωω → lev K′ q′ ≡ Ωω → C (Lw-tw 2) y V′ x′ → ⊥
  core {K′ = K′} iw r′ q′ er eq c =
    noKF (dl-limΩ iw r′ q′ (_ , eq))
      (c-way (c-cmp (c-LΩ c ω2 ωR-lgl) (inj₁ tt) r′ (sym er)
                (ʰ→Q (suc Ωω) K′ r′ (trR (sym er) (reflR (G.suc ωR)))))
             (inj₂ (inj₁ tt)) q′ (sym eq) (ʰ→Q Ωω K′ q′ (trR (sym eq) (reflR ωR))))

  kill : ∀ {K} {V : Lw K} {K′} {V′ : Lw K′} → PR V → PR V′ → IsWΩ V′ →
    ∀ {m} {x : Ext m K} {m′} {x′ : Ext m′ K′} → C V x V′ x′ → ⊥
  kill p p′ iw c = core iw (ιP p′ p₁) (ιP p′ p₀) (ιP-lev p′ p₁) (ιP-lev p′ p₀) (proj₂ (descend p c))

  no-tw : ∀ n j {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ (tw (suc (suc j)))} →
    C (Lw-tw (suc (suc n))) x (Lw-tw (suc (suc j))) x′ → ⊥
  no-tw n j = kill (pr-tw n) (pr-tw j) (isΩ-tw j)

  no-Λ : ∀ n {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ Λ} → C (Lw-tw (suc (suc n))) x VΛ x′ → ⊥
  no-Λ n c = no-tw n 0 (c-Rl c 2)

  no-ΛΛ : ∀ {m m′} {x : Ext m Λ} {x′ : Ext m′ Λ} → C VΛ x VΛ x′ → ⊥
  no-ΛΛ c = no-tw 0 0 (c-Rl (c-Ll c 2) 2)
```

## 5 前提可满足; 相邻项 `(tw 2, tw 3)` 上的错位 (有限测试)

`S∅` 是空族, 只说明 `Compat dl` 有实例. 相邻项上右边的一对位置在 `tw 3` 的第 1 支里.

```agda
S∅ : Compat dl
Compat.C S∅ V x V′ x′ = ⊥
Compat.c-top S∅ ()
Compat.c-way S∅ ()
Compat.c-cmp S∅ ()
Compat.c-self S∅ ()
Compat.c-Ls S∅ ()
Compat.c-Ll S∅ ()
Compat.c-LΩ S∅ ()
Compat.c-Rs S∅ ()
Compat.c-Rl S∅ ()
Compat.c-RΩ S∅ ()
Compat.c-root S∅ ()
Compat.c-obs S∅ ()

r₃ q₃ : Pre (tw 3)
r₃ = η₁ , tt , p₁
q₃ = η₁ , tt , p₀

r₃-lev : lev (tw 3) r₃ ≡ suc Ωω
r₃-lev = refl

q₃-lev : lev (tw 3) q₃ ≡ Ωω
q₃-lev = refl

left-keep : cmpw (lgl→Lw zero tt w0 ω2 ωR-lgl) (inj₁ tt) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl
left-keep = refl

right-fold : cmpw (Lw-tw 3) r₃ q₃ ≡ fold
right-fold = refl

mis : WayR (cmpw (lgl→Lw zero tt w0 ω2 ωR-lgl) (inj₁ tt) (inj₂ (inj₁ tt))) (cmpw (Lw-tw 3) r₃ q₃) → ⊥
mis = noKF right-fold
```
