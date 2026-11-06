# 按级回灌, 否定一路 (二): 坐标是高度的种类上, "升一份留别份" 仍是分离子

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 本篇**不依赖**构造一路的接口 `KindLvIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在三条条件定理 (`…→WLPO`) 里作前提.
>
> 已有的分离子 (`NegGenFoldUpd.upd₁-sep`, `updT-sep`, `NegNewTwrFeed.updΛ⁺-sep`) 都落在**底种类的拷贝**上 (坐标 `A`). "每个种类按自己的级回灌" 要升的是**坐标是高度的种类** (级 $y$, 坐标 `HB (Lev y)`) 的界. 问: 换成这些种类, 分离子还在不在? 本篇回答: 在, 而且前提可以更弱 (只要求升到一个**固定的**高度 $1$, 不要求升到任意给定的 $v$).
>
> - **`K₁ = Kc 1`** (第 1 站): 种类 `κH f = (inj₂ (hs (jx f)) , inj₂ tt)` 是分量 `hs (jx f)` 的新种类, 级 `jx f`, 坐标 `HB (Lev (jx f))` (类型随 $f$ 变). **`updH₁-sep`**.
> - **`T₀ = Lev X₀`** (第 1 站下降的层所在的级; 一个以高度为下标的 `Lev c` 的世界): 种类 `κhT f = (jx f , (0 , inj₂ tt))`, 坐标 `H₀`. **`updHT-sep`**.
> - **`step KΛc`** (最终坍缩的层所在的种类结构): 种类 `inj₁ (1 , κH f)`. **`updHΛ⁺-sep`**.
>
> 证明同 `upd₁-sep`: 基世界里这些种类的界都是 $0$; 把 `κH f` 的界升到 $1$ 以上, 看 `κH f′` 的界是不是 $0$ (`HB` 的构造子, 可判定). 是 $0$: 两下标不等 (由 "升"); 不是 $0$: 两下标不能不等 (由 "留", 界不是 $0$ 的高度不在 $0$ 之下).
>
> **两半各自可满足** (`upOne₁`/`stay₁`, `upOneT`/`stayT`, `upOneΛ`/`stayΛ`): 只升: 每个形如 `hs y` 的分量的新种类的界都换成 $1\boxplus$ 旧界 (按分量的构造子匹配, 不判定下标相等); 只留: 世界不动. **下标可判定时两半同时成立** (`upd-step`): `step S` 里升新种类, 留一切旧种类, 是配对. 所以墙来自**下标不可判定** (并的分量以高度为下标), 不来自 "坐标是高度".
>
> **只否定什么.** 只否定: 在 `K₁`, `T₀`, `step KΛc` 的世界上, 对一切世界与一切 $f$ 一致的操作, 同时把 `κH f` (或 `κhT f`) 的界升到 $1$ 以上 ("升") 并不升任何下标不同的拷贝 `κH f′` 的界 ("留"). 含 "升到任意 $v$" 的版本 (`PtUpdHv₁`) 是推论 (`full→H₁`). **不否定**: 只升不留 (`upOne₁`, 它把别的分量也升了, `upOne₁-moves`); 可判定下标上的点更新 (`upd-step`, `GenFoldInst.upd`); 有损回灌; "一起升" 到任意 $v$ (类型随级变, 见下面的判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvUpd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.LvKtIf using (Kc; KΛc; FN; injL)
open import OCF.Align.GenFoldIf using (K₁)
open import OCF.Align.NegDnFoldCopy using (X₀; T₀)
open import OCF.Align.NegGenFoldUpd using (jx; jx-inj; Sep; WDec; wdec→sep; sep→WLPO; z₁; zT; Fc)
open import OCF.Align.NegNewTwrFeed using (ext₁)
open import OCF.Align.NegKindLvLev using (lvK)
```

## §0 工具: 不是 $0$ 的高度不在 $0$ 之下

```agda
notz : ∀ {S : KS} {w} {x : HB S} → (x ≡ hz → ⊥) → ¬ (x ⊲[ w ] hz)
notz nz hself = nz refl

one⊀z : ∀ {S : KS} {w} → ¬ (hs {S} hz ⊲[ w ] hz)
one⊀z = notz (λ ())
```

## §1 `K₁`: 分量 `hs (jx f)` 的新种类

```agda
κH : (ℕ → H₀) → K K₁
κH f = inj₂ (hs (jx f)) , inj₂ tt

-- 它的坐标是高度, 级是 jx f
E-κH : ∀ f → E K₁ (κH f) ≡ HB (Lev (jx f))
E-κH f = refl

lv-κH : ∀ f → lvK (hs (jx f)) (inj₂ tt) ≡ inj₂ (jx f)
lv-κH f = refl

-- 升到任意 v (按级回灌要的形状)
record PtUpdHv₁ : Set where
  field
    updV   : Wd K₁ → (f : ℕ → H₀) → HB (Lev (jx f)) → Wd K₁
    raiseV : ∀ w f v → Bd K₁ (κH f) v (updV w f v)
    keepV  : ∀ w f v f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd K₁ (κH f′) c (updV w f v) → Bd K₁ (κH f′) c w

-- 更弱: 只升到固定的 1
record PtUpdH₁ : Set where
  field
    updH   : Wd K₁ → (ℕ → H₀) → Wd K₁
    raiseH : ∀ w f → Bd K₁ (κH f) (hs hz) (updH w f)
    keepH  : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd K₁ (κH f′) c (updH w f) → Bd K₁ (κH f′) c w

full→H₁ : PtUpdHv₁ → PtUpdH₁
full→H₁ P = record
  { updH = λ w f → updV w f (hs hz)
  ; raiseH = λ w f → raiseV w f (hs hz)
  ; keepH = λ w f f′ ne b → keepV w f (hs hz) f′ ne b }
  where open PtUpdHv₁ P

wdecH₁ : PtUpdH₁ → WDec
wdecH₁ P f f′ = go (proj₂ (W (inj₂ (hs (jx f′))))) refl
  where
  open PtUpdH₁ P
  W : Wd K₁
  W = updH z₁ f
  r1 : Bd K₁ (κH f) (hs hz) W
  r1 = raiseH z₁ f
  go : ∀ v → proj₂ (W (inj₂ (hs (jx f′)))) ≡ v → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go hz eq = inj₁ (λ e → one⊀z (subst (λ b → hs hz ⊲[ proj₁ (W (inj₂ (hs (jx f′)))) ] b) eq (h e)))
    where
    h : jx f′ ≡ jx f → Bd K₁ (κH f′) (hs hz) W
    h e = subst (λ g → Bd K₁ (κH g) (hs hz) W) (sym (jx-inj e)) r1
  go (hs v) eq = inj₂ (λ ne → notz (λ ()) (keepH z₁ f f′ ne (subst (λ b → hs v ⊲[ proj₁ (W (inj₂ (hs (jx f′)))) ] b) (sym eq) hself)))
  go (hl g) eq = inj₂ (λ ne → notz (λ ()) (keepH z₁ f f′ ne (subst (λ b → hl g ⊲[ proj₁ (W (inj₂ (hs (jx f′)))) ] b) (sym eq) hself)))
  go (hΩ κ g) eq = inj₂ (λ ne → notz (λ ()) (keepH z₁ f f′ ne (subst (λ b → hΩ κ g ⊲[ proj₁ (W (inj₂ (hs (jx f′)))) ] b) (sym eq) hself)))

updH₁-sep : PtUpdH₁ → Sep
updH₁-sep P = wdec→sep (wdecH₁ P)

updHv₁-sep : PtUpdHv₁ → Sep
updHv₁-sep P = updH₁-sep (full→H₁ P)

updH₁→WLPO : FE₀ → PtUpdH₁ → WLPO
updH₁→WLPO fe P = sep→WLPO fe (updH₁-sep P)
```

**两半各自可满足.** 只升: 按分量的构造子匹配, 每个形如 `hs y` 的分量的新种类的界换成 $1\boxplus$ 旧界 (`⊞-fst`). 只留: 世界不动.

```agda
upS : ∀ {S : KS} → Wd (step S) → Wd (step S)
upS w = proj₁ w , hs hz ⊞ proj₂ w

upOne₁ : Wd K₁ → (ℕ → H₀) → Wd K₁
upOne₁ w f (inj₁ tt) = w (inj₁ tt)
upOne₁ w f (inj₂ hz) = w (inj₂ hz)
upOne₁ w f (inj₂ (hs y)) = upS {Lev y} (w (inj₂ (hs y)))
upOne₁ w f (inj₂ (hl g)) = w (inj₂ (hl g))
upOne₁ w f (inj₂ (hΩ κ g)) = w (inj₂ (hΩ κ g))

half₁R : ∀ w f → Bd K₁ (κH f) (hs hz) (upOne₁ w f)
half₁R w f = ⊞-fst (hs hz) (proj₂ (w (inj₂ (hs (jx f)))))

stay₁ : Wd K₁ → (ℕ → H₀) → Wd K₁
stay₁ w f = w

half₁K : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd K₁ (κH f′) c (stay₁ w f) → Bd K₁ (κH f′) c w
half₁K w f f′ ne b = b

-- 只升的那一半把别的拷贝也升了
upOne₁-moves : ∀ w f f′ → Bd K₁ (κH f′) (hs hz) (upOne₁ w f)
upOne₁-moves w f f′ = ⊞-fst (hs hz) (proj₂ (w (inj₂ (hs (jx f′)))))
```

## §2 `T₀ = Lev X₀`: 分量 `jx f` 的第 0 个子分量 `step S₀` 的新种类 (坐标 `H₀`)

```agda
κhT : (ℕ → H₀) → K T₀
κhT f = jx f , (0 , inj₂ tt)

E-κhT : ∀ f → E T₀ (κhT f) ≡ H₀
E-κhT f = refl

record PtUpdHT : Set where
  field
    updH   : Wd T₀ → (ℕ → H₀) → Wd T₀
    raiseH : ∀ w f → Bd T₀ (κhT f) (hs hz) (updH w f)
    keepH  : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd T₀ (κhT f′) c (updH w f) → Bd T₀ (κhT f′) c w

wdecHT : PtUpdHT → WDec
wdecHT P f f′ = go (proj₂ (W (jx f′) 0)) refl
  where
  open PtUpdHT P
  W : Wd T₀
  W = updH zT f
  r1 : Bd T₀ (κhT f) (hs hz) W
  r1 = raiseH zT f
  go : ∀ v → proj₂ (W (jx f′) 0) ≡ v → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go hz eq = inj₁ (λ e → one⊀z (subst (λ b → hs hz ⊲[ proj₁ (W (jx f′) 0) ] b) eq (h e)))
    where
    h : jx f′ ≡ jx f → Bd T₀ (κhT f′) (hs hz) W
    h e = subst (λ g → Bd T₀ (κhT g) (hs hz) W) (sym (jx-inj e)) r1
  go (hs v) eq = inj₂ (λ ne → notz (λ ()) (keepH zT f f′ ne (subst (λ b → hs v ⊲[ proj₁ (W (jx f′) 0) ] b) (sym eq) hself)))
  go (hl g) eq = inj₂ (λ ne → notz (λ ()) (keepH zT f f′ ne (subst (λ b → hl g ⊲[ proj₁ (W (jx f′) 0) ] b) (sym eq) hself)))
  go (hΩ κ g) eq = inj₂ (λ ne → notz (λ ()) (keepH zT f f′ ne (subst (λ b → hΩ κ g ⊲[ proj₁ (W (jx f′) 0) ] b) (sym eq) hself)))

updHT-sep : PtUpdHT → Sep
updHT-sep P = wdec→sep (wdecHT P)

updHT→WLPO : FE₀ → PtUpdHT → WLPO
updHT→WLPO fe P = sep→WLPO fe (updHT-sep P)
```

**两半各自可满足.** 只升: 下标是 ℕ-极限 `hl g` 的分量, 若 `g 0` 是 $0$ (按构造子匹配), 第 0 个子分量是 `step S₀`, 把它的新种类的界换成 $1\boxplus$ 旧界.

```agda
raise0 : ∀ (y₀ : H₀) → Wd (Lev (hs hz ⊞ injL {S₀} (hs hz) (up {S₀} y₀))) → Wd (Lev (hs hz ⊞ injL {S₀} (hs hz) (up {S₀} y₀)))
raise0 hz w = upS {S₀} w
raise0 (hs y) w = w
raise0 (hl g) w = w
raise0 (hΩ κ g) w = w

upOneT : Wd T₀ → (ℕ → H₀) → Wd T₀
upOneT w f hz = w hz
upOneT w f (hs y) = w (hs y)
upOneT w f (hl g) zero = raise0 (g 0) (w (hl g) zero)
upOneT w f (hl g) (suc n) = w (hl g) (suc n)
upOneT w f (hΩ κ g) = w (hΩ κ g)

halfTR : ∀ w f → Bd T₀ (κhT f) (hs hz) (upOneT w f)
halfTR w f = ⊞-fst (hs hz) (proj₂ (w (jx f) 0))

stayT : Wd T₀ → (ℕ → H₀) → Wd T₀
stayT w f = w

halfTK : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd T₀ (κhT f′) c (stayT w f) → Bd T₀ (κhT f′) c w
halfTK w f f′ ne b = b
```

## §3 `step KΛc`: 最终坍缩的层所在的种类结构

`step KΛc` 的旧种类 `inj₁ (1 , κH f)` 就是第 1 站的 `κH f`. 证明只在一个世界 `(ext₁ w , hz)` 上用到点更新 (同 `NegNewTwrFeed.toBΛ`).

```agda
κHΛ : (ℕ → H₀) → K (step KΛc)
κHΛ f = inj₁ (1 , κH f)

record PtUpdHΛ⁺ : Set where
  field
    updH   : Wd (step KΛc) → (ℕ → H₀) → Wd (step KΛc)
    raiseH : ∀ w f → Bd (step KΛc) (κHΛ f) (hs hz) (updH w f)
    keepH  : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd (step KΛc) (κHΛ f′) c (updH w f) → Bd (step KΛc) (κHΛ f′) c w

toH₁ : PtUpdHΛ⁺ → PtUpdH₁
toH₁ P = record
  { updH = λ w f → proj₁ (updH (ext₁ w , hz) f) 1
  ; raiseH = λ w f → raiseH (ext₁ w , hz) f
  ; keepH = λ w f f′ ne b → keepH (ext₁ w , hz) f f′ ne b }
  where open PtUpdHΛ⁺ P

updHΛ⁺-sep : PtUpdHΛ⁺ → Sep
updHΛ⁺-sep P = updH₁-sep (toH₁ P)

updHΛ⁺→WLPO : FE₀ → PtUpdHΛ⁺ → WLPO
updHΛ⁺→WLPO fe P = sep→WLPO fe (updHΛ⁺-sep P)

-- 两半各自可满足
upOneΛ : Wd (step KΛc) → (ℕ → H₀) → Wd (step KΛc)
upOneΛ w f = (λ { zero → proj₁ w 0 ; (suc zero) → upOne₁ (proj₁ w 1) f ; (suc (suc s)) → proj₁ w (suc (suc s)) }) , proj₂ w

halfΛR : ∀ w f → Bd (step KΛc) (κHΛ f) (hs hz) (upOneΛ w f)
halfΛR w f = half₁R (proj₁ w 1) f

stayΛ : Wd (step KΛc) → (ℕ → H₀) → Wd (step KΛc)
stayΛ w f = w

halfΛK : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd (step KΛc) (κHΛ f′) c (stayΛ w f) → Bd (step KΛc) (κHΛ f′) c w
halfΛK w f f′ ne b = b
```

## §4 对照: 下标可判定时, 坐标是高度的种类上点更新是构造

`step S` 的新种类 (坐标 `HB S`) 与旧种类是配对的两个分量: 升新种类, 一切旧种类不动.

```agda
upd-step : ∀ {S : KS} → Wd (step S) → HB S → Wd (step S)
upd-step w v = proj₁ w , v

raise-step : ∀ {S : KS} (w : Wd (step S)) v → Bd (step S) (inj₂ tt) v (upd-step w v)
raise-step w v = hself

keep-step : ∀ {S : KS} (w : Wd (step S)) v (κ : K S) {c} → Bd (step S) (inj₁ κ) c (upd-step w v) → Bd (step S) (inj₁ κ) c w
keep-step w v κ b = b
```

## §5 结论 (按档)

- **[定理, 否定]** **`updH₁-sep`** (`K₁`), **`updHv₁-sep`**, **`updHT-sep`** (`T₀ = Lev X₀`), **`updHΛ⁺-sep`** (`step KΛc`): 对坐标是高度的种类, "升到 $1$ 以上 + 留别的拷贝" ⇒ 分离子. **[条件 `FE₀`]** `updH₁→WLPO`, `updHT→WLPO`, `updHΛ⁺→WLPO`.
- **[定理, 前提实例]** `half₁R`/`half₁K`, `halfTR`/`halfTK`, `halfΛR`/`halfΛK` (两半各自可满足); `upOne₁-moves`; `upd-step`, `raise-step`, `keep-step` (下标可判定处两半同时成立). 分离子 `Sep` 经典地成立 (判断); `FE₀` 在 Agda 里证不出也否证不了 (同 `NegGenFoldUpd`).
- **[判断]** "一起升" 对坐标是高度的种类比对底拷贝难: 底拷贝的坐标都是 `A`, 新界 $v$ 一个值就能放进每个分量 (`NegGenFoldUpd.rB`); 坐标是高度的种类的坐标类型随级变 (`E-κH`: `HB (Lev (jx f))`), 要把 $v$ 放进下标不同的分量, 要么判定两个级相等 (撞本篇), 要么有一个从 `HB (Lev y)` 到 `HB (Lev y′)` 的逐结构搬运, 它在 $y\equiv y'$ 时把 $v$ 放在新界的字面第一位置上; 后者对 $\Omega$-结点要函数外延才能证 (未写, 未否定). `upOne₁` 只对固定的 $1$ 做到了 "一起升".
