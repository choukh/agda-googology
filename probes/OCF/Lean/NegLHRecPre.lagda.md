# 底对 LH 递归, 否定一路 (一): 接口之前 (分量的比较, 世界的一层, 对角到 $\Lambda$)

> 不含记号. 入口 [NegLHRec](NegLHRec.lagda.md). 本篇**不依赖**构造一路 LHRec 的接口 (接口定稿之前写的部分). 只导入 [CRwBase](CRwBase.lagda.md) 与否定一路旧文件 [NegRecBPre](NegRecBPre.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **问题** (作者本轮选定 "RecB → 底对 LH 递归"). 构造一路让层号 `lΩ k g` 的底以第 $k$ 层的值 $c$ 为分量下标, 世界的一层是 (第 $k$ 层的世界, 第 $k$ 层的界). 本篇对**任一**种类结构 `S` 陈述 (第 $k$ 层取 `step S`, 即 $k\geq1$ 的情形), 不用 `LH`:
>
> 1. **分量之间的比较必须带同一个第 $k$ 层世界里的公共上界 (§1).** **`no-wfree-cmp`**: 没有与世界无关的比较: 不存在对一切合法的第 $k$ 层值 $a,b$ 给出 "在一切合法世界里 $a\lhd b$" 或 "在一切合法世界里 $b\lhd a$" 的全函数. **`no-tri-v0`**: 在一个固定的合法世界 $(w,0)$ 里, 两个合法值 $1$ 与 $\Omega$ 互不为第一位置. **`sep-worlds`**: 两个分量下标各自在**自己的**合法世界里有同一个合法的界 $B$ 之下的证据 ($2\lhd B$ 在 $(w,2)$ 里, $\Omega+1\lhd B$ 在 $(w,0)$ 里), 它们在后一个世界里仍不可比. 所以证据必须在**同一个**世界里; 同一个合法世界里有公共合法上界时可比是 `CRwBase.cmpB` (正面).
> 2. **世界的一层 $(w, B)$ 的移动 (§2).** **`layer-up`** (正面, 对一切 `S`): 按 `step` 的世界序 (低层世界 $w\le w'$, 且 $B\lhd_{w'}B'$) 移动, 分量的证据 $c\lhd_w B$ 搬到 $c\lhd_{w'}B'$. **`layer-reset`** (否定): 界变大 ($B\boxplus 1$, 在一切世界里 $B\lhd B\boxplus1$), 低层世界却从 $(w,1)$ 缩到 $(w,0)$, 证据 $1\lhd B$ 丢失. **`old-world-strict`** (边界): 若把层的序写成 "$B\lhd_w B'$ 在**旧**低层世界里", 它严格强于 `step` 的世界序: $((\mathrm{tt},0),1)\le((\mathrm{tt},1),\Omega)$ 按 `step` 成立, 但 $1\lhd_{(\mathrm{tt},0)}\Omega$ 不成立. 这是 `wdep-low` 对 (界, 世界) 一层的版本.
> 3. **回灌要合法化 (§3).** **`bad-illegal`**, **`no-plain-fb`**: 对一切 `S` (第 $k$ 层 `step S`, 有一个世界): $\lim(1,0,0,\dots)$ 不合法, 不加合法化的回灌 $0\boxplus c$ 在它上面也不合法. **`ev→lg`**: 合法世界里合法界之下的分量下标都合法, 所以以不合法值为下标的分量没有证据 (**`no-ev-bad`**).
> 4. **对角到 $\Lambda$ (§4).** $\Lambda$ 层的种类结构是并 `sup ℕ F` (`LH` 里的 `Lv (ll tw)`). **`Λ-naive-illegal`** (对一切 `F`): 第 $n$ 项写在第 $n$ 个分量里、第 $0$ 项含 $\Omega$-结点的对角不合法 (`NegRecBPre.sup-diag-illegal` 的特例). **`copy-diag-illegal`**: 即使第 $n+1$ 项是第 $n$ 项沿嵌入搬上来的拷贝 (内容相同), 仍不合法 (实例: 阶梯 `step`$^{n+1}$ `S⊥`, 拷贝用 `up`). **`Λ-acc-legal`** (正面): 同样的项按部分和累加, 对角合法.
>
> **前提实例.** 1: $w$ 取 `S⊥` 的 `tt` (合法); 世界 $(w,0)$, $(w,1)$, $(w,2)$ 合法 (`lgv`). 2: `layer-reset` 的两层都合法 (`lg-L1`, `lg-L0`); `old-world-strict` 在 `S⊥` 上写出. 3: 世界任取 (例如 `S⊥` 的 `(tt, 0)`). 4: `copy-ex` 给出满足全部前提的实例.
>
> **只否定什么.** 1 只否定: 第 $k\geq1$ 层分量下标的比较与世界无关; 各自世界里的证据足以比较. **不否定**在同一合法世界里带公共上界的比较. 2 只否定: 移动时低层世界缩小; 以旧低层世界写层的序. **不否定** `step` 的世界序 (`layer-up` 是它的正面). 3 只否定不合法化的回灌 $0\boxplus c$; **不否定**回灌本身. 4 只否定各项写在各自分量里的对角; **不否定**累加的对角, 也不否定闭项 (`Cd`) 上的累加对角. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLHRecPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.NegRecBPre
  using (Ωˢ; Lg-Ωˢ; one; module Top; module BoundW; HasΩ; here; sup-diag-illegal; Σᴬ; Lg-Σᴬ; Lg-ι; Lg-up)
```

## §1 分量之间的比较: 必须在同一个世界里带公共上界

第 $k$ 层是 `step S` (对一切 `S`, 一个合法的低层世界 $w$). 分量下标是第 $k$ 层的值.

```agda
module Cmp {S : KS} (w : Wd S) (lw : LgW S w) where
  open Top {S} w using (in-top1; not-top0)
  open BoundW {S} w lw using (noΩ⊲1)

  v0 v1 v2 : Wd (step S)
  v0 = w , hz
  v1 = w , one {S}
  v2 = w , hs (hs hz)

  lgv : LgW (step S) v0 × LgW (step S) v1 × LgW (step S) v2
  lgv = (lw , tt) , (lw , tt) , (lw , tt)

  -- 固定的合法世界 (w,0) 里, 1 与 Ω 互不为第一位置
  no-tri-v0 : LgB (one {step S}) × LgB (Ωˢ {S}) × ¬ (one {step S} ⊲[ v0 ] Ωˢ {S}) × ¬ (Ωˢ {S} ⊲[ v0 ] one {step S})
  no-tri-v0 = tt , Lg-Ωˢ {S} , not-top0 , noΩ⊲1

  -- 各自世界里的证据: 2 ⊲ B 在 (w,2) 里, Ω+1 ⊲ B 在 (w,0) 里; B = Ω+2 合法
  Bsep : HB (step S)
  Bsep = hs (hs (Ωˢ {S}))

  sep-worlds :
    LgB Bsep ×
    (hs (one {step S}) ⊲[ v2 ] Bsep) × (hs (Ωˢ {S}) ⊲[ v0 ] Bsep) ×
    ¬ (one {step S} ⊲[ v0 ] Ωˢ {S}) × ¬ (Ωˢ {S} ⊲[ v0 ] one {step S})
  sep-worlds = Lg-Ωˢ {S} , hsuc (hsuc (hLim {c = hs (hs hz)} hself hself)) , hsuc hself , not-top0 , noΩ⊲1

no-wfree-cmp : ∀ {S : KS} (w : Wd S) → LgW S w →
  ¬ (∀ (a b : HB (step S)) → LgB a → LgB b →
       (∀ {v} → LgW (step S) v → a ⊲[ v ] b) ⊎ (∀ {v} → LgW (step S) v → b ⊲[ v ] a))
no-wfree-cmp {S} w lw all with all (one {step S}) (Ωˢ {S}) tt (Lg-Ωˢ {S})
... | inj₁ p = Top.not-top0 {S} w (p {w , hz} (lw , tt))
... | inj₂ q = BoundW.noΩ⊲1 {S} w lw (q {w , hz} (lw , tt))

-- 前提实例: S⊥ 的世界 tt 合法
no-wfree-cmp₁ : ¬ (∀ (a b : HB (step S⊥)) → LgB a → LgB b →
       (∀ {v} → LgW (step S⊥) v → a ⊲[ v ] b) ⊎ (∀ {v} → LgW (step S⊥) v → b ⊲[ v ] a))
no-wfree-cmp₁ = no-wfree-cmp {S⊥} tt tt
```

## §2 世界的一层 (低层世界, 界)

一层是 `Wd (step U)` $=$ (第 $k$ 层的世界 $u$, 第 $k$ 层的界 $B$), 分量 $c$ 的证据是 $c\lhd_u B$ (`step` 的新种类的 `Bd`).

```agda
-- 正面: 按 step 的世界序移动, 证据随之搬动 (对一切 U)
layer-up : ∀ {U : KS} {L L′ : Wd (step U)} {c : HB U} →
  _≤w_ (step U) L L′ → c ⊲[ proj₁ L ] proj₂ L → c ⊲[ proj₁ L′ ] proj₂ L′
layer-up {U} q e = Bd↑ (step U) {κ = inj₂ tt} q e

module Reset {S : KS} (w : Wd S) (lw : LgW S w) where
  open Top {S} w using (in-top1; not-top0)

  U : KS
  U = step S

  L1 L0 : Wd (step U)
  L1 = (w , one {S}) , Ωˢ {S}
  L0 = (w , hz) , (Ωˢ {S} ⊞ one {U})

  lg-L1 : LgW (step U) L1
  lg-L1 = (lw , tt) , Lg-Ωˢ {S}

  lg-L0 : LgW (step U) L0
  lg-L0 = (lw , tt) , Lg-⊞ (Ωˢ {S}) (one {U}) (Lg-Ωˢ {S}) tt

  grows : ∀ {v} → Ωˢ {S} ⊲[ v ] Ωˢ {S} ⊞ one {U}
  grows = ⊞-fst (Ωˢ {S}) (one {U})

  lost : ¬ (one {U} ⊲[ proj₁ L0 ] proj₂ L0)
  lost (hsuc p) = not-top0 p

layer-reset : ∀ {S : KS} (w : Wd S) (lw : LgW S w) →
  LgW (step (step S)) (Reset.L1 {S} w lw) × LgW (step (step S)) (Reset.L0 {S} w lw) ×
  (∀ {v} → proj₂ (Reset.L1 {S} w lw) ⊲[ v ] proj₂ (Reset.L0 {S} w lw)) ×
  (one {step S} ⊲[ proj₁ (Reset.L1 {S} w lw) ] proj₂ (Reset.L1 {S} w lw)) ×
  ¬ (one {step S} ⊲[ proj₁ (Reset.L0 {S} w lw) ] proj₂ (Reset.L0 {S} w lw))
layer-reset {S} w lw = lg-L1 , lg-L0 , (λ {v} → grows {v}) , Top.in-top1 {S} w , lost
  where open Reset {S} w lw

-- 边界: 以旧低层世界写层的序, 严格强于 step 的世界序 (在 S⊥ 上)
U₁ : KS
U₁ = step S⊥

Lo Lh : Wd (step U₁)
Lo = (tt , hz) , one {U₁}
Lh = (tt , one {S⊥}) , Ωˢ {S⊥}

old-world-strict : _≤w_ (step U₁) Lo Lh × ¬ (proj₂ Lo ⊲[ proj₁ Lo ] proj₂ Lh)
old-world-strict = ((tt , hsuc hself) , Top.in-top1 {S⊥} tt) , Top.not-top0 {S⊥} tt
```

## §3 回灌要合法化

```agda
module Fb {U : KS} (u : Wd U) where
  fb : ℕ → HB U
  fb zero = hs hz
  fb (suc n) = hz

  bad : HB U
  bad = hl fb

  no1⊲0 : ∀ {v : Wd U} → ¬ (hs {U} hz ⊲[ v ] hz)
  no1⊲0 ()

  bad-illegal : ¬ LgB {U} bad
  bad-illegal (st , _) = no1⊲0 {u} (st {u} 0)

  -- 不加合法化的回灌 0 ⊞ c
  no-plain-fb : ¬ LgB {U} (hz ⊞ bad)
  no-plain-fb (st , _) = no1⊲0 {u} (st {u} 0)

  ev→lg : ∀ {c B : HB U} {v} → LgW U v → LgB B → c ⊲[ v ] B → LgB c
  ev→lg lv lB p = lgB⊲ p lv lB

  no-ev-bad : ∀ {B : HB U} {v} → LgW U v → LgB B → ¬ (bad ⊲[ v ] B)
  no-ev-bad lv lB p = bad-illegal (ev→lg lv lB p)

-- 前提实例: 第 1 层的世界 (tt, 0)
no-plain-fb₁ : ¬ LgB (hz ⊞ Fb.bad {step S⊥} (tt , hz))
no-plain-fb₁ = Fb.no-plain-fb {step S⊥} (tt , hz)
```

## §4 对角到 $\Lambda$

```agda
module _ {F : ℕ → KS} where
  z≢1 : ¬ (0 ≡ 1)
  z≢1 ()

  Λ-naive-illegal : (x : ∀ n → HB (F n)) → Wd (sup ℕ F) → HasΩ (x 0) →
    ¬ LgB (hl (λ n → ι {ℕ} {F} n (x n)))
  Λ-naive-illegal x w h = sup-diag-illegal {ℕ} {F} (λ n → n) x w h z≢1

  Λ-acc-legal : (x : ∀ n → HB (F n)) → (∀ n → LgB (x n)) →
    LgB (hl (Σᴬ (λ n → ι {ℕ} {F} n (x n))))
  Λ-acc-legal x lx = Lg-Σᴬ (λ n → ι {ℕ} {F} n (x n)) (λ n → Lg-ι {ℕ} {F} n (x n) (lx n))
```

**拷贝也不行.** 阶梯 $F\,n=$ `step`$^{n+1}$ `S⊥` ($\Omega_{n+1}$ 这一层), 第 $0$ 项是 $\Omega_1$, 第 $n+1$ 项是第 $n$ 项经 `up` 的拷贝. 内容相同, 对角仍不合法; 累加合法.

```agda
Fst : ℕ → KS
Fst zero = step S⊥
Fst (suc n) = step (Fst n)

xc : (n : ℕ) → HB (Fst n)
xc zero = Ωˢ {S⊥}
xc (suc n) = up (xc n)

Lg-xc : ∀ n → LgB (xc n)
Lg-xc zero = Lg-Ωˢ {S⊥}
Lg-xc (suc n) = Lg-up (xc n) (Lg-xc n)

wst : (n : ℕ) → Wd (Fst n)
wst zero = tt , hz
wst (suc n) = wst n , hz

copy-diag-illegal : ¬ LgB (hl (λ n → ι {ℕ} {Fst} n (xc n)))
copy-diag-illegal = Λ-naive-illegal {Fst} xc wst here

copy-ex : (∀ n → LgB (xc n)) × LgB (hl (Σᴬ (λ n → ι {ℕ} {Fst} n (xc n))))
copy-ex = Lg-xc , Λ-acc-legal {Fst} xc Lg-xc
```

## 结论 (按档)

- **[定理, 正面]** `layer-up` (对一切 `U`); `Λ-acc-legal` (对一切 `F`), 实例 `copy-ex`; `ev→lg`.
- **[定理, 否定]** **`no-wfree-cmp`** (对一切 `S` 与合法 $w$; 实例 `no-wfree-cmp₁`), `Cmp.no-tri-v0`, **`Cmp.sep-worlds`**; **`layer-reset`**, **`old-world-strict`**; `Fb.bad-illegal`, **`Fb.no-plain-fb`** (实例 `no-plain-fb₁`), `Fb.no-ev-bad`; **`Λ-naive-illegal`**, **`copy-diag-illegal`**.
- **[判断]** (a) 构造一路的分量比较若写成 `cmpB` (同一合法世界, 同一合法界), 不撞 §1. (b) 层的序若取 `step (Lv k)` 的世界序, 不撞 §2. (c) 回灌若含对第 $k$ 层一切值的合法化, 不撞 §3; 第 $k\geq1$ 层的合法化要对旧种类的坐标累加, 坐标类型是更低层的值 (`Lv` 的递归), 对一般 `KS` 写不出 (未证). (d) $\Lambda$ 层的地板与闭项若用部分和 (同 `CRwFold.topT`, `RecB.zω`), 不撞 §4.
