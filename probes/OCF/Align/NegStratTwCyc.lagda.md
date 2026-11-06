# 分层互递归塔, 否定一路 (一): 草稿的互递归是不是真循环

> 不含记号. 入口 [NegStratTw](NegStratTw.lagda.md). 本篇**不依赖**构造一路的接口 [StratTwIf](StratTwIf.lagda.md) (接口定稿之前写的部分), 只用 [HtTowerTy](HtTowerTy.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> KindLv 的草稿 (`KindLvTw-IR-attempt`) 写
> `Cs (suc s) = step (Lev (Ys s))`, `Ys : (s : ℕ) → HB (sup ℕ Cs)`, `Ys zero = ι 0 (hs hz)`, `Ys (suc s) = hs (Ys s) ⊞ ι (suc s) (evN (Ys s))` (一个 `mutual` 块).
>
> 检查器报 `Cs` 停机失败. 主审与构造一路的接口文件头判断 "这是类型层的真循环, 分层能解开". 本篇把这句话拆成可以编译的部分:
>
> 1. **方程组本身不矛盾 (`solZ`, `solFin`, 定理).** 把草稿的两条递推写成命题等式的**规格** `TwEq` ($C_0\equiv S_0$, $C_{s+1}\equiv\mathrm{step}(\mathrm{Lev}\,Y_s)$, $Y_s:\mathrm{HB}(\mathrm{sup}\ \mathbb N\ C)$). 它有解: 级取常数 $0$ (`solZ`); 级取严格增长的有限数 (`solFin`, $Y_s=s+1$, 相邻项是字面第一位置). 所以检查器的拒绝说的是 "这样写的**定义**不被接受", 不是 "满足这对方程的族不存在".
> 2. **依赖只向下 (`strat`, 定理).** 规格之外再加草稿的递推形状 (`Draft`: $Y_0\equiv\mathrm{hs}\,0$, $Y_{s+1}\equiv\mathrm{hs}\,Y_s\boxplus\iota_{s+1}(z_s)$, 其中 $z_s:\mathrm{HB}(\mathrm{step}(\mathrm{Lev}\,Y_s))$ **任意**, 经规格的等式搬进 $C_{s+1}$). 对**任何**满足它的族, $Y_s$ 的一切 $\Omega$-结点的种类都在分量 $\le s$ (`KBn (suc s) (Y s)`). 所以 $\mathrm{Lev}\,Y_s$ 只读 $C_0,\dots,C_s$ 的种类; "$Y_s$ 的类型含 $K(C_{s+1})$" 这条循环只在类型里, 不在值的依赖里. 前提可满足 (`draftFin`, Ω-自由的实例).
> 3. **[判断] 对 "分层能解开" 的挑战.** 草稿卖点是 "对角的第 $s$ 项**就是**第 $s+1$ 个分量的级 (定义相等, 不是另一个类型里的拷贝)" (`KindLvIf` 文件头). 分层后级 $X_s$ 在前缀 $P_s$ 里, 对角的项 $Y_s$ 在总结构 $T$ 里, 两者只由 `Sim` 连起来 (`StratTwIf` 头: "`Lev (Y s)` 与 `Lev (X s)` 一般不相等"). 所以分层解开的是停机检查, 代价是把草稿要消掉的 "另一个类型里的拷贝" 又放回来; 本篇第 2 条说这个代价不是逻辑上逼出的 (依赖本来就只向下), 是 Agda 的定义形式 (类型 `HB (sup ℕ C)` 一次要整个族) 逼出的. 是否存在**不经拷贝**、检查器接受、且级的头带 $\Omega$-结点 (草稿的 $z_s=$ `evN` 形状) 的写法, 本篇没有结论 (未定; 归纳-递归的种类结构码是一种候选, 没试).
>
> **只否定什么.** 本篇没有否定定理; 它否定的是**推断** "停机检查失败, 所以这对方程无解 / 依赖是循环的". 不否定分层路线, 不否定草稿 (它作为定义被拒, 作为规格可满足).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegStratTwCyc where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.HtTowerTy
```

## §1 规格

```agda
record TwEq : Set₁ where
  field
    C  : ℕ → KS
    Y  : (s : ℕ) → HB (sup ℕ C)
    c0 : C zero ≡ S₀
    cS : ∀ s → C (suc s) ≡ step (Lev (Y s))
open TwEq public
```

## §2 规格有解

级取常数 $0$: `Lev hz = S₀` 不看种类结构.

```agda
CZ : ℕ → KS
CZ zero = S₀
CZ (suc s) = step S₀

solZ : TwEq
solZ = record { C = CZ ; Y = λ _ → hz ; c0 = refl ; cS = λ s → refl }
```

级取有限数 $s+1$: 有限数的 `Lev` 不看种类结构 (`Lev-fin`, 对 $n$ 归纳).

```agda
fin : ∀ {S} → ℕ → HB S
fin zero = hz
fin (suc n) = hs (fin n)

Lev-fin : ∀ {S S′ : KS} n → Lev {S} (fin n) ≡ Lev {S′} (fin n)
Lev-fin zero = refl
Lev-fin (suc n) = cong step (Lev-fin n)

CF : ℕ → KS
CF zero = S₀
CF (suc s) = step (Lev {S₀} (fin (suc s)))

solFin : TwEq
solFin = record
  { C = CF ; Y = λ s → fin {sup ℕ CF} (suc s) ; c0 = refl
  ; cS = λ s → cong step (Lev-fin {S₀} {sup ℕ CF} (suc s)) }

-- 相邻项是字面第一位置 (对一切世界)
solFin-fst : ∀ s {w} → hs (Y solFin s) ⊲[ w ] Y solFin (suc s)
solFin-fst s = hself
```

## §3 草稿的递推形状与 "依赖只向下"

`KBn F k x`: $x$ 的一切 $\Omega$-结点的种类在分量 $<k$ (同 `HtTowerStrat.KB`, 对一切族 $F$).

```agda
module _ {F : ℕ → KS} where
  KBn : ℕ → HB (sup ℕ F) → Set
  KBn k hz = ⊤
  KBn k (hs x) = KBn k x
  KBn k (hl f) = ∀ n → KBn k (f n)
  KBn k (hΩ κ g) = (proj₁ κ <ᴺ k) × (∀ c → KBn k (g c))

  <-tr : ∀ {i j k} → i <ᴺ j → j <ᴺ k → i <ᴺ k
  <-tr p zero = suc p
  <-tr p (suc q) = suc (<-tr p q)

  KBn↑ : ∀ {j k} → j <ᴺ k → ∀ x → KBn j x → KBn k x
  KBn↑ q hz h = tt
  KBn↑ q (hs x) h = KBn↑ q x h
  KBn↑ q (hl f) h = λ n → KBn↑ q (f n) (h n)
  KBn↑ q (hΩ κ g) (p , h) = <-tr p q , (λ c → KBn↑ q (g c) (h c))

  KBn-ι : ∀ {j k} → j <ᴺ k → ∀ x → KBn k (ι {ℕ} {F} j x)
  KBn-ι q hz = tt
  KBn-ι q (hs x) = KBn-ι q x
  KBn-ι q (hl f) = λ n → KBn-ι q (f n)
  KBn-ι q (hΩ κ g) = q , (λ c → KBn-ι q (g c))

  KBn-⊞ : ∀ {k} a b → KBn k a → KBn k b → KBn k (a ⊞ b)
  KBn-⊞ a hz ha hb = ha
  KBn-⊞ a (hs b) ha hb = KBn-⊞ a b ha hb
  KBn-⊞ a (hl f) ha hb = λ n → KBn-⊞ a (f n) ha (hb n)
  KBn-⊞ a (hΩ κ g) ha (p , hb) = p , (λ c → KBn-⊞ a (g c) ha (hb c))
```

草稿的形状: $z_s$ 任意 (草稿里是 `evN (Ys s)`), 经 `cS` 搬进 $C_{s+1}$.

```agda
tr : (E : TwEq) (s : ℕ) → HB (step (Lev (Y E s))) → HB (C E (suc s))
tr E s = subst HB (sym (cS E s))

record Draft (E : TwEq) : Set where
  field
    z  : (s : ℕ) → HB (step (Lev (Y E s)))
    y0 : Y E zero ≡ ι {ℕ} {C E} zero (hs hz)
    yS : ∀ s → Y E (suc s) ≡ hs (Y E s) ⊞ ι {ℕ} {C E} (suc s) (tr E s (z s))
open Draft public

strat : (E : TwEq) → Draft E → ∀ s → KBn {C E} (suc s) (Y E s)
strat E D zero = subst (KBn (suc zero)) (sym (y0 D)) tt
strat E D (suc s) =
  subst (KBn (suc (suc s))) (sym (yS D s))
    (KBn-⊞ (hs (Y E s)) (ι (suc s) (tr E s (z D s)))
      (KBn↑ zero (Y E s) (strat E D s)) (KBn-ι zero (tr E s (z D s))))
```

前提可满足: `solFin` 是草稿形状的 ($z_s=0$; 搬运把 $0$ 送到 $0$, `subst-hz`).

```agda
subst-hz : ∀ {S S′ : KS} (e : S ≡ S′) → subst HB e hz ≡ hz
subst-hz refl = refl

draftFin : Draft solFin
draftFin = record
  { z = λ s → hz
  ; y0 = refl
  ; yS = λ s → cong (λ t → hs (Y solFin s) ⊞ ι {ℕ} {CF} (suc s) t) (sym (subst-hz (sym (cS solFin s)))) }
```

## §4 结论 (按档)

- **[定理]** `solZ`, `solFin`, `solFin-fst` (规格可满足, 级可严格增长); **`strat`** (草稿形状的任何解, $Y_s$ 只用分量 $\le s$ 的种类); `draftFin` (前提实例).
- **[判断]** 停机失败是定义形式的循环 (类型 `HB (sup ℕ C)` 要整个族), 不是值的循环 (`strat`). 分层 (`StratTwIf`) 用 "前缀里的级 $X_s$ + 总结构里的同形项 $Y_s$ + `Sim`" 换掉草稿的 "对角的项就是级"; 这是在停机与 "级不是拷贝" 之间二选一, 本篇不说只能二选一 (未定).
- **[未定]** 草稿形状里 $z_s$ 带 $\Omega$-结点 (如 `evN`) 时, 不经拷贝的解是否可写.
