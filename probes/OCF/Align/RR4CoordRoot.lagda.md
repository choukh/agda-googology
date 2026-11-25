# RR4 实验 (四): 读回域上 `Reg` 的根条件由坐标自己给出; 第十轮的反例不在读回域里

> 第四次路线审查 (`probes/Survey/RR4-Fable52.md`) 的实验文件, 不进成品. 在**原** `LevelFixCore`/`LevelFixVal` 块上 (含退化坐标的那一块), 只导入 [YiDispBase](YiDispBase.lagda.md) 与 [YiRegZeroLimit](YiRegZeroLimit.lagda.md). 导入闭包不含记号. 不改任何已有文件.
>
> **要检验的问题.** 第十轮 `YiRegZeroLimit.no-omega-preservation` 否定了 "对一切合法且 `Reg` 的 $t$, $\hat\Omega\,t$ 仍 `Reg`". 反例 $x=\mathrm{suc}\,(\lim\,\mathrm{const}\,0)$ 失败在根条件: $x$ 不是 $\hat\Omega\,x$ 的字面子树. RouteReview3 §5.8 由此判断 "生成域避不开退化坐标". 问: 对**作为坐标读回出现**的层号 (规范 $\Omega_1$ 的合法守卫坐标 $\eta$ 的读回 `up 0 η`), 根条件是否成立?
>
> **结果.**
>
> 1. **`coordinate-root` (定理, 无前提).** 对一切合法守卫坐标 $\eta$ (含退化的, 如 $\lim\,\mathrm{const}\,1$): `Below (up 0 η) (Ω̂ (up 0 η))`. 证据就是坐标自己: `up 0 η` 字面地是 $\hat\Omega\,1$ 在 $\eta$ 处的分支, 而守卫把字面的 1 放在 `up 0 η` 的第一位置上, 于是 $\hat\Omega\,1$ 是 $\hat\Omega(\mathtt{up}\,0\,\eta)$ 的第一位置 (`Ω̂-CP`). 不比较, 不编码, 不用函数外延.
> 2. **`reg-root-suc` (推论).** $\eta=\mathrm{suc}\,\eta_1$ 时, 这正是 `Reg (Ω̂ (suc (up 0 η₁)))` 的第一个分量.
> 3. **`x-not-coordinate` (定理).** 第十轮的 $x$ 不是任何合法守卫坐标的读回. 所以那个反例在读回域之外.
> 4. **`junk-coordinate-root` (实例).** 退化坐标 $\mathrm{suc}\,(\lim\,\mathrm{const}\,1)$ 过守卫, 它的读回满足根条件.
>
> **读法 (判断).** 第十轮的否定对 "全合法域" 成立; 对 "读回域" 的根条件, 本文给出正面定理. 两者不矛盾: 全合法域里有不是读回的层号. 本文**没有**证读回域上完整的 `Reg` (还要对 `Ω̂ (suc x₁)` 的一切分支 `up x₁ η′` 递归, 那里有 `em` 嵌入的低层值, 未检验), 也只做了第 0 层坐标. 所以它只说明: 第十轮的反例不挡 "证据随坐标携带" 这个方向.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR4CoordRoot where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP; Legal)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase using (Edge; Below; one; more; e-suc; e-lim; e-first; e-branch)
open import OCF.Align.YiRegBase using (Reg)
import OCF.Align.YiRegZeroLimit as Z
```

## §1 根条件

```agda
edge-cp : ∀ {a b c} → Edge a b → CP b c → Below a c
edge-cp e V.self      = one e
edge-cp e (V.suc p)   = more (edge-cp e p) e-suc
edge-cp e (V.lim n p) = more (edge-cp e p) (e-lim n)
edge-cp e (V.fst p)   = more (edge-cp e p) e-first

Coord : Set
Coord = Σ (Raw F.zero) (λ η → Gd F.zero (V.cO F.zero) η)

read : Coord → LF
read p = V.up F.zero (proj₁ p)

Ω₁ᶠ : LF
Ω₁ᶠ = V.Ω̂ (F.suc F.zero)

branch-edge : ∀ (p : Coord) → Edge (read p) Ω₁ᶠ
branch-edge (η , e) = e-branch η e

spine : ∀ (p : Coord) → CP Ω₁ᶠ (V.Ω̂ (read p))
spine (η , e) = V.Ω̂-CP (V.cp→CP F.zero (proj₁ e))

coordinate-root : ∀ (p : Coord) → Below (read p) (V.Ω̂ (read p))
coordinate-root p = edge-cp (branch-edge p) (spine p)

reg-root-suc : ∀ η₁ (e : Gd F.zero (V.cO F.zero) (G.suc η₁)) →
  Below (F.suc (V.up F.zero η₁)) (V.Ω̂ (F.suc (V.up F.zero η₁)))
reg-root-suc η₁ e = coordinate-root (G.suc η₁ , e)
```

读回的合法性由旧定理给出, 这里只是把它与根条件并排.

```agda
read-legal : ∀ (p : Coord) → Legal (read p)
read-legal (η , e) = V.lgl→Legal F.zero tt η (proj₂ e)
```

## §2 退化坐标的实例

$\eta=\mathrm{suc}\,(\lim\,\mathrm{const}\,1)$: 相邻步是自反的 `Cp`, 原块里合法; 守卫经极限的第 0 项.

```agda
raw1 : Raw F.zero
raw1 = G.suc G.zero

junk : Raw F.zero
junk = G.suc (G.lim (λ _ → raw1))

junk-lgl : Lgl F.zero junk
junk-lgl = (λ _ → inj₁ refl) , (λ _ → tt)

junk-guard : Gd F.zero (V.cO F.zero) junk
junk-guard = inj₂ (inj₂ (0 , inj₁ refl)) , junk-lgl

junk-read : V.up F.zero junk ≡ F.suc (F.lim (λ _ → F.suc F.zero))
junk-read = refl

junk-coordinate-root : Below (V.up F.zero junk) (V.Ω̂ (V.up F.zero junk))
junk-coordinate-root = coordinate-root (junk , junk-guard)
```

## §3 第十轮的 $x$ 不是坐标的读回

`Z.x = suc (lim const 0)`. 若 `up 0 η ≡ x`, 则 $\eta=\mathrm{suc}\,(\lim f)$ 且各 $f\,n$ 读回为 0, 于是 $f\,n$ 就是 0; 守卫要求字面的 1 在某个 $f\,n$ 的第一位置上, 矛盾. 只逐项读极限, 不比较函数.

```agda
at : ℕ → LF → LF
at n F.zero         = F.zero
at n (F.suc t)      = F.zero
at n (F.lim f)      = f n
at n (F.lc k c t g) = F.zero

suc-inj : ∀ {a b : LF} → F.suc a ≡ F.suc b → a ≡ b
suc-inj refl = refl

read-zero : ∀ (a : Raw F.zero) → V.up F.zero a ≡ F.zero → a ≡ G.zero
read-zero G.zero         e = refl
read-zero (G.suc a)      ()
read-zero (G.lim f)      ()
read-zero (G.lc () c t g) e
read-zero (G.em () T)    e
read-zero G.top          ()

no-one-below-zero : ∀ {a : Raw F.zero} → a ≡ G.zero → Cp F.zero raw1 a → ⊥
no-one-below-zero refl (inj₁ ())
no-one-below-zero refl (inj₂ ())

lim-case : ∀ (f : ℕ → Raw F.zero) →
  F.lim (λ n → V.up F.zero (f n)) ≡ F.lim (λ _ → F.zero) →
  Cp F.zero raw1 (G.lim f) → ⊥
lim-case f eq (inj₁ ())
lim-case f eq (inj₂ (n , c)) = no-one-below-zero (read-zero (f n) (cong (at n) eq)) c

inner : ∀ (η₁ : Raw F.zero) → V.up F.zero η₁ ≡ Z.q → Cp F.zero raw1 η₁ → ⊥
inner G.zero          () c
inner (G.suc a)       () c
inner (G.lim f)       eq c = lim-case f eq c
inner (G.lc () c′ t g) eq c
inner (G.em () T)     eq c
inner G.top           () c

x-not-coordinate : ∀ (p : Coord) → read p ≡ Z.x → ⊥
x-not-coordinate (G.zero , e)          ()
x-not-coordinate (G.suc η₁ , (inj₁ refl , l)) ()
x-not-coordinate (G.suc η₁ , (inj₂ d , l)) eq = inner η₁ (suc-inj eq) d
x-not-coordinate (G.lim f , e)         ()
x-not-coordinate (G.lc () c t g , e)   eq
x-not-coordinate (G.em () T , e)       eq
x-not-coordinate (G.top , e)           ()
```

## §4 并排

```agda
-- 第十轮: x 合法且 Reg, Ω̂ x 不 Reg (旧定理, 原样引用)
round10 : Legal Z.x → Reg Z.x → (Reg (V.Ω̂ Z.x) → ⊥)
round10 _ _ = Z.no-reg-omega-x

-- 本文: x 不在读回域; 读回域上根条件成立
outside : ∀ (p : Coord) → read p ≡ Z.x → ⊥
outside = x-not-coordinate

inside : ∀ (p : Coord) → Below (read p) (V.Ω̂ (read p))
inside = coordinate-root
```

**范围.** 第 0 层坐标, 原块. 只有根条件; 完整的 `Reg (Ω̂ (read p))` 未证, 也未否定. 高层坐标 (`Raw k`, $k\ge1$) 的根条件未做: 那里守卫的下界是 `top`, 需要的第一位置是 $\hat\Omega\,k$ 而不是 $\mathrm{suc}\,k$, 论证不能照搬.
