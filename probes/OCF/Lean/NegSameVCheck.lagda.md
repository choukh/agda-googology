# NegSameV (七): 对构造一路定理的检查: `_≼X_` 与 `self≰copy`, `floor-block` 对得上; 地板律不是白给的; 不自反

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 对构造一路 SameV 已交的文件 (`SameVRel`, `SameVLeg`, `SameVMono`, `SameVX`, `SameVGoal`; 只导入, 不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 模块参数 `uipC` 是 `Cd` 上的 UIP (条件, 只因导入的模块带它).
>
> **定理.**
>
> 1. **`self-no` (对一切配对).** $\Omega_1$ 本身不能比到拷贝: $\neg(X_n\preceq_X Y_n)$. 原因是字段 `Wl` (新世界的值单调) 在世界 $0$ 处失败. 所以 `crossX` 不撞 `NegValXSelf.self≰copy`.
> 2. **`copy-ok` (配对含 $0\sim0$).** 反方向 $Y_n\preceq_X X_n$ 成立, 与 `copy≤self` 一致. 所以 `_≼X_` 真的跨分量 (分量 $1$ 比到分量 $0$).
> 3. **`not-reflect`.** `_≼X_` (取 `floor-block` 那一对的配对) 不层反射: `¬ LvRefl _≼X_`. 由构造一路的 `gtP` 与本路的 `not⊲′`. 这说明 `gtP` 与 `floor-block` 没有矛盾的唯一出路正是 "不层反射".
> 4. **`Mw`, `tp-not-free`.** 配对的记录 `Match` 不含值: 有配对 $\omega_1\sim1$ (`Mw`), 而 $\omega_1\not\le1$ (`w-not-le`), 这对层的地板不相关 (`tp-not-free`). 所以 `crossΦ`, `crossX` 的前提 `tp` 不是配对的推论, 值的内容全在 `tp` 与 `gtP` 上.
> 5. **`LE-not-refl` (配对含 $0\sim0$ 或任意).** 跨层关系不自反: 分支不单调的结点 $x$ 上 $\neg(x\preceq x)$. 这是逻辑关系的代价, 与自反律的矛盾只在非值合法的输入上; 构造一路只把关系用在右边值合法的地方, 不要自反.
>
>
> **对构造一路的四个问题.** (1) 严格档: [NegSameVStrict](NegSameVStrict.lagda.md). (2) `Wl` 不是空的: `self-no` 用它排除本身配拷贝, `copy-ok` 给出它成立的跨分量实例. (3) 隐含依赖: 读 `SameVRel`, `SameVMono`, `SameVX`, `SameVGoal` (判断): 模块参数只有 `uipC`, `ShLaw` (实例是定理 `shLaw₁`), `Match`, `tp` (实例是定理 `Core.tp`); 左边的界不要值合法也不要在地板之上, 这是对的: 左边只在 `chX` 里被右边的界拉住. (4) `TU-mono` 的卡点: 本篇 §5.
>
> **前提实例.** 1: 一切 `Mt`. 2: `Mt` 含 $0\sim0$; 例如 `Mw` (`copy-Mw`). 3: `le₁₂`. 4, 5: 实例就是定理. `uipC`: 函数外延推出 (条件 Funext).
>
> **只否定什么.** 1 只否定本身比到拷贝. 4 只否定 "`Match` 的律推出地板律". 5 只否定自反. `tu-block` 只否定以 `inU₁` 为 `crossX` 的右边, 不否定 `TU-mono`. **都不否定** `P2-thm`, `goal`, `crossX`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.NegSameVCheck (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; leg)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁ using (noPP)
open import OCF.Lean.ValXRel I₁ using (HX; lvX; toX; ShLaw; MoX)
open import OCF.Lean.ValXTm using (shLaw₁)
open import OCF.Lean.ValXBase I₁ shLaw₁ using (nW)
open import OCF.Lean.ValXObs I₁ using (LvRefl; has-inv; Inv-gt; le₁₂)
open import OCF.Lean.SameVRel I₁ using (Match; module X)
open import OCF.Lean.SameVLeg using (module M)
import OCF.Lean.SameVX as SX
open import OCF.Lean.SameVGoal uipC using (module Core)
open import OCF.Lean.NegValXSelf using (Xn; Yn; g; Big; g-cases; g-up; κΩ; κc)
open import OCF.Lean.NegValXInst using (c₁′; c₂′; not⊲′; ¬MoX-inU₁)
open import OCF.Lean.NegSameVSpine using (ω₁)
open import OCF.Lean.NegSameVMor using (M₁₂)
open import OCF.Lean.SameV using (lv→match)
open import OCF.Lean.ValXIf I₁ using (inU₁)
import OCF.Lean.ValXP1 uipC as P1m
import OCF.Lean.SameVIf as IF
import OCF.Lean.SameVGoal uipC as G
open ShLaw shLaw₁
```

## §1 本身与拷贝

```agda
module Sc (Mt : Match) where
  open SX I₁ uipC shLaw₁ Mt
  open X Mt using (module R2; LE; _~_)

  noΩ-z : ∀ {κ h} → ¬ (hΩ κ h ≼X hz)
  noΩ-z ()

  noΩ-1 : ∀ {κ h} → ¬ (hΩ κ h ≼X hs hz)
  noΩ-1 (≼s p) = noΩ-z p

  noΩ-2 : ∀ {κ h} → ¬ (hΩ κ h ≼X Big)
  noΩ-2 (≼s p) = noΩ-1 p

  noΩ-g : ∀ {κ h} c → ¬ (hΩ κ h ≼X g c)
  noΩ-g {κ} {h} c p with g-cases c
  ... | inj₁ e = noΩ-z (subst (λ z → hΩ κ h ≼X z) e p)
  ... | inj₂ e = noΩ-2 (subst (λ z → hΩ κ h ≼X z) e p)

  self-no : ¬ (Xn ≼X Yn)
  self-no (≼Ω c bd mc p) = noΩ-g c (p hz)
  self-no (Ω≼Ω e wl h) with wl {hz} {hz} tt tt Rel.z≤ {hz} {hz} R2.z≼
  ... | ()

  le← : ∀ {x y} → LE hz hz x y → LeAt hz x y
  le← R2.z≼ = Rel.z≤
  le← (R2.s≼s p) = Rel.s≤s (le← p)
  le← (R2.≼s p) = Rel.≤s (le← p)
  le← (R2.l≼l σ i h) = Rel.l≤l σ i (λ n → le← (h n))
  le← (R2.≼l n p) = Rel.≤l n (le← p)
  le← (R2.≼Ω {κ′ = ()} _ _ _ _)
  le← (R2.Ω≼Ω {κ′ = ()} _ _)

  gLe : ∀ {c c′} → LeAt hz c c′ → g c ≼X g c′
  gLe {c} {c′} p with g-cases c
  ... | inj₁ e = subst (λ z → z ≼X g c′) (sym e) z≼
  ... | inj₂ e = subst₂ _≼X_ (sym e) (sym (g-up p e)) (s≼s (s≼s z≼))

  copy-ok : hz ~ hz → Yn ≼X Xn
  copy-ok ez = Ω≼Ω ez
    (λ {B₁} {B₂} l₁ l₂ w {d} {d′} r → Rel.≤s (L.≤-trans hz w (L.≤⊞ hz B₂ (leg d′))))
    (λ d d′ md r B₁ B₂ w → gLe (L.≤-trans hz (le← r) (shI d′)))
```

## §2 `floor-block` 那一对: 不层反射

```agda
ple : LeAt hz (hs (hl (λ n → _))) _
ple = le₁₂

not-reflect : LvRefl (SX._≼X_ I₁ uipC shLaw₁ (M.match ple)) → ⊥
not-reflect rf = not⊲′ (has-inv (rf (Core.gtP ple)) (Inv-gt (hs c₂′) hself))
```

## §3 配对不含值

```agda
-- ω₁ 写成方程: 否则模式匹配要消去 nat = nat
data Wp : Cd → Cd → Set where
  w0 : Wp hz hz
  w1 : ∀ {a} → a ≡ ω₁ → Wp a (hs hz)

Mw : Match
Mw = record { _~_ = Wp ; ~fun = fun ; ~s = ss ; ~pp = pp }
  where
  fun : ∀ {a b b′} → Wp a b → Wp a b′ → b ≡ b′
  fun w0 w0 = refl
  fun (w1 _) (w1 _) = refl
  fun w0 (w1 ())
  fun (w1 ()) w0
  ss : ∀ {j j′ u u′} → Wp j j′ → Wp u u′ → hs j ⊲ u → hs j′ ⊲ u′
  ss w0 (w1 _) q = hself
  ss (w1 refl) (w1 refl) q = ⊥-elim (nos q)
  ss w0 w0 ()
  ss (w1 _) w0 ()
  pp : ∀ {t t′ u u′} → Wp t t′ → Wp u u′ → Pp t u → Pp t′ u′
  pp w0 (w1 _) q = pps hself
  pp (w1 refl) (w1 refl) q = ⊥-elim (noPP q hself)
  pp w0 w0 ()
  pp (w1 _) w0 ()

w-not-le : ¬ LeAt hz ω₁ (hs hz)
w-not-le (Rel.≤s ())

module Wm = X Mw

copy-Mw : SX._≼X_ I₁ uipC shLaw₁ Mw Yn Xn
copy-Mw = Sc.copy-ok Mw w0

tp-not-free : ¬ Wm.LE ω₁ (hs hz) (top b⊥ ω₁) (top b⊥ (hs hz))
tp-not-free (Wm.R2.≼Ω _ Rel.z≤ _ ())
```

## §4 不自反

```agda
gn : Cd → H (hs hz)
gn hz = hs hz
gn _ = hz

xn : H (hs hz)
xn = hΩ (inj₂ tt) gn

module Rf (Mt : Match) where
  open X Mt

  LE-not-refl : hz ~ hz → ¬ LE (hs hz) (hs hz) xn xn
  LE-not-refl ez (R2.≼Ω _ Rel.z≤ _ (R2.≼s ()))
  LE-not-refl ez (R2.Ω≼Ω {κ = inj₂ tt} {κ′ = inj₂ tt} ev h) with h hz (hs hz) tt R2.z≼
  ... | ()
```

## §5 `TU-mono` 的接手: 第三个卡点与一个实例

构造一路的接手清单第 1 条列了两个卡点 ((a) 底是 `XS` 的塔上没有同层值理论; (b) 裸的 $m$ 没有部分和保护). 这里补两条.

- **(c) 右边的值合法** (构造一路 `SameVObs.¬Mo-u₀` 同时独立得到). `crossX` 要右边 `MoX`. `TU 1` 的跨底输入 `inU₁` 不是 `MoX` (`NegValXInst.¬MoX-inU₁`, 第 0 个部分和的根 $u_0$ 的分支 $g_0$ 不对 $\le_X$ 单调). 所以 `crossX` 不能以 `inU₁` 为右边 (`tu-block`). `goal` 绕开这一点, 只在根上比较分支 $U(\mathrm{gt}\,C)$ (`MoX-U`). 要比较 `Fn 1` 以后的项, 或 `TU 1 ≤ TU 2`, 要先弱化这个前提.
- **(b) 的边界.** 裸的 $m$ 上结构递归的配对不单值, 但配对本身可以存在: `floor-block` 那一对层号上, `M₁₂` 经 `SameV.lv→match` 给出 `Match` (`Mb`). 这里只有配对; 它的地板律 `tp` 没有证.

```agda
tu-block : ¬ MoX inU₁
tu-block = ¬MoX-inU₁

Mb : Match
Mb = lv→match M₁₂
```

## §6 陈述的核对

`P2-thm` 的陈述就是 `ValXP1.P2`, 也就是接口的 `SameVIf.P2` (字面相同, `refl`). `goal` 的陈述就是接口的 `SameVIf.Goal`.

```agda
P2-same : P1m.P2 ≡ IF.P2
P2-same = refl

p2-at : IF.P2
p2-at = G.P2-thm

goal-at : IF.Goal
goal-at = G.goal
```

## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP (只因导入)]** `P2-same`, `p2-at`, `goal-at`.
- **[条件定理, 条件: `Cd` 上的 UIP (只因导入)]** `Sc.self-no`, `Sc.copy-ok`, `copy-Mw`, **`not-reflect`**, `tp-not-free`, `Rf.LE-not-refl`.
- **[定理]** `Mw`, `w-not-le`, `Sc.gLe`, `Sc.le←`, `tu-block`, `Mb`. (这些定义不用 UIP, 但本模块带参数.)
- **[判断]** `TU-mono` 的卡点 (a), (b), (c); 跨层关系与传递性没有矛盾 (同配对下取右边的坐标作插值; 没有写成定理). 没有证 `Mb` 的地板律.
