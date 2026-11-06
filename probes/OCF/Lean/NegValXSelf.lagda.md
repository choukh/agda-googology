# NegValX (一): $\Omega_1$ 本身与分量里的拷贝, "本身 ≤ 拷贝" 与跨底单调不相容

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 本篇**不依赖**构造一路 ValX 的接口 ([ValXIf](ValXIf.lagda.md)); 对接口的推论在 [NegValXIfSelf](NegValXIfSelf.lagda.md). 只导入 [CRwBase](CRwBase.lagda.md), [CRwFold](CRwFold.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`, 即 `TX` 用的那一个), 第 0 层的标准前序 [TLRuleSpec](../Align/TLRuleSpec.lagda.md) (经 `ValCIf.toA`), 与 [ValCRel](ValCRel.lagda.md) (只为陈述 `g-up` 的前提). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有). 第 4 层: 只新增定理, 不改树, 折叠, 合法性.
>
> **问题.** $\Omega_1$ 层的种类结构 `XS` 里, $\Omega_1$ **本身**是分量 $0$ 的新种类 `κΩ = (0, inj₂ tt)` (策略 `poΩ`: 进入分支时回灌 $B\boxplus\mathrm{leg}\,c$, 世界换成 $B\boxplus\mathrm{leg}\,c+1$); 分量 $c\ge1$ 里有它的**拷贝**, 例如 `κc = (1, inj₁ (inj₂ tt))` (策略 `poF`: 坐标原样, 世界不动). 两者的层都是 $0$ (`lvΩ`, `lvc`), 坐标类型都是 `Cd`. 若 $\Omega_1$ 层上的值关系 "按层比较" (同 ValC 的 `Ω≤Ω`, 只要求层相等), 同一分支 $g$ 的两个结点 $X=\Omega_1^{\text{本身}}(g)$, $Y=\Omega_1^{\text{拷贝}}(g)$ 就互相可比. 本篇问: 跨底折叠能否对 "$X\le Y$" 单调.
>
> **`self≰copy` (定理, 对一切满足下列前提的世界 $B$).** 取分支 $g$: $g\,c=0$ 若 $c$ 的后继脊上没有 ℕ-极限, 否则 $g\,c=2$ (`Big`). 世界 $B$ 合法, $2\lhd B$, $g\,B=2$ (即 $B$ 的后继脊上有 ℕ-极限). 跨底折叠到第 $0$ 层, 界 $0$, 任一目标证据: $\Phi X\ge\omega+1$, $\Phi Y\le\omega$; 所以 $\Phi X\not\le\Phi Y$ (`TLRuleSpec._≤_`, 第 0 层的标准前序, 含 "极限在左边"; 它是一切可靠的第 0 层关系的上界). 原因: $X$ 的回灌链在 $B\boxplus\mathrm{leg}\,b'$ 处读 $g$, 那里已经过了极限; $Y$ 的链在 $b'$ 本身处读 $g$, 链点都是有限数.
>
> **`copy≤self` (定理, 同一前提).** 反方向成立: $\Phi Y\le\Phi X$. 所以本篇**不**否定 "拷贝 ≤ 本身".
>
> **前提实例.** $B=\hat\omega=\lim(1,2,3,\dots)$ (`inst-ω`), 与 $B_1=\mathrm{nxt}_0\,W_0\,(\mathrm{sh}_0\,W_0\,\hat\omega)=W_0\boxplus\mathrm{leg}\,\hat\omega+1$: `TX` 的折叠在 $\Omega_1$ 结点处以坐标 $\hat\omega$ 进入分支后所在的世界 (`inst-B₁`). 输入 $X, Y$ 合法 (`Lg-X`, `Lg-Y`), 带路径 (`ndX`, `ndY`). $g$ 对 ValC 的可数层关系单调 (`g-up`: $c\le c'$ 且 $g\,c=2$ ⟹ $g\,c'=2$; 另一种情形 $g\,c=0$).
>
> **只否定什么.** 只否定: 在 $\Omega_1$ 层上把本身与拷贝按层比较 (允许 "本身 ≤ 拷贝"), 同时要求跨底折叠单调 (同一世界, 同一目标, 同一界). **不否定**: 按 (层, 策略) 比较的关系; 只允许 "拷贝 ≤ 本身" 的关系; 跨底折叠对别的关系单调. 世界 $W_0=1$ 本身不满足前提 ($g\,1=0$): 在 `TX` 的最外层, 两种结点的折叠值相同 (判断, 没有写); 前提由折叠进入一次 $\Omega_1$ 分支后的世界满足 (`inst-B₁`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXSelf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf using (CRwIf)
open import OCF.Lean.CRw using (I₁; leg; Lg-leg; W₀)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.ValCRel I₁ using (lvK; LeAt; module Rel)
import OCF.Align.TLRuleSpec as TL
open import OCF.Align.CumReadCF using (asuc)
```

## §1 两个种类, 分支 $g$, 两个输入

```agda
κΩ κc : K XS
κΩ = hz , inj₂ tt
κc = hs hz , inj₁ (inj₂ tt)

-- 两者的层都是 0, 坐标类型都是 Cd
lvΩ : lvK (hs hz) (inj₂ tt) ≡ hz
lvΩ = refl

lvc : lvK (hs (hs hz)) (inj₁ (inj₂ tt)) ≡ hz
lvc = refl

eΩ : E XS κΩ ≡ Cd
eΩ = refl

ec : E XS κc ≡ Cd
ec = refl

-- 策略: 本身用接口的回灌 (poΩ), 拷贝不动世界 (poF)
polΩ : pX hz (inj₂ tt) ≡ poΩ
polΩ = refl

polc : pX (hs hz) (inj₁ (inj₂ tt)) ≡ poF
polc = refl

Big : HB XS
Big = hs (hs hz)

g : Cd → HB XS
g hz = hz
g (hs c) = g c
g (hl f) = Big
g (hΩ () _)

Xn Yn : HB XS
Xn = hΩ κΩ g
Yn = hΩ κc g
```

**合法.** $g$ 对第一位置单调 (`g-⊲`), 分支合法. 世界任意.

```agda
gBig : ∀ c {w} → g c ⊲[ w ] Big
gBig hz = z⊲ᴮ Big
gBig (hs c) = gBig c
gBig (hl f) = hself
gBig (hΩ () _)

g-⊲ : ∀ {x : ⊤} {c c′ : Cd} → c ⊲[ x ] c′ → ∀ {w} → g c ⊲[ w ] g c′
g-⊲ hself = hself
g-⊲ (hsuc p) = g-⊲ p
g-⊲ {c = c} (hlim n p) = gBig c
g-⊲ (hLim {κ = ()} _ _)

lg-g : ∀ c → LgB (g c)
lg-g hz = tt
lg-g (hs c) = lg-g c
lg-g (hl f) = tt
lg-g (hΩ () _)

Lg-X : LgB Xn
Lg-X = (λ lw e e′ p → g-⊲ p) , (λ {w} {c} lw e → lg-g c)

Lg-Y : LgB Yn
Lg-Y = (λ lw e e′ p → g-⊲ p) , (λ {w} {c} lw e → lg-g c)

-- 带路径: 分支没有 Ω-结点
PH-g : ∀ W e → PH PSX W (g e)
PH-g W hz = tt
PH-g W (hs e) = PH-g W e
PH-g W (hl f) = tt
PH-g W (hΩ () _)
```

**$g$ 对 ValC 的可数层关系单调** (给 `MoX` 的前提可满足性用): $c\le c'$ (`LeAt hz`, 极限在左边只对严格增子列), $g\,c=2$ ⟹ $g\,c'=2$; 另一种情形 $g\,c=0$, 在一切之下.

```agda
g-cases : ∀ c → (g c ≡ hz) ⊎ (g c ≡ Big)
g-cases hz = inj₁ refl
g-cases (hs c) = g-cases c
g-cases (hl f) = inj₂ refl
g-cases (hΩ () _)

g-up : ∀ {c c′} → LeAt hz c c′ → g c ≡ Big → g c′ ≡ Big
g-up Rel.z≤ ()
g-up (Rel.s≤s {a = a} {b = b} p) e = g-up {a} {b} p e
g-up {c} (Rel.≤s {b = b} p) e = g-up {c} {b} p e
g-up (Rel.l≤l σ i h) e = refl
g-up (Rel.≤l n p) e = refl
g-up (Rel.≤Ω {κ = ()} _ _ _ _)
g-up (Rel.Ω≤Ω {κ = ()} _ _)
```

## §2 跨底折叠的两个值

`F B lB pt b h nd`: 跨底折叠到第 $0$ 层 (同 `ValXIf.FX` 取 $t=0$). 两种结点的决定都是 "同层" (层 $0$ 等于目标 $0$): `pickS` 对 `cmpB` 的一切结果成立 (不用 UIP: 这里 $t$ 与 $i$ 都是字面 `hz`, 没有自反方程要消).

```agda
F : (B : Cd) → LgB B → hz ⊲ B → Cd → (h : HB XS) → PH PSX B h → Cd
F B lB pt b h nd = Φ bX hz (wf bX hz) tt b⊥ hz (cx B lB pt) b h nd

pickS : ∀ {X : Cd} {A R : Set} (Q : R → Set) (to : Cd → A) (u : hs hz ⊲ X)
        (r : (hz ⊲ hs hz) ⊎ (hs hz ⊲ hz)) {k s ab} →
        Q (caseDc (same {L = Tw S⊥} {X = X} {t = hz} to) k s ab) → Q (caseDc (pick S⊥ to u r) k s ab)
pickS Q to u (inj₁ (hsuc hself)) p = p
pickS Q to u (inj₂ ())

-- 输入值确定的两个小引理 (对一切世界, 目标, 界, 路径)
module _ {a : Acc bX hz} {tg : Tg bX hz b⊥ hz} {b : Cd} where
  Φ0 : ∀ {h} (nd : Nd tg h) → h ≡ hz → Φ bX hz a tt b⊥ hz tg b h nd ≡ hs hz
  Φ0 nd refl = refl

  ΦBig : ∀ {h} (nd : Nd tg h) → h ≡ Big →
         asuc (toA (hl (mul (hs hz)))) TL.≤ toA (Φ bX hz a tt b⊥ hz tg b h nd)
  ΦBig nd refl = TL.≤l 1 (TL.≤l 0 (TL.≤-refl _))

ω̂ : Cd
ω̂ = hl (mul (hs hz))

gfin : ∀ n → g (hz ⊞ mul (hs hz) n) ≡ hz
gfin zero = refl
gfin (suc n) = gfin n

chainFin : (k : Cd → Cd) → (∀ c → g c ≡ hz → k c ≡ hs hz) → ∀ n → chain hz k n ≡ mul (hs hz) n
chainFin k h zero = h hz refl
chainFin k h (suc n) =
  cong₂ _⊞_ (chainFin k h n) (h _ (trans (cong (λ z → g (hz ⊞ z)) (chainFin k h n)) (gfin n)))

gB⊞ : ∀ {B} → g B ≡ Big → ∀ x → g (B ⊞ x) ≡ Big
gB⊞ e hz = e
gB⊞ e (hs x) = gB⊞ e x
gB⊞ e (hl f) = refl
gB⊞ e (hΩ () _)
```

**主定理.** 世界 $B$ 的前提: 合法, $2\lhd B$, $g\,B=2$; 目标证据 $0\lhd B$ 任取.

```agda
module Self (B : Cd) (lB : LgB B) (e2 : hs (hs hz) ⊲ B) (gB : g B ≡ Big) where
  e1 : hs hz ⊲ B
  e1 = ⊲ᴮ-tr (hsuc hself) e2

  ndX : PH PSX B Xn
  ndX = e1 , λ e a → PH-g _ e

  ndY : PH PSX B Yn
  ndY = e2 , λ e a → PH-g _ e

  module _ (pt : hz ⊲ B) where
    -- 本身: 链的第 0 点在 B ⊞ leg 0 = B 处读 g, 已是 2
    X≥ : asuc (toA ω̂) TL.≤ toA (F B lB pt hz Xn ndX)
    X≥ = pickS (λ z → asuc (toA ω̂) TL.≤ toA z) _ _ _
           (TL.≤l 0 (ΦBig _ gB))

    -- 拷贝: 链点都是有限数 n+1
    Y≤ : toA (F B lB pt hz Yn ndY) TL.≤ toA ω̂
    Y≤ = pickS (λ z → toA z TL.≤ toA ω̂) _ _ _
           (TL.l≤ (λ n → TL.≤l n (subst (λ z → toA z TL.≤ toA (mul (hs hz) n))
              (sym (chainFin _ (λ c e → Φ0 _ e) n)) (TL.≤-refl _))))

    self≰copy : ¬ (toA (F B lB pt hz Xn ndX) TL.≤ toA (F B lB pt hz Yn ndY))
    self≰copy p = TL.irr (toA ω̂) (TL.≤-trans X≥ (TL.≤-trans p Y≤))

    copy≤self : toA (F B lB pt hz Yn ndY) TL.≤ toA (F B lB pt hz Xn ndX)
    copy≤self = TL.≤-trans Y≤ (TL.≤-trans (TL.≤-suc (TL.≤-refl _)) X≥)
```

## §3 前提实例

$\hat\omega$, 与 `TX` 的折叠进入 $\Omega_1$ 分支 (坐标 $\hat\omega$) 后的世界 $B_1=\mathrm{nxt}_0\,W_0\,(\mathrm{sh}_0\,W_0\,\hat\omega)$.

```agda
Lg-mul1 : ∀ n → LgB {S⊥} (mul (hs hz) n)
Lg-mul1 zero = tt
Lg-mul1 (suc n) = Lg-mul1 n

Lg-ω̂ : LgB ω̂
Lg-ω̂ = (λ n → hsuc hself) , Lg-mul1

inst-ω : Σ (LgB ω̂) (λ _ → (hs (hs hz) ⊲ ω̂) × (g ω̂ ≡ Big))
inst-ω = Lg-ω̂ , hlim 1 hself , refl

module Sω = Self ω̂ Lg-ω̂ (hlim 1 hself) refl

selfω : ¬ (toA (F ω̂ Lg-ω̂ (z⊲ᴮ ω̂) hz Xn Sω.ndX) TL.≤ toA (F ω̂ Lg-ω̂ (z⊲ᴮ ω̂) hz Yn Sω.ndY))
selfω = Sω.self≰copy (z⊲ᴮ ω̂)

-- TX 的世界: 初始 W₀ = 1, 在坐标 ω̂ 处进入 Ω₁ 分支
aω : CRwIf.Adm₀ I₁ W₀ (CRwIf.sh₀ I₁ W₀ ω̂)
aω = CRwIf.adm-sh I₁ ω̂ tt

B₁ : Cd
B₁ = CRwIf.nxt₀ I₁ W₀ (CRwIf.sh₀ I₁ W₀ ω̂) aω

B₁≡ : B₁ ≡ hs (W₀ ⊞ leg ω̂)
B₁≡ = refl

Lg-B₁ : LgB B₁
Lg-B₁ = CRwIf.lg-nx I₁ aω tt

inst-B₁ : Σ (LgB B₁) (λ _ → (hs (hs hz) ⊲ B₁) × (g B₁ ≡ Big))
inst-B₁ = Lg-B₁ , hsuc (hlim 0 hself) , refl

module S₁ = Self B₁ Lg-B₁ (hsuc (hlim 0 hself)) refl

-- 目标证据取折叠里实际搬过来的那一条: 0 ⊲ W₀ 经 nx-up 搬到 B₁
pt₁ : hz ⊲ B₁
pt₁ = ⊲ᴮ-tr (z⊲ᴮ W₀) (CRwIf.nx-up I₁ aω)

selfB₁ : ¬ (toA (F B₁ Lg-B₁ pt₁ hz Xn S₁.ndX) TL.≤ toA (F B₁ Lg-B₁ pt₁ hz Yn S₁.ndY))
selfB₁ = S₁.self≰copy pt₁

copyB₁ : toA (F B₁ Lg-B₁ pt₁ hz Yn S₁.ndY) TL.≤ toA (F B₁ Lg-B₁ pt₁ hz Xn S₁.ndX)
copyB₁ = S₁.copy≤self pt₁
```

## 结论 (按档)

- **[定理, 实例 `I₁`, 对一切合法世界 $B$ 满足 $2\lhd B$, $g\,B=2$, 一切目标证据]** `Self.self≰copy`: 同一分支 $g$ 的 $\Omega_1$ 本身结点 $X$ 与拷贝结点 $Y$ (层都是 $0$, 坐标类型都是 `Cd`), 跨底折叠到第 $0$ 层 (界 $0$) 后 $\Phi X\not\le\Phi Y$ (`TLRuleSpec._≤_`); `Self.copy≤self`: $\Phi Y\le\Phi X$. `Self.X≥`: $\Phi X\ge\omega+1$; `Self.Y≤`: $\Phi Y\le\omega$.
- **[定理]** 前提实例 `inst-ω`, `inst-B₁` (`TX` 的折叠进入一次 $\Omega_1$ 分支后的世界), `selfω`, `selfB₁`, `copyB₁`; 输入合法 `Lg-X`, `Lg-Y`; `g-up` ($g$ 对 ValC 的可数层关系单调).
- **[判断]** 在 `TX` 的最外层世界 $W_0=1$, $g$ 读到的坐标都是有限的, 两种结点折出相同的值; 所以反例只在进入过一次 $\Omega_1$ 分支的世界里出现.
