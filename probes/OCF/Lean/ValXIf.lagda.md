# ValX: 接口 (值关系在跨底折叠上应满足的律)

> 不含记号. 构造一路 ValX, 否定一路 NegValX 共用. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md), [CRwFold](CRwFold.lagda.md), [ValCIf](ValCIf.lagda.md) (只用, 不改), 与第 0 层的标准前序 [TLRuleSpec](../Align/TLRuleSpec.lagda.md) (经 `ValCIf.toA` 作锚).
>
> **接口定稿 2026-11-06 08:05 (首次编译通过).** 定稿后只增不改.
>
> **这一篇做什么.** 第 4 层 (值的验收), 不改 CRw 的树、折叠、合法性. 对象是 CRw 的跨底折叠 `Φ bX hz … b⊥ t (cx B lB pt) b h nd`: $\Omega_1$ 层的高度 $h$ (带世界 $B$ 里的路径 `nd`) 折到可数层号 $t$, 界 $b$. 闭项 `TX`, `TU m` 都是它作用在 $\Omega_1$ 层的某个高度上 (`topL`; 同底折叠 `inU m` 的输出). 接口把 $\Omega_1$ 层上的值关系 `LeX` 与值合法 `MoX` 作为**字段**, 可数层号上的关系取 [ValCIf](ValCIf.lagda.md) 的 `ValC⊥ᵖ` (字段 `V`).
>
> **律, 带字面公共上界.** 跨底折叠里一切比较的公共上界是世界的界 $B$ (目标带 $t\lhd B$, 种类带 $c+1\lhd B$). 律里两边**同一个世界** $B$ (字面公共上界就是 $B$), 同一个目标 $t$; 目标证据、路径证明两边可以不同.
>
> - `X-mono`: 输入 $x\le y$ ($\Omega_1$ 层, 都值合法), 界 $\mathrm{top}\,t\le b\le b'$ (都值合法) ⟹ $\Phi^{\times}_{B\to t,b}\,x\le\Phi^{\times}_{B\to t,b'}\,y$.
> - `X-Mo`: 跨底折叠保值合法.
> - `X-one≤`: 输出不低于 $1$.
> - 锚: `MoX-topL` ($\Omega_1$ 层的地板值合法; 否则 `MoX = ⊥` 让律空真). 第 0 层的锚就是 `V` 的 `sound₀`.
>
> **回灌.** 回灌 $B\boxplus\mathrm{leg}\,c$ 不在律里出现 (它是折叠内部的事). 否定一路 `NegValCInst.sh-not-mono≤` 对 Fab5 式关系 (含 `l≤`) 成立; 在 `l≤l σ` 的关系下 (ValC 的关系) 这一对不再相关. 本路的证明里世界会变 (进入 $\Omega_1$ 分支后世界换成 `nxt₀`), 两边的内部世界只按值比较; 这只是证明的内部引理, 不是接口的律.
>
> §3 记录 `ValXU₁`: $\Omega_1\oplus 1$ 层的地板经同底折叠 (底 `XS`) 折到 $\Omega_1$ 层的两条值事实 (公共上界: 层号 $1$, $0\lhd 1$ 字面是 `z⊲ᴮ (hs hz)`). 有了它与 `ValX`, 闭项 "`TX` + 1 ≤ `TU 1`" 只差把两条律接起来 (陈述 `Goal₁`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValXIf (I : CRwIf) where

open import Data.Unit using (⊤; tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCIf I using (L; ValC⊥ᵖ; toA)
import OCF.Align.TLRuleSpec as TL
open import OCF.Align.CumReadCF using (asuc)
```

## §1 记法

`LX`: $\Omega_1$ 层的高度. `FX B lB t pt b h nd`: 跨底折叠, 世界 $B$, 目标 $t\lhd B$, 界 $b$. `FU m lm b x`: 第 $\Omega_1\oplus m$ 层折到 $\Omega_1$ 层 (同底, 底 `XS`), 界 $b$.

```agda
LX : Set
LX = HB XS

FX : (B : Cd) → LgB B → ∀ t → t ⊲ B → L t → (h : LX) → PH PSX B h → L t
FX B lB t pt b h nd = Φ bX hz (wf bX hz) tt b⊥ t (cx B lB pt) b h nd

LU : Cd → Set
LU m = HB (Lev bX m)

FU : ∀ m → LgB m → LX → LU m → LX
FU m lm b x = Φ bX m (wf bX m) lm bX hz (sm (z⊲ᴮ m)) b x tt
```

## §2 跨底折叠的值律

```agda
record ValX : Set₁ where
  field
    V : ValC⊥ᵖ
  open ValC⊥ᵖ V public
  field
    LeX       : LX → LX → Set
    MoX       : LX → Set
    leX-refl  : ∀ x → LeX x x
    leX-trans : ∀ {x y z} → LeX x y → LeX y z → LeX x z
    MoX-topL  : MoX topL
    X-one≤    : ∀ B lB t pt b x nd → Le t (hs hz) (FX B lB t pt b x nd)
    X-Mo      : ∀ B lB t pt {b} → Mo t b → Le t (top b⊥ t) b →
                ∀ x nd → MoX x → Mo t (FX B lB t pt b x nd)
    X-mono    : ∀ B lB t (pt pt′ : t ⊲ B) {b b′ x y} (nd : PH PSX B x) (nd′ : PH PSX B y) →
                Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
                MoX x → MoX y → LeX x y →
                Le t (FX B lB t pt b x nd) (FX B lB t pt′ b′ y nd′)
```

## §3 $\Omega_1\oplus 1$ 层折到 $\Omega_1$ 层: 两条值事实

`inU₁`: 第 $\Omega_1\oplus1$ 层的地板以界 `topL` 折到 $\Omega_1$ 层 (即 `CRw.inU (hs hz) tt`, 对一切 `I` 写出).

```agda
inU₁ : LX
inU₁ = FU (hs hz) tt topL (top bX (hs hz))

record ValXU₁ (X : ValX) : Set where
  open ValX X
  field
    U₁-Mo : MoX inU₁
    U₁-ge : LeX topL inU₁
```

## §4 目标陈述 (闭项)

世界 $W_0=1$, 目标 $0$, 界 $0$: `TX` 与 `TU 1` 的形状 (路径证明作参数, 实例 `I₁` 里取 `CRw` 的 `PH-topL`, `PH-inU`).

```agda
W₀′ : Cd
W₀′ = hs hz

Goal₁ : (ndX : PH PSX W₀′ topL) (ndU : PH PSX W₀′ inU₁) → Set
Goal₁ ndX ndU = asuc (toA (FX W₀′ tt hz (z⊲ᴮ W₀′) hz topL ndX)) TL.≤ toA (FX W₀′ tt hz (z⊲ᴮ W₀′) hz inU₁ ndU)
```

## §5 (追加 2026-11-06) 锚换成 $\Omega_1$ 结点本身

> **追加, 不改 §2.** 构造一路 [ValXObs](ValXObs.lagda.md) `floor-block` (定理): 对一切 "层反射" 的关系 (左边是第 $k$ 层种类的 $\Omega$-结点时, 右边含第 $k$ 层种类的结点), 地板的分支 `gt` 在 $1+\omega_1\le1+\omega_2$ 处不单调; 推论 `¬MoX-topL`: 按分支对坐标值单调的值合法, 地板 `topL` 不值合法. 所以 §2 的锚 `MoX-topL` 对本路的关系不能满足. 这里追加记录 `ValX⁻`: 其余字段同 `ValX`, 锚换成 `MoX-Ω₁ : MoX (gt (hs hz))` (`gt 1` 就是 $\Omega_1$ 结点, 分支 $c\mapsto c$ 的嵌入; 仍是 $\Omega$-结点, 排除 `MoX = ⊥` 一类退化).

```agda
record ValX⁻ : Set₁ where
  field
    V : ValC⊥ᵖ
  open ValC⊥ᵖ V public
  field
    LeX       : LX → LX → Set
    MoX       : LX → Set
    leX-refl  : ∀ x → LeX x x
    leX-trans : ∀ {x y z} → LeX x y → LeX y z → LeX x z
    MoX-Ω₁    : MoX (gt (hs hz))
    X-one≤    : ∀ B lB t pt b x nd → Le t (hs hz) (FX B lB t pt b x nd)
    X-Mo      : ∀ B lB t pt {b} → Mo t b → Le t (top b⊥ t) b →
                ∀ x nd → MoX x → Mo t (FX B lB t pt b x nd)
    X-mono    : ∀ B lB t (pt pt′ : t ⊲ B) {b b′ x y} (nd : PH PSX B x) (nd′ : PH PSX B y) →
                Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
                MoX x → MoX y → LeX x y →
                Le t (FX B lB t pt b x nd) (FX B lB t pt′ b′ y nd′)
```
