# NegSameV (一): $k_R$ 不是坐标在标准前序下的值的函数

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 模块参数 `uipC` 是 `Cd` 上的 UIP (条件, 经 `ValXMono.monoX`, `ValXP1`).
>
> **`stall-up` (条件定理, 条件 UIP).** 对一切可数树 $x$, 记 $\mathrm{st}\,x=\lim(x,x,x,\dots)$: $k_R\,x+1\le k_R(\mathrm{st}\,x)$ (第 0 层的值关系 `LeAt hz`). 而 $x$ 与 $\mathrm{st}\,x$ 在标准前序 `TLRuleSpec._≤_` 下互相 $\le$ (`st-val`). 所以 `kR-not-val`: $k_R$ 不是坐标的标准值的函数, 对一切 $x$.
>
> **这不是 P2 的反例.** `ValXP1.P2` 的前提是 `LeAt hz b₁ b₂`, 而 $\mathrm{st}\,x\not\le x$ 在 `LeAt` 下 (`st-not-le`), 只有 $x\le\mathrm{st}\,x$ (`le-st`), 那个方向与本篇的不等式一致. 本篇只说明 **P2 的前提不能放宽到标准前序** (`P2ᵀᴸ-false`). (构造一路后来证了 `P2` 本身, `SameVGoal.P2-thm`, 条件 UIP; 两者不矛盾, 前提不同.)
>
> **前提实例.** $x$ 任取; 合法的实例: $x$ 合法时 $\mathrm{st}\,x$ 合法 (`Lg-st`, 相邻项是 `hself`). `uipC`: 函数外延推出 (`ValCUip.fe→uipC`, 条件 Funext).
>
> **只否定什么.** 只否定 "$k_R$ 对 `TLRuleSpec._≤_` 单调". **不否定** `P2`; 不否定 `LeAt` 下的单调.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.NegSameVKr (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀; leg; Σ₀)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValXTm using (shLaw₁; sound₀)
open import OCF.Lean.ValXBase I₁ shLaw₁
open import OCF.Lean.ValXMono I₁ uipC shLaw₁ using (monoX)
open import OCF.Lean.ValXGoal using (κΩ; g₀; nd₀; kR)
open import OCF.Lean.ValXP1 uipC using (MoX-gt; MoX-U)
open import OCF.Lean.ValCIf I₁ using (toA)
open import OCF.Lean.NegSameVSpine using (¬l≤)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
```

## §1 停滞的坐标

```agda
st : Cd → Cd
st x = hl (λ _ → x)

Lg-st : ∀ x → LgB x → LgB (st x)
Lg-st x l = (λ n → hself) , (λ n → l)

st-val : ∀ x → (toA (st x) TL.≤ toA x) × (toA x TL.≤ toA (st x))
st-val x = TL.l≤ (λ n → TL.≤-refl (toA x)) , TL.≤l 0 (TL.≤-refl (toA x))

le-st : ∀ x → LeAt hz x (st x)
le-st x = Rel.≤l 0 (L.≤-refl hz x)

-- 回灌之后: 第 n 个坐标
fS : Cd → ℕ → Cd
fS x n = W₀ ⊞ Σ₀ (λ _ → leg x) n

gS : Cd → ℕ → HX
gS x = Σ⁺ (λ k → g₀ (fS x k))

pg₀ : PGt W₀ κΩ g₀
pg₀ = proj₂ nd₀

-- 坐标 x 处的新世界 (世界 W₀ 显式写出)
Wx : Cd → Cd
Wx x = nWE κΩ {W₀} tt x

lW : ∀ x → LgB (Wx x)
lW x = lgE κΩ {W₀} tt x

pW : ∀ x → hz ⊲ Wx x
pW x = ptE κΩ {W₀} tt (z⊲ᴮ W₀) x

Fm : ∀ x → ℕ → Cd
Fm x n = FXa (wf bX hz) (Wx (st x)) (lW (st x)) (pW (st x)) (st x) (gS x n) (pgE κΩ {W₀} tt pg₀ (st x) n)
```

## §2 主定理

$k_R(\mathrm{st}\,x)$ 字面是部分和的极限, 第 0 项就是 $k_R\,x$ 的输入 (世界变大, 界变大).

```agda
kR-st : ∀ x → kR (st x) ≡ hl (Σ⁺ (Fm x))
kR-st x = Relation.Binary.PropositionalEquality.refl

w≤ : ∀ x → LeAt hz (Wx x) (Wx (st x))
w≤ x = Rel.s≤s (Rel.≤l 0 (L.≤-refl hz (fS x 0)))

kR≤F0 : ∀ x → LeAt hz (kR x) (Fm x 0)
kR≤F0 x = monoX (wf bX hz) (wf bX hz) {Wx x} {Wx (st x)} (lW x) (lW (st x)) (w≤ x) (pW x) (pW (st x))
            (moZ x , moZ (st x) , Rel.z≤ , le-st x)
            (g₀ (fS x 0)) (pgE κΩ {W₀} tt pg₀ x) (pgE κΩ {W₀} tt pg₀ (st x) 0)
            (MoX-U topL (gt (fS x 0)) (MoX-gt (fS x 0))) (MoX-U topL (gt (fS x 0)) (MoX-gt (fS x 0)))
            (≤X-refl (g₀ (fS x 0)))

one≤F1 : ∀ x → LeAt hz (hs hz) (Fm x 1)
one≤F1 x = oneX (wf bX hz) {Wx (st x)} (lW (st x)) (pW (st x)) (st x) (gS x 1) (pgE κΩ {W₀} tt pg₀ (st x) 1)

stall-up : ∀ x → LeAt hz (hs (kR x)) (kR (st x))
stall-up x = Rel.≤l {a = hs (kR x)} {g = Σ⁺ (Fm x)} 1
  (L.≤-trans hz {hs (kR x)} {hs (Fm x 0)} {Fm x 0 ⊞ Fm x 1}
     (Rel.s≤s (kR≤F0 x)) (L.⊞-monoʳ hz (Fm x 0) {hs hz} {Fm x 1} (one≤F1 x)))

kR-not-val : ∀ x → ¬ (toA (kR (st x)) TL.≤ toA (kR x))
kR-not-val x p = TL.irr (toA (kR x)) (TL.≤-trans (sound₀ (stall-up x)) p)

P2ᵀᴸ-false : ¬ (∀ b₁ b₂ → toA b₁ TL.≤ toA b₂ → toA (kR b₁) TL.≤ toA (kR b₂))
P2ᵀᴸ-false h = kR-not-val hz (h (st hz) hz (proj₁ (st-val hz)))
```

## §3 这一对不在 `LeAt` 里

```agda
st-not-le : ∀ x → ¬ LeAt hz (st x) x
st-not-le x p = ¬l≤ x 0 p (L.≤-refl hz x)
```

## 结论 (按档)

- **[条件定理, 条件: `Cd` 上的 UIP]** `kR≤F0`, **`stall-up`**: $k_R\,x+1\le k_R(\mathrm{st}\,x)$ (对一切 $x$); **`kR-not-val`**: $k_R(\mathrm{st}\,x)\not\le k_R\,x$ (`TLRuleSpec._≤_`); **`P2ᵀᴸ-false`**: $k_R$ 对标准前序不单调.
- **[定理, 不用 UIP]** `st-val`, `le-st`, `Lg-st`, `st-not-le`, `kR-st` (`refl`).
- **[说明]** 这一对不是 `P2` 的反例.
