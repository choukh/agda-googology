# 验收: 累加的账, 数字

> **验收文件**, 读 `NoCumsum` 的 `BTBOᴵ` (通过基本列验收). **全部是有限测试** (`refl`), 不是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpAcceptLedger where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Empty
import OCF.Free.Level as FL
open import OCF.Align.Level using (Ordᶜ; Ordᴵ; zero; suc; lim; limᵢ; up; FGH)
open FL using () renaming (FGH to FGH₀)
import OCF.Align.Level as Lv
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.CumReadBase using (Ord₀; cumA; cs; natO; ω₁; next; _⊞_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.CumReadTop using (Tᶜ; ysᶜ; chainᶜ; η)
open import OCF.Align.CumUpClean using (Tᵇ; ysB; chainB; cumB; nextB; cB; rd)
import OCF.Align.CumUpClean as K
open import OCF.Align.CumUpAcceptSim using (fr)
open import OCF.Align.CumReadAccept using (Fp; fpO; stop; fz′; fs′; fl′; take; natA)
open import Data.List using (List; []; _∷_)
```

## §1 比较器

`G`: 慢增长层级 $G_x(n)$: $G_0=0$, $G_{x+1}=G_x+1$, $G_{\lim f}(n)=G_{f(n)}(n)$. 它对基本列敏感, 而且算得完. `GA`, `GI` 同样读下标. 盲区: 只走一条路径 ($n$ 固定), 看不到其他分支; 它不是 FGH.

```agda
G : Ord₀ → ℕ → ℕ
G FL.zero n = 0
G (FL.suc a) n = suc (G a n)
G (FL.lim f) n = G (f n) n
G (FL.limᵢ () f) n
G (FL.up () x) n

GL : Ordᶜ Ordᴵ.zero → ℕ → ℕ
GL Lv.zero n = 0
GL (Lv.suc a) n = suc (GL a n)
GL (Lv.lim f) n = GL (f n) n
GL (Lv.limᵢ () f) n
GL (Lv.up () x) n

GA : A → ℕ → ℕ
GA azero n = 0
GA (asuc a) n = suc (GA a n)
GA (alim f) n = GA (f n) n

GI : Ordᴵ → ℕ → ℕ
GI Ordᴵ.zero n = 0
GI (Ordᴵ.suc a) n = suc (GI a n)
GI (Ordᴵ.lim f s) n = GI (f n) n
```

## §2 指纹与计数

`fpL`: Level 第 0 层的树的指纹, 与 `CumReadAccept.fpO` 同形. `szO`, `szL`, `szA`: 截断到深度 $d$, 宽度 $w$ 的节点数. 盲区同指纹.

```agda
fpL : ℕ → ℕ → Ordᶜ Ordᴵ.zero → Fp
fpL zero w x = stop
fpL (suc d) w Lv.zero = fz′
fpL (suc d) w (Lv.suc x) = fs′ (fpL d w x)
fpL (suc d) w (Lv.lim f) = fl′ (take w (λ n → fpL d w (f n)))
fpL (suc d) w (Lv.limᵢ () f)
fpL (suc d) w (Lv.up () x)

open import Data.Nat using (_+_)
sumℓ : ℕ → (ℕ → ℕ) → ℕ
sumℓ zero F = 0
sumℓ (suc w) F = F 0 + sumℓ w (λ n → F (suc n))

szA : ℕ → ℕ → A → ℕ
szA zero w x = 0
szA (suc d) w azero = 1
szA (suc d) w (asuc x) = suc (szA d w x)
szA (suc d) w (alim f) = suc (sumℓ w (λ n → szA d w (f n)))

szI : ℕ → ℕ → Ordᴵ → ℕ
szI zero w x = 0
szI (suc d) w Ordᴵ.zero = 1
szI (suc d) w (Ordᴵ.suc x) = suc (szI d w x)
szI (suc d) w (Ordᴵ.lim f s) = suc (sumℓ w (λ n → szI d w (f n)))

-- 基本列的数值: 下标 ω 的前几项
plain cumω cumBω : ℕ → ℕ
plain n = GA (rd (natO n)) 0
cumω n = GA (cs (λ k → cumA (natO k)) n) 0
cumBω n = GA (cB (λ k → cumB (natO k)) n) 0
```

## §3 下标的基本列

下标 $\omega$ 的前几项. 四本账: 逐点读出, `cumB` (不加 1), `cumA` (加 1). **有限测试, 算的是自然数, 精确.**

| $n$ | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| 逐点 $f(n)$ | 0 | 1 | 2 | 3 | 4 | 5 |
| `cumB` | 0 | 1 | 3 | 6 | 10 | 15 |
| `cumA` | 0 | 2 | 5 | 9 | 14 | 20 |

```agda
_ : plain 5 ≡ 5
_ = refl
_ : cumBω 1 ≡ 1
_ = refl
_ : cumBω 2 ≡ 3
_ = refl
_ : cumBω 5 ≡ 15
_ = refl
_ : cumω 1 ≡ 2
_ = refl
_ : cumω 2 ≡ 5
_ = refl
_ : cumω 5 ≡ 20
_ = refl
```

## §4 链上第一个下标

同一位置的下标: 不累加的 $L_1$ (`toLevel` 读 $\gamma_1$); 影子 `chainS 0`; 不加 1 的 `chainB 0`; 上一轮的 `chainᶜ 0`. 比较器 `GA`, `GI`: 慢增长值.

| $n$ | $L_1$ | 影子 | `chainB` | `chainᶜ` |
|---|---|---|---|---|
| 0 | 0 | 1 | 1 | 2 |
| 1 | 1 | 4 | 4 | 9 |
| 2 | 16 | 76 | 111994 | 206933 |

```agda
_ : GI (N.L 1) 0 ≡ 0
_ = refl
_ : GI (N.L 1) 1 ≡ 1
_ = refl
_ : GI (N.L 1) 2 ≡ 16
_ = refl
_ : GA (K.IxS.ηs (K.chainS 0)) 0 ≡ 1
_ = refl
_ : GA (K.IxS.ηs (K.chainS 0)) 1 ≡ 4
_ = refl
_ : GA (K.IxS.ηs (K.chainS 0)) 2 ≡ 76
_ = refl
_ : GA (K.IxB.η (chainB 0)) 0 ≡ 1
_ = refl
_ : GA (K.IxB.η (chainB 0)) 1 ≡ 4
_ = refl
_ : GA (K.IxB.η (chainB 0)) 2 ≡ 111994
_ = refl
_ : GA (η (chainᶜ 0)) 0 ≡ 2
_ = refl
_ : GA (η (chainᶜ 0)) 1 ≡ 9
_ = refl
_ : GA (η (chainᶜ 0)) 2 ≡ 206933
_ = refl
```

截断节点数 (`szA 4 2`, `szI 4 2`) 给 7, 12, 11 (`chainᶜ`, `chainB`, $L_1$). 这个比较器分不开方向: 同样的截断下, 累加多出的层把分支推到截断以下. 只记录, 不据此下结论.

```agda
_ : szA 4 2 (η (chainᶜ 0)) ≡ 7
_ = refl
_ : szA 4 2 (K.IxB.η (chainB 0)) ≡ 12
_ = refl
_ : szI 4 2 (N.L 1) ≡ 11
_ = refl
```

## §5 树的基本列

$T^c$ 的第 0 项与 $\gamma_1$ 相同 (定理 `CumUpAcceptVal.y₀≅γ₁`). 第 1 项在指纹的深度 4 上第一次不同形: 不累加的树的路径 $[0][0][0]$ 在第 4 层到了极限 $(0,1)$, 累加的树还要往下走.

```agda
_ : fpO 3 2 (ysᶜ 1) ≡ fpL 3 2 (N.γ 2)
_ = refl

_ : G (ysᶜ 0) 2 ≡ GL (N.γ 1) 2
_ = refl

-- 深度 4 的第一处不同
diff₄ : fpO 4 2 (ysᶜ 1) ≡ fpL 4 2 (N.γ 2) → Data.Empty.⊥
diff₄ ()

-- 参数 0: 相等, 比较器分不开
_ : FGH₀ Tᶜ 0 ≡ FGH BTBOᴵ 0
_ = refl

_ : FGH BTBOᴵ 1 ≡ 2
_ = refl
```

**FGH 在算得到的参数上分不开.** 参数 1 上**一切**树都给 2 (`FGH₀-1`, 定理, 对树归纳), 所以 `FGH₀ Tᶜ 1 ≡ FGH BTBOᴵ 1 ≡ 2` 是定理, 比较器在这里是瞎的. 参数 0 也相等. 参数 2 两边都算不完. 所以 **FGH 的小值没有区分这两棵树的有限测试**, 这条账只能靠上面的 `G`, 指纹和下标.

```agda
FGH₀-1 : ∀ x → FGH₀ x 1 ≡ 2
FGH₀-1 FL.zero = refl
FGH₀-1 (FL.suc a) = FGH₀-1 a
FGH₀-1 (FL.lim f) = FGH₀-1 (f 1)
FGH₀-1 (FL.limᵢ () f)
FGH₀-1 (FL.up () x)
```

**计时观察 (不是定理, 也不是测试的结论):** `GL (N.γ 2) 1` 瞬时给 1; `G (ysᶜ 1) 1` 在 240 秒内没有算完, `G (ysB 1) 1`, `G (K.ysS 1) 1` 在 20 到 25 秒内没有算完. 超时只说明 Agda 归约的代价, 不说明值的大小, 也不说明 FGH 的大小.
