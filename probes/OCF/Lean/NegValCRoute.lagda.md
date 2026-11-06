# NegValC (三): 接口的 `route` 在 $t=j$ (`pt = hself`) 处不成立

> 不含记号. 入口 [NegValC](NegValC.lagda.md). 对构造一路 ValC 的接口 [ValCIf](ValCIf.lagda.md) 的记录 `ValC⊥` (定稿 2026-11-06 01:41, 本路不改它). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 接口的路线引理 `route` 对一切 `pt : t ⊲ j` 陈述, 包括 `pt = hself` ($t=j$). 这时右边先以地板 `top j` 为界折到第 $j=t$ 层, 再从第 $t$ 层折到第 $t$ 层; 第 $t$ 层的树里没有第 $t$ 层的结点, 所以外层的界 $b'$ 不起作用. 左边直接折到 $t$, "同层" 结点的链从界 $b$ 出发. 界取得大, 左边就超过右边. 构造一路已经判断这里失败 (只对 `hsuc`/`hlim` 开头的 `pt` 证); 本篇把它写成定理.
>
> **`route-hself` (定理, 对一切 `I`, 一切 `V : ValC⊥`).** 取 $m=1$, $j=t=0$, $x=y=$ 地板 `top b⊥ 1` ($\Omega_1$ 结点, 分支 `up`), $b=b'=R$, 其中 $T=\Phi_{1\to0,\,0}(\mathrm{top}\,1)$, $R=\Phi_{0\to0,\,0}\,T$ (都是折叠的输出, 所以值合法是 `Mo-Φ` 给的). 则 `¬ Le hz hz R`. 证明: `route` 与 `sound₀` 给出 $\Phi_{1\to0,R}(\mathrm{top}\,1)\le\Phi_{0\to0,R}\,T$ (第 0 层, `TL.≤`); 第 0 层到第 0 层的折叠与界无关 (`BI`), 右边 $\le R$; 左边是从 $R$ 出发的链, 它的第 1 点 $\ge R+1$ (`hsR≤`). 矛盾.
>
> **推论 `no-z≤`.** 若 `Le hz` 含 "$0$ 在一切之下" (`z≤`), 则 `V` 不存在. 所以按 `ValCIf` 定稿的 `ValC⊥` 没有第 0 层含 `z≤` 的实例. 第 0 层上的标准前序就含 `z≤`, `TL.≤` 的拉回也含.
>
> **前提实例.** `V` 的前提是全称的; `route-hself` 不需要 `V` 有任何额外性质. `no-z≤` 的前提 "`Le hz` 含 `z≤`" 被第 0 层的标准前序满足, 构造一路的关系 (按它的消息, 有 `z≤`) 也满足.
>
> **只否定什么.** 只否定 `route` 在 `pt = hself` 时成立 (对第 0 层含 `z≤` 的关系). **不否定** `pt` 以 `hsuc` 或 `hlim` 开头 ($t\lhd j$ 真) 时的 `route`; 不否定 `Φ-mono`, `Mo-Φ`, `one≤Φ`. 修补是在接口里追加一个只对真 $t\lhd j$ 陈述 `route` 的新记录 (判断; 接口 "只增不改").

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.NegValCRoute (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCIf I
import OCF.Align.TLRuleSpec as TL
import OCF.Lean.NegValCInst as NI

private
  module R₀ = NI.Rel NI.cr⊥
open R₀ using (z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω; ≤-refl; ≤-trans)

infix 4 _≤₀_
_≤₀_ : Cd → Cd → Set
a ≤₀ b = a R₀.≤[ tt ] b
```

## §1 第 0 层: 加法单调 (同 Fab5ValRel, 只在 `Cd` 上), 读成 `TL.≤`

```agda
≤⊞ : ∀ a b → a ≤₀ a ⊞ b
≤⊞ a hz = ≤-refl a
≤⊞ a (hs b) = ≤s (≤⊞ a b)
≤⊞ a (hl f) = ≤l 0 (≤⊞ a (f 0))
≤⊞ a (hΩ () _)

≤⊞ˡ : ∀ a x → x ≤₀ a ⊞ x
≤⊞ˡ a hz = z≤
≤⊞ˡ a (hs x) = s≤s (≤⊞ˡ a x)
≤⊞ˡ a (hl f) = l≤ (λ n → ≤l n (≤⊞ˡ a (f n)))
≤⊞ˡ a (hΩ () _)

⊞-monoˡ : ∀ {a a′} x → a ≤₀ a′ → a ⊞ x ≤₀ a′ ⊞ x
⊞-monoˡ hz p = p
⊞-monoˡ (hs x) p = s≤s (⊞-monoˡ x p)
⊞-monoˡ (hl f) p = l≤ (λ n → ≤l n (⊞-monoˡ (f n) p))
⊞-monoˡ (hΩ () _) p

⊞-monoʳ : ∀ a {x y} → x ≤₀ y → a ⊞ x ≤₀ a ⊞ y
⊞-monoʳ a (z≤ {b = y}) = ≤⊞ a y
⊞-monoʳ a (s≤s p) = s≤s (⊞-monoʳ a p)
⊞-monoʳ a (≤s p) = ≤s (⊞-monoʳ a p)
⊞-monoʳ a (l≤ h) = l≤ (λ n → ⊞-monoʳ a (h n))
⊞-monoʳ a (≤l n p) = ≤l n (⊞-monoʳ a p)
⊞-monoʳ a (≤Ω {κ = ()} _ _ _)
⊞-monoʳ a (Ω≤Ω {κ = ()} _)

⊞-mono : ∀ {a a′ x y} → a ≤₀ a′ → x ≤₀ y → a ⊞ x ≤₀ a′ ⊞ y
⊞-mono {x = x} p q = ≤-trans (⊞-monoˡ x p) (⊞-monoʳ _ q)

one-step₀ : ∀ a b → hs hz ≤₀ b → hs a ≤₀ a ⊞ b
one-step₀ a hz ()
one-step₀ a (hs b) p = s≤s (≤⊞ a b)
one-step₀ a (hl f) (≤l n q) = ≤l n (one-step₀ a (f n) q)
one-step₀ a (hΩ () _) p

mul-mono : ∀ {a a′} → a ≤₀ a′ → ∀ n → mul a n ≤₀ mul a′ n
mul-mono p zero = p
mul-mono p (suc n) = ⊞-mono (mul-mono p n) p

Σ-mono : ∀ {g g′ : ℕ → Cd} → (∀ n → g n ≤₀ g′ n) → ∀ n → Σ⁺ g n ≤₀ Σ⁺ g′ n
Σ-mono h zero = h 0
Σ-mono h (suc n) = ⊞-mono (Σ-mono h n) (h (suc n))

Σ≥ : ∀ (g : ℕ → Cd) n → g n ≤₀ Σ⁺ g n
Σ≥ g zero = ≤-refl _
Σ≥ g (suc n) = ≤⊞ˡ (Σ⁺ g n) (g (suc n))

conv : ∀ {a b} → a ≤₀ b → toA a TL.≤ toA b
conv z≤ = TL.z≤
conv (s≤s p) = TL.s≤ (conv p)
conv (≤s p) = TL.≤-suc (conv p)
conv (l≤ h) = TL.l≤ (λ n → conv (h n))
conv (≤l n p) = TL.≤l n (conv p)
conv (≤Ω {κ = ()} _ _ _)
conv (Ω≤Ω {κ = ()} _)
```

## §2 第 0 层到第 0 层的折叠与界无关; 第 1 层的嵌入折回不降值

```agda
Φ0 : Cd → Cd → Cd
Φ0 b z = F hz tt hz hself b z

BI : ∀ b b′ z → Φ0 b z ≤₀ Φ0 b′ z
BI b b′ hz = ≤-refl _
BI b b′ (hs h) = l≤ (λ n → ≤l n (mul-mono (BI b b′ h) n))
BI b b′ (hl f) = l≤ (λ n → ≤l n (Σ-mono (λ k → BI b b′ (f k)) n))
BI b b′ (hΩ () _)

Φ1 : Cd → L (hs hz) → Cd
Φ1 b x = F (hs hz) tt hz (hsuc hself) b x

oneU : ∀ b (c : Cd) → hs hz ≤₀ Φ1 b (up c)
oneU b hz = ≤-refl _
oneU b (hs c) = ≤l 0 (oneU b c)
oneU b (hl f) = ≤l 0 (oneU b (f 0))
oneU b (hΩ () _)

infl : ∀ b (c : Cd) → c ≤₀ Φ1 b (up c)
infl b hz = z≤
infl b (hs c) = ≤l 1 (≤-trans (s≤s (infl b c)) (one-step₀ (Φ1 b (up c)) (Φ1 b (up c)) (oneU b c)))
infl b (hl f) = l≤ (λ n → ≤l n (≤-trans (infl b (f n)) (Σ≥ (λ k → Φ1 b (up (f k))) n)))
infl b (hΩ () _)
```

**地板 $\Omega_1$ 折到第 0 层是从界出发的链** (`refl`), 第 1 点 $\ge$ 界 $+1$.

```agda
kU : Cd → Cd
kU b′ = Φ1 b′ (up b′)

top1≡ : ∀ B → Φ1 B (top b⊥ (hs hz)) ≡ hl (chain B kU)
top1≡ B = refl

hsB≤ : ∀ B → hs B ≤₀ Φ1 B (top b⊥ (hs hz))
hsB≤ B = ≤l 1 (≤-trans (one-step₀ B (kU B) (oneU B B))
                (≤-trans (infl (B ⊞ kU B) (B ⊞ kU B)) (≤⊞ˡ (kU B) (kU (B ⊞ kU B)))))
```

## §3 `route` 在 `pt = hself` 处

```agda
T : Cd
T = Φ1 hz (top b⊥ (hs hz))

R : Cd
R = Φ0 hz T

module _ (V : ValC⊥) where
  open ValC⊥ V

  Mo-T : Mo hz T
  Mo-T = Mo-Φ (hs hz) tt hz (hsuc hself) (Mo-hz hz) (le-refl hz hz) (top b⊥ (hs hz)) (Mo-top (hs hz) tt)

  Mo-R : Mo hz R
  Mo-R = Mo-Φ hz tt hz hself (Mo-hz hz) (le-refl hz hz) T Mo-T

  -- route 的这一个实例: m = 1, j = t = 0, pt = hself, b = b′ = R, x = y = top 1
  route-inst : Le hz hz R → Le hz (Φ1 R (top b⊥ (hs hz))) (Φ0 R T)
  route-inst z =
    route (hs hz) tt hz hself hz hself Mo-R Mo-R z (le-refl hz R)
          (Mo-top (hs hz) tt) (Mo-top (hs hz) tt) (le-refl (hs hz) (top b⊥ (hs hz)))

  route-hself : ¬ Le hz hz R
  route-hself z =
    TL.irr (toA R)
      (TL.≤-trans (conv (hsB≤ R))
        (TL.≤-trans (sound₀ (route-inst z)) (conv (BI R hz T))))

  no-z≤ : ¬ (∀ {y} → Le hz hz y)
  no-z≤ z = route-hself z
```

## 结论 (按档)

- **[定理, 对一切 `I`, 一切 `V : ValC⊥`]** `route-hself`: `¬ Le hz hz R` ($R$ 是一棵具体的第 0 层树, 折叠的输出, 值合法 `Mo-R`). `no-z≤`: `Le hz` 不能含 `z≤`. 即按定稿的 `ValC⊥` 没有第 0 层含 `z≤` 的实例.
- **[定理]** 第 0 层: `BI` (第 0 层到第 0 层的折叠与界无关, 两个方向), `infl` (第 1 层的嵌入折回不降值), `hsB≤` (地板 $\Omega_1$ 以界 $B$ 折到第 0 层 $\ge B+1$), `top1≡` (`refl`).
- **[判断]** 修补: 只对真 $t\lhd j$ (`pt` 以 `hsuc`/`hlim` 开头) 陈述 `route` 的新记录. 本篇不判定那个版本.
