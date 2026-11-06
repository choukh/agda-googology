# 第三种组织, 否定一路 (四): 对构造一路闭项的检查

> 不含记号. 入口 [NegThird](NegThird.lagda.md). 只读导入构造一路的 [ThirdTw](ThirdTw.lagda.md), [ThirdFold](ThirdFold.lagda.md), [ThirdSan](ThirdSan.lagda.md), [ThirdPS](ThirdPS.lagda.md), [ThirdLeg](ThirdLeg.lagda.md), [ThirdX](ThirdX.lagda.md), [ThirdTm](ThirdTm.lagda.md), [ThirdVal](ThirdVal.lagda.md) (21:47 版), 与 [NegCRwInst](NegCRwInst.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **构造一路交了什么.** 闭项 `TΛ : Cd`, 证书 `LgB-TΛ`, FGH `fghΛ`. 它自己判断读法在 ψ₀(Ω_{Ω·ω}) 附近, 不报为 ψ₀Λ 候选. 本篇检查它.
>
> **结果.**
>
> 1. **$\Lambda$ 层没有整层折下来 (§1).** **`TΛ-shape`**, **`yΛ-succ`**: `TΛ` 是对 $k$ 的部分和, 第 $k$ 项是第 $k+1$ 个底的地板下降的结果 (`TN`), 界 $y_k+1$. [读文件] `ThirdTm` 不引用 `flΛ`: 第 $\Lambda$ 层的地板不进闭项. 这与 `RecB.Tω` 同形 (对 $n$ 的对角), 不是 "把 $\Lambda$ 层折到第 $0$ 层".
> 2. **证书 (§1).** **`cert-std`**: 类型就是 `CRwBase.LgB TΛ`, 标准. 中间层: **`G.ΦX-acc`** (对一切底, 一切洗法): 跨底折叠不保第一位置 ($1\lhd\lim(0,1,1,\dots)$, 像不是). 同 CRw, RecB; 不否定证书.
> 3. **决定 (§2).** 指标种类: **`G.root-same`**, **`G.pick-same`** (目标层 $0$: 对一切底塌缩), **`G.pick-keep`** (目标层 $\geq1$ 的后继: 留). 这是对一切底一条规则, 按读法 $\Omega_{x+1}$ 对第 $x+t$ 层是对的 (判断). 指标分量的旧种类: **`G.old-pk`**, **`G.old-const`**: **不是决定**: 结点换成代表坐标处的那一支, 其余分支完全不读 (`refl`). 所以闭项路径上分支坐标 $y$ 的 $\Omega$-结点 (`G.gtX-Ω`) 对输出的贡献只有一支. 这是 `keep-req`, `no-lower-rule` 不适用于本实例的原因 (前提 "根留成底种类" 不成立), 也是损失的位置.
> 4. **洗 (§2).** **`Sa.san-noΩ`**: $\Omega$-头的高度上, 洗后的值**没有** $\Omega$-结点 (一切坐标): 留下的新种类在 $\Omega$-头的层上, 分支只读 $\mathbb N$-树. **`Sa.tp-bot`**: 这一层的地板是 `bot` 分量的地板. 所以在 `san`, `tp` 出现的地方, $\Omega$-头的高度 $\Omega[g]$ 只通过 $g(\mathrm{bot})$ 起作用 (形状定理; 不是值的定理).
> 5. **`rk-⊲` 推不出上界 (§3).** **`RW`**: `Rk` 的前提对 $U=$ `step S⊥` 的**每个**合法世界成立 (代表坐标取界), 所以 `rk-⊲` 在会移动的世界 (`LHRec.J₁`) 的每个世界里也成立. **`rk-wdep`**: `rk` 依赖世界 ($\Omega$ 的 `rk` 在世界 $1$, $2$ 里分别是 $1$, $2$). 它只关于高度的第一位置, 不涉及折叠的输出. 能推出的是 **`comp-rk`**: 一站里走到的分量, `rk` $(c+1)\lhd$ `rk B`; 这是高度的界. **`first-rk`** ($n=1,\dots,4$, 第 $0$ 层的界取 $1$, `refl`): 第 $n$ 个底的地板经 $1\boxplus\mathrm{leg}$ 后 `rk` 是 $1$: 地板的 $\Omega$-结构对这一站的第一个回灌没有贡献.
> 6. **上界: 未得到.** 没有 `TΛ` 或 `TN` 的值的上界定理. 一个上界要把折叠模拟到更低的系统 (例如 RecB), 本路没有写. [有限测试] [NegThirdTest](NegThirdTest.lagda.md): 见那里. 读法仍是判断.
>
> **前提实例.** 2: `phI`, `NegCRwInst.one⊲fI`. 3: `G` 的参数由 `ThirdTm.Cn.St` 填上 (`legS`, `pkS`, `pk-bd`, `Er`). 5: `RW` 对一切合法 $B$. `no-wash` 与 `Er` 不矛盾: `Er` 在有位置的结点上也换根 (`ThirdVal.er-drop`), `no-wash` 的第二条前提不成立.
>
> **只否定什么.** 本篇不否定任何路线. 2 只否定保第一位置 (证书不要它). 3, 4 是形状: 指出闭项哪里不读输入; 它们不是读法定理, 不等于 "读法低". 5 只否定 "由 `rk-⊲` 直接得到值的上界". 没有编译的定理说 `TΛ` 低于 ψ₀Λ; "`TΛ` 读法在 ψ₀(Ω_{Ω·ω}) 附近" 是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThirdInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw
open import OCF.Lean.ThirdLeg
open import OCF.Lean.ThirdTm using (TΛ; LgB-TΛ; yΛ; lg-yΛ; module Cn)
open import OCF.Lean.ThirdVal using (module Rk; module Stage)
open import OCF.Lean.ThirdPS using (PH)
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdSan as TS
import OCF.Lean.ThirdX as TX
open import OCF.Lean.NegCRwInst using (fI; module AccNMᶜ)
import OCF.Lean.NegCRwInst as N
```

## §1 $\Lambda$ 层, 证书

```agda
TΛ-shape : TΛ ≡ hl yΛ
TΛ-shape = refl

yΛ-succ : ∀ k → yΛ (suc k) ≡ yΛ k ⊞ Cn.TN (hs (yΛ k)) (lg-yΛ k) k
yΛ-succ k = refl

cert-std : LgB TΛ
cert-std = LgB-TΛ
```

## §2 决定与形状 (对一切底, 一切洗法)

```agda
module G (U : KS) (w : Wd U) (lw : LgW U w) (Sn : TF.San U w lw)
         (leg : HB U → HB U) (Lg-leg : ∀ a → LgB (leg a))
         (pk : (κ : K U) → E U κ) (pk-bd : ∀ κ → Bd U κ (pk κ) w) where
  open TF U w lw
  open F Sn
  open TX U w lw Sn leg Lg-leg pk pk-bd

  hz′ : HB U
  hz′ = hz

  data IsLim {S : KS} : HB S → Set where
    lim : ∀ {f} → IsLim (hl f)

  data IsSame {X t A P} : Dg X t A P → Set where
    isS : ∀ {to a} → IsSame (same to a)

  no1⊲0 : ¬ (_⊲[_]_ {U} (hs hz) w hz)
  no1⊲0 ()

  pick-same : ∀ {X A P} (to : HB (T hz) → A) (ad : ∀ c → Gd hz c → P (to c)) (u : hs hz ⊲ᵘ X)
    (r : (hz ⊲ᵘ hs hz) ⊎ (hs hz ⊲ᵘ hz)) → IsSame {X} {hz} {A} {P} (pickG to ad u r)
  pick-same to ad u (inj₁ (hsuc hself)) = isS
  pick-same to ad u (inj₂ ())

  node-lim : ∀ {X A P} (d : Dg X hz A P) (pt : hz ⊲ᵘ X) (b : GT hz) rec dn → IsSame d → IsLim (proj₁ (nodeG d pt b rec dn))
  node-lim d pt b rec dn isS = lim

  -- 指标种类在第 0 层: 对一切底都塌缩 (没有 "n ≥ 1 一律留")
  root-same : ∀ B lB pt b (g : HB U → HB (XSof U)) o pg →
    IsLim (proj₁ (ΦX hz B lB pt b (hΩ (ιK {U}) g) (o , pg)))
  root-same B lB pt b g o pg =
    node-lim (dcI lB pt o) pt b _ _ (pick-same (λ c → c) (λ c _ → tt) o (cmpB {U} o pt lw lB))

  -- 指标分量的旧种类: 不是决定, 只读代表坐标
  old-pk : ∀ t B lB pt b κ (g : E (XSof U) (inj₁ tt , inj₁ κ) → HB (XSof U)) o pg →
    ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) (o , pg) ≡ ΦX t B lB pt b (g (pk κ)) (pg _ (pk-bd κ))
  old-pk t B lB pt b κ g o pg = refl

  -- 其余分支完全不读
  old-const : ∀ t B lB pt b κ (g : E (XSof U) (inj₁ tt , inj₁ κ) → HB (XSof U)) o pg →
    ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) g) (o , pg) ≡
    ΦX t B lB pt b (hΩ (inj₁ tt , inj₁ κ) (λ _ → g (pk κ))) (o , λ _ _ → pg _ (pk-bd κ))
  old-const t B lB pt b κ g o pg = refl

  -- t ≥ 1: 指标种类留 (第 0 层的新种类)
  data IsKeep {X t A P} : Dg X t A P → Set where
    isK : ∀ {κ′ p fr a} → IsKeep (keep κ′ p fr a)

  no-s⊲0 : ∀ {x} → ¬ (hs x ⊲ᵘ hz)
  no-s⊲0 ()

  pick-keep : ∀ {X A P t′} (to : HB (T hz) → A) (ad : ∀ c → Gd hz c → P (to c)) (u : hs hz ⊲ᵘ X)
    (r : (hs t′ ⊲ᵘ hs hz) ⊎ (hs hz ⊲ᵘ hs t′)) → IsKeep {X} {hs t′} {A} {P} (pickG to ad u r)
  pick-keep to ad u (inj₁ hself) = isK
  pick-keep to ad u (inj₁ (hsuc q)) = ⊥-elim′ (no-s⊲0 q)
    where ⊥-elim′ : ∀ {a} {A : Set a} → ⊥ → A
          ⊥-elim′ ()
  pick-keep to ad u (inj₂ q) = isK

  -- 折叠不保第一位置
  phI : ∀ B n → PH PSX B (fI n)
  phI B zero = tt
  phI B (suc n) = tt

  mulC : ∀ n → proj₁ (mulG {hz′} (hs hz , tt) n) ≡ N.num (suc n)
  mulC zero = refl
  mulC (suc n) = cong hs (mulC n)

  ΦX-acc : ∀ B lB (pt : hz′ ⊲ᵘ B) (b : GT hz′) {v : Wd (T hz′)} →
    ¬ (proj₁ (ΦX hz′ B lB pt b (hs hz) tt) ⊲[ v ] proj₁ (ΦX hz′ B lB pt b (hl fI) (phI B)))
  ΦX-acc B lB pt b =
    AccNMᶜ.acc-not-mono _ _ _ (λ n → proj₁ (mulG {hz′} (hs hz , tt) n))
      (λ n → proj₁ (ΣG (λ k → ΦX hz′ B lB pt b (fI k) (phI B k)) n)) refl refl mulC refl refl (λ n → refl)

  gtX-Ω : ∀ fb κ (h : E U κ → HB U) → gtX U fb (hΩ κ h) ≡ hΩ (inj₁ tt , inj₁ κ) (λ e → gtX U fb (h e))
  gtX-Ω fb κ h = refl
```

**洗.** $\Omega$-头的高度: 洗后没有结点; 地板只走 `bot`.

```agda
module _ {S : KS} where
  NoΩ : HB S → Set
  NoΩ hz = ⊤
  NoΩ (hs h) = NoΩ h
  NoΩ (hl f) = ∀ n → NoΩ (f n)
  NoΩ (hΩ _ _) = ⊥

module Sa (U : KS) (w : Wd U) (lw : LgW U w) (fb : HB U) where
  open TS U w lw fb

  san-noΩ : ∀ κ₀ (g : E U κ₀ → HB U) c → NoΩ (san (hΩ κ₀ g) c)
  san-noΩ κ₀ g hz = tt
  san-noΩ κ₀ g (hs c) = san-noΩ κ₀ g c
  san-noΩ κ₀ g (hl f) = λ n → san-noΩ κ₀ g (f n)
  san-noΩ κ₀ g (hΩ κ h) = tt

  tp-bot : ∀ κ (g : E U κ → HB U) → tpS (hΩ κ g) ≡ ι {E U κ} {λ e → Tw U (g e)} (bot U κ) (tpS (g (bot U κ)))
  tp-bot κ g = refl
```

## §3 `rk-⊲` 不是上界

**`Rk` 的前提对每个单独的世界都成立.** $U=$ `step S⊥`, 世界 $(\mathrm{tt}, B)$ 任取: 代表坐标取界 $B$. 所以 `rk-⊲` 对会移动的世界 (`LHRec` 的 `J₁`) 的每个世界也成立; 分开 "固定世界" 与 "移动世界" 的不是这条定理, 是 `rk` 依赖世界 (`rk-wdep`). 它只说高度序, 与折叠的值无关.

```agda
module RW (B : Cd) (lB : LgB B) where
  U₁ : KS
  U₁ = step S⊥

  pk₁ : (κ : K U₁) → E U₁ κ
  pk₁ (inj₁ ())
  pk₁ (inj₂ _) = B

  pkb₁ : ∀ κ → Bd U₁ κ (pk₁ κ) (tt , B)
  pkb₁ (inj₁ ())
  pkb₁ (inj₂ _) = hself

  top₁ : ∀ κ e → Bd U₁ κ e (tt , B) → Pr U₁ κ (tt , B) e (pk₁ κ)
  top₁ (inj₁ ()) e b
  top₁ (inj₂ _) e b = b

  open Rk U₁ (tt , B) (tt , lB) pk₁ pkb₁ top₁ public

Ω₁ : HB (step S⊥)
Ω₁ = hΩ (inj₂ tt) up

num : ∀ {S} → ℕ → HB S
num zero = hz
num (suc n) = hs (num n)


rk-wdep : RW.rk (num 1) tt Ω₁ ≡ num 1 × RW.rk (num 2) tt Ω₁ ≡ num 2
rk-wdep = refl , refl
```

**一站里走到的分量被 `B` 的 `rk` 界住 (推论).** 跨底折叠走到第 $c$ 个分量时有证据 $c+1\lhd_w B$ (`EvX`), 所以 `rk` $(c+1)\lhd$ `rk B`. 这是高度的界, 不是输出的界.

```agda
comp-rk : ∀ c₀ lc₀ n {c B} → _⊲[_]_ {Sb n} (hs c) (W.wS c₀ lc₀ n) B → LgB B →
  Stage.rk c₀ lc₀ n (hs c) ⊲ Stage.rk c₀ lc₀ n B
comp-rk c₀ lc₀ n {B = B} p l = Stage.rk-⊲ c₀ lc₀ n B p l
```

**第一步回灌后的 `rk`.** 世界的第 $0$ 层的界取 $1$. 第 $n$ 个底的地板经 $1\boxplus\mathrm{leg}$ 后, `rk` 是 $1$ ($n=1,\dots,4$, `refl`): 坐标里的结点全在代表坐标处取值, 地板对 `rk` 没有贡献.

```agda
rk₁ : ∀ n → HB (Sb n) → Cd
rk₁ n = Stage.rk (hs hz) tt n

first-rk : (rk₁ 1 (hs hz ⊞ legS 1 (fl 1)) ≡ num 1) × (rk₁ 2 (hs hz ⊞ legS 2 (fl 2)) ≡ num 1) ×
           (rk₁ 3 (hs hz ⊞ legS 3 (fl 3)) ≡ num 1) × (rk₁ 4 (hs hz ⊞ legS 4 (fl 4)) ≡ num 1)
first-rk = refl , refl , refl , refl
```

## 结论 (按档)

- **[定理, 形状]** `TΛ-shape`, `yΛ-succ`, `G.root-same`, `G.pick-same`, `G.pick-keep`, `G.old-pk`, `G.old-const`, `G.gtX-Ω`, `Sa.san-noΩ`, `Sa.tp-bot`; `first-rk` ($n\leq4$).
- **[定理]** `cert-std`; `comp-rk`; `RW.rk-⊲` (每个世界), `rk-wdep`.
- **[定理, 否定]** `G.ΦX-acc`.
- **[读文件]** `ThirdTm` 不引用 `flΛ`.
- **[判断]** 决定的读法正确性; "$\Omega$-结点只通过一支起作用" 对闭项值的后果; 读法.
- **[未得到]** 值的上界与下界.
