# 高度坐标的共享槽 (三): 分层互递归塔里每站的深拷贝

> 不含记号. 入口 [Slot](Slot.lagda.md). 只读导入 [StratTwTw](StratTwTw.lagda.md) (`P`, `X`, `C`, `U`, `QF`, `st`, `GU`, `genC`) 与否定一路的旧文件 [NegStratTwDeep](NegStratTwDeep.lagda.md) (`κd`, `b₁`, `a₁`, `Cp.kup`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> `StratTwTw` 的第 $s+1$ 站的级是 $X_{s+1}=a_s\boxplus B_s$, $a_s=\mathrm{hs}\,(\iota_{\mathrm l}\,X_s)$, $B_s=\iota_{\mathrm r}(\mathrm{ev}\,X_s)$ (**定义相等**, `nxtS` 的写法). 所以总结构 $U$ 的分量 $s+2$ (`C (s+2) = step (Lev (X (s+1)))`) 的旧种类里, 有 `Lev a_s` 的新种类 (坐标 `HB (Lev (ι_l X_s))`, 是高度) 沿 $B_s$ 的一切路径的拷贝; 路径经过 $B_s$ 的 $\Omega$-结点, 下标是坐标 (含函数). [NegStratTwDeep](NegStratTwDeep.lagda.md) 的 `κd c` 是 $s=0$ 时沿坐标 $c$ 再走最小坐标支的那一份.
>
> - **`slotU s`** (构造): 这一族在 $U$ 上的共享槽, 槽是 `Lev a_s` 与它的新种类.
> - **`famU s`** (构造): 一族一起满足 `RsK` (`KLv` 的三条升界律), 世界带证据 `ShW (slotU s)`, **对一切 $s$**, 不判定下标. `ev0U s`: 证据在 $U$ 的基世界上有实例.
> - **`κd≡`, `κd-rs`** (定理, 构造): `NegStratTwDeep.κd c` 是这一族 ($s=0$) 的成员; 于是每个 `κd c` 有 `RsK`. 那里证了逐份升撞分离子 (`updD-sep`), 并写 "一起升 (`halfR`) 未被否定也未构造"; 这里是带 `KLv` 升界律的一起升.
> - **`κd-other`** (定理, 值): 升 `κd c` 到 $v$ 后, 每个 `κd c′` 的顶都是 $v$ (经搬运): 一起升的代价.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SlotTw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; tpK; w₀)
open import OCF.Align.GenFoldInst using (genLev)
open import OCF.Align.KindLvEv using (evK)
open import OCF.Align.StratTwTw using (P; X; C; U; QF; st; GU; genC)
import OCF.Align.NegStratTwDeep as ND
open import OCF.Align.RsOwnIf using (RsK; subW; topSub)
open import OCF.Align.SlotIf
open import OCF.Align.SlotGen using (module Gen)
open import OCF.Align.SlotCp
```

## §1 每站的级拆成 $a_s\boxplus B_s$

```agda
a′ : ∀ s → HB (P (suc s))
a′ s = ι {⊤ ⊎ ⊤} {QF (st s)} (inj₁ tt) (X s)

aS : ∀ s → HB (P (suc s))
aS s = hs (a′ s)

BS : ∀ s → HB (P (suc s))
BS s = ι {⊤ ⊎ ⊤} {QF (st s)} (inj₂ tt) (evK (X s))

X≡ : ∀ s → X (suc s) ≡ aS s ⊞ BS s
X≡ s = refl
```

## §2 $U$ 上的共享槽与一起升

```agda
memU : ∀ s → Path (BS s) → K U
memU s p = suc (suc s) , inj₁ (Cp.kupP (aS s) (inj₂ tt) (BS s) p)

slotU : ∀ s → Slot U (tpK GU) (Path (BS s)) (memU s) (Lev (aS s)) (tpK (genLev (aS s))) (inj₂ tt)
slotU s = supℕSlot C (λ i → tpK (genC i)) (suc (suc s)) (stepSlot (CpNew.SN (a′ s) (BS s)))

ev0U : ∀ s → ShW (slotU s) (w₀ GU)
ev0U s = w₀ (genLev (aS s)) , Cp.al0 (aS s) (inj₂ tt) (BS s)

module GU′ (s : ℕ) = Gen (slotU s) (rsNew (a′ s))

famU : ∀ s → RsFam (subW U (ShW (slotU s))) (topSub (tpK GU)) (Path (BS s)) (memU s)
famU s = GU′.famS s

-- 成员的坐标经搬运是 HB (Lev (a′ s)) 的高度
coordU : ∀ s p → E U (memU s p) → HB (Lev (a′ s))
coordU s p = cE (slotU s) p
```

## §3 `NegStratTwDeep.κd` 是成员

```agda
open ND.Cp ND.a₁ using (kup)

kup≡ : ∀ (b : HB (P 1)) → Cp.kupP (aS 0) (inj₂ tt) b (Cp.botP (aS 0) (inj₂ tt) b) ≡ kup b (inj₂ tt)
kup≡ hz = refl
kup≡ (hs b) = cong inj₁ (kup≡ b)
kup≡ (hl f) = cong (λ k → 0 , k) (kup≡ (f 0))
kup≡ (hΩ κ′ g) = cong (λ k → bot (P 1) κ′ , k) (kup≡ (g (bot (P 1) κ′)))

pd : HB (step S₀) → Path (BS 0)
pd c = c , Cp.botP (aS 0) (inj₂ tt) (ND.b₁ c)

κd≡ : ∀ c → memU 0 (pd c) ≡ ND.κd c
κd≡ c = cong (λ k → 2 , inj₁ (c , k)) (kup≡ (ND.b₁ c))

κd-rs : ∀ c → RsK (subW U (ShW (slotU 0))) (topSub (tpK GU)) (ND.κd c)
κd-rs c = subst (RsK (subW U (ShW (slotU 0))) (topSub (tpK GU))) (κd≡ c) (famU 0 (pd c))

-- 一起升的代价: 升 κd c 之后, 每个 κd c′ 的顶经搬运都是 v 经搬运
κd-other : ∀ c c′ (w : Wd U) (p : ShW (slotU 0) w) v →
  cE (slotU 0) (pd c′) (top (tpK GU) (memU 0 (pd c′)) (GU′.rsW 0 (pd c) w p v)) ≡ cE (slotU 0) (pd c) v
κd-other c c′ w p v = GU′.rs-same 0 (pd c) (pd c′) w p v
```

## §4 结论 (按档)

- **[构造]** `slotU`, **`famU`** (对一切 $s$), **`κd-rs`** (对一切坐标 $c$).
- **[定理]** `X≡` (`refl`), `ev0U` (证据的实例), `kup≡`, `κd≡`, `κd-other`.
- **[判断]** `famU s` 只覆盖 $U$ 的分量 $s+2$ 里**拷贝**来的深种类 (`Lev a_s` 的新种类沿 $B_s$ 的路径). 同一分量里 $B_s$ 自己的 `step` 产生的新种类 (坐标 `HB (Lev (a_s ⊞ y))`, $y$ 随路径变) 不是拷贝, 坐标类型随下标变, 与 `K₁` 的 `κHc` 同型 ([SlotKH](SlotKH.lagda.md)); 本篇对它们没有构造.
- **[判断]** 本篇没有把 `famU` 接进 `StratTwTw` 的折叠: 那要 (i) 拷贝的读回 `rd` (坐标 `HB (Lev (ι_l X_s))`, 与头种类 `hd s` 的坐标 `HB (Lev (X s))` 不定义相等, 要一层搬运), (ii) `KA`, `KT s′` 在带证据的世界类型上保证据 (`KT (s+1)` 只改分量 $s+2$ 的第二分量, 保证据; 其余在别的分量上, 要 `upd` 的分量不等引理). 都没写.
