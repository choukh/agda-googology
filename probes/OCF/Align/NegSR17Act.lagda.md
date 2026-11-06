# 第十七轮的否定 (三): 动作限制 `ActNZ` 与折叠实际用到的动作

> 不读记号. 入口 [NegSR17](NegSR17.lagda.md). 对着接口 [StrRel17If](StrRel17If.lagda.md) (定稿 2026-11-05 12:12) §4 写. 实例 $\Lambda_2=2$.
>
> 1. **(定理, 正面) `actNZ-Act`**: 闭项的动作 `Act` 满足 `ActNZ` (第 $0$ 层输出 $\omega\cdot(1⨾\ldots)$).
> 2. **(定理, 正面) `lead-run`, `actNZ-Ai`**: 节点的分支一律以 `n1` 开头 (`Lead1`, 例如 `Ωd` 里的节点, 分支是 `n1`) 时, 分支动作 `Ai` 继承 `ActNZ`. `Kp`, `Kb`, `Walk`, `BNi` 用的是 `Ig↾ p A₀`, 它对 `ActNZ` 的继承是定义性的 (`actNZ-Ai` 的证明里那一步).
> 3. **(否定) `¬actNZ-kept`, `¬keptNZ`**: `ActNZ` 只约束第 $0$ 层目标上的输出. 一对满足 `HAWᴺ` 的产生时动作 (`AL`: 第 $0$ 层输出 `n1`, 别的层输出 `n0`; 右边 `C1`, `hawL`) 下, 节点 `r₀` (层 $\Lambda_2$, 坐标层 $0$, 分支 `n1`) 在 $T_1$ 上保留, 保留输出的节点的分支定义性地是 `n0` (`keptL`, `brZero`), 它的分支动作在**一切**再折叠动作下都违反 `ActNZ`. 所以 "产生时与再折叠时的动作都满足 `HAWᴺ` ⇒ 保留输出的分支动作满足 `ActNZ`" 不成立 (`¬keptNZ`, 再折叠动作取 `Act`).
>
> 4. **(定理, 正面) `zPos`**: `NKp` 的条件 (`Lead1` 的前一段, `ActNZ` 的动作) 下, `nκ` 运行时的第 $0$ 层累计字面地非零 (`Pos0`), 所以 `NegSR16Kap.Cells.cellZ` 的机制 (累计为空, 每一格都空) 被挡住.
>
> **构造一路为什么需要这条律.** `SemXᴺ` 只对 `HAWᴺ` 的动作给结论. 节点的语义要沿链运行坐标层上的树, 用的动作是分支动作 `Ai` (`HtFeedFold.RKi` 的 rise 句); 保留的输出是一个新节点, 它日后被再折叠时, 链的动作是它的 `Ai`. 若要在这些链里用 `NKp` (修补后的 "ni 对 nκ"), 就要这些 `Ai` 满足 `ActNZ`. 第 3 条说: 以 `HAWᴺ` 为动作前提的语义, 不能把限制传到保留输出的分支动作上; 要么限制写成对一切层的输出 (那要另看 `HAW²⁺` 的跨层对), 要么只对 `Act` 产生的折叠用 (第 1, 2 条: 那时成立).
>
> **只否定什么.** 只否定限制的这一条封闭律 (`KeptNZ`). 不否定 `NKp` (没有找到值的反例, 见入口 §4), 不说违反限制的那一边会造成值的错误 (判断: 分支为 `n0` 的一边在第 $0$ 层的输出全为零, 值上只会更小; 这是证明结构上的缺口, 不是值的反例). 不说限制是空的: `Act` 与 `Lead1` 分支的 `Ai` 满足它 (第 1, 2 条). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `hawL` (定理), `actNZ-Act tt`, 状态 $Y_1$; `¬actNZ-kept` 对一切状态与再折叠动作.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR17Act where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; Vs; outS; ⊲ᴴ↑; hz; hs; hl; hΩ; hself; hsuc; ss; StH; D; n0; n1; _⨾_; ni; accL; AccY)
open import OCF.Align.StrRel13Val using (Λ₂; r₀)
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
import OCF.Align.StrRel16If as If³
import OCF.Align.StrRel17If as If⁴

open FinΛ⁺ Λ₂ tt tt using (Y₁)
open If³ Λ₂ tt using (module P; RelX⁺; n0⁺; n1⁺)
open If⁴ Λ₂ tt using (ActNZ; HAWᴺ; Pos0; p1; pE; pL; Lead1)
open P using (Tg; tg; wm; tm; τ₀; St; df; yc; Run; Ig; Act; Ai; RKi; keep; kk)
```

## 1 `Act` 满足限制

```agda
-- Act 满足限制
actNZ-Act : ∀ {L W} (lW : Lg W) → ActNZ {L} {W} lW Act
actNZ-Act lW p lW₁ w Y = pE (pL p1)
```

## 2 一对满足 `HAWᴺ` 的产生时动作

```agda
-- 第 0 层输出 n1, 别的层输出 n0 的动作: 满足 HAWᴺ (右边取常数 n1)
lowOnly : ∀ t {m} → D t m
lowOnly hz = n1
lowOnly (hs b) = n0
lowOnly (hl f) = n0
lowOnly (hΩ g) = n0

one : ∀ t {m} → D t m
one t = n1

AL C1 : ∀ {L W} → Ig L W
AL p l w Y = df (λ {t} T → lowOnly t)
C1 p l w Y = df (λ T → n1)

hawL : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAWᴺ L L′ lW lW′ (AL {L} {W}) (C1 {L′} {W′})
hawL L L′ = (λ p p′ l l′ cp w w′ hw Y Y′ hY {t} T T′ tx → go t) , ((λ p l w Y → p1) , (λ p l w Y → p1))
  where
  go : ∀ t {t′ m m′} {lm : Lg m} {lm′ : Lg m′} → RelX⁺ t t′ lm lm′ (lowOnly t {m}) (one t′ {m′})
  go hz = n1⁺
  go (hs b) = n0⁺
  go (hl f) = n0⁺
  go (hΩ g) = n0⁺
```

## 3 `Lead1` 分支: 分支动作继承限制

```agda
-- Lead1 的分支: 分支动作继承限制 (一切 Λ 的同一证明, 这里写在 Λ₂ 上)
lead-run : ∀ {L W V} (ac : AccY L) (x : D L V) (q : V ⊲ W) (lW : Lg W) (ll : P.LW L W) (A₀ : Ig L W) (w : D L W) (Y : St W) →
           Lead1 x → ActNZ lW A₀ → Pos0 (yc (Run ac x q lW ll A₀ w Y) (τ₀ lW))
lead-run ac n1 q lW ll A₀ w Y If⁴.l1 h = h C.self lW w Y
lead-run ac (x ⨾ y) q lW ll A₀ w Y (If⁴.lL l) h = pL (lead-run ac x q lW ll A₀ w Y l h)

actNZ-Ai : ∀ {ly W₀ W k} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
             (q₀ : W₀ ⊲ W) (hk : P.LW k W) (ll : P.LW ly W) (A₀ : Ig ly W) (w : D ly W) (lW : Lg W) →
           (∀ {W′} (p : W₀ ⊲ W′) (l : Lg W′) y → Lead1 (u p l y)) → ActNZ lW A₀ → ActNZ lW (Ai ac ac′ r u q₀ hk ll A₀ w)
actNZ-Ai ac ac′ r u q₀ hk ll A₀ w lW hu h p lW₁ z Y =
  lead-run ac _ C.self lW₁ (⊲ᴴ↑ p ll) (P.Ig↾ p A₀) _ Y (hu _ lW₁ _) (λ p′ l′ w′ Y′ → h (⊲-tr p p′) l′ w′ Y′)
```

## 4 保留输出的分支

```agda
-- 产生时动作对 (AL, C1) 满足 HAWᴺ; 节点 r₀ 在 T₁ 上保留, 输出节点的分支定义性地是 n0
uN : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
uN _ _ _ = n1

rk1 : StH azero hz (hs hz)
rk1 = ss hself

BRL : P.St azero → ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs (hs hz) rk1 W′ → D (hs hz) W′
BRL Y p lW′ y = yc (P.BNi (accL Λ₂) (accL hz) r₀ uN C.self hself AL n0 Y (kk r₀ C.self hself) (⊲-tr (wm T₁) p) lW′ (outS rk1 y))
                   (tg C.self (⊲ᴴ↑ p (tm T₁)) lW′)

keptL : ∀ (Y : P.St azero) → RKi (accL Λ₂) (accL hz) r₀ uN C.self tt hself AL n0 Y T₁ (keep rk1) ≡ ni rk1 (BRL Y)
keptL Y = refl

brZero : ∀ (Y : P.St azero) {W′} (p : azero ⊲ W′) (l : Lg W′) y → BRL Y p l y ≡ n0
brZero Y p l y = refl
```

## 5 否定

```agda
-- 它的分支动作在一切再折叠动作下都违反限制
¬actNZ-kept : ∀ (Y : P.St azero) (A₀ : Ig (hs hz) azero) →
              ¬ ActNZ tt (Ai (accL (hs hz)) (accL hz) rk1 (BRL Y) C.self (kk rk1 C.self (hsuc hself)) (hsuc hself) A₀ n0)
¬actNZ-kept Y A₀ h with h C.self tt n0 P.Y₀
... | ()

-- 律的形状: "产生与再折叠的动作都满足 HAWᴺ ⇒ 保留输出的分支动作满足 ActNZ" 不成立
KeptNZ : Set
KeptNZ = ∀ (Y : P.St azero) (A₀ A₀′ : Ig Λ₂ azero) → HAWᴺ Λ₂ Λ₂ tt tt A₀ A₀′ →
         ∀ (B₀ : Ig (hs hz) azero) → ActNZ tt B₀ →
         ActNZ tt (Ai (accL (hs hz)) (accL hz) rk1
                     (λ p lW′ y → yc (P.BNi (accL Λ₂) (accL hz) r₀ uN C.self hself A₀ n0 Y (kk r₀ C.self hself) (⊲-tr (wm T₁) p) lW′ (outS rk1 y))
                                     (tg C.self (⊲ᴴ↑ p (tm T₁)) lW′))
                     C.self (kk rk1 C.self (hsuc hself)) (hsuc hself) B₀ n0)

¬keptNZ : ¬ KeptNZ
¬keptNZ h = ¬actNZ-kept (Y₁ tt) Act (h (Y₁ tt) AL C1 (hawL Λ₂ Λ₂) Act (actNZ-Act tt))
```
## 6 (正面) 修补的条件挡住了 `NegSR16` 的机制

`NegSR16Kap.Cells.cellZ` 的反例要 `nκ` 运行时第 $0$ 层累计为空 (第 $0$ 格不走). `NKp` 的条件 (右边 `nκ` 前一段 `Lead1`, 动作 `ActNZ`) 下, `nκ` 运行时的累计字面地非零: 它是 `z Y ⨾ (前一段在第 $0$ 层的输出)`, 后者由 `lead-run` 是 `Pos0`. 所以 `cellZ` 那种 "每一格都空" 不会发生 (第 $0$ 格走到 $W+z$, 至少一步). 这是 `NKp` 的设计意图的编译形式, 不是 `NKp` 的证明.

```agda
zPos : ∀ {L W V} (ac : AccY L) (x′ : D L V) (q : V ⊲ W) (lW : Lg W) (ll : P.LW L W) (A₀ : Ig L W) (w : D L W) (Y : St W) →
       Lead1 x′ → ActNZ lW A₀ → Pos0 (P.z (Y P.⊕⟨ lW ⟩ Run ac x′ q lW ll A₀ w Y))
zPos ac x′ q lW ll A₀ w Y l h = If⁴.pR (lead-run ac x′ q lW ll A₀ w Y l h)
```
