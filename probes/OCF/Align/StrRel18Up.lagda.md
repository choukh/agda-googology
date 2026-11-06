# 结构关系, 第十八轮 (四): `Up`: 只能是新关系; 最小实验的前一半; 第 $0$ 层的传递性归约为对齐路径对的横向复合

> 不读记号. 入口 [StrRel18](StrRel18.lagda.md). 接口 [StrRel18If](StrRel18If.lagda.md) §3. 实例 $\Lambda_2=2$, 一对是 `StrRel17Obs` 的障碍那一对 (`ReL` = `LaterL`, `ReR` = `keepO`; `riseO` = `LaterR`).
>
> 1. **(定理, 约化) `upX`**: 若 `RelX⁺` 自己对 `Up` 封闭 (`UpClosed`), 则 `RkLeft tt ReL`. 理由: `valLK⁺` 给 `ReL ≤ riseO`, `Up` 给 `ReL ≤ keepO`, 右边是节点, `invNi`. 所以 `Up` 不能靠证明 "`RelX⁺` 已对它封闭" 得到 (那就是第一个障碍本身), 只能是**新的关系** (`RelX⁺` 加一条构造子) 或新的关系族上的封闭性.
> 2. **(定理) `upHalf`, `upHalfV`**: 最小实验 (把障碍那一对 $(\mathrm{ReL},\mathrm{ReR})$ 以 `Act`, `n0`, $Y_1$ 再折叠一次, 在 $(\tau_0,\tau_0)$ 上比) 的前一半: `ReL` 的再折叠 $\le$ `riseO` 的再折叠 (`semX00⁺`, 第 $0$ 层对第 $0$ 层, 无条件). **(条件定理) `upExp`**: 加上缺的一半 `UpStep` (`riseO` 的再折叠 $\le$ `keepO` 的再折叠, 第 $0$ 层目标, `RelX⁺ hz hz`), 值的结论成立.
> 3. **(条件定理) `trans00`: `APH ⇒ Trans00`**; **(定理, 约化) `trans→APH₀`: `Trans00 ⇒ APH₀`.** 第 $0$ 层的 `RelX⁺` 的传递性, 恰好卡在 `nw⁺` 对 `nw⁺` 的那一种情形: 要对齐路径对 (`AP`) 能横向复合 (中间一条路径相同). 别的情形 (`n0`, `n1`, `⨾`, `nl`, `pr⁺`, `in⁺`) 由对推导的字典序归纳直接得到 (`comp`: 分量的推导).
>
> **第一个障碍 (判断, 依据折叠的字面, 未编译).** `UpStep` 是节点 `O` (`keepO` 与 `riseO` 共同的节点: 层 $1$, 坐标层 $0$, 分支 `CY.brR`) 的 "上升输出的再折叠 $\le$ 保留输出的再折叠 (再折叠时上升)", 即 `StrRel17Time.valT` 的形状, 只是节点从 `xL` (分支 `n1`) 换成 `O` (分支是 `BNi` 的输出, $\omega\cdot(\Omega_1⨾\ldots)$, 含坐标层 $0$ 的节点 $N$). `valT` 的四步证明在第 2 步用 `Z00.rr00`, 它要两个节点的分支动作满足 `HAW²⁺ hz hz`. 对 `O` 与 `keepO` 链里的节点 (保留后的 $N$), 两个分支动作都是 "以 `Act` 运行 $\omega\cdot(\Omega_1⨾\text{读数})$", 它们的 `HAW²⁺` 在目标对 $(\tau_0,T_1)$ 上要 "$N$ 的链极限 $\le$ 保留的 $N$", 只能由 `rk⁺` 给出, 而 `rk⁺` 的前提是**旧关系** (`StrRel16If` 文件头 "严格正性" 一段已写明的缺口), `HAW²⁺` 只提供新关系的输入. 所以 `UpStep` 卡在接口 `StrRel16If` 的严格正性缺口上, 不在 (a)(c) 上.
>
> **只否定什么.** 本文没有否定. `upX`, `trans→APH₀` 是约化. `APH` 是否成立没有判定 (判断: 它要 `Adm` 的横向复合, 即序数加法的左消去 $c'\oplus\delta_1\le c'\oplus\delta_2\Rightarrow\delta_1\le\delta_2$ 在布劳威尔树的 `≤` 上, 加 `Al` 的横向复合; 都没有试).
>
> **前提可满足.** `upHalf` 无前提. `upExp` 的前提 `UpStep` 没有实例 (它是缺的引理). `trans00` 的前提 `APH`: 没有实例, 也没有否定 (自反的实例 `ap-self` 只给中间为 `self` 的情形). `upX`: 前提 `UpClosed` 的可满足性等价于第一个障碍, 本文不判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18Up where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; z⊲ᴴ; D; D₀; n0; nw; accL; sum)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel12Al using (AP)
open import OCF.Align.StrRel13Val using (Λ₂; cp00)
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; LeX⁺; In; here; inL; inR; inE; n0⁺; n1⁺; ⨾⁺; nl⁺; pr⁺; nw⁺; ni⁺; κ⁺; in⁺; rk⁺; nκ⁺)
open import OCF.Align.StrRel16Sem Λ₂ tt using (semX00⁺)
open import OCF.Align.StrRel16Val using (LaterL; LaterR; valLK⁺)
open import OCF.Align.StrRel17Obs using (ReL; ReR; riseO; keepO; RkLeft; invNi; pick; module CY)
open import OCF.Align.StrRel18If Λ₂ tt using (UpClosed; Trans00)

open Rk Λ₂ tt using (s∞)
open FinΛ⁺ Λ₂ tt tt using (hawAct²⁺; Y₁; hY₁⁺)
open V0 Λ₂ tt using (vsum⁺)
module P = At Λ₂ tt
open P using (St; yc; Run; Act; τ₀; keep)
```

## 1 `RelX⁺` 自己对 `Up` 封闭 ⇒ 第一个障碍

```agda
Y1 : St azero
Y1 = Y₁ tt

upX : UpClosed (λ L L′ → RelX⁺ L L′) → RkLeft tt ReL
upX up = pick (invNi (up {x = LaterL} (ss hself) {u = CY.brR} tt (accL (hs hz)) (accL hz) C.self (hsuc hself) Act n0 Y1
                          (τ₀ tt) T₁ (ss hself) refl refl valLK⁺))
```

## 2 最小实验

```agda
ReL₂ riseO₂ ReR₂ : D₀ azero
ReL₂ = yc (Run (accL hz) ReL C.self tt (z⊲ᴴ Λ₂) Act n0 Y1) (τ₀ tt)
riseO₂ = yc (Run (accL hz) riseO C.self tt (z⊲ᴴ Λ₂) Act n0 Y1) (τ₀ tt)
ReR₂ = yc (Run (accL (hs hz)) ReR C.self tt (hsuc hself) Act n0 Y1) (τ₀ tt)

-- 前一半: ReL ≤ riseO (valLK⁺) 有第 0 层的语义
upHalf : RelX⁺ hz hz tt tt ReL₂ riseO₂
upHalf = semX00⁺ valLK⁺ tt tt (accL hz) (accL hz) (z⊲ᴴ Λ₂) (z⊲ᴴ Λ₂) C.self C.self cp00 Act Act (hawAct²⁺ hz hz)
           n0 n0 n0⁺ Y1 Y1 (hY₁⁺ tt tt) (τ₀ tt) (τ₀ tt) (cp00 , s∞)

upHalfV : sum azero ReL₂ ≤ sum azero riseO₂
upHalfV = vsum⁺ upHalf (≤-refl azero)

-- 缺的一半 (节点 O 的上升输出的再折叠 ≤ 保留输出的再折叠)
UpStep : Set
UpStep = RelX⁺ hz hz tt tt riseO₂ ReR₂

upExp : UpStep → sum azero ReL₂ ≤ sum azero ReR₂
upExp h = ≤-trans upHalfV (vsum⁺ h (≤-refl azero))
```

## 3 第 $0$ 层的传递性

`APH`: 对齐路径对的横向复合 (中间的路径 $p'$ 相同; 中间世界的 `Lg` 证明可以只是命题相等).

```agda
APH : Set
APH = ∀ {V₀ V₀′ V₀″ V V′ V″} {l₀ : Lg V₀} {l₀′ k₀′ : Lg V₀′} {l₀″ : Lg V₀″} {l : Lg V} {l′ k′ : Lg V′} {l″ : Lg V″}
        {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′} {p″ : V₀″ ⊲ V″} →
      AP l₀ l₀′ p l p′ l′ → AP k₀′ l₀″ p′ k′ p″ l″ → l′ ≡ k′ → AP l₀ l₀″ p l p″ l″

APH₀ : Set
APH₀ = ∀ {V₀ V₀′ V₀″ V V′ V″} {l₀ : Lg V₀} {l₀′ : Lg V₀′} {l₀″ : Lg V₀″} {l : Lg V} {l′ : Lg V′} {l″ : Lg V″}
         {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′} {p″ : V₀″ ⊲ V″} →
       AP l₀ l₀′ p l p′ l′ → AP l₀′ l₀″ p′ l′ p″ l″ → Σ (Lg V₀) (λ m₀ → Σ (Lg V₀″) (λ m₀″ → AP m₀ m₀″ p l p″ l″))
```

分量的推导: $y_0$ 是 $y$ 的分量, $y\le z$ ⇒ $y_0\le z$.

```agda
comp : ∀ {V V″} {l : Lg V} {l″ : Lg V″} {y₀ y : D₀ V} {x″ : D₀ V″} → In y₀ y → RelX⁺ hz hz l l″ y x″ → RelX⁺ hz hz l l″ y₀ x″
comp here d = d
comp i (pr⁺ d) = pr⁺ (comp i d)
comp i (in⁺ d j) = in⁺ (comp i d) j
comp (inL i) (⨾⁺ a b) = in⁺ (comp i a) (inL here)
comp (inR i) (⨾⁺ a b) = in⁺ (comp i b) (inR here)
comp (inE n i) (nl⁺ f) = in⁺ (comp i (f n)) (inE n here)
comp i (rk⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _)
```

传递性, 以 `APH` 为前提. 中间世界的 `Lg` 证明带一条命题相等 (`nw⁺` 的分支世界的 `Lg` 证明不在结论里).

```agda
module Tr (aph : APH) where
  tr : ∀ {V V′ V″} {l : Lg V} {l′ k′ : Lg V′} {l″ : Lg V″} {x : D₀ V} {y : D₀ V′} {x″ : D₀ V″} →
       RelX⁺ hz hz l l′ x y → RelX⁺ hz hz k′ l″ y x″ → l′ ≡ k′ → RelX⁺ hz hz l l″ x x″
  tr n0⁺ d e = n0⁺
  tr d (pr⁺ d′) e = pr⁺ (tr d d′ e)
  tr d (in⁺ d′ j) e = in⁺ (tr d d′ e) j
  tr (pr⁺ d) d′ e = tr d (comp (inL here) d′) e
  tr (in⁺ d i) d′ e = tr d (comp i d′) e
  tr n1⁺ n1⁺ e = n1⁺
  tr (⨾⁺ a b) (⨾⁺ c c′) e = ⨾⁺ (tr a c e) (tr b c′ e)
  tr (nl⁺ f) (nl⁺ g) e = nl⁺ (λ n → tr (f n) (g n) e)
  tr {l′ = l′} {k′} (nw⁺ {lV₀′ = m′} {p′ = p′} ap d) (nw⁺ {lV₀ = k₀} ap′ d′) e =
    nw⁺ (aph ap ap′ e) (tr d d′ (trans (proj₂ (proj₂ (proj₂ ap))) (trans (cong (lg⊲ p′) e) (sym (proj₁ (proj₂ (proj₂ ap′)))))))
  tr (ni⁺ {r = ()} _ _) d′ e
  tr (κ⁺ {zz = ()} _) d′ e
  tr (nκ⁺ {r = ()} _) d′ e
  tr (rk⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _) d′ e
  tr d (rk⁺ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ () _ _ _ _) e

trans00 : APH → Trans00
trans00 aph d d′ = Tr.tr aph d d′ refl
```

反方向: 传递性推出 `nw` 对 `nw` 的横向复合.

```agda
invNw : ∀ {V₀ V₀″ V V″} {l : Lg V} {l″ : Lg V″} {p : V₀ ⊲ V} {p″ : V₀″ ⊲ V″} {x : D₀ V₀} {x″ : D₀ V₀″} →
        RelX⁺ hz hz l l″ (nw p x) (nw p″ x″) → Σ (Lg V₀) (λ m₀ → Σ (Lg V₀″) (λ m₀″ → AP m₀ m₀″ p l p″ l″))
invNw (nw⁺ ap d) = _ , _ , ap
invNw (in⁺ d here) = invNw d

trans→APH₀ : Trans00 → APH₀
trans→APH₀ t {l₀ = l₀} {l₀′} {l₀″} ap ap′ = invNw (t (nw⁺ {lV₀ = l₀} {lV₀′ = l₀′} {x = n0} {x′ = n0} ap n0⁺) (nw⁺ {lV₀ = l₀′} {lV₀′ = l₀″} {x′ = n0} ap′ n0⁺))
```
