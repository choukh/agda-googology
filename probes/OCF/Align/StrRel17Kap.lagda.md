# 结构关系, 第十七轮 (四): "ni 对 nκ" 的修补: 排除已知反例; 一个实例上的值

> 不读记号. 入口 [StrRel17](StrRel17.lagda.md). 接口 [StrRel17If](StrRel17If.lagda.md) §4. 实例 $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$ (`NegSR16Kap`).
>
> 1. **(定理) `actNZ`**: 闭项的动作 `Act` 属于 `ActNZ` (一切 $\Lambda$, 一切世界). **(定理) `¬azNZ`, `¬hawᴺAz`**: `NegSR16Kap.Az` 不属于 (在状态 `YN` 上输出零), 所以 `NegSR16Sem.¬semΩ` 的动作不满足修补后的动作前提 `HAWᴺ`.
> 2. **(定理) `lead1Ω`**: 一切 $\Omega_L$ (`Ωd L`) 以 `n1` 开头; **`¬lead1κ`**: `NegSR16Kap.xK` (`nκ` 本身) 不以 `n1` 开头. 修补后的规则 `NKp` 的结论形如 $x⨾\text{节点}\le x'⨾\mathrm{n\kappa}$, `NegSR16Sem.¬semNK` 的那一对 (`xN` 对 `xK`) 不是这个形状.
> 3. **(定理, 值) `nkpΩ`: 修补的规则在本来要的那一对上, 第 $0$ 层目标上值成立.** $\Omega_1$ (`Ωd 1`) 对 $\Omega_{\Lambda_\kappa}$ (`Ωd Λκ`), 动作 `Act`, 上下文 `n0`, 状态 `YN`, 世界 $0$, 路径 `self`: 对一切底 $\beta\le\beta'$, $\Sigma_\beta(\text{左})\le\Sigma_{\beta'}(\text{右})$. 这是 `NegSR16` 说 "不否定" 的那一种 (动作 `Act`, 累计非空).
>
> **`nkpΩ` 的证明 (每一步是编译的定理).** 左边是 $\mathrm{Step}\,\mathrm{YN}⨾\nu$, $\nu$ 是 $\Omega_1$ 的节点 $N$ (坐标层 $0$) 在状态 $\mathrm{YN}\oplus\mathrm{Step}\,\mathrm{YN}$ 上的上升输出. 右边是 $\mathrm{Step}\,\mathrm{YN}⨾$ (`nκ` 的回灌). 开头的 `n1` 让累计非空, 回灌的第 $0$ 格的世界 $v=\Sigma_0(\text{累计})$ 是一个极限; 第 $0$ 格在世界 $0$ 上运行分支 (坐标层 $1$ 的节点 $u_0$), 它在第 $0$ 层目标上上升, 链的第一项是换世界之后的状态在第 $1$ 层上的读数, 读数里的 $\Omega_1$ 又含一个坐标层 $0$ 的节点 $N'$. 由 `StrRel16Node.Z00.rr00` (两个坐标层都是 $0$), $\nu\le$ ($N'$ 的上升输出); 状态前提 `domN` 由 "换世界之后读数不变 (`Laterᵈ`)" 与 $N'$ 之前的那个 `n1` 给出. 再沿分量走到回灌的第 $0$ 格 (`inSum`), `drp` 不减和 (`sum-drp`).
>
> **范围.** 一个实例, 一组运行参数, 一个目标对 $(\tau_0,\tau_0)$, 只比值. 不是 `NKp`, 也不是 `NKpV` (那要对一切满足前提的 $x$, 节点, 分支, 一切 `ActNZ` 动作与 `J²⁺` 状态).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel17Kap where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ; YN; Az; xK; llN)
open import OCF.Align.StrRel17If Λκ lΛκ using (Pos0; p1; pL; pR; pE; pW; Lead1; l1; lL; ActNZ; HAWᴺ; Laterᵈ)

module P = At Λκ lΛκ
open P using (Tg; tg; tm; τ₀; St; st; Df; df; d; z; yc; Run; Act; Step; Ig; cv; _⊕⟨_⟩_)
```

## 1 动作与开头

```agda
-- 闭项的动作 (一切 Λ) 在第 0 层目标上输出 ω⋅(1 ⨾ …)
module AllΛ (Λ′ : H) (lΛ′ : LgH Λ′) where
  open import OCF.Align.StrRel17If Λ′ lΛ′ using () renaming (ActNZ to ActNZ′; Lead1 to Lead1′; pE to pE′; pL to pL′; p1 to p1′;
    l1 to l1′; lL to lL′)
  module Q = At Λ′ lΛ′

  actNZ : ∀ {L W} (lW : Lg W) → ActNZ′ lW (Q.Act {L} {W})
  actNZ lW p lW₁ w Y = pE′ (pL′ p1′)

  lead1Ω : ∀ L {W} → Lead1′ (Ωd L {W})
  lead1Ω hz = l1′
  lead1Ω (hs b) = lL′ l1′
  lead1Ω (hl f) = lL′ l1′
  lead1Ω (hΩ g) = lL′ l1′

-- Az 在 YN 上输出零
¬azNZ : ¬ ActNZ {hs hz} {azero} tt Az
¬azNZ h with h C.self tt n0 YN
... | ()

¬hawᴺAz : ¬ HAWᴺ (hs hz) Λκ {azero} {azero} tt tt Az Az
¬hawᴺAz (_ , (h , _)) = ¬azNZ h

¬lead1κ : ¬ Lead1 xK
¬lead1κ ()
```

## 2 实例: $\Omega_1$ 对 $\Omega_{\Lambda_\kappa}$, 动作 `Act`, 状态 `YN`

```agda
open import OCF.Align.StrRel11Rk Λκ lΛκ using (s∞)
open import OCF.Align.StrRel12Al using (CP; cp-self)
open import OCF.Align.StrRel12Rel using (cohSum)
open import OCF.Align.StrRel14J Λκ lΛκ using (NE; Lf; ne⊕) renaming (here to lfHere; left to lfLeft)
open import OCF.Align.StrRel16If Λκ lΛκ using (RelX⁺; J²⁺; n0⁺; n1⁺; ⨾⁺; nl⁺; pr⁺; In; here; inL; inR; inE)
open import OCF.Align.StrRel16Lem using (Lp; here; left; module Pf)
open import OCF.Align.StrRel16Sem Λκ lΛκ using (lp→rel⁺)
open import OCF.Align.StrRel16Node Λκ lΛκ using (module Z00)
open import OCF.Align.NegSR16Sem using (jN⁺; stepOA⁺; ΩXκ; vsum⁺; inSum; sum-mono)
open Pf Λκ lΛκ using (lp-lf)

lp-tr : ∀ {t m} {a b c : D t m} → Lp a b → Lp b c → Lp a c
lp-tr p here = p
lp-tr p (left q) = left (lp-tr p q)

-- drp 不减和
≤drp : ∀ {W W′} b (x : D₀ W) → sum b x ≤ sum b (drp {W} {W′} x)
≤pt  : ∀ {W W′} b (e : ℕ → D₀ W) n → pt b e n ≤ pt b (λ k → drp {W} {W′} (e k)) n
mono′ : ∀ {W} (x : D₀ W) {b b′} → b ≤ b′ → sum b x ≤ sum b′ x
mono′ x h = sum-mono x h
≤drp b n0 = ≤-refl b
≤drp b n1 = ≤-refl (asuc b)
≤drp {W′ = W′} b (x ⨾ y) = ≤-trans (≤drp {W′ = W′} (sum b x) y) (mono′ (drp y) (≤drp {W′ = W′} b x))
≤drp {W′ = W′} b (nl e) = l≤ (λ n → ≤l n (≤pt {W′ = W′} b e n))
≤drp b (ni () u)
≤drp b (nκ () u)
≤drp {W′ = W′} b (nw p x) = ≤drp {W′ = W′} b x
≤pt b e zero = ≤-refl b
≤pt {W′ = W′} b e (suc n) = ≤-trans (≤drp {W′ = W′} (pt b e n) (e n)) (mono′ (drp (e n)) (≤pt {W′ = W′} b e n))

Y1′ : St azero
Y1′ = YN ⊕⟨ tt ⟩ Step YN

LeftO RightO : D₀ azero
LeftO = yc (Run (accL (hs hz)) (Ωd (hs hz)) C.self tt llN Act n0 YN) (τ₀ tt)
RightO = yc (Run (accL Λκ) (Ωd Λκ) C.self tt hself Act n0 YN) (τ₀ tt)

-- 回灌第 0 格的世界: 运行世界 0 加上累计
zY : D₀ azero
zY = z Y1′

v : A
v = sum azero zY

lv : Lg v
lv = Lg-sum azero zY tt

sf : azero ⊲ v
sf = sum-fst azero zY

cpTop : CP {V = azero} {V′ = v} tt lv C.self tt C.self lv
cpTop = cp-self tt lv z≤ tt (cohSum azero zY tt tt)

-- 换世界后读数不变 (Laterᵈ) 的状态, 再经一个 n1, 支配 YN ⊕ Step YN
neL : (S : St v) → Laterᵈ sf Y1′ S → NE S
neL S lat T = n0 , lp-lf (lfLeft lfHere) (lat T)

domN : (S : St v) → Laterᵈ sf Y1′ S → J²⁺ tt lv Y1′ (S ⊕⟨ lv ⟩ Step S)
domN S lat =
  ((λ T T′ tx → ⨾⁺ (Rd T T′ tx) (nl⁺ (λ _ → ⨾⁺ (ΩXκ (tm T) (tm T′) (proj₂ tx)) (Rd T T′ tx)))) ,
   ⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ (Rd (τ₀ tt) (τ₀ lv) (cpTop , s∞))))) ,
  (ne⊕ {lW = tt} YN (Step YN) (λ T → n0 , lfHere) , ne⊕ {lW = lv} S (Step S) (neL S lat))
  where
  Rd : ∀ {t t′ m m′} (T : Tg azero t m) (T′ : Tg v t′ m′) → _ → RelX⁺ t t′ (P.lm T) (P.lm T′) (yc (d YN) T) (yc (d S) T′)
  Rd T T′ tx = lp→rel⁺ (proj₁ (proj₁ (jN⁺ {lW = tt} {lW′ = lv})) T T′ tx) (lp-tr (left here) (lat T′))
```

`nkpΩ`: 左边 $\nu$ 不超过回灌第 $0$ 格里 $N'$ 的上升输出 (`rr00`), 后者是第 $0$ 格的分量, 第 $0$ 格经 `drp` 是回灌的第 $0$ 项.

```agda
viaL : ∀ {W} β (a x : D₀ W) {c} → sum (sum β a) x ≤ c → sum β (a ⨾ x) ≤ c
viaL β a x h = h

viaR : ∀ {W} β (a x : D₀ W) {c} → c ≤ sum (sum β a) x → c ≤ sum β (a ⨾ x)
viaR β a x h = h

nkpΩ : ∀ β β′ → β ≤ β′ → sum β LeftO ≤ sum β′ RightO
nkpΩ β β′ h = viaL β _ _ (viaR β′ _ _ (
  ≤-trans
    (vsum⁺
      (Z00.rr00 {lV = tt} {lV′ = lv} (ss hself) (ss hself) (λ _ _ _ → n1) (λ _ _ _ → n1) tt lv (accL (hs hz)) (accL hz) _ _
         C.self _ llN _ Act _ _ _ Y1′ _
         cpTop (λ p p′ l l′ cp z₁ z₁′ hz₁ Y Y′ hY → stepOA⁺ hY)
         (domN _ (λ T → left (left here)))
         (τ₀ tt) (τ₀ lv) (cpTop , s∞) refl refl)
      (sum-mono (yc (Step YN) (τ₀ tt)) h))
    (≤-trans (inSum (inR (inE 0 (inL (inR (inE 0 (inL (inL (inL (inE 0 (inL (inR here))))))))))) (sum β′ (yc (Step YN) (τ₀ tt))))
             (≤l 1 (≤drp _ _)))))
```
