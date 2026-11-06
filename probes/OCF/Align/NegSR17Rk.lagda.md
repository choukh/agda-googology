# 第十七轮的否定 (一): 不带时间条件的 `rk⁺` 可靠性在 $\Lambda_2$ 上为假; 反例恰好违反 `DomL`

> 不读记号. 入口 [NegSR17](NegSR17.lagda.md). 对着接口 [StrRel17If](StrRel17If.lagda.md) (定稿 2026-11-05 12:12) 与它所引的 [StrRel16If](StrRel16If.lagda.md) 写. 实例 $\Lambda_2=2$ (`StrRel13Val.Λ₂`), 没有 $\Omega$-极限.
>
> 1. **(否定, 值) `¬RkSound`**: `StrRel16If.RkSound hz (hs hz)` (即 `RkSound₀ (hs hz)`) 不成立. 一对 `rk⁺` 的输出 (`relLR`, 前提 `RkPre` 全部写出) 以较小的状态 `YN` 再折叠, 第 $0$ 层的和左边 $\ge\omega\cdot\mathrm{BIG}$, 右边 $\le\omega\cdot\mathrm{SM}$, 而 $\omega\cdot\mathrm{SM}<\omega\cdot\mathrm{BIG}$ (`¬valRef`).
> 2. **(否定) `¬sem∀`, `¬semLR`, `¬semᴺLR`**: 于是 "`RelX⁺ hz (hs hz)` ⇒ `SemX²⁺`" 不成立; 动作限制为 `ActNZ` 的 `SemXᴺ` 也不成立 (反例的再折叠动作 `C1` 在第 $0$ 层输出 `n1`). 关系 `RelX⁺` 因为含 `rk⁺`, 对任何不带时间条件的语义都不可靠 (在本实例的意义上).
> 3. **(定理) `¬domEx`, `domOK`, `valOK`**: 反例的再折叠状态**不**满足接口的时间条件 `DomL` (右边再折叠时的 `YN` 不支配左边产生时的 `YB`); 把右边的再折叠状态换成满足 `DomL` 的 `YB`, 同一对输出的值就是对的 (`valOK`, 这一个实例上). 所以本反例**不**否定 `RkSoundT`, 它说明接口 §3 的时间条件不是多余的. (`RkSoundT` 本身由另一个反例否定: [NegSR17RkT](NegSR17RkT.lagda.md), 产生时的动作读累计.)
>
> **反例的机制 (判断, 依据证明).** 左边是上升的链极限, 它的每一段从**产生时**状态在坐标层 $0$ 上的读数 (`YB`, 读 $\omega\cdot(1⨾\omega)$) 起; 右边是保留的节点, 它的分支是产生时的动作的输出. 产生时的动作 `C1` 不读状态 (常数 `n1`), 所以右边的分支不带产生时的读数; 再折叠时右边的链从**再折叠时**的读数 (`YN`, 读 $\omega\cdot1$) 起. 产生时大, 再折叠时小, 右边就追不上. 动作若读状态 (`Act`), 右边的分支会带上产生时的读数 (`StrRel17Val` 的实验就是这样), 本反例不覆盖那种情形.
>
> **前提可满足.** 全部写出, 都是定理: `pre` (`cp00`, `s∞`, 分支 `n1ˣ`, `hawC1`, `n0ˣ`, `hYB`), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl`/`refl` (与 `StrRel16Kr.rkAt` 同); 再折叠一侧 `cp00`, `hawC1⁺`/`hawC1ᴺ`, `n0⁺`, `jYN`, 目标对 `(cp00 , s∞)`. 否定不是空真.
>
> **构造一路为什么需要这条律.** `StrRel16If` §6 的 `RkSound` 是 `semX0⁺` 的条件, `StrRel16Sem.Zero⁺.semX0⁺` 与 `StrRel16Node.ZRk` 都以它为前提; 构造一路的接手清单第 1 项问它能否对一切状态成立. 本文说: 不能, 要带时间条件 (接口 §3 的 `RkSoundT` 正是这样改的).
>
> **只否定什么.** 只否定不带时间条件的 `RkSound hz (hs hz)` (以及由它推出的 "`RelX⁺` ⇒ `SemX²⁺`/`SemXᴺ`" 在层对 $(0,1)$ 上); 反例用的产生时动作是不读状态的常数动作 `C1`. 本反例不否定 `RkSoundT` (它违反 `DomL`, `¬domEx`; `RkSoundT` 另见 `NegSR17RkT`), 不否定动作限制为读状态的一类 (如只用 `Act`) 之后的 `RkSound`, 不涉及 $\Omega$-极限. 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR17Rk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (H; Vs; outS; ⊲ᴴ↑; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; accL; AccY; sum; pt)
open import OCF.Align.HtFeedGrow using (nz≤)
open import OCF.Align.StrRel13Later using (nzb-ok)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
open import OCF.Align.StrRel15Fin using (fin⊲; T₁; module FinΛ)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (sum-mono; module V0)
open import OCF.Align.StrRel16If Λ₂ tt
import OCF.Align.StrRel17If as If⁴

open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (n0ˣ; n1ˣ; ⨾ˣ; nlˣ)
open If² Λ₂ tt using (J²; HAW²)
open FinΛ Λ₂ tt tt using (ΩRX²)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺)
open V0 Λ₂ tt using (vsum⁺)
open P using (Tg; tg; wm; tm; τ₀; St; st; Df; df; yc; d; z; Run; Ig; Chn; LW; RKi; rise; keep; kk; _⊕⟨_⟩_)
```

## 1 动作, 状态, 前提

`C1`: 一切目标上输出 `n1` 的常数动作. `YB`: 每个目标 (层 $t$) 上读 $\omega\cdot(\Omega_t⨾\mathrm{SM})$, $\mathrm{SM}=\omega\cdot(1⨾0)$; `YN`: 读 $\omega\cdot(\Omega_t⨾0)$. 两者的累计都是 `n0`, 都满足 `NE`. `hYB` 是旧的 `J²` (产生时 `RkPre` 要的), `jYN` 是 `J²⁺` (再折叠时 `SemX²⁺` 要的).

```agda
-- 常数动作
C1 : ∀ {L W} → Ig L W
C1 p l w Y = df (λ T → n1)

SM : ∀ {t m} → D t m
SM = nl (λ _ → n1 ⨾ n0)

YB YN : ∀ {W} → St W
YB = st (df (λ {t} T → nl (λ _ → Ωd t ⨾ SM))) n0
YN = st (df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))) n0

hYB : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J² lW lW′ (YB {W}) (YB {W′})
hYB = ((λ T T′ tx → nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) (nlˣ (λ _ → ⨾ˣ n1ˣ n0ˣ)))) , n0ˣ) ,
      ((λ T → SM , J14.here) , (λ T → SM , J14.here))

jYN : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J²⁺ lW lW′ (YN {W}) (YN {W′})
jYN = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺)) , n0⁺) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

hawC1 : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW² L L′ lW lW′ (C1 {L} {W}) (C1 {L′} {W′})
hawC1 L L′ p p′ l l′ cp w w′ hw Y Y′ hY T T′ tx = n1ˣ

hawC1⁺ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW²⁺ L L′ lW lW′ (C1 {L} {W}) (C1 {L′} {W′})
hawC1⁺ L L′ p p′ l l′ cp w w′ hw Y Y′ hY T T′ tx = n1⁺
```

## 2 常数动作下, 第 $0$ 层的运行与坐标层 $0$ 的上升输出不改值

`RK.le`/`RK.ge`: 动作在第 $0$ 层目标上恒输出 `n1` 时, 第 $0$ 层的树运行之后在第 $0$ 层目标上的和与原树的和互相 $\le$ (对 `⨾`, `nl`, `nw` 归纳; `Rpt` 的状态与上下文不起作用). 于是链的每一段与第 $0$ 段同值 (`chLe`, `chGe`), 上升输出 `Rise` 与 "坐标层 $0$ 的读数的 $\omega$ 次和" 互相 $\le$ (`riseLe`, `riseGe`).

```agda
-- 常数动作下第 0 层树的运行: 值不变
module RK {W} (lW : Lg W) (A₀ : Ig hz W) (hA : ∀ (w : D hz W) (Y : St W) {m} (T : Tg W hz m) → yc (A₀ C.self lW w Y) T ≡ n1) where
  le : ∀ (ac : AccY hz) {V} (x : D₀ V) (q : V ⊲ W) (ll : LW hz W) (w : D₀ W) (Y : St W) {m} (T : Tg W hz m) b →
       sum b (yc (Run ac x q lW ll A₀ w Y) T) ≤ sum b x
  le ac n0 q ll w Y T b = ≤-refl b
  le ac n1 q ll w Y T b = subst (λ y → sum b y ≤ asuc b) (sym (hA w Y T)) (≤-refl (asuc b))
  le ac (x ⨾ y) q ll w Y T b =
    ≤-trans (le ac y q ll (w ⨾ nw q x) (Y ⊕⟨ lW ⟩ Run ac x q lW ll A₀ w Y) T (sum b (yc (Run ac x q lW ll A₀ w Y) T)))
            (sum-mono y (le ac x q ll w Y T b))
  le ac (nl F) q ll w Y T b = l≤ (λ n → ≤l n (go n))
    where
    go : ∀ n → pt b (λ n → yc (Run ac (F n) q lW ll A₀ (proj₁ (P.Rpt ac F q lW ll A₀ w Y n)) (proj₂ (P.Rpt ac F q lW ll A₀ w Y n))) T) n ≤ pt b F n
    go zero = ≤-refl b
    go (suc n) = ≤-trans (le ac (F n) q ll (proj₁ (P.Rpt ac F q lW ll A₀ w Y n)) (proj₂ (P.Rpt ac F q lW ll A₀ w Y n)) T _) (sum-mono (F n) (go n))
  le ac (nw p x) q ll w Y T b = le ac x (⊲-tr p q) ll w Y T b
  le ac (ni () u) q ll w Y T b
  le ac (nκ () u) q ll w Y T b

  ge : ∀ (ac : AccY hz) {V} (x : D₀ V) (q : V ⊲ W) (ll : LW hz W) (w : D₀ W) (Y : St W) {m} (T : Tg W hz m) b →
       sum b x ≤ sum b (yc (Run ac x q lW ll A₀ w Y) T)
  ge ac n0 q ll w Y T b = ≤-refl b
  ge ac n1 q ll w Y T b = subst (λ y → asuc b ≤ sum b y) (sym (hA w Y T)) (≤-refl (asuc b))
  ge ac (x ⨾ y) q ll w Y T b =
    ≤-trans (sum-mono y (ge ac x q ll w Y T b))
            (ge ac y q ll (w ⨾ nw q x) (Y ⊕⟨ lW ⟩ Run ac x q lW ll A₀ w Y) T (sum b (yc (Run ac x q lW ll A₀ w Y) T)))
  ge ac (nl F) q ll w Y T b = l≤ (λ n → ≤l n (go n))
    where
    go : ∀ n → pt b F n ≤ pt b (λ n → yc (Run ac (F n) q lW ll A₀ (proj₁ (P.Rpt ac F q lW ll A₀ w Y n)) (proj₂ (P.Rpt ac F q lW ll A₀ w Y n))) T) n
    go zero = ≤-refl b
    go (suc n) = ≤-trans (sum-mono (F n) (go n)) (ge ac (F n) q ll (proj₁ (P.Rpt ac F q lW ll A₀ w Y n)) (proj₂ (P.Rpt ac F q lW ll A₀ w Y n)) T _)
  ge ac (nw p x) q ll w Y T b = ge ac x (⊲-tr p q) ll w Y T b
  ge ac (ni () u) q ll w Y T b
  ge ac (nκ () u) q ll w Y T b

  -- 链的每一段与第 0 段同值
  seg : AccY hz → LW hz W → St W → ℕ → D₀ W
  seg ac hk Y n = proj₁ (proj₂ (Chn ac hk lW A₀ Y n))

  chLe : ∀ ac hk Y n b → sum b (seg ac hk Y n) ≤ sum b (yc (d Y) (tg C.self hk lW))
  chLe ac hk Y zero b = ≤-refl _
  chLe ac hk Y (suc n) b =
    ≤-trans (le ac (seg ac hk Y n) C.self hk (proj₁ (Chn ac hk lW A₀ Y n)) (proj₂ (proj₂ (Chn ac hk lW A₀ Y n))) (tg C.self hk lW) b)
            (chLe ac hk Y n b)

  chGe : ∀ ac hk Y n b → sum b (yc (d Y) (tg C.self hk lW)) ≤ sum b (seg ac hk Y n)
  chGe ac hk Y zero b = ≤-refl _
  chGe ac hk Y (suc n) b =
    ≤-trans (chGe ac hk Y n b)
            (ge ac (seg ac hk Y n) C.self hk (proj₁ (Chn ac hk lW A₀ Y n)) (proj₂ (proj₂ (Chn ac hk lW A₀ Y n))) (tg C.self hk lW) b)

  -- 上升输出 (坐标层 0) 与 "读数的 ω 次和" 同值
  Rise : AccY hz → LW hz W → St W → ∀ {m} → Tg W hz m → D₀ m
  Rise ac hk Y T = nl (λ n → yc (Run ac (seg ac hk Y n) C.self lW hk A₀ (proj₁ (Chn ac hk lW A₀ Y n)) (proj₂ (proj₂ (Chn ac hk lW A₀ Y n)))) T)

  riseLe : ∀ ac hk Y {m} (T : Tg W hz m) b → sum b (Rise ac hk Y T) ≤ sum b (nl (λ (_ : ℕ) → yc (d Y) (tg C.self hk lW)))
  riseLe ac hk Y T b = nlLe _ _ (λ n b′ → ≤-trans (le ac (seg ac hk Y n) C.self hk _ _ T b′) (chLe ac hk Y n b′)) b
    where
    nlLe : ∀ {W₁ W₂} (e : ℕ → D₀ W₁) (e′ : ℕ → D₀ W₂) → (∀ n b → sum b (e n) ≤ sum b (e′ n)) → ∀ b → sum b (nl e) ≤ sum b (nl e′)
    nlLe e e′ h b = l≤ (λ n → ≤l n (go n))
      where
      go : ∀ n → pt b e n ≤ pt b e′ n
      go zero = ≤-refl b
      go (suc n) = ≤-trans (sum-mono (e n) (go n)) (h n (pt b e′ n))

  riseGe : ∀ ac hk Y {m} (T : Tg W hz m) b → sum b (nl (λ (_ : ℕ) → yc (d Y) (tg C.self hk lW))) ≤ sum b (Rise ac hk Y T)
  riseGe ac hk Y T b = nlLe _ _ (λ n b′ → ≤-trans (chGe ac hk Y n b′) (ge ac (seg ac hk Y n) C.self hk _ _ T b′)) b
    where
    nlLe : ∀ {W₁ W₂} (e : ℕ → D₀ W₁) (e′ : ℕ → D₀ W₂) → (∀ n b → sum b (e n) ≤ sum b (e′ n)) → ∀ b → sum b (nl e) ≤ sum b (nl e′)
    nlLe e e′ h b = l≤ (λ n → ≤l n (go n))
      where
      go : ∀ n → pt b e n ≤ pt b e′ n
      go zero = ≤-refl b
      go (suc n) = ≤-trans (sum-mono (e n) (go n)) (h n (pt b e′ n))
```

## 3 一对 `rk⁺` 的输出

层 $\Lambda_2$, 坐标层 $0$ 的节点 `r₀`, 分支 `n1`, 产生时的动作 `C1`, 状态 `YB`: 在 $T_0$ (层 $0$) 上升, 在 $T_1$ (层 $1$) 保留. `relLR` 是 `rk⁺` 的一个实例 (与 `StrRel16Kr.rkAt` 同形, 动作与状态换了).

```agda
-- 产生: 层 Λ₂ 坐标层 0 的节点 r₀, 分支 n1, 动作 C1, 状态 YB; 左在 T₀ (层 0) 上升, 右在 T₁ (层 1) 保留
uN : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
uN _ _ _ = n1

OL : D hz azero
OL = RKi (accL Λ₂) (accL hz) r₀ uN C.self tt hself C1 n0 YB (τ₀ tt) rise

OR : D (hs hz) azero
OR = RKi (accL Λ₂) (accL hz) r₀ uN C.self tt hself C1 n0 YB T₁ (keep (ss hself))

pre : RkPre {lW₀ = tt} {lW₀′ = tt} r₀ r₀ uN uN tt tt C.self C.self C1 C1 n0 n0 YB YB
pre = cp00 , s∞ , (λ p p′ lc lc′ cp y y′ b → n1ˣ) , hawC1 Λ₂ Λ₂ , n0ˣ , hYB

relLR : RelX⁺ hz (hs hz) tt tt OL OR
relLR = rk⁺ r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself C1 C1 n0 n0 YB YB (τ₀ tt) T₁ (ss hself)
          pre (cp00 , u∞ s∞) refl refl
```

## 4 再折叠与两边的值

两边都以 `YN` 再折叠, 动作 `C1`, 读第 $0$ 层. 左: 再折叠不改值 (`RL`), 产生时的输出是 `BIG` $=\omega\cdot(1⨾\mathrm{SM})$ 的 $\omega$ 次和 (`RO`). 右: 保留的节点 (层 $1$, 坐标层 $0$) 的分支 `BR` 经 `BNi`, `Ai`, `Run n1` 定义性地化成 `C1` 的输出 `n1`, 所以它的分支动作也是常数 `n1` (`RR` 的 `refl`); 再折叠时它在第 $0$ 层上升, 链从 `YN` 的读数 `SM` 起.

```agda
-- 再折叠: 两边状态 YN, 动作 C1, 读第 0 层
RefL : D₀ azero
RefL = yc (Run (accL hz) OL C.self tt (z⊲ᴴ Λ₂) C1 n0 YN) (τ₀ tt)
RefR : D₀ azero
RefR = yc (Run (accL (hs hz)) OR C.self tt (hsuc hself) C1 n0 YN) (τ₀ tt)

-- 左: 再折叠不改值, 产生时的输出是读数 BIG 的 ω 次和
module RL = RK {azero} tt C1 (λ w Y T → refl)
module RO = RK {azero} tt (P.Ai (accL Λ₂) (accL hz) r₀ uN C.self (kk r₀ C.self hself) hself C1 n0) (λ w Y T → refl)

BIG : D₀ azero
BIG = nl (λ _ → n1 ⨾ SM)

lowL : ∀ b → sum b (nl (λ (_ : ℕ) → BIG)) ≤ sum b RefL
lowL b = ≤-trans (RO.riseGe (accL hz) (kk r₀ C.self hself) YB (τ₀ tt) b) (RL.ge (accL hz) OL C.self (z⊲ᴴ Λ₂) n0 YN (τ₀ tt) b)

-- 右: 节点 (层 1, 坐标层 0) 的分支定义性地是 n1; 再折叠从 YN 的读数起
rk1 : StH azero hz (hs hz)
rk1 = ss hself

BR : ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs (hs hz) rk1 W′ → D (hs hz) W′
BR p lW′ y = yc (P.BNi (accL Λ₂) (accL hz) r₀ uN C.self hself C1 n0 YB (kk r₀ C.self hself) (⊲-tr (wm T₁) p) lW′ (outS rk1 y))
                (tg C.self (⊲ᴴ↑ p (tm T₁)) lW′)

module RR = RK {azero} tt (P.Ai (accL (hs hz)) (accL hz) rk1 BR C.self (kk rk1 C.self (hsuc hself)) (hsuc hself) C1 n0) (λ w Y T → refl)

upR : ∀ b → sum b RefR ≤ sum b (nl (λ (_ : ℕ) → SM {hz} {azero}))
upR b = RR.riseLe (accL hz) (kk rk1 C.self (hsuc hself)) YN (τ₀ tt) b
```

## 5 否定

```agda
-- 值: 左 ≥ ω⋅BIG 严格大于右 ≤ ω⋅SM
gap : asuc (sum azero (nl (λ (_ : ℕ) → SM {hz} {azero}))) ≤ sum azero (nl (λ (_ : ℕ) → BIG))
gap = ≤-trans (s≤ (vsum⁺ {lV = tt} {lV′ = tt} (nl⁺ (λ _ → in⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺)) (inR here))) (≤-refl azero)))
              (≤-trans (nz≤ (sum azero BIG) (nzb-ok BIG tt)) (≤l 2 (≤-refl _)))

¬valRef : ¬ (sum azero RefL ≤ sum azero RefR)
¬valRef h = irr _ (≤-trans gap (≤-trans (lowL azero) (≤-trans h (upR azero))))

¬semLR : ¬ SemX²⁺ hz (hs hz) tt tt OL OR
¬semLR s = ¬valRef (vsum⁺ (s tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz))
                             n0 n0 n0⁺ YN YN jYN (τ₀ tt) (τ₀ tt) (cp00 , s∞)) (≤-refl azero))

¬RkSound : ¬ RkSound hz (hs hz)
¬RkSound h = ¬semLR (h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself C1 C1 n0 n0 YB YB (τ₀ tt) T₁ (ss hself)
                        pre (cp00 , u∞ s∞) refl refl)

¬sem∀ : ¬ (∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D hz V} {x′ : D (hs hz) V′} → RelX⁺ hz (hs hz) lV lV′ x x′ → SemX²⁺ hz (hs hz) lV lV′ x x′)
¬sem∀ h = ¬semLR (h relLR)
```

## 6 与时间条件的关系; 动作限制的版本

```agda
-- 反例的再折叠状态不满足时间条件 DomL (右边再折叠的 YN 不支配左边产生时的 YB)
open If⁴ Λ₂ tt using (DomL; SemXᴺ; HAWᴺ; p1)

¬domEx : ¬ DomL {azero} tt YB {azero} {azero} tt tt YN YN
¬domEx ((r , _) , _) =
  irr _ (≤-trans (s≤ (sum-mono SM {azero} {asuc azero} z≤))
          (≤-trans (nz≤ (sum (asuc azero) (SM {hz} {azero})) (nzb-ok (n1 ⨾ SM {hz} {azero}) tt))
            (≤-trans (≤l 2 (≤-refl _)) (vsum⁺ (r (τ₀ tt) (τ₀ tt) (cp00 , s∞)) (≤-refl azero)))))

-- 对照: 右边以 YB 再折叠 (满足 DomL) 时, 同一对的值是对的
jYB : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J²⁺ lW lW′ (YB {W}) (YB {W′})
jYB = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺)))) , n0⁺) ,
      ((λ T → SM , J14.here) , (λ T → SM , J14.here))

domOK : DomL {azero} tt YB {azero} {azero} tt tt YN YB
domOK = jYB

RefRB : D₀ azero
RefRB = yc (Run (accL (hs hz)) OR C.self tt (hsuc hself) C1 n0 YB) (τ₀ tt)

valOK : sum azero RefL ≤ sum azero RefRB
valOK = ≤-trans (RL.le (accL hz) OL C.self (z⊲ᴴ Λ₂) n0 YN (τ₀ tt) azero)
          (≤-trans (RO.riseLe (accL hz) (kk r₀ C.self hself) YB (τ₀ tt) azero)
                   (RR.riseGe (accL hz) (kk rk1 C.self (hsuc hself)) YB (τ₀ tt) azero))

-- 动作限制为 ActNZ 的语义也不行: C1 在第 0 层输出 n1
hawC1ᴺ : HAWᴺ hz (hs hz) {azero} {azero} tt tt C1 C1
hawC1ᴺ = hawC1⁺ hz (hs hz) , ((λ p l w Y → p1) , (λ p l w Y → p1))

¬semᴺLR : ¬ SemXᴺ hz (hs hz) tt tt OL OR
¬semᴺLR s = ¬valRef (vsum⁺ (s tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 hawC1ᴺ
                             n0 n0 n0⁺ YN YN jYN (τ₀ tt) (τ₀ tt) (cp00 , s∞)) (≤-refl azero))

```
