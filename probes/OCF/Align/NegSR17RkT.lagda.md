# 第十七轮的否定 (四): 带时间条件的 `RkSoundT` 也不成立 (产生时的动作读累计)

> 不读记号. 入口 [NegSR17](NegSR17.lagda.md). 对着接口 [StrRel17If](StrRel17If.lagda.md) (定稿 2026-11-05 12:12) §3 的 `RkSoundT` 写. 实例 $\Lambda_2=2$, 没有 $\Omega$-极限.
>
> **(否定, 值) `¬RkSoundT`: `RkSoundT hz (hs hz)` 不成立.** 一对 `rk⁺` 的输出 (节点 `r₀`, 层 $2$, 坐标层 $0$, 分支 `n1`; 左在 $T_0$ 上升, 右在 $T_1$ 保留), 产生时的状态 `YP` (读数同 `YN`, 第 $0$ 层累计 $z_P$ 很大), 产生时的动作 `Az` (输出 "累计 ⨾ 1"); 两边都以**产生时的状态 `YP` 本身**再折叠, 动作 `C1`. 这时字面的时间关系 `Later YP YP` 与时间条件 `DomL` 都成立 (`laterP`, `domP`), `RkPre` 全部写出 (`preP`), 而第 $0$ 层的和左边 $>$ 右边.
>
> **机制 (判断, 依据证明).** 左边是上升的链极限: 链在**产生时**运行, 动作 `Az` 读到的累计含 $z_P$, 所以左边的第一项就含 $z_P$ (`lowOL`). 右边是保留的节点: 它的分支由 `BNi` 在**换世界之后** (`cv p Y`) 才运行, `cv` 把累计清零 (`HtFeedFold.cv` 的字面), 所以分支里没有 $z_P$; 再折叠的动作 `C1` 不读状态, 于是右边的值与再折叠状态的累计无关 (`refR≈`: 把再折叠状态换成累计为 `n0` 的 `Y0`, 输出逐点结构相同). 取 $z_P$ 为 "右边在 `Y0` 下的输出加 $1$" (`zP`, 不循环: 右边的保留输出定义性地不依赖产生时的累计, `orEq`), 左边 $\ge z_P+1>$ 右边. 时间条件只约束**状态**, 碰不到 "保留的分支在换世界之后才运行, 累计已被清零" 这一点.
>
> **证明的工具 (定理).** `_≈_`: 无节点的树的逐点结构相等 (对 `nl` 逐项, 不用 `Funext`); `Cong.run≈`: `Run` 对 `≈` 的同余, 树、上下文、状态各带一个关系, 动作把相关的输入送到 `≈` 的输出; `sum≈`: `≈` 的树的和互相 $\le$. 三层实例: `In₁` (`BNi` 里以 `Az` 运行, 状态关系是累计 `≈`), `In₂` (再折叠的分支动作以 `C1` 运行), `In₃` (再折叠时右边节点的链, 状态任意).
>
> **前提可满足.** 全部是定理: `preP` (`cp00`, `s∞`, 分支 `n1ˣ`, `hawAz` (旧 `HAW²`, 由 `liftMono`), `n0ˣ`, `hYP` (旧 `J²`)), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl`/`refl`; 再折叠 `cp00`, `hawC1⁺`, `n0⁺`, `jYP` (`J²⁺ YP YP`), 条件 `DomL` 由 `jYP` 给出, 目标对 `(cp00 , s∞)`. 不是空真.
>
> **构造一路为什么需要这条律.** `RkSoundT` 是接口 §3 为 `rk⁺` 写的可靠性, B1 路线 ("带时间关系的语义") 的核心; `StrRel17Time.valT` 是它在动作 `Act`、一个再折叠目标对上的实例. 本文说: 对接口允许的一切产生时动作 (`HAW²`), 它不成立.
>
> **只否定什么.** 只否定 `RkSoundT hz (hs hz)` 的字面陈述 (产生时动作取遍 `HAW²`, 再折叠动作取遍 `HAW²⁺`). 用到的产生时动作 `Az` 读第 $0$ 层累计; **不否定**把产生时动作限制为不读累计的一类 (例如只用 `Act`) 之后的版本: `StrRel17Time.valT` 是那一类在一个目标对上的正面结果. 判断: 折叠里读累计的动作是存在的: 分支含 `nκ` 的节点的分支动作 `Ai` 经 `RKy` 在第 $0$ 层回灌, 回灌的格从累计起 (`HtFeedFold.κc`), 所以在有 $\Omega$-极限的 $\Lambda$ 上, "动作不读累计" 不是折叠自动满足的条件 (没有编译). 本文不涉及右边保留的再折叠目标对 (`StrRel17Obs` 的障碍). 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR17RkT where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; irr)
open import OCF.Align.HtFeedTree using (H; Vs; outS; inS; drp; ⊲ᴴ↑; hz; hs; hself; hsuc; ss; z⊲ᴴ; StH; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; accL; AccY; sum; pt)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; cp00)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
open import OCF.Align.StrRel15Fin using (fin⊲; T₁; module FinΛ)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Lem using (sum-mono; module V0; Lp; here)
open import OCF.Align.StrRel16If Λ₂ tt hiding (here)
open import OCF.Align.NegSR17Rk using (C1; hawC1⁺; module RK)
import OCF.Align.StrRel17If as If⁴

open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; prˣ; nwˣ; niˣ; κˣ)
open If² Λ₂ tt using (J²; HAW²)
open FinΛ Λ₂ tt tt using (ΩRX²)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺)
open V0 Λ₂ tt using (vsum⁺)
open If⁴ Λ₂ tt using (RkSoundT; DomL; Later)
open P using (Tg; tg; wm; tm; τ₀; St; st; Df; df; yc; d; z; Run; Ig; Chn; LW; RKi; rise; keep; kk; _⊕⟨_⟩_)
```

## 1 逐点结构相等 `≈`

```agda
-- 逐点的结构相等 (没有节点): 不用函数外延也能对 nl 逐项比较
data _≈_ {t : H} : ∀ {m} → D t m → D t m → Set where
  n0≈ : ∀ {m} → n0 {W = m} ≈ n0
  n1≈ : ∀ {m} → n1 {W = m} ≈ n1
  ⨾≈  : ∀ {m} {a a′ b b′ : D t m} → a ≈ a′ → b ≈ b′ → (a ⨾ b) ≈ (a′ ⨾ b′)
  nl≈ : ∀ {m} {e e′ : ℕ → D t m} → (∀ n → e n ≈ e′ n) → nl e ≈ nl e′
  nw≈ : ∀ {V₀ m} (p : V₀ ⊲ m) {a a′ : D t V₀} → a ≈ a′ → nw p a ≈ nw p a′

sum≈ : ∀ {W} {x y : D₀ W} → x ≈ y → ∀ b → sum b x ≤ sum b y
sum≈ n0≈ b = ≤-refl b
sum≈ n1≈ b = ≤-refl (asuc b)
sum≈ (⨾≈ {b = y₁} h k) b = ≤-trans (sum-mono y₁ (sum≈ h b)) (sum≈ k _)
sum≈ (nl≈ {e = e} {e′} f) b = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b e n ≤ pt b e′ n
  go zero = ≤-refl b
  go (suc n) = ≤-trans (sum-mono (e n) (go n)) (sum≈ (f n) _)
sum≈ (nw≈ p h) b = sum≈ h b

refl≈₀ : ∀ {W} (x : D₀ W) → x ≈ x
refl≈₀ n0 = n0≈
refl≈₀ n1 = n1≈
refl≈₀ (x ⨾ y) = ⨾≈ (refl≈₀ x) (refl≈₀ y)
refl≈₀ (nl e) = nl≈ (λ n → refl≈₀ (e n))
refl≈₀ (nw p x) = nw≈ p (refl≈₀ x)
refl≈₀ (ni () u)
refl≈₀ (nκ () u)
```

## 2 搬层 `lift`, 旧关系下的单调性, `drp` 的自反

```agda
-- 第 0 层的树搬到任意层 (丢掉 nw)
lift : ∀ {t m W} → D₀ W → D t m
lift n0 = n0
lift n1 = n1
lift (x ⨾ y) = lift x ⨾ lift y
lift (nl e) = nl (λ n → lift (e n))
lift (nw p x) = lift x
lift (ni () u)
lift (nκ () u)

lift≈ : ∀ {t m W} {x y : D₀ W} → x ≈ y → lift {t} {m} x ≈ lift y
lift≈ n0≈ = n0≈
lift≈ n1≈ = n1≈
lift≈ (⨾≈ h k) = ⨾≈ (lift≈ h) (lift≈ k)
lift≈ (nl≈ f) = nl≈ (λ n → lift≈ (f n))
lift≈ {t} {m} (nw≈ {V₀} p {a} {a′} h) = lift≈ {t} {m} {V₀} {a} {a′} h

sumLift : ∀ {W m} (x : D₀ W) b → sum b x ≤ sum b (lift {hz} {m} x)
sumLift n0 b = ≤-refl b
sumLift n1 b = ≤-refl (asuc b)
sumLift (x ⨾ y) b = ≤-trans (sum-mono y (sumLift x b)) (sumLift y _)
sumLift {m = m} (nl e) b = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b e n ≤ pt b (λ n → lift {hz} {m} (e n)) n
  go zero = ≤-refl b
  go (suc n) = ≤-trans (sum-mono (e n) (go n)) (sumLift (e n) _)
sumLift (nw p x) b = sumLift x b
sumLift (ni () u) b
sumLift (nκ () u) b

sumDrp : ∀ {W W′} (x : D₀ W) b → sum b x ≤ sum b (drp {W′ = W′} x)
sumDrp n0 b = ≤-refl b
sumDrp n1 b = ≤-refl (asuc b)
sumDrp (x ⨾ y) b = ≤-trans (sum-mono y (sumDrp x b)) (sumDrp y _)
sumDrp {W′ = W′} (nl e) b = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b e n ≤ pt b (λ n → drp {W′ = W′} (e n)) n
  go zero = ≤-refl b
  go (suc n) = ≤-trans (sum-mono (e n) (go n)) (sumDrp (e n) _)
sumDrp (nw p x) b = sumDrp x b
sumDrp (ni () u) b
sumDrp (nκ () u) b

-- 旧关系: 第 0 层相关 ⇒ 搬到任意层仍相关
liftMono : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX hz hz lV lV′ x x′ →
           ∀ {t t′ m m′} {lm : Lg m} {lm′ : Lg m′} → RelX t t′ lm lm′ (lift x) (lift x′)
liftMono n0ˣ = n0ˣ
liftMono n1ˣ = n1ˣ
liftMono (⨾ˣ h k) = ⨾ˣ (liftMono h) (liftMono k)
liftMono (nlˣ f) = nlˣ (λ n → liftMono (f n))
liftMono (prˣ h) = prˣ (liftMono h)
liftMono (nwˣ ap h) = liftMono h
liftMono (niˣ {r = ()} _ _)
liftMono (κˣ {zz = ()} _)

reflDrp : ∀ {V V′ W} {lV : Lg V} {lV′ : Lg V′} (x : D₀ W) → RelX hz hz lV lV′ (drp x) (drp x)
reflDrp n0 = n0ˣ
reflDrp n1 = n1ˣ
reflDrp (x ⨾ y) = ⨾ˣ (reflDrp x) (reflDrp y)
reflDrp (nl e) = nlˣ (λ n → reflDrp (e n))
reflDrp (nw p x) = reflDrp x
reflDrp (ni () u)
reflDrp (nκ () u)

reflDrp⁺ : ∀ {V V′ W} {lV : Lg V} {lV′ : Lg V′} (x : D₀ W) → RelX⁺ hz hz lV lV′ (drp x) (drp x)
reflDrp⁺ n0 = n0⁺
reflDrp⁺ n1 = n1⁺
reflDrp⁺ (x ⨾ y) = ⨾⁺ (reflDrp⁺ x) (reflDrp⁺ y)
reflDrp⁺ (nl e) = nl⁺ (λ n → reflDrp⁺ (e n))
reflDrp⁺ (nw p x) = reflDrp⁺ x
reflDrp⁺ (ni () u)
reflDrp⁺ (nκ () u)
```

## 3 `Run` 对 `≈` 的同余

```agda
-- Run 对 ≈ 的同余 (树, 上下文, 状态各带一个关系; 动作把它们送到 ≈ 的输出)
module Cong {L W} (lW : Lg W) (A₁ A₂ : Ig L W) (CR : D L W → D L W → Set) (SR : St W → St W → Set)
  (crC : ∀ {V} (q : V ⊲ W) {w₁ w₂ : D L W} {x₁ x₂ : D L V} → CR w₁ w₂ → x₁ ≈ x₂ → CR (w₁ ⨾ nw q x₁) (w₂ ⨾ nw q x₂))
  (srC : ∀ {Y₁ Y₂ : St W} {Δ₁ Δ₂ : Df W} → SR Y₁ Y₂ → (∀ {t m} (T : Tg W t m) → yc Δ₁ T ≈ yc Δ₂ T) → SR (Y₁ ⊕⟨ lW ⟩ Δ₁) (Y₂ ⊕⟨ lW ⟩ Δ₂))
  (hA : ∀ w₁ w₂ Y₁ Y₂ → CR w₁ w₂ → SR Y₁ Y₂ → ∀ {t m} (T : Tg W t m) → yc (A₁ C.self lW w₁ Y₁) T ≈ yc (A₂ C.self lW w₂ Y₂) T) where
  run≈ : ∀ (ac : AccY L) {V} {x₁ x₂ : D L V} → x₁ ≈ x₂ → (q : V ⊲ W) (ll : LW L W) (w₁ w₂ : D L W) (Y₁ Y₂ : St W) → CR w₁ w₂ → SR Y₁ Y₂ →
         ∀ {t m} (T : Tg W t m) → yc (Run ac x₁ q lW ll A₁ w₁ Y₁) T ≈ yc (Run ac x₂ q lW ll A₂ w₂ Y₂) T
  rpt≈ : ∀ (ac : AccY L) {V} {e₁ e₂ : ℕ → D L V} → (∀ n → e₁ n ≈ e₂ n) → (q : V ⊲ W) (ll : LW L W) (w₁ w₂ : D L W) (Y₁ Y₂ : St W) →
         CR w₁ w₂ → SR Y₁ Y₂ → ∀ n →
         CR (proj₁ (P.Rpt ac e₁ q lW ll A₁ w₁ Y₁ n)) (proj₁ (P.Rpt ac e₂ q lW ll A₂ w₂ Y₂ n)) ×
         SR (proj₂ (P.Rpt ac e₁ q lW ll A₁ w₁ Y₁ n)) (proj₂ (P.Rpt ac e₂ q lW ll A₂ w₂ Y₂ n))
  run≈ ac n0≈ q ll w₁ w₂ Y₁ Y₂ c s T = n0≈
  run≈ ac n1≈ q ll w₁ w₂ Y₁ Y₂ c s T = hA w₁ w₂ Y₁ Y₂ c s T
  run≈ ac (⨾≈ {a = a} {a′} h k) q ll w₁ w₂ Y₁ Y₂ c s T =
    ⨾≈ (run≈ ac h q ll w₁ w₂ Y₁ Y₂ c s T)
       (run≈ ac k q ll (w₁ ⨾ nw q a) (w₂ ⨾ nw q a′) (Y₁ ⊕⟨ lW ⟩ Run ac a q lW ll A₁ w₁ Y₁) (Y₂ ⊕⟨ lW ⟩ Run ac a′ q lW ll A₂ w₂ Y₂)
          (crC q c h) (srC s (λ T′ → run≈ ac h q ll w₁ w₂ Y₁ Y₂ c s T′)) T)
  run≈ ac (nl≈ f) q ll w₁ w₂ Y₁ Y₂ c s T =
    nl≈ (λ n → run≈ ac (f n) q ll _ _ _ _ (proj₁ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n)) (proj₂ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n)) T)
  run≈ ac (nw≈ p h) q ll w₁ w₂ Y₁ Y₂ c s T = run≈ ac h (⊲-tr p q) ll w₁ w₂ Y₁ Y₂ c s T
  rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s zero = c , s
  rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s (suc n) =
    crC q (proj₁ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n)) (f n) ,
    srC (proj₂ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n))
        (λ T → run≈ ac (f n) q ll _ _ _ _ (proj₁ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n)) (proj₂ (rpt≈ ac f q ll w₁ w₂ Y₁ Y₂ c s n)) T)
```

## 4 实例: 读累计的产生时动作, 产生时状态, 两个输出

```agda
-- 读第 0 层累计的产生时动作
Az : ∀ {L W} → Ig L W
Az p l w Y = df (λ T → lift (z Y) ⨾ n1)

hawAz : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW² L L′ lW lW′ (Az {L} {W}) (Az {L′} {W′})
hawAz L L′ p p′ l l′ cp w w′ hw Y Y′ hY T T′ tx = ⨾ˣ (liftMono (proj₂ (proj₁ hY))) n1ˣ

dN : ∀ {W} → Df W
dN = df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))

Ys : ∀ {W} → D₀ W → St W
Ys zz = st dN zz

uN : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λ₂ r₀ W₁ → D Λ₂ W₁
uN _ _ _ = n1

rk1 : StH azero hz (hs hz)
rk1 = ss hself

hk : LW hz azero
hk = kk r₀ C.self hself

OLof : St azero → D hz azero
OLof Y = RKi (accL Λ₂) (accL hz) r₀ uN C.self tt hself Az n0 Y (τ₀ tt) rise

ORof : St azero → D (hs hz) azero
ORof Y = RKi (accL Λ₂) (accL hz) r₀ uN C.self tt hself Az n0 Y T₁ (keep rk1)

Y0 : St azero
Y0 = Ys n0

RefRof : St azero → D₀ azero
RefRof Y = yc (Run (accL (hs hz)) (ORof Y0) C.self tt (hsuc hself) C1 n0 Y) (τ₀ tt)

RefR₀ : D₀ azero
RefR₀ = RefRof Y0

zP : D₀ azero
zP = drp RefR₀ ⨾ n1

YP : St azero
YP = Ys zP

-- 产生时的累计在保留的输出里被 cv 清掉: 定义性地相同
orEq : ORof YP ≡ ORof Y0
orEq = refl
```

## 5 右边的再折叠与再折叠状态的累计无关

```agda
AiO : Ig hz azero
AiO = P.Ai (accL Λ₂) (accL hz) r₀ uN C.self hk hself Az n0

BR₀ : ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs (hs hz) rk1 W′ → D (hs hz) W′
BR₀ p lW′ y = yc (P.BNi (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 Y0 hk (⊲-tr (wm T₁) p) lW′ (outS rk1 y))
                 (tg C.self (⊲ᴴ↑ p (tm T₁)) lW′)

hk′ : LW hz azero
hk′ = kk rk1 C.self (hsuc hself)

AiR : Ig hz azero
AiR = P.Ai (accL (hs hz)) (accL hz) rk1 BR₀ C.self hk′ (hsuc hself) C1 n0

-- (一) BNi 里的运行: 动作读累计, 状态关系是累计 ≈
module In₁ {W₁} (p : azero ⊲ W₁) (lW₁ : Lg W₁) =
  Cong {hz} {W₁} lW₁ (P.Ig↾ p AiO) (P.Ig↾ p AiO) (λ _ _ → ⊤) (λ Y₁ Y₂ → z Y₁ ≈ z Y₂)
       (λ q c h → tt) (λ s hΔ → ⨾≈ s (hΔ (τ₀ lW₁))) (λ w₁ w₂ Y₁ Y₂ c s T → ⨾≈ (lift≈ s) n1≈)

br≈ : ∀ {W₁} (p₀ : azero ⊲ W₁) (lW₁ : Lg W₁) {w₁ w₂ : D₀ W₁} → w₁ ≈ w₂ → BR₀ p₀ lW₁ (inS rk1 w₁) ≈ BR₀ p₀ lW₁ (inS rk1 w₂)
br≈ p₀ lW₁ {w₁} {w₂} h =
  ⨾≈ (lift≈ (⨾≈ n0≈ (In₁.run≈ (⊲-tr (wm T₁) p₀) lW₁ (accL hz) h C.self (⊲ᴴ↑ (⊲-tr (wm T₁) p₀) hk) n0 n0
                        (P.cv (⊲-tr (wm T₁) p₀) Y0) (P.cv (⊲-tr (wm T₁) p₀) Y0) tt n0≈ (τ₀ lW₁)))) n1≈

-- (二) 再折叠的分支动作 AiR: 上下文 ≈ ⇒ 输出 ≈, 不看状态
module In₂ = Cong {hs hz} {azero} tt (P.Ig↾ C.self C1) (P.Ig↾ C.self C1) (λ _ _ → ⊤) (λ _ _ → ⊤)
               (λ q c h → tt) (λ s hΔ → tt) (λ w₁ w₂ Y₁ Y₂ c s T → n1≈)

hAR : ∀ (w₁ w₂ : D₀ azero) (Y₁ Y₂ : St azero) → w₁ ≈ w₂ → ⊤ → ∀ {t m} (T : Tg azero t m) →
      yc (AiR C.self tt w₁ Y₁) T ≈ yc (AiR C.self tt w₂ Y₂) T
hAR w₁ w₂ Y₁ Y₂ h _ T = In₂.run≈ (accL (hs hz)) (br≈ C.self tt h) C.self _ _ _ Y₁ Y₂ tt tt T

-- (三) 外层: 再折叠时右边节点的链, 状态任意
module In₃ = Cong {hz} {azero} tt AiR AiR _≈_ (λ _ _ → ⊤) (λ q c h → ⨾≈ c (nw≈ q h)) (λ _ _ → tt) hAR

chain≈ : ∀ (Y₁ Y₂ : St azero) → yc (d Y₁) (tg C.self hk′ tt) ≈ yc (d Y₂) (tg C.self hk′ tt) → ∀ n →
         (proj₁ (P.Chn (accL hz) hk′ tt AiR Y₁ n) ≈ proj₁ (P.Chn (accL hz) hk′ tt AiR Y₂ n)) ×
         (proj₁ (proj₂ (P.Chn (accL hz) hk′ tt AiR Y₁ n)) ≈ proj₁ (proj₂ (P.Chn (accL hz) hk′ tt AiR Y₂ n)))
chain≈ Y₁ Y₂ h0 zero = n0≈ , h0
chain≈ Y₁ Y₂ h0 (suc n) =
  ⨾≈ (proj₁ (chain≈ Y₁ Y₂ h0 n)) (proj₂ (chain≈ Y₁ Y₂ h0 n)) ,
  In₃.run≈ (accL hz) (proj₂ (chain≈ Y₁ Y₂ h0 n)) C.self hk′ _ _ _ _ (proj₁ (chain≈ Y₁ Y₂ h0 n)) tt (tg C.self hk′ tt)

refR≈ : RefRof YP ≈ RefRof Y0
refR≈ = nl≈ (λ n → In₃.run≈ (accL hz) (proj₂ (chain≈ YP Y0 h0 n)) C.self hk′ _ _ _ _ (proj₁ (chain≈ YP Y0 h0 n)) tt (τ₀ tt))
  where
  h0 = refl≈₀ (yc (dN {azero}) (tg C.self hk′ tt))
```

## 6 前提与否定

```agda
-- 前提
hYP : J² {azero} {azero} tt tt YP YP
hYP = ((λ T T′ tx → nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0ˣ)) , ⨾ˣ (reflDrp RefR₀) n1ˣ) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

jYP : J²⁺ {azero} {azero} tt tt YP YP
jYP = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺)) , ⨾⁺ (reflDrp⁺ RefR₀) n1⁺) ,
      ((λ T → n0 , J14.here) , (λ T → n0 , J14.here))

preP : RkPre {lW₀ = tt} {lW₀′ = tt} r₀ r₀ uN uN tt tt C.self C.self Az Az n0 n0 YP YP
preP = cp00 , s∞ , (λ p p′ lc lc′ cp y y′ b → n1ˣ) , hawAz Λ₂ Λ₂ , n0ˣ , hYP

-- 左边: 产生时的链的第一项就含 lift zP
lowOL : ∀ b → asuc (sum b (lift {hz} {azero} zP)) ≤ sum b (OLof YP)
lowOL b = ≤l 1 (≤l 1 (≤-refl _))

RefLP : D₀ azero
RefLP = yc (Run (accL hz) (OLof YP) C.self tt (z⊲ᴴ Λ₂) C1 n0 YP) (τ₀ tt)

module RL = RK {azero} tt C1 (λ w Y T → refl)

relRef : RkSoundT hz (hs hz) → RelX⁺ hz hz tt tt RefLP (RefRof YP)
relRef h =
  h r₀ r₀ tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL hz) C.self C.self hself hself Az Az n0 n0 YP YP (τ₀ tt) T₁ rk1 preP (cp00 , u∞ s∞) refl refl
    tt tt (accL hz) (accL (hs hz)) (z⊲ᴴ Λ₂) (hsuc hself) C.self C.self cp00 C1 C1 (hawC1⁺ hz (hs hz))
    n0 n0 n0⁺ YP YP jYP jYP (τ₀ tt) (τ₀ tt) (cp00 , s∞)

¬RkSoundT : ¬ RkSoundT hz (hs hz)
¬RkSoundT h =
  irr (sum azero RefR₀)
    (≤-trans (s≤ (sumDrp RefR₀ azero))
    (≤-trans (sumLift zP azero)
    (≤-trans (≤-suc (≤-refl _))
    (≤-trans (lowOL azero)
    (≤-trans (RL.ge (accL hz) (OLof YP) C.self (z⊲ᴴ Λ₂) n0 YP (τ₀ tt) azero)
    (≤-trans (vsum⁺ (relRef h) (≤-refl azero))
             (sum≈ refR≈ azero)))))))

-- 再折叠的状态就是产生时的状态: 字面的时间关系 Later 与时间条件 DomL 都成立
laterP : Later YP YP
laterP = (λ T → here) , here

domP : DomL {azero} tt YP {azero} {azero} tt tt YP YP
domP = jYP
```
