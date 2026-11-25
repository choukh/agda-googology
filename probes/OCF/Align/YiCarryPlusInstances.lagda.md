# Carry⁺：规范全塔与 Λ

本篇按 YiK1b 的同一有限次数归纳构造 Carry⁺，不以已有全塔 Carry
冒充新增 Nested 的证明。根 raw1 的 Nested 是 tt；后继坐标产生的
Ω 根使用 cO-nested。读回 lc 的 NestedLow 已由 Read 沿原槽位运输。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryPlusInstances where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below; one; e-first)
import OCF.Align.YiK1 as K
open import OCF.Align.YiCarryBounds using (cO-nested)
open import OCF.Align.YiCarryPlus
  using (Carry⁺; Source⁺; source⁺; PointB; seed⁺; cp-carry⁺)
open import OCF.Align.YiCarryPlusRead
open import OCF.Align.YiK1bBase
import OCF.Align.YiK1bReg as R
import OCF.Align.RR4RegOmega2 as O

CarryStage⁺ : ℕ → Set
CarryStage⁺ n = Carrys⁺ (suc n) F.zero ×
  (∀ η → F.Gd F.zero (V.cO F.zero) η → Carrys⁺ n (V.up F.zero η))

carry-stage-step⁺ : ∀ n → CarryStage⁺ n → CarryStage⁺ (suc n)
carry-stage-step⁺ n (r , old) = (r , rn) , coordinates
  where
  rn : Carry⁺ (pow (suc (suc n)) F.zero)
  rn = pow-node-carry⁺ n F.zero O.raw1 (F.suc F.zero)
    (λ η e → V.up F.zero η) (R.pow-zero-reg (suc (suc n))) (tt , tt)
    (carrys-last⁺ (suc n) F.zero r)
    (λ η e b → carrys-last⁺ n (V.up F.zero η) (old η e))

  coordinate-reg : ∀ η → F.Gd F.zero (V.cO F.zero) η →
    Reg (pow (suc n) (V.up F.zero η))
  coordinate-reg η e = regs-last (suc n) (V.up F.zero η)
    (proj₂ (R.stages (suc n)) η e)

  under-one : ∀ a → F.Cp F.zero a O.raw1 → Carry⁺ (pow (suc n) (V.up F.zero a))
  under-one a (inj₁ refl) = rn
  under-one a (inj₂ (inj₁ refl)) = carrys-last⁺ (suc n) F.zero r
  under-one a (inj₂ (inj₂ ()))

  go : ∀ η → F.Lgl F.zero η → F.Cp F.zero O.raw1 η →
    Carry⁺ (pow (suc n) (V.up F.zero η))
  go G.zero l (inj₁ ())
  go G.zero l (inj₂ ())
  go (G.suc a) l (inj₁ refl) = rn
  go (G.suc a) l (inj₂ q) =
    pow-node-carry⁺ n (V.up F.zero a) (V.cO (V.up F.zero a))
      (V.Ω̂ (V.up F.zero a)) (λ ζ d → V.up (V.up F.zero a) ζ)
      (coordinate-reg (G.suc a) (inj₂ q , l))
      (V.Lgl-cO (V.up F.zero a) , cO-nested (V.up F.zero a)) (go a l q)
      (λ ζ d b → carrys-last⁺ n (V.up (V.up F.zero a) ζ)
        (read-carrys⁺ n (V.up F.zero a) pa ra ζ d b))
    where
    ea : F.Gd F.zero (V.cO F.zero) a
    ea = q , l
    pa : Below (F.suc (V.up F.zero a)) (V.Ω̂ (V.up F.zero a))
    pa = R.coordinate-suc-root a ea
    ra : Carrys⁺ (suc n) (V.up F.zero a)
    ra = old a ea , go a l q
  go (G.lim f) (st , lf) (inj₁ ())
  go (G.lim f) (st , lf) (inj₂ (m , q)) =
    pow-lim-carry⁺ (suc n) (λ j → V.up F.zero (f j)) term
    where
    term : ∀ j → Carry⁺ (pow (suc n) (V.up F.zero (f j)))
    term j with F.cmpC F.zero (f (j + m))
      (subst (λ z → F.Cp F.zero (f j) (f z)) (+-comm m j) (K.up-to F.zero f st m j))
      (F.Cp-tr F.zero q (K.up-to F.zero f st j m)) (lf (j + m))
    ... | inj₁ below-one = under-one (f j) below-one
    ... | inj₂ above-one = go (f j) (lf j) above-one
  go (G.lc () c t g) l q
  go (G.em () a) l q
  go G.top l (inj₁ ())
  go G.top l (inj₂ ())

  coordinates : ∀ η → F.Gd F.zero (V.cO F.zero) η →
    Carrys⁺ (suc n) (V.up F.zero η)
  coordinates η e = old η e , go η (proj₂ e) (proj₁ e)

carry-stages⁺ : ∀ n → CarryStage⁺ n
carry-stages⁺ zero = (tt , tt) , (λ η e → read0-carry⁺ η)
carry-stages⁺ (suc n) = carry-stage-step⁺ n (carry-stages⁺ n)

pow-zero-carry⁺ : ∀ n → Carry⁺ (pow n F.zero)
pow-zero-carry⁺ n = carrys-last⁺ n F.zero (proj₁ (proj₁ (carry-stages⁺ n)))

tower-carry⁺ : ∀ n → Carry⁺ (V.tw n)
tower-carry⁺ n = subst Carry⁺ (pow-tw n) (pow-zero-carry⁺ n)

limit-carry⁺ : Carry⁺ V.Λ
limit-carry⁺ = tower-carry⁺

tower-source⁺ : ∀ n → Source⁺
tower-source⁺ n = source⁺ (V.tw n) (tower-carry⁺ n) (V.Legal-tw n)

limit-source⁺ : Source⁺
limit-source⁺ = source⁺ V.Λ limit-carry⁺ V.Legal-Λ

-- 同旧反例的非零层参数，改用原规范 cO 作下界的独立闭实例。
high-node : F.LF
high-node = F.lc (V.tw 2) (V.cO (V.tw 2)) (F.suc (V.tw 2))
  (λ _ _ → F.suc (V.tw 2))

high-node-carry⁺ : Carry⁺ high-node
high-node-carry⁺ =
  (one e-first , R.tower-reg 2 , R.tower-reg 2 , (λ _ _ → R.tower-reg 2)) ,
  V.Lgl-cO (V.tw 2) , cO-nested (V.tw 2) , tower-carry⁺ 2 ,
  (λ _ _ _ → tower-carry⁺ 2)

high-seed⁺ : PointB (V.tw 2) (V.cO (V.tw 2))
high-seed⁺ = seed⁺ high-node-carry⁺
```

编译定理为全 n 的 tower-carry⁺、limit-carry⁺ 及对应原 Legal 闭源。
有限测试无；未给序数值或 FGH 比较，没有提高值前沿。
全塔与 Λ 的正面目标成立，未触发规范实例不可满足时的止损。

新增使用的字段逐项为：

- pow-upN-carry⁺：原 LglB.Nested 在 Raw lc 中保存的 NestedLow；
  沿 Pre 槽位下降后成为目标 LF.lc 根的 Nested。
- carry-step⁺ 的后继行及本篇 go 后继行：cO-nested 对一切树层参数成立。
- 最小坐标的 rn：raw1 的 Nested 为 tt，连同原 Lgl 实填 LglB。
- 第一支与带 LglB 分支的 Carry⁺：沿原 YiK1b 次数归纳递归；
  Reg 全分支仍使用旧 read-regs／stages，没有收窄量词。

条件前提可满足：carry-stages⁺ 给每一次数的整个有限证书包，
coordinate-suc-root 只用于有原守卫的 Raw 0 正坐标（例如 raw1 自反）；
read-carrys⁺ 在 go 后继行被实际应用，pa 与 ra 均已构造。
guard-read-carry⁺ 的环境可取 y=0：Reg 为 tt，根路径为 one e-suc，
Carry⁺ (Ω̂ 0) 为 tt，输入 raw1 的守卫自反，LglB 为 tt , tt。
高层 seed⁺ 的闭应用另有 high-node-carry⁺ 与 high-seed⁺，没有空前提。

全部 cmpC 仍有字面公共界 f(j+m) 及其 Lgl，范围与 YiK1b 一致。
翻译账：只为旧证书增补树侧起点反例所缺的 Nested，复用原 Ω 的
有限合取归纳，不读记号规则、标签或基本列，没有阶段专属前提。
第 4 层逼出：无。无引用不等于树自足；完整生成器及 K2′⁺ 未证。
