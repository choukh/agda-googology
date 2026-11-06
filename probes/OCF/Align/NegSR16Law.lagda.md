# 第十六轮的否定 (三): 两条状态律与 `in⁺` 的可靠性 (正面); 旧的对齐生成对 `RelX⁺` 不成立

> 不读记号. 入口 [NegSR16](NegSR16.lagda.md). 对着接口 [StrRel16If](StrRel16If.lagda.md) (定稿 2026-11-05 11:28) 写, 对一切合法的 $\Lambda$.
>
> 1. **(定理, 正面) `law⊕⁺`, `lawcv⁺`**: 接口 §3 的 `Law⊕⁺`, `Lawcv⁺` 成立 (证明同 `StrRel15NDead.law⊕`/`lawcv`, 只用 `⨾⁺`, `n0⁺`). 所以新规则不让状态关系对拼接 `⊕` 或换世界 `cv` 不封闭.
> 2. **(定理, 正面) `jwk`, `rptwk`, `sem-in⁺`**: 状态不变量与上下文**只在右边加东西**时保持 (`pr⁺`, `ne⊕`); 由此, `in⁺` 一句是可靠的: 若 $x$ 与 $y'$ 有 `SemX²⁺`, 且 $y'$ 是 $x'$ 的分量, 则 $x$ 与 $x'$ 有 `SemX²⁺`. 证明对 `In` 归纳: `⨾` 的右边与 `nl` 的第 $n$ 项在折叠里用的状态与上下文是起点在右边加了东西 (`Run` 与 `Rpt` 的字面), 输出是整棵输出的分量. **不用 `NE`**: `in⁺` 的可靠性与 `StrRel13Later.¬laterV` 无关; `¬laterV` 的那一对只是推不出来 (接口的判断), 不是被语义排除.
> 3. **(否定) `¬genAl⁺`**: 旧的对齐生成 (`StrRel12Rel.genAl` 的形状: 第 $0$ 层关系 ⇒ 两条 `sum-fst` 路径的 `Al`) 对 `RelX⁺ hz hz` 不成立. 实例 `in⁺ n1⁺ (inE 0 here) : n1 ≤ nl (λ _ → n1)`; 左路径是 `suc self`, 右路径是 `lim 0 self`, `StrRel13Kr.¬alLim0` 说 `Al` 对不齐. 前提可满足: `Adm` 取 $\delta=0$ (`adm1ω`).
>
> **构造一路为什么需要这些.** 第 1 条: `Law⊕⁺`, `Lawcv⁺` 是接口的律. 第 2 条: `RelX⁺ ⇒ SemX²⁺` 要逐条规则证, `in⁺` 是其中一条. 第 3 条: `κ⁺` 一句在第 $0$ 层目标上的语义 (`nκ` 回灌) 在旧的证明 (`StrRel12Kp`) 里由状态的第 $0$ 层分量 `z Y ≤ z Y′` 生成第 $0$ 格的对齐; `J²⁺` 里这一分量是 `RelX⁺ hz hz`, 可以由 `in⁺` 推出.
>
> **只否定什么.** 第 3 条只否定 "照旧用 `genAl` 的形状由 `RelX⁺ hz hz` 生成对齐", 不否定 `κ⁺` 的可靠性 (值上没有找到反例; 判断: 要给 `Al` 加 "左边进入右边极限的第 $n$ 段" 的构造子, `In` 的 `inE n` 字面给出 $n$, 不需要从值求位置, 所以不是 `StrRel2Neg.phead→LPO` 的形状; 没有编译). 第 1, 2 条是正面的.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.NegSR16Law (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (hz; D; D₀; n1; nl; nw; _⨾_; AccY; sum; sum-fst; Lg-sum; pt)
open import OCF.Align.StrRel11Rk Λ lΛ using (s∞)
open import OCF.Align.StrRel12Al using (cp-tr)
open import OCF.Align.StrRel14J Λ lΛ using (ne⊕; necv)
open import OCF.Align.StrRel16If Λ lΛ
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel13Kr using (¬alLim0)
open P using (tg↑; τ₀; St; Df; Ig; LW; Run; Rpt; _⊕⟨_⟩_)
```

## 1 两条状态律

```agda
-- 两条状态律 (正面)
law⊕⁺ : Law⊕⁺
law⊕⁺ {lW = lW} {lW′} tp Y Y′ Δ Δ′ ((r , rz) , (ne , ne′)) O =
  ((λ T T′ tx → ⨾⁺ (r T T′ tx) (O T T′ tx)) , ⨾⁺ rz (O (τ₀ lW) (τ₀ lW′) (tp , s∞))) ,
  (ne⊕ {lW = lW} Y Δ ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

lawcv⁺ : Lawcv⁺
lawcv⁺ {q = q} {q′ = q′} ap Y Y′ ((r , rz) , (ne , ne′)) =
  ((λ T T′ tx → r (tg↑ q T) (tg↑ q′ T′) (cp-tr ap (proj₁ tx) , proj₂ tx)) , n0⁺) ,
  (necv q Y ne , necv q′ Y′ ne′)
```

## 2 `in⁺` 的可靠性

```agda
-- 右边加东西: 状态不变量与上下文都保持
jwk : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} (Δ′ : Df W′) → J²⁺ lW lW′ Y Y′ → J²⁺ lW lW′ Y (Y′ ⊕⟨ lW′ ⟩ Δ′)
jwk {lW′ = lW′} {Y′ = Y′} Δ′ ((r , rz) , (ne , ne′)) = ((λ T T′ tx → pr⁺ (r T T′ tx)) , pr⁺ rz) , (ne , ne⊕ {lW = lW′} Y′ Δ′ ne′)

-- nl 的第 n 项的运行用的上下文与状态, 相对于起点只在右边加了东西
rptwk : ∀ {L L′ W W′ V₀′} {lW : Lg W} {lW′ : Lg W′} (ac′ : AccY L′) (e : ℕ → D L′ V₀′) (q′ : V₀′ ⊲ W′) (ll′ : LW L′ W′) (A₀′ : Ig L′ W′)
        {w : D L W} {w′ : D L′ W′} {Y : St W} {Y′ : St W′} → RelX⁺ L L′ lW lW′ w w′ → J²⁺ lW lW′ Y Y′ → ∀ n →
        RelX⁺ L L′ lW lW′ w (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n)) × J²⁺ lW lW′ Y (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n))
rptwk ac′ e q′ ll′ A₀′ hw hY zero = hw , hY
rptwk {lW′ = lW′} ac′ e q′ ll′ A₀′ {w′ = w′} {Y′ = Y′} hw hY (suc n) =
  pr⁺ (proj₁ (rptwk ac′ e q′ ll′ A₀′ hw hY n)) ,
  jwk (Run ac′ (e n) q′ lW′ ll′ A₀′ (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n)) (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n)))
      (proj₂ (rptwk ac′ e q′ ll′ A₀′ hw hY n))

-- in⁺ 一句的可靠性: 前提的语义 ⇒ 结论的语义
sem-in⁺ : ∀ {L L′ V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {y′ x′ : D L′ V′} →
          SemX²⁺ L L′ lV lV′ x y′ → In y′ x′ → SemX²⁺ L L′ lV lV′ x x′
sem-in⁺ s here = s
sem-in⁺ s (inL i) lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx =
  in⁺ (sem-in⁺ s i lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx) (inL here)
sem-in⁺ {x′ = a ⨾ b} s (inR i) lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx =
  in⁺ (sem-in⁺ s i lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w (w′ ⨾ nw q′ a) (pr⁺ hw) Y (Y′ ⊕⟨ lW′ ⟩ Run ac′ a q′ lW′ ll′ A₀′ w′ Y′)
         (jwk (Run ac′ a q′ lW′ ll′ A₀′ w′ Y′) hY) T T′ tx) (inR here)
sem-in⁺ {x′ = nl e} s (inE n i) lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w w′ hw Y Y′ hY T T′ tx =
  in⁺ (sem-in⁺ s i lW lW′ ac ac′ ll ll′ q q′ cp A₀ A₀′ ha w (proj₁ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n))
         (proj₁ (rptwk ac′ e q′ ll′ A₀′ hw hY n)) Y (proj₂ (Rpt ac′ e q′ lW′ ll′ A₀′ w′ Y′ n)) (proj₂ (rptwk ac′ e q′ ll′ A₀′ hw hY n)) T T′ tx)
      (inE n here)
```

## 3 旧的对齐生成对 `RelX⁺` 不成立

```agda
-- 第 0 层生成对齐: 旧的 genAl (StrRel12Rel) 对 RelX⁺ hz hz 不成立
GenAl⁺ : Set
GenAl⁺ = ∀ {L L′ V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺ hz hz lV lV′ x x′ →
         (w : Lg b) (w′ : Lg b′) → b ≤ b′ → Adm (sum b x) (sum b′ x′) L L′ →
         Al L L′ (sum-fst b x) (Lg-sum b x w) (sum-fst b′ x′) (Lg-sum b′ x′ w′)

x₁ xω : D₀ azero
x₁ = n1
xω = nl (λ _ → n1)

rel1ω : RelX⁺ hz hz tt tt x₁ xω
rel1ω = in⁺ n1⁺ (inE 0 here)

adm1ω : Adm (sum azero x₁) (sum azero xω) (sum azero x₁) (sum azero xω)
adm1ω = azero , ≤-refl _ , ≤-refl _

¬genAl⁺ : ¬ GenAl⁺
¬genAl⁺ g = ¬alLim0 {f = pt azero (λ _ → n1)}
  (g {L = sum azero x₁} {L′ = sum azero xω} {b = azero} {b′ = azero} {x = x₁} {x′ = xω} rel1ω tt tt (≤-refl azero) adm1ω)
```
