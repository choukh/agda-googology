# 第十六轮的否定 (二): 以 `RelX⁺` 为输出关系的语义, 对第三条规则 `nκ⁺` 不可靠; `rk⁺` 的旧关系前提在 $\Lambda_\kappa$ 的 `J²⁺` 状态上不成立

> 不读记号. 入口 [NegSR16](NegSR16.lagda.md). 对着接口 [StrRel16If](StrRel16If.lagda.md) (定稿 2026-11-05 11:40) 写, 实例 $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$ (见 [NegSR16Kap](NegSR16Kap.lagda.md)).
>
> 1. **(定理) `vsum⁺`, `vs0⁺`**: `RelX⁺ hz hz` 值可靠 (三条新规则里只有 `in⁺` 能落在第 $0$ 层; `rk⁺` 与 `nκ⁺` 在第 $0$ 层没有实例, 因为第 $0$ 层没有节点). 用到 `inSum`: 分量的和不超过整体的和.
> 2. **(定理, 前提可满足) `ΩXκ`, `jN⁺`, `hawAct⁺`**: $\Lambda_\kappa$ 上一切 `TX` 对 $(t,t')$ 都有 `RelX⁺ t t′ (Ωd t) (Ωd t′)`; 其中 $(1,\Lambda_\kappa)$ 一对正是用 `nκ⁺` 得到的 (第三条规则的本意). 于是 `YN` 与自己 `J²⁺` 相关, `Act` 满足 `HAW²⁺`.
> 3. **(否定) `relNK`, `¬semNK`, `¬sem∀⁺`**: 层 $1$ 的节点 `xN` 与层 $\Lambda_\kappa$ 的 `xK` 由 `nκ⁺` 相关 (`relNK`), 但 `SemX²⁺ (hs hz) Λκ tt tt xN xK` 不成立: 第 $0$ 层目标对 $(\tau_0,\tau_0)$ 上两边的读数由 `NegSR16Kap.¬NK` 值上左大右小, 而 `RelX⁺ hz hz` 值可靠. 所以 "`RelX⁺` ⇒ `SemX²⁺`" 不成立.
> 4. **(否定) `relΩ`, `¬semΩ`**: 带开头 `n1` 的一对 `Ωd 1` 对 `Ωd Λκ` (由 `⨾⁺ n1⁺ relNK` 相关) 的 `SemX²⁺` 也不成立, 动作取 `Az` (`hawAz`: `Az` 满足 `HAW²⁺`; 关键是 `inv0`: `RelX⁺ hz hz x n0` 推出 $x$ 字面为 `n0`).
> 5. **(否定, 缺口的编译形式) `Old.¬J²YN`, `Old.¬rkPreYN`, `kRK`**: `YN` 满足 `J²⁺` 却**不**满足旧的 `J²` (`StrRel15If.J²`, 因为旧 `RelX` 里 $\Omega_1$ 对 $\Omega_{\Lambda_\kappa}$ 不相关); 所以以 `YN` 为状态的 `RkPre` 一律不成立. 而在同一实例上, 同一个节点 (层 $\Lambda_\kappa$, 坐标层 $0$) 在目标对 $(0,1)$ 上实际是左升右留 (`kRK`, `refl`), 那正是 `rk⁺` 要收的一对.
>
> **前提可满足.** 第 3, 4 条: `cp00`; `hawAct⁺`, `hawAz`; 上下文 `n0⁺`; 状态 `jN⁺`; 目标对 `(cp00 , s∞)`. 全部是定理, 否定不是空真. `YN` 是换世界之后的状态 (`NegSR16Kap.cvYN`), 接口的 `Lawcv⁺` 把任何 `J²⁺` 状态对送到第 $0$ 层累计为 `n0` 的状态对.
>
> **构造一路为什么需要这些.** `SemX²⁺` 是 `RelX⁺` 的语义; 构造一路要的是 "`RelX⁺` ⇒ `SemX²⁺`" (各规则的可靠性), 而 `nκ⁺` 的唯一目的就是让 $\Omega^{\mathsf H}$ 上闭项的状态进入 `J²⁺` (接口 §2), 状态的读数 (`Step` 输出 $\omega\cdot(\Omega_t⨾\ldots)$) 会作为链的段被运行 (`HtFeedFold.Chn`), 所以读数对要有语义. `rk⁺` 是接口给 "左升右留" 的规则; `OblRK²⁺` 要它在实际出现的一切参数上可用.
>
> **只否定什么.** 第 3 条只否定 `nκ⁺` 一句的可靠性 (以 `SemX²⁺` 为语义); 对任何第 $0$ 层值可靠的输出关系都成立 (`NegSR16Kap.noRel`), 所以换掉 `in⁺`, `rk⁺` 也救不回. 第 4 条要的是不尊重值的动作 `Az`; 它只否定 "动作前提只要求关系、不要求尊重值" 时带 `n1` 的保护; 不否定把动作限制到尊重值的一类之后的版本, 也不否定动作 `Act` 下 `Ωd 1` 对 `Ωd Λκ` 的语义 (那时 `z` 非空, 本文没有比). 第 5 条不说 `RelX⁺` 里 (`nl …`, `ni …`) 那一对一定不相关 (`rk⁺` 的参数是存在量化的, 本文没有对它求逆); 只说 `rk⁺` 不能以这组参数 (状态 `YN`) 来用. 不否定 `in⁺` (它的可靠性在 [NegSR16Law](NegSR16Law.lagda.md) 里是正面的定理). 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR16Sem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree
open import OCF.Align.NegSR16Kap renaming (module P to PK)
open import OCF.Align.StrRel11Rk Λκ lΛκ using (_⊑∞_; s∞; u∞; L∞)
open import OCF.Align.StrRel12Al using (CP)
open import OCF.Align.StrRel13Val using (cp00)
open import OCF.Align.StrRel14J Λκ lΛκ using (NE; here; ne⊕)
open import OCF.Align.StrRel16If Λκ lΛκ
open import OCF.Align.StrRel15If Λκ lΛκ using (TX)

open P using (Tg; tm; St; Df; yc; d; z; Run; Ig; Act; τ₀; Step; zeroD)
```

## 1 第 $0$ 层值可靠

```agda
-- 第 0 层: RelX⁺ hz hz 值可靠 (新规则只有 in⁺ 落在第 0 层)
sum-mono : ∀ {W} (x : D₀ W) {b b′} → b ≤ b′ → sum b x ≤ sum b′ x
pt-mono : ∀ {W} (e : ℕ → D₀ W) {b b′} → b ≤ b′ → ∀ n → pt b e n ≤ pt b′ e n
sum-mono n0 h = h
sum-mono n1 h = s≤ h
sum-mono (x ⨾ y) h = sum-mono y (sum-mono x h)
sum-mono (nl e) h = l≤ (λ n → ≤l n (pt-mono e h n))
sum-mono (ni () u) h
sum-mono (nκ () u) h
sum-mono (nw p x) h = sum-mono x h
pt-mono e h zero = h
pt-mono e h (suc n) = sum-mono (e n) (pt-mono e h n)

pt≥ : ∀ {W} b (e : ℕ → D₀ W) n → b ≤ pt b e n
pt≥ b e zero = ≤-refl b
pt≥ b e (suc n) = ≤-trans (pt≥ b e n) (⊲→≤ (sum-fst (pt b e n) (e n)))

-- 分量的和不超过整体的和 (同一底)
inSum : ∀ {W} {y x : D₀ W} → In y x → ∀ b → sum b y ≤ sum b x
inSum here b = ≤-refl _
inSum {x = a ⨾ c} (inL i) b = ≤-trans (inSum i b) (⊲→≤ (sum-fst (sum b a) c))
inSum {x = a ⨾ c} (inR i) b = ≤-trans (sum-mono _ (⊲→≤ (sum-fst b a))) (inSum i (sum b a))
inSum {y = y} {x = nl e} (inE n i) b = ≤l (suc n) (≤-trans (sum-mono y (pt≥ b e n)) (inSum i (pt b e n)))

vsum⁺ : ∀ {V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → RelX⁺ hz hz lV lV′ x x′ → b ≤ b′ → sum b x ≤ sum b′ x′
vsum⁺ {b′ = b′} {x′ = x′} n0⁺ h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
vsum⁺ n1⁺ h = s≤ h
vsum⁺ {b = b} {b′} (⨾⁺ {x = x} {y} {x′} {y′} hx hy) h = vsum⁺ {b = sum b x} {sum b′ x′} {x = y} {y′} hy (vsum⁺ {x = x} {x′} hx h)
vsum⁺ {b = b} {b′} (nl⁺ {d₁ = e} {d₁′ = e′} hd) h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b e n ≤ pt b′ e′ n
  go zero = h
  go (suc n) = vsum⁺ {b = pt b e n} {pt b′ e′ n} {x = e n} {e′ n} (hd n) (go n)
vsum⁺ {b = b} {b′} (pr⁺ {x = x} {x′ = x′} {y′} hx) h = ≤-trans (vsum⁺ {b = b} {b′} {x = x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
vsum⁺ {b = b} {b′} (nw⁺ {x = x} {x′} hp hx) h = vsum⁺ {b = b} {b′} {x = x} {x′} hx h
vsum⁺ (ni⁺ {r = ()} _ _)
vsum⁺ (κ⁺ {zz = ()} _)
vsum⁺ {b = b} {b′} {x = x} (in⁺ {y′ = y′} {x′} hx i) h = ≤-trans (vsum⁺ {b = b} {b′} {x = x} {y′} hx h) (inSum i b′)
vsum⁺ (rk⁺ r r′ lW lW′ ac ac₁ ac′ ac₁′ q₀ q₀′ ll ll′ A₀ A₀′ w w′ Y Y′ T T′ () pre tx e e′)
vsum⁺ (nκ⁺ {r = ()} _)

vs0⁺ : VS0 RelX⁺
vs0⁺ h = vsum⁺ h (≤-refl azero)
```

## 2 前提: $\Lambda_\kappa$ 上 $\Omega_t$ 跨层相关, `YN` 满足 `J²⁺`; `nκ⁺` 的否定

```agda
-- Λκ 上一切 TX 对: Ω_t 与 Ω_t′ 按 RelX⁺ 相关 (第三条规则 nκ⁺ 用在 (1, Λκ) 上)
ΩXκ : ∀ {t t′ m m′} {lm : Lg m} {lm′ : Lg m′} → t ⊲[ m ] Λκ → t′ ⊲[ m′ ] Λκ → t ⊑∞ t′ →
      RelX⁺ t t′ lm lm′ (Ωd t {m}) (Ωd t′ {m′})
ΩXκ hself hself le = ⨾⁺ n1⁺ (κ⁺ (λ p p′ lc lc′ cp → ni⁺ s∞ (λ p₁ p₁′ lc₁ lc₁′ cp₁ y y′ b → n1⁺)))
ΩXκ hself (hLim e hself) (u∞ ())
ΩXκ hself (hLim e (hsuc hself)) ()
ΩXκ (hLim e hself) hself le = ⨾⁺ n1⁺ (nκ⁺ (ni⁺ (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1⁺)))
ΩXκ (hLim e hself) (hLim e′ hself) le = ⨾⁺ n1⁺ (ni⁺ s∞ (λ p p′ lc lc′ cp y y′ b → n1⁺))
ΩXκ (hLim e hself) (hLim e′ (hsuc hself)) ()
ΩXκ (hLim e (hsuc hself)) hself le = pr⁺ n1⁺
ΩXκ (hLim e (hsuc hself)) (hLim e′ hself) le = pr⁺ n1⁺
ΩXκ (hLim e (hsuc hself)) (hLim e′ (hsuc hself)) le = n1⁺

jN⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J²⁺ lW lW′ (YN {W}) (YN {W′})
jN⁺ = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩXκ (tm T) (tm T′) (proj₂ tx)) n0⁺)) , n0⁺) , ((λ T → n0 , here) , (λ T → n0 , here))

stepOA⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J²⁺ lW lW′ Y Y′ → OA²⁺ lW lW′ (Step Y) (Step Y′)
stepOA⁺ hY T T′ tx = nl⁺ (λ _ → ⨾⁺ (ΩXκ (tm T) (tm T′) (proj₂ tx)) (proj₁ (proj₁ hY) T T′ tx))

hawAct⁺ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW²⁺ L L′ lW lW′ (Act {L} {W}) (Act {L′} {W′})
hawAct⁺ L L′ p p′ l l′ cp w w′ hw Y Y′ hY = stepOA⁺ hY

-- 第三条规则给出节点 ≤ nκ
relNK : RelX⁺ (hs hz) Λκ tt tt xN xK
relNK = nκ⁺ (ni⁺ (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1⁺))

¬semNK : ¬ SemX²⁺ (hs hz) Λκ tt tt xN xK
¬semNK s = noRel RelX⁺ vs0⁺
  (s tt tt (accL (hs hz)) (accL Λκ) llN hself C.self C.self cp00 Act Act (hawAct⁺ (hs hz) Λκ) n0 n0 n0⁺ YN YN jN⁺ (τ₀ tt) (τ₀ tt) (cp00 , s∞))

¬sem∀⁺ : ¬ (∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D (hs hz) V} {x′ : D Λκ V′} → RelX⁺ (hs hz) Λκ lV lV′ x x′ → SemX²⁺ (hs hz) Λκ lV lV′ x x′)
¬sem∀⁺ h = ¬semNK (h relNK)
```

## 3 带开头 `n1` 的一对, 动作 `Az`

```agda
-- 带开头 n1 的一对 (Ω₁ 对 Ω_Λκ), 动作 Az
inv0 : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {x : D₀ W} → RelX⁺ hz hz lW lW′ x (n0 {W = W′}) → x ≡ n0
inv0 n0⁺ = refl
inv0 (in⁺ h here) = inv0 h

module AzM {W W′} {lW : Lg W} {lW′ : Lg W′} (Y : St W) (Y′ : St W′) (hY : J²⁺ lW lW′ Y Y′) where
  azL : ∀ (a : D₀ W) → OA²⁺ lW lW′ (Az′ a Y) (Step Y′)
  azL n0 T T′ tx = n0⁺
  azL n1 = stepOA⁺ hY
  azL (x ⨾ y) = stepOA⁺ hY
  azL (nl e) = stepOA⁺ hY
  azL (nw p x) = stepOA⁺ hY

  azOA : ∀ (a : D₀ W) (b : D₀ W′) → RelX⁺ hz hz lW lW′ a b → OA²⁺ lW lW′ (Az′ a Y) (Az′ b Y′)
  azOA a n0 r = subst (λ a₁ → OA²⁺ lW lW′ (Az′ a₁ Y) (Az′ n0 Y′)) (symm (inv0 r)) (λ T T′ tx → n0⁺)
    where
    symm : ∀ {a b : D₀ W} → a ≡ b → b ≡ a
    symm refl = refl
  azOA a n1 r = azL a
  azOA a (x ⨾ y) r = azL a
  azOA a (nl e) r = azL a
  azOA a (nw p x) r = azL a

hawAz : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW²⁺ L L′ lW lW′ (Az {L} {W}) (Az {L′} {W′})
hawAz L L′ p p′ l l′ cp w w′ hw Y Y′ hY = AzM.azOA Y Y′ hY (z Y) (z Y′) (proj₂ (proj₁ hY))

relΩ : RelX⁺ (hs hz) Λκ tt tt (Ωd (hs hz) {azero}) (Ωd Λκ {azero})
relΩ = ⨾⁺ n1⁺ relNK

¬semΩ : ¬ SemX²⁺ (hs hz) Λκ tt tt (Ωd (hs hz) {azero}) (Ωd Λκ {azero})
¬semΩ s = noRel₂ RelX⁺ vs0⁺
  (s tt tt (accL (hs hz)) (accL Λκ) llN hself C.self C.self cp00 Az Az (hawAz (hs hz) Λκ) n0 n0 n0⁺ YN YN jN⁺ (τ₀ tt) (τ₀ tt) (cp00 , s∞))
```

## 4 `rk⁺` 的前提是旧关系: 在 `YN` 上不成立, 而左升右留确实出现

```agda
-- 旧不变量 J² (StrRel15If, 用 StrRel14If.RelX) 不含 YN: rk⁺ 的前提 RkPre 在这对状态上不成立
module Old where
  open import OCF.Align.StrRel14If Λκ lΛκ using () renaming (RelX to RelXo; ⨾ˣ to ⨾o; prˣ to pro; nlˣ to nlo)
  open import OCF.Align.StrRel15If Λκ lΛκ using () renaming (J² to J²o)

  ¬ΩΩ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → ¬ RelXo (hs hz) Λκ lW lW′ (Ωd (hs hz) {W}) (Ωd Λκ {W′})
  ¬ΩΩ (⨾o _ ())
  ¬ΩΩ (pro ())

  ¬seg : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → ¬ RelXo (hs hz) Λκ lW lW′ (Ωd (hs hz) {W} ⨾ n0) (Ωd Λκ {W′} ⨾ n0)
  ¬seg (⨾o h _) = ¬ΩΩ h
  ¬seg (pro (⨾o () _))
  ¬seg (pro (pro ()))

  ¬rd : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} →
        ¬ RelXo (hs hz) Λκ lW lW′ (nl (λ _ → Ωd (hs hz) {W} ⨾ n0)) (nl (λ _ → Ωd Λκ {W′} ⨾ n0))
  ¬rd (nlo h) = ¬seg (h 0)

  T₁ : Tg azero (hs hz) azero
  T₁ = P.tg C.self (hLim {c = azero} C.self hself) tt
  TΛ : Tg azero Λκ azero
  TΛ = P.tg C.self hself tt

  ¬J²YN : ¬ J²o {W = azero} {W′ = azero} tt tt YN YN
  ¬J²YN ((r , _) , _) = ¬rd (r T₁ TΛ (cp00 , L∞ azero s∞))

  -- rk⁺ 的前提的最后一项是旧的 J²; 以 YN 为状态的 RkPre 都不成立
  ¬rkPreYN : ∀ {ly ly′ W₀ W₀′ k k′} {lW₀ : Lg W₀} {lW₀′ : Lg W₀′} (r : StH W₀ k ly) (r′ : StH W₀′ k′ ly′)
               (u : ∀ {W₁} → W₀ ⊲ W₁ → Lg W₁ → Vs ly r W₁ → D ly W₁) (u′ : ∀ {W₁} → W₀′ ⊲ W₁ → Lg W₁ → Vs ly′ r′ W₁ → D ly′ W₁)
               (q₀ : W₀ ⊲ azero) (q₀′ : W₀′ ⊲ azero) (A₀ : Ig ly azero) (A₀′ : Ig ly′ azero) (w : D ly azero) (w′ : D ly′ azero) →
             ¬ RkPre {lW₀ = lW₀} {lW₀′} r r′ u u′ tt tt q₀ q₀′ A₀ A₀′ w w′ YN YN
  ¬rkPreYN r r′ u u′ q₀ q₀′ A₀ A₀′ w w′ (_ , _ , _ , _ , _ , j) = ¬J²YN j

-- 在 Λκ 与 YN 上, 左升右留实际出现 (同一个节点, 目标层 0 对 1)
rΛ0 : StH azero hz Λκ
rΛ0 = sL {c = azero} C.self (hsuc hself)

module K = NodeObl²⁺ {lV = tt} {lV′ = tt} rΛ0 rΛ0 (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λκ) (accL hz) (accL Λκ) (accL hz)
                     C.self C.self hself hself Act Act n0 n0 YN YN

kRK : (K.rkL (τ₀ tt) ≡ P.rise) × (K.rkR Old.T₁ ≡ P.keep (ss hself))
kRK = refl , refl

txRK : TX tt tt (τ₀ tt) Old.T₁
txRK = cp00 , u∞ s∞
```
