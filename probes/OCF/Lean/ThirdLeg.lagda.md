# Third (五): 回灌用的合法化, 每个底的世界

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. θ 累加与它的单调, 合法取自 [LHRecLeg](LHRecLeg.lagda.md) 的 `New` (不改).
>
> **`legS n`.** 第 $n$ 个底的合法化, 输出对一切输入合法 (`Lg-legS`). 指标种类的结点取 θ 累加 (坐标里的结点映成指标分量的旧种类, 同 `LHRecFl` 的地板); **其余种类的结点取常值分支** ($e\mapsto\mathrm{leg}\,(h\,\mathtt{bot})$): 合法 (相邻坐标的分支字面相同), 但丢掉了分支对坐标的依赖 (判断: 有损). 累加到一切种类要对 `Tw` 的坐标递归, 本路没有写.
>
> **世界.** 第 $n+1$ 个底的世界 `wS (n+1)`: 指标分量是 (`wS n`, 界 `bnd n`), 其余分量是默认世界 (`wT`, 界都是 $0$); `bnd 0` 是模块参数 $c_0$ (可数树), `bnd (n+1)` 是地板的合法化. `NegThirdPre.upd→WLPO` 说按分量写回推出 WLPO; 这里不写回, 世界在每一站固定, 只有指标分量的界是真的 (判断: 穿过其余种类的 $\Omega$-结点只能走 `bot`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdLeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw
open import OCF.Lean.LHRecLeg using (Ctx; here; viaL; lgpw; module New)

module _ {S : KS} where
  Σᴸ : (ℕ → HB S) → ℕ → HB S
  Σᴸ f zero = f 0
  Σᴸ f (suc n) = Σᴸ f n ⊞ f (suc n)

cxX : ∀ U → Ctx (XSof U) (step U)
cxX U = viaL {F = FX U} here (inj₁ tt)

module LX (U : KS) where
  X = XSof U

  legX : HB X → HB X
  legN : (κ : K X) → (E X κ → HB X) → HB X
  legX hz = hz
  legX (hs a) = hs (legX a)
  legX (hl f) = hl (Σᴸ (λ n → legX (f n)))
  legX (hΩ κ h) = legN κ h
  legN (inj₁ _ , inj₂ _) h = hΩ ιK (New.θ (cxX U) (λ e → legX (h e)))
  legN κ@(inj₁ _ , inj₁ _) h = hΩ κ (λ _ → legX (h (bot X κ)))
  legN κ@(inj₂ _ , _) h = hΩ κ (λ _ → legX (h (bot X κ)))

  Lg-legX : ∀ a → LgB (legX a)
  Lg-legN : ∀ κ h → LgB (legN κ h)
  Lg-Σ : ∀ f n → LgB (Σᴸ (λ m → legX (f m)) n)
  Lg-legX hz = tt
  Lg-legX (hs a) = Lg-legX a
  Lg-legX (hl f) = (λ n → ⊞-fst (Σᴸ (λ m → legX (f m)) n) (legX (f (suc n)))) , Lg-Σ f
  Lg-legX (hΩ κ h) = Lg-legN κ h
  Lg-legN (inj₁ _ , inj₂ _) h =
    (λ lw b b′ p → New.θ-⊲ (cxX U) (λ e → legX (h e)) p) ,
    (λ lw b → New.Lg-θ (cxX U) (λ e → legX (h e)) (λ e → Lg-legX (h e)) _
       (lgB⊲ b (proj₁ (lw (inj₁ tt))) (proj₂ (lw (inj₁ tt)))))
  Lg-legN κ@(inj₁ _ , inj₁ _) h = (λ lw b b′ p → hself) , (λ lw b → Lg-legX (h (bot X κ)))
  Lg-legN κ@(inj₂ _ , _) h = (λ lw b b′ p → hself) , (λ lw b → Lg-legX (h (bot X κ)))
  Lg-Σ f zero = Lg-legX (f 0)
  Lg-Σ f (suc n) = Lg-⊞ _ (legX (f (suc n))) (Lg-Σ f n) (Lg-legX (f (suc n)))

legC : Cd → Cd
legC hz = hz
legC (hs a) = hs (legC a)
legC (hl f) = hl (Σᴸ (λ n → legC (f n)))
legC (hΩ () _)

Lg-legC : ∀ a → LgB (legC a)
Lg-ΣC : ∀ f n → LgB (Σᴸ (λ m → legC (f m)) n)
Lg-legC hz = tt
Lg-legC (hs a) = Lg-legC a
Lg-legC (hl f) = (λ n → ⊞-fst (Σᴸ (λ m → legC (f m)) n) (legC (f (suc n)))) , Lg-ΣC f
Lg-legC (hΩ () _)
Lg-ΣC f zero = Lg-legC (f 0)
Lg-ΣC f (suc n) = Lg-⊞ _ (legC (f (suc n))) (Lg-ΣC f n) (Lg-legC (f (suc n)))

legS : ∀ n → HB (Sb n) → HB (Sb n)
legS zero = legC
legS (suc n) = LX.legX (Sb n)

Lg-legS : ∀ n a → LgB (legS n a)
Lg-legS zero = Lg-legC
Lg-legS (suc n) = LX.Lg-legX (Sb n)

-- 默认世界: 塔的每层界都是 0
wT : ∀ U → Wd U → ∀ m → Wd (Tw U m)
wT U w hz = w
wT U w (hs x) = wT U w x , hz
wT U w (hl f) = λ n → wT U w (f n)
wT U w (hΩ κ g) = λ e → wT U w (g e)

lwT : ∀ U w → LgW U w → ∀ m → LgW (Tw U m) (wT U w m)
lwT U w lw hz = lw
lwT U w lw (hs x) = lwT U w lw x , tt
lwT U w lw (hl f) = λ n → lwT U w lw (f n)
lwT U w lw (hΩ κ g) = λ e → lwT U w lw (g e)

-- 世界由第 0 层的界 c₀ 决定: 闭项的对角把上一个输出喂回 c₀
module W (c₀ : Cd) (lc₀ : LgB c₀) where
  bnd : ∀ n → HB (Sb n)
  bnd zero = c₀
  bnd (suc n) = legS (suc n) (fl (suc n))

  lg-bnd : ∀ n → LgB (bnd n)
  lg-bnd zero = lc₀
  lg-bnd (suc n) = Lg-legS (suc n) (fl (suc n))

  wS : ∀ n → Wd (Sb n)
  wS zero = tt
  wS (suc n) (inj₁ _) = wS n , bnd n
  wS (suc n) (inj₂ c) = wT (Sb n) (wS n) (hs c)

  lwS : ∀ n → LgW (Sb n) (wS n)
  lwS zero = tt
  lwS (suc n) (inj₁ _) = lwS n , lg-bnd n
  lwS (suc n) (inj₂ c) = lwT (Sb n) (wS n) (lwS n) (hs c)

  -- 每个种类的代表坐标: 世界里这个种类的界 (`pk-top`: 界之下的坐标都是它的第一位置)
  module PT (U : KS) (u : Wd U) (pk : (κ : K U) → E U κ) (pkb : ∀ κ → Bd U κ (pk κ) u)
            (ptp : ∀ κ e → Bd U κ e u → Pr U κ u e (pk κ)) where
    pkT : ∀ m (κ : K (Tw U m)) → E (Tw U m) κ
    pkT hz κ = pk κ
    pkT (hs x) (inj₁ κ) = pkT x κ
    pkT (hs x) (inj₂ _) = hz
    pkT (hl f) (n , κ) = pkT (f n) κ
    pkT (hΩ κ₀ g) (e , κ) = pkT (g e) κ

    pkT-bd : ∀ m κ → Bd (Tw U m) κ (pkT m κ) (wT U u m)
    pkT-bd hz κ = pkb κ
    pkT-bd (hs x) (inj₁ κ) = pkT-bd x κ
    pkT-bd (hs x) (inj₂ _) = hself
    pkT-bd (hl f) (n , κ) = pkT-bd (f n) κ
    pkT-bd (hΩ κ₀ g) (e , κ) = pkT-bd (g e) κ

    pkT-top : ∀ m κ e → Bd (Tw U m) κ e (wT U u m) → Pr (Tw U m) κ (wT U u m) e (pkT m κ)
    pkT-top hz κ e b = ptp κ e b
    pkT-top (hs x) (inj₁ κ) e b = pkT-top x κ e b
    pkT-top (hs x) (inj₂ _) e b = b
    pkT-top (hl f) (n , κ) e b = pkT-top (f n) κ e b
    pkT-top (hΩ κ₀ g) (c , κ) e b = pkT-top (g c) κ e b

  pkS : ∀ n (κ : K (Sb n)) → E (Sb n) κ
  pk-bd : ∀ n κ → Bd (Sb n) κ (pkS n κ) (wS n)
  pk-top : ∀ n κ e → Bd (Sb n) κ e (wS n) → Pr (Sb n) κ (wS n) e (pkS n κ)
  pkS zero ()
  pkS (suc n) (inj₁ _ , inj₂ _) = bnd n
  pkS (suc n) (inj₁ _ , inj₁ κ) = pkS n κ
  pkS (suc n) (inj₂ c , κ) = PT.pkT (Sb n) (wS n) (pkS n) (pk-bd n) (pk-top n) (hs c) κ
  pk-bd zero ()
  pk-bd (suc n) (inj₁ _ , inj₂ _) = hself
  pk-bd (suc n) (inj₁ _ , inj₁ κ) = pk-bd n κ
  pk-bd (suc n) (inj₂ c , κ) = PT.pkT-bd (Sb n) (wS n) (pkS n) (pk-bd n) (pk-top n) (hs c) κ
  pk-top zero ()
  pk-top (suc n) (inj₁ _ , inj₂ _) e b = b
  pk-top (suc n) (inj₁ _ , inj₁ κ) e b = pk-top n κ e b
  pk-top (suc n) (inj₂ c , κ) e b = PT.pkT-top (Sb n) (wS n) (pkS n) (pk-bd n) (pk-top n) (hs c) κ e b
```
