# SameV (三): 跨底折叠沿配对单调

> 不含记号. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 模块参数: `uipC` (`Cd` 上的 UIP, 经 ValC, ValX 的定理), `SL : ShLaw I`, 配对 `Mt`, 地板律 `tp`. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValC*`, `OCF.Lean.ValX*` (只用, 不改), [SameVRel](SameVRel.lagda.md), [SameVMono](SameVMono.lagda.md).
>
> **关系 `_≼X_`.** $\Omega_1$ 层上的跨结构关系. 与 `ValXRel._≤X_` 的差:
>
> 1. **`Ω≼Ω`.** 两边的种类不要求同分量: 只要层配对 (`lvX κ ~ lvX κ′`), 分支是逻辑关系. 种类的回灌与新世界的差写成字段: 分支取在回灌后的坐标处 (对一切一对世界), `Wl` 是新世界的值单调. 这样本身 ($\Omega_1$, 动世界) 与拷贝 (不动世界) 不必在关系里分开: 一个种类对能否进关系, 取决于能否给出 `Wl` 与分支的比较. `NegValXSelf.self≰copy` 说本身对拷贝给不出.
> 2. **`≼Ω`.** 右边取回灌后的一支, 对一切世界.
>
> **定理 `crossX`.** 世界 $B_1\le B_2$, 目标对 $t\sim t'$, 界 $b\preceq b'$, 输入 $x\preceq_X y$, 右边 `MoX` ⟹ 跨底折叠相关. 左边不要 `MoX`. 与 `crossΦ` 同样, 决定由配对的律决定, 这一步不用 UIP; 路线引理只经 `brX` 在同层出现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Lean.SameVRel as SR
import OCF.Lean.ValXRel as XR
module OCF.Lean.SameVX (I : CRwIf) (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) (SL : XR.ShLaw I) (Mt : SR.Match I) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
open import OCF.Lean.ValCMono I uipC
open import OCF.Lean.ValXRel I
open import OCF.Lean.ValXBase I SL
open import OCF.Lean.ValXMono I uipC SL using (MoXΦ; moChX; kpX; brX; dvX)
open import OCF.Lean.SameVMono I uipC Mt
```

## §1 关系

`Wl κ κ′`: 进入两个种类的相关坐标后, 新世界值单调.

```agda
Wl : (κ κ′ : K XS) → Set
Wl κ κ′ = ∀ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ → ∀ {d d′} → LE (lvX κ) (lvX κ′) d d′ →
          LeAt hz (nW κ l₁ d) (nW κ′ l₂ d′)

infix 4 _≼X_
data _≼X_ : HX → HX → Set where
  z≼  : ∀ {b} → hz ≼X b
  s≼s : ∀ {a b} → a ≼X b → hs a ≼X hs b
  ≼s  : ∀ {a b} → a ≼X b → a ≼X hs b
  l≼l : ∀ {f g} (σ : ℕ → ℕ) → Inc σ → (∀ n → f n ≼X g (σ n)) → hl f ≼X hl g
  ≼l  : ∀ {a g} n → a ≼X g n → a ≼X hl g
  ≼Ω  : ∀ {a κ g} c → LeAt (lvX κ) c (top b⊥ (lvX κ)) → MoAt (lvX κ) c →
        (∀ B → a ≼X g (psh (P κ) B (toX κ c))) → a ≼X hΩ κ g
  Ω≼Ω : ∀ {κ κ′ g g′} → lvX κ ~ lvX κ′ → Wl κ κ′ →
        (∀ d d′ → MoAt (lvX κ′) d′ → LE (lvX κ) (lvX κ′) d d′ → ∀ B₁ B₂ → LeAt hz B₁ B₂ →
           g (psh (P κ) B₁ (toX κ d)) ≼X g′ (psh (P κ′) B₂ (toX κ′ d′))) →
        hΩ κ g ≼X hΩ κ′ g′
```

**右边加一段, 两边都加.**

```agda
≼X⊞ : ∀ {a b} → a ≼X b → ∀ z → a ≼X b ⊞ z
≼X⊞ p hz = p
≼X⊞ p (hs z) = ≼s (≼X⊞ p z)
≼X⊞ p (hl f) = ≼l 0 (≼X⊞ p (f 0))
≼X⊞ p (hΩ κ g) = ≼Ω hz Rel.z≤ tt (λ B → ≼X⊞ p (g (psh (P κ) B (toX κ hz))))

⊞X : ∀ {a a′ x y} → a ≼X a′ → x ≼X y → a ⊞ x ≼X a′ ⊞ y
⊞X p (z≼ {b = y}) = ≼X⊞ p y
⊞X p (s≼s q) = s≼s (⊞X p q)
⊞X p (≼s q) = ≼s (⊞X p q)
⊞X p (l≼l σ i h) = l≼l σ i (λ n → ⊞X p (h n))
⊞X p (≼l n q) = ≼l n (⊞X p q)
⊞X p (≼Ω c bd mc q) = ≼Ω c bd mc (λ B → ⊞X p (q B))
⊞X p (Ω≼Ω ev wl h) = Ω≼Ω ev wl (λ d d′ md r B₁ B₂ w → ⊞X p (h d d′ md r B₁ B₂ w))
```

## §2 定理

```agda
module ThmX (tp : ∀ {k k′} → k ~ k′ → LE k k′ (top b⊥ k) (top b⊥ k′)) where
  open Thm tp

  mutual
    crossX : ∀ (a a′ : Acc bX hz) {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
             ∀ {t t′} (pt₁ : t ⊲ B₁) (pt₂ : t′ ⊲ B₂) → t ~ t′ → {b : H t} {b′ : H t′} → Ch.Bx t t′ b b′ →
             ∀ {x} y (n₁ : PH PSX B₁ x) (n₂ : PH PSX B₂ y) → MoX y → x ≼X y →
             LE t t′ (FXa a B₁ l₁ pt₁ b x n₁) (FXa a′ B₂ l₂ pt₂ b′ y n₂)
    crossX a a′ l₁ l₂ w {t} {t′} pt₁ pt₂ ev B y n₁ n₂ my z≼ = Lm.one≼ t t′ (oneX a′ l₂ pt₂ _ y n₂)
    crossX a a′ l₁ l₂ w {t} {t′} pt₁ pt₂ ev B {hs x} (hs y) n₁ n₂ my (s≼s p) =
      R2.l≼l (λ n → n) (L.idInc t) (Lm.mul≼ t t′ (crossX a a′ l₁ l₂ w pt₁ pt₂ ev B y n₁ n₂ my p))
    crossX a a′ l₁ l₂ w pt₁ pt₂ ev B (hs y) n₁ n₂ my (≼s p) =
      R2.≼l 0 (crossX a a′ l₁ l₂ w pt₁ pt₂ ev B y n₁ n₂ my p)
    crossX a a′ l₁ l₂ w {t} {t′} pt₁ pt₂ ev B {hl f} (hl g) n₁ n₂ my (l≼l σ i h) =
      R2.l≼l σ i (Lm.Σ≼ t t′ _ _ σ i (λ n → crossX a a′ l₁ l₂ w pt₁ pt₂ ev B (g (σ n)) (n₁ n) (n₂ (σ n)) (my (σ n)) (h n)))
    crossX a a′ l₁ l₂ w {t} {t′} pt₁ pt₂ ev B (hl g) n₁ n₂ my (≼l n p) =
      R2.≼l n (Lm.tr≼ t t′ (crossX a a′ l₁ l₂ w pt₁ pt₂ ev B (g n) n₁ (n₂ n) (my n) p) (Ac0.Σ-ge t′ _ n))
    crossX a a′ {B₁} {B₂} l₁ l₂ w {t} {t′} pt₁ pt₂ ev B@(mb′ , tb , bb) (hΩ κ g′) n₁ (ev₂ , pg₂) my (≼Ω c bd mc p) =
      Lm.tr≼ t t′
        (crossX a a′ l₁ (lgW κ l₂ c) (L.≤-trans hz w (nW-up κ l₂ c)) pt₁ (ptW κ l₂ pt₂ c) ev B
           (g′ (psh (P κ) B₂ (toX κ c))) n₁ (pgW κ l₂ pg₂ c) (brMo κ g′ B₂ my c mc) (p B₂))
        (brX a′ l₂ pt₂ (Ac0.bnd-refl t′ mb′ tb) κ g′ ev₂ pg₂ my c bd mc)
    crossX (acc rs) (acc rs′) {B₁} {B₂} l₁ l₂ w {t} {t′} pt₁ pt₂ ev {b} {b′} B {hΩ κ g} (hΩ κ′ g′) (ev₁ , pg₁) (ev₂ , pg₂) my (Ω≼Ω e wl h) =
      ΦΩX rs l₁ pt₁ b κ g ev₁ pg₁ (λ z → LE t t′ z (FXa (acc rs′) B₂ l₂ pt₂ b′ (hΩ κ′ g′) (ev₂ , pg₂)))
        (ΦΩX rs′ l₂ pt₂ b′ κ′ g′ ev₂ pg₂
          (λ z → LE t t′ (caseDc (pick S⊥ (toX κ) (pkX κ ev₁) (cmpB (pkX κ ev₁) pt₁ tt l₁))
                            (KcX rs l₁ pt₁ b κ g pg₁) (ScX rs l₁ pt₁ b κ g pg₁) (AcX rs l₁ pt₁ b κ g pg₁)) z)
          (mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl (dvX κ ev₁ pt₁ l₁) (dvX κ′ ev₂ pt₂ l₂) my
             (λ d d′ md r → h d d′ md r B₁ B₂ w)))

    mΩX : ∀ rs rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {t t′} (pt₁ : t ⊲ B₁) (pt₂ : t′ ⊲ B₂) → t ~ t′ → {b : H t} {b′ : H t′} → Ch.Bx t t′ b b′ →
          ∀ κ κ′ (g : E XS κ → HX) (g′ : E XS κ′ → HX) (pg₁ : PGt B₁ κ g) (pg₂ : PGt B₂ κ′ g′) →
          lvX κ ~ lvX κ′ → Wl κ κ′ → ∀ {pk pk′ d d′} →
          DV (lvX κ) t (toX κ) pk d → DV (lvX κ′) t′ (toX κ′) pk′ d′ → MoX (hΩ κ′ g′) →
          (∀ c c′ → MoAt (lvX κ′) c′ → LE (lvX κ) (lvX κ′) c c′ →
             g (psh (P κ) B₁ (toX κ c)) ≼X g′ (psh (P κ′) B₂ (toX κ′ c′))) →
          LE t t′ (caseDc d (KcX rs l₁ pt₁ b κ g pg₁) (ScX rs l₁ pt₁ b κ g pg₁) (AcX rs l₁ pt₁ b κ g pg₁))
                  (caseDc d′ (KcX rs′ l₂ pt₂ b′ κ′ g′ pg₂) (ScX rs′ l₂ pt₂ b′ κ′ g′ pg₂) (AcX rs′ l₂ pt₂ b′ κ′ g′ pg₂))
    mΩX rs rs′ {B₁} {B₂} l₁ l₂ w {t} {t′} pt₁ pt₂ ev {b} {b′} B κ κ′ g g′ pg₁ pg₂ e wl (dk κ₁ e₁ fr₁ ft₁ u₁) (dk κ₂ e₂ fr₂ ft₂ u₂) my H′ =
      keepX κ₁ κ₂ e₁ e₂ fr₁ fr₂ ft₁ ft₂ e (br (acc rs) l₁ pt₁ κ g pg₁ b) (br (acc rs′) l₂ pt₂ κ′ g′ pg₂ b′)
        (λ d d′ md r → brC rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ wl my H′ d d′ md r)
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl (dk κ₁ e₁ fr₁ ft₁ u₁) ds my H′ = ⊥-elim (nos (~s e ev u₁))
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl (dk κ₁ e₁ fr₁ ft₁ u₁) (da q′ pp′) my H′ = ⊥-elim (nos′ (~s e ev u₁) q′)
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl ds (dk κ₂ e₂ fr₂ ft₂ u₂) my H′ =
      ⊥-elim (nos (subst (λ z → hs z ⊲ _) (~fun e ev) u₂))
    mΩX rs rs′ {B₁} {B₂} l₁ l₂ w {t} {t′} pt₁ pt₂ ev {b} {b′} B κ κ′ g g′ pg₁ pg₂ e wl ds ds my H′ =
      Ch.chX-hl t t′ (λ b₁ → br (acc rs) l₁ pt₁ κ g pg₁ b₁ b₁) (λ b₁ → br (acc rs′) l₂ pt₂ κ′ g′ pg₂ b₁ b₁) B
        (kpX (acc rs′) l₂ κ′ pt₂ g′ pg₂ my)
        (λ {b₁} {b₂} B′@(m2 , t2 , le) → brC rs rs′ l₁ l₂ w pt₁ pt₂ ev B′ κ κ′ g g′ pg₁ pg₂ wl my H′ b₁ b₂ m2 le)
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl ds (da q′ pp′) my H′ =
      ⊥-elim (noPP (subst (λ z → Pp _ z) (~fun e ev) pp′) hself)
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl (da q pp) (dk κ₂ e₂ fr₂ ft₂ u₂) my H′ =
      ⊥-elim (noPP (~pp ev e pp) (⊏⊑ u₂))
    mΩX rs rs′ l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ e wl (da q pp) ds my H′ =
      ⊥-elim (noPP (~pp ev e pp) hself)
    mΩX rs rs′ {B₁} {B₂} l₁ l₂ w {t} {t′} pt₁ pt₂ ev {b} {b′} B κ κ′ g g′ pg₁ pg₂ e wl {pk} {pk′} (da q pp) (da q′ pp′) my H′ =
      crossΦ (apWf (lvX κ)) (rs b⊥ (lvX κ) lx) (rs′ b⊥ (lvX κ′) lx) (lg↓ pk l₁) (lg↓ pk′ l₂) q q′ ev B
        (hl (chain (top b⊥ (lvX κ′)) (λ b₁ → br (acc rs′) l₂ (⊏⊑ pk′) κ′ g′ pg₂ b₁ b₁)))
        (moChX (acc rs′) l₂ κ′ (⊏⊑ pk′) g′ pg₂ my)
        (Ch.chX-hl (lvX κ) (lvX κ′) (λ b₁ → br (acc rs) l₁ (⊏⊑ pk) κ g pg₁ b₁ b₁) (λ b₁ → br (acc rs′) l₂ (⊏⊑ pk′) κ′ g′ pg₂ b₁ b₁)
           (Mo-top (lvX κ′) , L.≤-refl (lvX κ′) _ , tp e)
           (kpX (acc rs′) l₂ κ′ (⊏⊑ pk′) g′ pg₂ my)
           (λ {b₁} {b₂} B′@(m2 , t2 , le) → brC rs rs′ l₁ l₂ w (⊏⊑ pk) (⊏⊑ pk′) e B′ κ κ′ g g′ pg₁ pg₂ wl my H′ b₁ b₂ m2 le))

    -- 分支的比较: 界任意 (相关), 坐标相关
    brC : ∀ rs rs′ {B₁ B₂} (l₁ : LgB B₁) (l₂ : LgB B₂) → LeAt hz B₁ B₂ →
          ∀ {t t′} (pt₁ : t ⊲ B₁) (pt₂ : t′ ⊲ B₂) → t ~ t′ → {b : H t} {b′ : H t′} → Ch.Bx t t′ b b′ →
          ∀ κ κ′ (g : E XS κ → HX) (g′ : E XS κ′ → HX) (pg₁ : PGt B₁ κ g) (pg₂ : PGt B₂ κ′ g′) → Wl κ κ′ → MoX (hΩ κ′ g′) →
          (∀ c c′ → MoAt (lvX κ′) c′ → LE (lvX κ) (lvX κ′) c c′ →
             g (psh (P κ) B₁ (toX κ c)) ≼X g′ (psh (P κ′) B₂ (toX κ′ c′))) →
          ∀ d d′ → MoAt (lvX κ′) d′ → LE (lvX κ) (lvX κ′) d d′ →
          LE t t′ (br (acc rs) l₁ pt₁ κ g pg₁ b d) (br (acc rs′) l₂ pt₂ κ′ g′ pg₂ b′ d′)
    brC rs rs′ {B₁} {B₂} l₁ l₂ w pt₁ pt₂ ev B κ κ′ g g′ pg₁ pg₂ wl my H′ d d′ md r =
      crossX (acc rs) (acc rs′) (lgW κ l₁ d) (lgW κ′ l₂ d′) (wl l₁ l₂ w r) (ptW κ l₁ pt₁ d) (ptW κ′ l₂ pt₂ d′) ev B
        (g′ (psh (P κ′) B₂ (toX κ′ d′))) (pgW κ l₁ pg₁ d) (pgW κ′ l₂ pg₂ d′) (brMo κ′ g′ B₂ my d′ md) (H′ d d′ md r)
```

## 结论 (按档)

- **[定理, 不用 UIP]** 关系 `_≼X_`, `Wl`; `≼X⊞`, `⊞X`.
- **[条件定理, 条件: `Cd` 上的 UIP (经 ValC, ValX), `ShLaw I`, 地板律 `tp`]** **`ThmX.crossX`**, `mΩX`, `brC`: 跨底折叠沿配对单调, 对一切配对 `Mt`.
