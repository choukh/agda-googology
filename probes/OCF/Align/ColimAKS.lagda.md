# 只对可入层号给分量 (一): `LevC′ X w` 是种类结构, 认同与拷贝

> 不含记号. 入口 [ColimA](ColimA.lagda.md), 接口 [ColimAIf](ColimAIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> - **`LevC′ X w = pb (LevA w X) (GWA X w) (restrA X hself)`** (`ColimWKS.pb`): 对一切 `S`, 一切 $X$, 一切 $w$, 是种类结构; `cmpKC′`, `botBdC′` 是接口 `CmpKC`, `BotBdC` 的实例 (拉回原样给出).
> - **`globA`, `globPrA`** (接口 `GlobA`, `GlobPrA`): 一切种类的界与第一位置只由它的 (层号, 证据) 与世界在那里的分量决定. 每步 `refl`.
> - **`crossA`, `crossPrA`** (接口 `CrossA`, `CrossPrA`): 相干世界里, 同一层号的两个证据下的界 (第一位置) 互推. 证明: 对层号结构递归搬低层世界的证据 (`restr-move`), 在层号处沿 `CohA` 换分量. 不用函数外延: 结论是 "互推", 不是两个低层世界相等 (低层世界是函数, 相等要外延).
> - **相干是必要的** (`noCrossA`, 定理): 有一个合法而不相干的世界, 层号 `finH 1` 的两个拷贝 `κ₂`, `κ₂′` 读到不同的界. 所以认同 "同一层号的拷贝读同一分量" 在以证据为参数的世界里**要**跨证据相干, 不是免费的.
> - **整体合法与世界序** (`lgGA→`, `≤GA→`), 最小世界 (`W₀`, `lgW₀`, `cohW₀`), `no-retract` 的实例 (`no-retractA`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimAKS where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.ColimWIf using (AdmL; S₁; finH; x₀; ω₀)
open import OCF.Align.ColimWKS using (pb)
open import OCF.Align.ColimWRaise using (eqFin)
open import OCF.Align.ColimWNeg using (wω; Lg-wω)
open import OCF.Align.ColimAIf
```

## §1 `LevC′`

```agda
LevC′ : ∀ {S} → HB S → Wd S → KS
LevC′ X w = pb (LevA w X) (GWA X w) (Adm.restrA X w X hself)

module _ {S : KS} (X : HB S) (w : Wd S) where
  open Adm X w

  cmpKC′ : CmpKC
  cmpKC′ = cmpK (LevC′ X w)

  botBdC′ : BotBdC
  botBdC′ = botBd (LevC′ X w)
```

## §2 认同律

```agda
  globA : GlobA
  globA hz π κ c W = refl
  globA (hs x) π (inj₁ κ) c W = globA x (dnS π) κ c W
  globA (hs x) π (inj₂ _) c W = refl
  globA (hl f) π (n , κ) c W = globA (f n) (dnL n π) κ c W
  globA (hΩ κ g) π (ce , κ′) c W = globA (g (proj₁ ce)) (dnΩ (proj₂ ce) π) κ′ c W

  globPrA : GlobPrA
  globPrA hz π κ W c c′ = refl
  globPrA (hs x) π (inj₁ κ) W c c′ = globPrA x (dnS π) κ W c c′
  globPrA (hs x) π (inj₂ _) W c c′ = refl
  globPrA (hl f) π (n , κ) W c c′ = globPrA (f n) (dnL n π) κ W c c′
  globPrA (hΩ κ g) π (ce , κ′) W c c′ = globPrA (g (proj₁ ce)) (dnΩ (proj₂ ce) π) κ′ W c c′
```

**整体合法与世界序推出每一级的** (沿任一路径).

```agda
  lgGA→ : ∀ (x : HB S) (π : x ⊲[ w ] X) {W} → LgGA W → LgW (LevA w x) (restrA x π W)
  lgGA→ hz π l = proj₁ l
  lgGA→ (hs x) π l = lgGA→ x (dnS π) l , proj₂ l x π
  lgGA→ (hl f) π l = λ n → lgGA→ (f n) (dnL n π) l
  lgGA→ (hΩ κ g) π l = λ ce → lgGA→ (g (proj₁ ce)) (dnΩ (proj₂ ce) π) l

  ≤GA→ : ∀ (x : HB S) (π : x ⊲[ w ] X) {W W′} → W ≤GA W′ → _≤w_ (LevA w x) (restrA x π W) (restrA x π W′)
  ≤GA→ hz π q = proj₁ q
  ≤GA→ (hs x) π q = ≤GA→ x (dnS π) q , proj₂ q x π
  ≤GA→ (hl f) π q = λ n → ≤GA→ (f n) (dnL n π) q
  ≤GA→ (hΩ κ g) π q = λ ce → ≤GA→ (g (proj₁ ce)) (dnΩ (proj₂ ce) π) q

  ≤GA-rf : ∀ {W} → W ≤GA W
  ≤GA-rf = C.self , λ y p → hself

  W₀ : GWA X w
  W₀ = azero , λ y p → hz

  lgW₀ : LgGA W₀
  lgW₀ = tt , λ y p → tt

  cohW₀ : CohA W₀
  cohW₀ y p p′ = refl
```

## §3 拷贝: 相干世界里两个证据的界互推

`⊲-map`: 世界之间的界的映射搬第一位置 (对任一种类结构). `restr-move`: 相干世界里, 沿两条路径算出的低层世界, 界互推 (对层号结构递归). 不说两个低层世界相等.

```agda
⊲-map : ∀ {T : KS} {u v : Wd T} → (∀ {κ c} → Bd T κ c u → Bd T κ c v) →
  ∀ {a b} → _⊲[_]_ {T} a u b → _⊲[_]_ {T} a v b
⊲-map m hself = hself
⊲-map {T} m (hsuc p) = hsuc (⊲-map {T} m p)
⊲-map {T} m (hlim n p) = hlim n (⊲-map {T} m p)
⊲-map {T} m (hLim e p) = hLim (m e) (⊲-map {T} m p)

module _ {S : KS} (X : HB S) (w : Wd S) where
  open Adm X w

  restr-move : ∀ {W} → CohA W → ∀ (x : HB S) (π π′ : x ⊲[ w ] X) {κ c} →
    Bd (LevA w x) κ c (restrA x π W) → Bd (LevA w x) κ c (restrA x π′ W)
  restr-move coh hz π π′ e = e
  restr-move coh (hs x) π π′ {inj₁ κ} e = restr-move coh x (dnS π) (dnS π′) e
  restr-move {W} coh (hs x) π π′ {inj₂ _} {c} e =
    subst (λ t → _⊲[_]_ {LevA w x} c (restrA x (dnS π′) W) t) (coh x π π′) (⊲-map {T = LevA w x} (restr-move coh x (dnS π) (dnS π′)) e)
  restr-move coh (hl f) π π′ {n , κ} e = restr-move coh (f n) (dnL n π) (dnL n π′) e
  restr-move coh (hΩ κ g) π π′ {ce , κ′} e = restr-move coh (g (proj₁ ce)) (dnΩ (proj₂ ce) π) (dnΩ (proj₂ ce) π′) e

  crossA : CrossA
  crossA {W} coh y p p′ c e =
    subst (λ t → _⊲[_]_ {LevA w y} c (restrA y (dnS p′) W) t) (coh y p p′) (⊲-map {T = LevA w y} (restr-move coh y (dnS p) (dnS p′)) e)

  crossPrA : CrossPrA
  crossPrA {W} coh y p p′ c c′ e = ⊲-map {T = LevA w y} (restr-move coh y (dnS p) (dnS p′)) e
```

**实例: 层号 `up ω₀` 与 `finH 1` 的拷贝** (相干世界里互推; 由 `globA` 定义地归约到 `crossA`).

```agda
module _ {W : GWA x₀ wω} (coh : Adm.CohA x₀ wω W) where
  open Adm x₀ wω

  copyω : ∀ {c} → Bd L₀ κω c (restrA x₀ hself W) → Bd L₀ κω′ c (restrA x₀ hself W)
  copyω {c} e = crossA x₀ wω coh (up ω₀) _ _ c e

  copyω← : ∀ {c} → Bd L₀ κω′ c (restrA x₀ hself W) → Bd L₀ κω c (restrA x₀ hself W)
  copyω← {c} e = crossA x₀ wω coh (up ω₀) _ _ c e

  copy₂ : ∀ {c} → Bd L₀ κ₂ c (restrA x₀ hself W) → Bd L₀ κ₂′ c (restrA x₀ hself W)
  copy₂ {c} e = crossA x₀ wω coh (finH 1) _ _ c e
```

## §4 相干是必要的

不相干的合法世界: 层号的界按证据的坐标取, 坐标是 2 时为 $1$, 否则为 $0$. `κ₂` 经坐标 2, `κ₂′` 经坐标 3; 坐标 $1$ 在前者之下有界, 在后者之下没有.

```agda
one : ∀ {T : KS} → HB T
one = hs hz

pick : ∀ {T : KS} {c : HB S₀} → (finH 2 ≡ c) ⊎ ¬ (finH 2 ≡ c) → HB T
pick (inj₁ _) = one
pick (inj₂ _) = hz

lg-pick : ∀ {T : KS} {c : HB S₀} (d : (finH 2 ≡ c) ⊎ ¬ (finH 2 ≡ c)) → LgB {T} (pick d)
lg-pick (inj₁ _) = tt
lg-pick (inj₂ _) = tt

βbad : (y : HB S₁) → AdmL x₀ wω y → HB (LevA wω y)
βbad y (hLim {c = c} e q) = pick (eqFin 2 c)

lg-βbad : ∀ y (p : AdmL x₀ wω y) → LgB (βbad y p)
lg-βbad y (hLim {c = c} e q) = lg-pick (eqFin 2 c)

Wbad : GWA x₀ wω
Wbad = azero , βbad

lgWbad : Adm.LgGA x₀ wω Wbad
lgWbad = tt , lg-βbad

bad₂ : Bd L₀ κ₂ one (Adm.restrA x₀ wω x₀ hself Wbad)
bad₂ = hself

noCrossA : ¬ (∀ {c W} → Adm.LgGA x₀ wω W → Bd L₀ κ₂ c (Adm.restrA x₀ wω x₀ hself W) → Bd L₀ κ₂′ c (Adm.restrA x₀ wω x₀ hself W))
noCrossA h with h {one} {Wbad} lgWbad bad₂
... | ()

¬cohWbad : ¬ Adm.CohA x₀ wω Wbad
¬cohWbad coh = noCrossA′ (copy₂ coh bad₂)
  where
  noCrossA′ : ¬ Bd L₀ κ₂′ one (Adm.restrA x₀ wω x₀ hself Wbad)
  noCrossA′ ()
```

## §5 不违反 `no-retract`

```agda
no-retractA : ∀ {S} (X : HB S) (w : Wd S) (κ : K (LevC′ X w)) (e : HB (LevC′ X w) → E (LevC′ X w) κ) (d : E (LevC′ X w) κ → HB (LevC′ X w)) →
  ¬ (∀ y → d (e y) ≡ y)
no-retractA X w κ e d = no-retract {LevC′ X w} κ e d
```
