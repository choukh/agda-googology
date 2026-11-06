# `Tᴰ₊` 的折叠 (一): 一致世界与到两种种类的投影

> 不含记号. 入口 [TdPlus](TdPlus.lagda.md). [DiagK3Grow](DiagK3Grow.lagda.md) 的 `growL′` 是选项 (ii) 要的世界操作: 回灌时不挑分量, **一切 `A` 界接同一个 $f$, 一切高度界接同一个 $H_0$ 增量** (经 `embL`, `embK`). 从最小世界出发只用这种操作, 到达的世界都是**一致世界**: 一切 `A` 界相同 ($a$), 一切高度界是同一个 $\beta:H_0$ 的嵌入. 一致世界由一对 $(a,\beta)$ 决定, 正是两种种类的世界 `Wd S₁ = A × H₀` ([HtTowerFTree](HtTowerFTree.lagda.md)).
>
> 这一篇对 `towerL′` 用到的一切种类结构 (`S₀`, `step`, `sup`, 于是一切 `Lev x` 与 `L′ k`) 一条一条地给出:
>
> - **`Uni S`** (记录): 一致世界 `uW a β`, 合法 (`luW`), 单调 (`uW≤`: 两种种类的世界变大, 一致世界就变大); 第二数类的嵌入 `emb` (就是 `embL`, `embK` 的形状), 保第一位置 (`emb⊲`), 保合法, **可逆** (`embI`: 一致世界里在 `emb h` 之下的高度都是某个 `emb h′`, $h'\lhd h$); 每个种类的**分类** `cls`: 坐标是 `A` 的种类 (`cA`) 或坐标是高度的种类 (`cH`), 连同它在一致世界里的界与第一位置.
> - 实例 `uS₀`, `uStep`, `uSup`, **`uLev x`**, **`uL k`**: 对种类结构的构造子一步一条, 不判定任何相等; 分类只看种类的字面构造子 (`inj₁`/`inj₂`, 并的下标).
> - **`pr`** (定义): 高度投影到 `HB S₁`: `cA` 种类的 $\Omega$-节点成 `κA` 节点 (坐标 $c\mapsto e\,c$), `cH` 种类的成 `κH` 节点 (坐标 $h\mapsto e\,h$). **`pr-mono`**: 一致世界 `uW a β` 里的第一位置投影成世界 $(a,\beta)$ 里的第一位置 (用 `embI`/分类的逆); **`Lg-pr`**: 合法高度投影成合法高度. 这是 [DiagK3Zero](DiagK3Zero.lagda.md) 的 `pr₀`, `Lg-pr₀` 对一切级的推广, 区别是 `Lev` 种类不再压成底坐标, 而按一致世界读成 $H_0$ 坐标.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlusUni where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two)
open import OCF.Align.HtTowerFTree using (S₁; H₀; κA; κH)
```

## §1 `up` 与 `ι` 的像在第一位置下封闭

```agda
module _ {S : KS} where
  up-inv : ∀ {x : HB (step S)} {t w b} → x ⊲[ (w , b) ] up t → Σ (HB S) (λ t′ → (x ≡ up t′) × (t′ ⊲[ w ] t))
  up-inv {t = hz} hself = hz , refl , hself
  up-inv {t = hs t} hself = hs t , refl , hself
  up-inv {t = hs t} (hsuc p) with up-inv p
  ... | t′ , eq , q = t′ , eq , hsuc q
  up-inv {t = hl f} hself = hl f , refl , hself
  up-inv {t = hl f} (hlim n p) with up-inv p
  ... | t′ , eq , q = t′ , eq , hlim n q
  up-inv {t = hΩ κ g} hself = hΩ κ g , refl , hself
  up-inv {t = hΩ κ g} (hLim bd p) with up-inv p
  ... | t′ , eq , q = t′ , eq , hLim bd q

module _ {I : Set} {F : I → KS} where
  ι-inv : ∀ {i} {x : HB (sup I F)} {t} {w : Wd (sup I F)} → x ⊲[ w ] ι i t → Σ (HB (F i)) (λ t′ → (x ≡ ι i t′) × (t′ ⊲[ w i ] t))
  ι-inv {i} {t = hz} hself = hz , refl , hself
  ι-inv {i} {t = hs t} hself = hs t , refl , hself
  ι-inv {i} {t = hs t} (hsuc p) with ι-inv p
  ... | t′ , eq , q = t′ , eq , hsuc q
  ι-inv {i} {t = hl f} hself = hl f , refl , hself
  ι-inv {i} {t = hl f} (hlim n p) with ι-inv p
  ... | t′ , eq , q = t′ , eq , hlim n q
  ι-inv {i} {t = hΩ κ g} hself = hΩ κ g , refl , hself
  ι-inv {i} {t = hΩ κ g} (hLim bd p) with ι-inv p
  ... | t′ , eq , q = t′ , eq , hLim bd q
```

## §2 一致世界的记录

`Cls S uW κ`: 种类 $\kappa$ 在一致世界里读成 `A` 坐标 (`cA`) 或 $H_0$ 坐标 (`cH`). 五个字段: 坐标的嵌入 $e$; 界 ($c\lhd a$ 或 $h\lhd_{[a]}\beta$ 推出 $e$ 的像有界); 第一位置; **逆** (一致世界里有界的坐标都是 $e$ 的像, 原像有界); 合法.

```agda
data Cls (S : KS) (uW : A → H₀ → Wd S) (κ : K S) : Set where
  cA : (e : A → E S κ) →
       (∀ {c a β} → c ⊲ a → Bd S κ (e c) (uW a β)) →
       (∀ {c c′ a β} → c ⊲ c′ → Pr S κ (uW a β) (e c) (e c′)) →
       (∀ {x a β} → Bd S κ x (uW a β) → Σ A (λ c → (x ≡ e c) × (c ⊲ a))) →
       (∀ c → Lg c → LgE S κ (e c)) → Cls S uW κ
  cH : (e : H₀ → E S κ) →
       (∀ {h a β} → h ⊲[ a ] β → Bd S κ (e h) (uW a β)) →
       (∀ {h h′ a β} → h ⊲[ a ] h′ → Pr S κ (uW a β) (e h) (e h′)) →
       (∀ {x a β} → Bd S κ x (uW a β) → Σ H₀ (λ h → (x ≡ e h) × (h ⊲[ a ] β))) →
       (∀ h → LgB h → LgE S κ (e h)) → Cls S uW κ

record Uni (S : KS) : Set where
  field
    uW   : A → H₀ → Wd S
    luW  : ∀ {a β} → Lg a → LgB β → LgW S (uW a β)
    uW≤  : ∀ {a β a′ β′} → a ⊲ a′ → β ⊲[ a′ ] β′ → _≤w_ S (uW a β) (uW a′ β′)
    emb  : H₀ → HB S
    emb⊲ : ∀ {h h′ a β} → h ⊲[ a ] h′ → emb h ⊲[ uW a β ] emb h′
    embI : ∀ {x h a β} → x ⊲[ uW a β ] emb h → Σ H₀ (λ h′ → (x ≡ emb h′) × (h′ ⊲[ a ] h))
    Lemb : ∀ h → LgB h → LgB (emb h)
    cls  : (κ : K S) → Cls S uW κ
open Uni public
```

## §3 实例: 底, 一步, 并

```agda
uS₀ : Uni S₀
uS₀ = record
  { uW = λ a β → a ; luW = λ la lβ → la ; uW≤ = λ p q → p
  ; emb = λ h → h ; emb⊲ = λ p → p ; embI = λ {x} p → x , refl , p ; Lemb = λ h l → l
  ; cls = λ _ → cA (λ c → c) (λ p → p) (λ p → p) (λ {x} p → x , refl , p) (λ c l → l) }

module _ {S : KS} (U : Uni S) where
  private
    uW⁺ : A → H₀ → Wd (step S)
    uW⁺ a β = uW U a β , emb U β

  liftStep : ∀ {κ} → Cls S (uW U) κ → Cls (step S) uW⁺ (inj₁ κ)
  liftStep (cA e bd pr iv lg) = cA e bd pr iv lg
  liftStep (cH e bd pr iv lg) = cH e bd pr iv lg

  embI⁺ : ∀ {x h a β} → x ⊲[ uW⁺ a β ] up (emb U h) → Σ H₀ (λ h′ → (x ≡ up (emb U h′)) × (h′ ⊲[ a ] h))
  embI⁺ {h = h} p with up-inv {t = emb U h} p
  ... | t′ , eq , q with embI U {x = t′} {h = h} q
  ... | h′ , eq′ , r = h′ , trans eq (cong up eq′) , r

  clsStep : (κ : K (step S)) → Cls (step S) uW⁺ κ
  clsStep (inj₁ κ) = liftStep (cls U κ)
  clsStep (inj₂ tt) = cH (emb U) (λ p → emb⊲ U p) (λ p → emb⊲ U p) (λ p → embI U p) (Lemb U)

  uStep : Uni (step S)
  uStep = record
    { uW = uW⁺ ; luW = λ la lβ → luW U la lβ , Lemb U _ lβ ; uW≤ = λ p q → uW≤ U p q , emb⊲ U q
    ; emb = λ h → up (emb U h) ; emb⊲ = λ p → up-⊲ (emb⊲ U p) ; embI = embI⁺
    ; Lemb = λ h l → Lg-up (emb U h) (Lemb U h l) ; cls = clsStep }

module _ {I : Set} {F : I → KS} (i₀ : I) (U : (i : I) → Uni (F i)) where
  private
    uWˢ : A → H₀ → Wd (sup I F)
    uWˢ a β i = uW (U i) a β

  liftSup : ∀ {i κ} → Cls (F i) (uW (U i)) κ → Cls (sup I F) uWˢ (i , κ)
  liftSup (cA e bd pr iv lg) = cA e bd pr iv lg
  liftSup (cH e bd pr iv lg) = cH e bd pr iv lg

  embIˢ : ∀ {x h a β} → x ⊲[ uWˢ a β ] ι {F = F} i₀ (emb (U i₀) h) → Σ H₀ (λ h′ → (x ≡ ι {F = F} i₀ (emb (U i₀) h′)) × (h′ ⊲[ a ] h))
  embIˢ {h = h} p with ι-inv {F = F} {i = i₀} {t = emb (U i₀) h} p
  ... | t′ , eq , q with embI (U i₀) {x = t′} {h = h} q
  ... | h′ , eq′ , r = h′ , trans eq (cong (ι {F = F} i₀) eq′) , r

  uSup : Uni (sup I F)
  uSup = record
    { uW = uWˢ ; luW = λ la lβ i → luW (U i) la lβ ; uW≤ = λ p q i → uW≤ (U i) p q
    ; emb = λ h → ι {F = F} i₀ (emb (U i₀) h) ; emb⊲ = λ p → ι-⊲ {F = F} (emb⊲ (U i₀) p) ; embI = embIˢ
    ; Lemb = λ h l → Lg-ι {F = F} i₀ (emb (U i₀) h) (Lemb (U i₀) h l)
    ; cls = λ { (i , κ) → liftSup (cls (U i) κ) } }
```

## §4 一切 `Lev x` 与 `L′ k`

`uLev` 的 `emb` 与 `DiagK3Grow.embL` 逐构造子同形 (并取下标 $0$ 与 `bot`), `uL` 的 `emb` 与 `DiagK3Grow.embK` 同形 (取 `true` 分量再 `up`); 等式在 [TdPlusGrow](TdPlusGrow.lagda.md).

```agda
uLev : ∀ {S} (x : HB S) → Uni (Lev x)
uLev hz = uS₀
uLev (hs x) = uStep (uLev x)
uLev (hl f) = uSup 0 (λ n → uLev (f n))
uLev {S} (hΩ κ g) = uSup (bot S κ) (λ c → uLev (g c))

uTwo : ∀ {S S′} → Uni S → Uni S′ → (b : Bool) → Uni (two S S′ b)
uTwo U U′ true = U
uTwo U U′ false = U′

uL : ∀ k → Uni (L′ k)
uL zero = uS₀
uL (suc k) = uSup true (uTwo (uStep (uL k)) (uLev (Ωtop (L′ k))))
```

## §5 投影

`prK κ cl G`: 种类 $\kappa$ 的 $\Omega$-节点, 分支已投影成 $G$, 按分类成 `κA` 或 `κH` 节点. `pr` 对高度结构递归.

```agda
module Pr {S : KS} (U : Uni S) where
  prK : ∀ κ → Cls S (uW U) κ → (E S κ → HB S₁) → HB S₁
  prK κ (cA e _ _ _ _) G = hΩ κA (λ c → G (e c))
  prK κ (cH e _ _ _ _) G = hΩ κH (λ h → G (e h))

  pr : HB S → HB S₁
  pr hz = hz
  pr (hs x) = hs (pr x)
  pr (hl f) = hl (λ n → pr (f n))
  pr (hΩ κ g) = prK κ (cls U κ) (λ z → pr (g z))

  lim-case : ∀ {κ} (cl : Cls S (uW U) κ) {G : E S κ → HB S₁} {x y a β} →
             Bd S κ y (uW U a β) → x ⊲[ (a , β) ] G y → x ⊲[ (a , β) ] prK κ cl G
  lim-case (cA e bd pr′ iv lg) {G} {x} {a = a} {β} b p with iv b
  ... | c , eq , cb = hLim {S₁} {κ = κA} {c = c} cb (subst (λ z → x ⊲[ (a , β) ] G z) eq p)
  lim-case (cH e bd pr′ iv lg) {G} {x} {a = a} {β} b p with iv b
  ... | h , eq , hb = hLim {S₁} {κ = κH} {c = h} hb (subst (λ z → x ⊲[ (a , β) ] G z) eq p)

  pr-mono : ∀ {x y a β} → x ⊲[ uW U a β ] y → pr x ⊲[ (a , β) ] pr y
  pr-mono hself = hself
  pr-mono (hsuc p) = hsuc (pr-mono p)
  pr-mono (hlim n p) = hlim n (pr-mono p)
  pr-mono (hLim {κ = κ} b p) = lim-case (cls U κ) b (pr-mono p)

  lg-case : ∀ {κ} (cl : Cls S (uW U) κ) {g : E S κ → HB S} →
            (∀ {w c c′} → LgW S w → Bd S κ c w → Bd S κ c′ w → Pr S κ w c c′ → g c ⊲[ w ] g c′) →
            (∀ c → LgE S κ c → LgB (pr (g c))) → LgB (prK κ cl (λ z → pr (g z)))
  lg-case (cA e bd pr′ iv lg) mo L =
    (λ {W} lW b b′ q → pr-mono {a = proj₁ W} {proj₂ W}
        (mo {uW U (proj₁ W) (proj₂ W)} (luW U (proj₁ lW) (proj₂ lW)) (bd {β = proj₂ W} b) (bd {β = proj₂ W} b′) (pr′ {β = proj₂ W} q))) ,
    (λ c lc → L (e c) (lg c lc))
  lg-case (cH e bd pr′ iv lg) mo L =
    (λ {W} lW b b′ q → pr-mono {a = proj₁ W} {proj₂ W}
        (mo {uW U (proj₁ W) (proj₂ W)} (luW U (proj₁ lW) (proj₂ lW)) (bd b) (bd b′) (pr′ {β = proj₂ W} q))) ,
    (λ h lh → L (e h) (lg h lh))

  Lg-pr : ∀ x → LgB x → LgB (pr x)
  Lg-pr hz l = tt
  Lg-pr (hs x) l = Lg-pr x l
  Lg-pr (hl f) (st , l) = (λ {W} n → pr-mono {a = proj₁ W} {proj₂ W} (st {uW U (proj₁ W) (proj₂ W)} n)) , (λ n → Lg-pr (f n) (l n))
  Lg-pr (hΩ κ g) (mo , l) = lg-case (cls U κ) mo (λ c lc → Lg-pr (g c) (l c lc))
```
