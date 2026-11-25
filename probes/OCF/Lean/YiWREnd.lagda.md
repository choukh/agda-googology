# 换基折叠的 EBO 闭项: 对一切站的条件下界

> 验收文件 (读记号). 判决: 编译定理. `Wire.ebo-end`: 对任何状态不变式 `Inv` (根上成立, 嵌入一步保持, 推出第 0 层的底条件), 结点链的关系 `ChainRel` 与出口条件推出 `toL EBO-tree′ ≼ readRW EBOᴮ` (`EBOᴮ` 是 `YiBSFold` 上 Λ 的闭项); `ChainRel` 由朝槽位层的保持 `LowSlot` 给出 (`chain←slot`, `ebo-endˢ`). 非结点的五条出口, 七条生成规则, 结点的余尾与基本列都已实填; `Leaf` 用读回域 (`YiGLDom.dom-top`, `dom-keel`).
> `Inv₀` (第 0 层的底条件) 与 `Inv₁` (再加各层底不低于 Ω 树) 的三条都实填 (`ebo-end₀`, `ebo-end₁`). 判断: 这两个 `Inv` 下 `LowSlot` 的量化域太宽 (上下文 K 只受第 0 层约束, 而 y = 0 时 `LowSlot` 要槽位层的底支配 ψ_κ(K)); 要换成记下各层底对 K 的支配的 `Inv`, 那时 `inv-step` 是朝各层的保持, 换基一行在那里.
> 不给出什么: 不比较换基折叠与主线; `LowSlot`, `ChainRel` 与出口条件在记号上是否成立未证. 来源: 塔与终点照 `YiGIEnd`, 生成原理照 `YiFIGen.genᴷ`, 出口的记号引理取自 `YiGTGen`, `YiMENote`, `YiMWPre`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWREnd where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath using (Ok; _≤_; z≤; inc; Ok-tw; Ok-Λ)
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase using (Rb; rb-tw)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ; Bsᴮ)
open import OCF.Lean.YiGIBlock using (blkᵍ; slTᵍ; slT⁼ᵍ)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLeanView using (ne; cof0)
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_; ≼-refl; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiMENote using (cofψω; fsnψω; cof++ω; fsn++; cofψΩ; fsnψΩ)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiGTGen using (weakenᴿ; closeᴿ; nextψ; app≤ν; Ω≤ψ)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiFIIface using (module FI)
open import OCF.Lean.YiXTIface using (module XT; module Rest)
open import OCF.Lean.YiFIGen using (module Ind; →low; low→)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (Wlᵍ; wz; pre; exitᵍ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs; reference)
open import OCF.Lean.YiGLDom using (Dom; dom-top; dom-keel)
open import OCF.Lean.YiWRZero
open ExSuff gradedᵍ domsᵍ using (Exit₀; Keel⁻)
```

## 分级实例

同 `YiGIInst.gradedᵍ`, 折叠换成 `foldᴮ`, 层号读法换成读回域 `Dom` (于是 `Leaf` 是 `dom-top`).

```agda
Bdᴮ : ∀ {ℓ j} → Bsᴮ ℓ → j ≤ ℓ → O.Tr⁺ j → E.T → Set
Bdᴮ {ℓ} {j} (o , r , b) w β t₀ = GR.R j (E.ψ [] t₀ ∷ []) (proj₁ β)

gradedᴮ : Graded blkᵍ foldᴮ rowsᴮ refᴱ SI.𝕍
gradedᴮ = record
  { ℓ₀ = zero ; v = K.readRW ; R = GR.R ; Rd = Dom ; Nu = GR.Nu ; bt = proj₁
  ; cl = λ _ t → E.ψ [] t ∷ [] ; Cx = λ _ _ → E.T ; app = λ t₀ a → E.ψ [] (t₀ ++ a) ∷ [] ; Bd = Bdᴮ }

domsᴮ : Doms blkᵍ foldᴮ
domsᴮ = record { Gx = λ ℓ x → x ≡ proj₁ (O.Ωt ℓ) ; Gb = λ _ _ → ⊤ ; Wl = Wlᵍ ; Gl = λ k x → x ≡ proj₁ (O.Ωt k) }

open Laws gradedᴮ domsᴮ using (Leaf; LowKeep; Zero; Succ; Lim; Weak; Node; Emb)
open FI gradedᴮ domsᴮ using (Gen⁺)
open Row gradedᴮ domsᴮ using (Rules)

leafᴮ : Leaf
leafᴮ = dom-top
```

## 关系的生成规则

```agda
genᴮ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ
genᴮ zero Q rs qc = Ind.ind Q (qz refl) q1 qL (λ ()) (λ ()) qw qc
  where open Rules rs
genᴮ (nd s h) Q rs qc = Ind.ind Q (qz refl) q1 qL
  (λ p g e nu hR hQ → qΩ p g e nu (λ η c l → hR η c (→low (nd s h) p l)) (λ η c l → hQ η c (→low (nd s h) p l)))
  (λ c y e m q ch → qU c (y , e) m q ch) qw qc
  where open Rules rs

weakᴮ : Weak
weakᴮ {ℓ = zero}   = H.mw
weakᴮ {ℓ = nd s h} = H.mw

limᴮ : Lim
limᴮ {ℓ = zero}   = H.mL
limᴮ {ℓ = nd s h} = H.mL

nodeᴮ : Node
nodeᴮ {ℓ = nd s h} p g e nu hyp = H.mΩ e nu (λ η c l → hyp η c (low→ (nd s h) p l))

emptyᵀ : ∀ t → E.cof t ≡ E.c0 → t ≡ []
emptyᵀ [] e = refl
emptyᵀ t@(_ ∷ _) e = ⊥-elim (cof0 t ne e)

mz′ : ∀ ℓ {x} → GR.R ℓ [] x
mz′ zero = H.mz
mz′ (nd s h) = H.mz

zeroᴮ : Zero
zeroᴮ {ℓ} {t} {x} e = subst (λ u → GR.R ℓ u x) (sym (emptyᵀ t e)) (mz′ ℓ)

succᴮ : Succ
succᴮ {ℓ = zero}   = H.m1
succᴮ {ℓ = nd s h} = H.m1

embᴮ : Emb
embᴮ {ℓ = nd s h} c (y , e) m ch = H.mU m ch

leRᴮ : ∀ {s t o} → s ≤ᵀ t → GR.R zero t o → GR.R zero s o
leRᴮ = H.mc
```

## 闭项

`EBOᴮ` 的第 n 项逐字是塔第 n 项以 `baseᴮ n`, `betaᴮ n` 为底与底值的闭项 (`upperᴮ` 只用定义展开), 同 `YiGIInst.keelᴱ`.

```agda
rbΛ : Rb Λ
rbΛ = tt , rb-tw

EBOᴮ : Tr zero
EBOᴮ = proj₁ (BS.ψ₀ Λ Ok-Λ rbΛ (proj₁ (O.Ωt Λ)))

baseᴮ : ∀ n → Base (tw n)
baseᴮ n i u = BS.ψ Λ Ok-Λ rbΛ (B₀ Λ) i (inc n u) (O.Ωt i) (pre n)

betaᴮ : ℕ → O.Tr⁺ zero
betaᴮ n = BS.ψ Λ Ok-Λ rbΛ (B₀ Λ) zero (z≤ Λ) (O.Ωt zero) (pre n)

rootᴮ : ∀ n → Stᶻ (tw n)
rootᴮ n = Ok-tw n , rb-tw n , baseᴮ n , betaᴮ n

twcᴮ : ℕ → Tr zero
twcᴮ n = proj₁ (Φᶻ (rootᴮ n) (proj₁ (O.Ωt (tw n))))

upperᴮ : ∀ n → K.readRW (twcᴮ n) ≼ K.readRW EBOᴮ
upperᴮ zero    = ≼l zero (≼-refl _)
upperᴮ (suc n) = ≼l (suc n) (≼-refl _)

mutual
  slT-fb : (ℓ : L) (p : Pos ℓ) (y : Tr (at ℓ p)) → slTᵍ ℓ p (fromBr ℓ p y) ≡ y
  slT-fb (nd s h)      (inj₂ (c , t)) y = slT-fb⁼ (h c) t y
  slT-fb (nd (sΩ k) h) (inj₁ t)       y = slT-fb⁼ k t y

  slT-fb⁼ : (a : L) (t : Pos⁼ a) (y : Tr (proj₁ (sl⁼ a t))) → slT⁼ᵍ a t (proj₂ (sl⁼ a t) y) ≡ y
  slT-fb⁼ a (inj₁ _) y = refl
  slT-fb⁼ a (inj₂ p) y = slT-fb a p y

ψ-⊵ᴮ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : O.Tr⁺ j) (x : Tr ℓ)
  → proj₁ β ⊴ proj₁ (BS.ψ ℓ o r B j w β x)
ψ-⊵ᴮ ℓ o r B j w β x with O.zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ (BS.mono ℓ o r B j w β d)
```

## 接线

`Inv s K`: 状态 s 对着上下文 K (前缀) 的不变式. 结点链的关系 `ChainRel`: 每个状态的每个结点上, 折叠自己的第 k 个链点 (从第 1 个起) 在槽位层上不低于记号的对角链 `γT (K ++ t) κ k`.

```agda
apᴱ : E.T → E.T → E.T
apᴱ K t = E.ψ [] (K ++ t) ∷ []

sucgt : ∀ ν → E.cmpᵀ (E.sucT ν) [] ≡ E.gt
sucgt []      = refl
sucgt (_ ∷ _) = refl

module Wire (Inv : ∀ {a} → Stᶻ a → E.T → Set)
    (inv-zero : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) (β : O.Tr⁺ zero) {K} → Inv (o , r , B , β) K → GR.R zero (E.ψ [] K ∷ []) (proj₁ β))
    (inv-step : ∀ {a} (s : Stᶻ a) K → Inv s K → (c : CH a) → ∀ {t x} → GR.R a t x
              → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv (stepᶻ s c x) (K ++ t))
    (inv-root : ∀ n → Inv (rootᴮ n) []) where
  open Zero gradedᴮ domsᴮ E.T apᴱ Inv
  open XT gradedᴮ domsᴮ
  open Rest gradedᴮ domsᴮ
  open WithRules _≤ᵀ_ weakᴮ limᴮ nodeᴮ zeroᴮ succᴮ embᴮ leRᴮ genᴮ

  restᴱ : OutDN sysᶻ _≤ᵀ_ fallᶻ
  restᴱ = record
    { zeroE = λ { {a} (o , r , B , β) K bd {t} {x} e →
        subst (λ u → GR.R zero (E.ψ [] (K ++ u) ∷ []) (proj₁ (BS.ψ a o r B zero (z≤ a) β x))) (sym (emptyᵀ t e))
          (subst (λ u → GR.R zero (E.ψ [] u ∷ []) (proj₁ (BS.ψ a o r B zero (z≤ a) β x))) (sym (++-identityʳ K))
            (weakenᴿ zero (inv-zero o r B β bd) (ψ-⊵ᴮ a o r B zero (z≤ a) β x))) }
    ; succE = λ s K bd {t} {x} e r q → nextψ zero [] K t e (Φᶻ s x) q
    ; limE  = λ s K bd {t} e → cofψω [] (K ++ t) (cof++ω K t e)
        , λ n → trans (fsnψω [] (K ++ t) n (cof++ω K t e)) (cong (λ z → E.ψ [] z ∷ []) (fsn++ K t n e))
    ; upE   = λ s K bd c {t} {x} r q → (K ++ t) , inv-step s K bd c r q , λ u → cong (λ z → E.ψ [] z ∷ []) (++-assoc K t u)
    ; leE   = λ s K bd le r → closeᴿ zero (app≤ν [] _ le) r }

  ChainRel : Set
  ChainRel = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {t κ} (g : Br a p → Tr a)
    → E.cof t ≡ E.cΩ κ → GR.Nu a p κ → (∀ η c → GR.R (at a p) η (slTᵍ a p c) → GR.R a (E.fsT t η) (g c))
    → ∀ k → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (ptᶻ s p g k))

  aboveᴱ : ChainRel → AboveL sysᶻ keepᶻ Dᶻ xtᶻ
  aboveᴱ cr s K bd p {t} {κ} g d e nu hR _ _ = (λ k → E.γT (K ++ t) κ k)
    , trans (cofψΩ [] (K ++ t) (cof++Ω K t e)) (cong (E.cofψ₊ [] κ) (sucgt κ))
    , (λ k → trans (fsnψΩ [] (K ++ t) k (cof++Ω K t e))
        (trans (cong (λ c → E.fsnc [] (K ++ t) κ c k) (sucgt κ))
          (cong (λ z → E.ψ [] z ∷ []) (fsT++ K t (E.γT (K ++ t) κ k) e))))
    , cr s K bd p g e nu hR
```

`ChainRel` 归到朝槽位层的保持 `LowSlot`: 状态 s 在槽位 p 上朝槽位层的折叠 (`slotFold`, 底值取底在槽位层上的值) 把 R a η y 变成以 ψ_κ(K ++ η) 为参照的关系. 第 0 个链点用 η = 0 与 Ω_κ ≤ ψ_κ(…) (`Ω≤ψ`), 之后逐项用代入与前缀交换 (`fsT++`).

```agda
  LowSlot : Set
  LowSlot = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {κ} → GR.Nu a p κ
    → ∀ {η y} → GR.R a η y → GR.R (at a p) (E.ψ κ (K ++ η) ∷ []) (slotFold s p y)

  chain←slot : LowSlot → ChainRel
  chain←slot ls {a} s K bd p {t} {κ} g e nu hR = go
    where
    go : ∀ k → GR.R (at a p) (E.γT (K ++ t) κ k) (slTᵍ a p (ptᶻ s p g k))
    go zero = subst (GR.R (at a p) (E.Ωt κ)) (sym (slT-fb a p _))
      (closeᴿ (at a p) (Ω≤ψ κ (K ++ E.fsT t [])) (ls s K bd p nu (hR [] (fromBr a p zero) (mz′ (at a p)))))
    go (suc k) = subst₂ (GR.R (at a p)) (cong (λ z → E.ψ κ z ∷ []) (sym (fsT++ K t (E.γT (K ++ t) κ k) e))) (sym (slT-fb a p _))
      (ls s K bd p nu (hR (E.γT (K ++ t) κ k) (ptᶻ s p g k) (go k)))
```

塔与终点: 每一项朝第 0 层折一次 (`folded`), 出口条件只对这一次的推导要 (同 `YiGIEnd.Assembly.ExitCondition`).

```agda
  module _ (cr : ChainRel) where
    folded : ∀ n → GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)
    folded n = lowᶻ restᴱ (aboveᴱ cr) (rootᴮ n) [] (inv-root n) (dom-top (dom-keel n))

    ExitCondition : Set
    ExitCondition = ∀ n → H.Exᴴ (folded n)

    ebo-end : ExitCondition → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
    ebo-end ex = ≼-trans reference (l≼ (λ n → ≼-trans (Exit₀.exit exitᵍ (folded n) (ex n) (hs n)) (upperᴮ n)))

  ebo-endˢ : (ls : LowSlot) → ExitCondition (chain←slot ls) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
  ebo-endˢ ls = ebo-end (chain←slot ls)
```

## 只记第 0 层的底条件

```agda
Inv₀ : ∀ {a} → Stᶻ a → E.T → Set
Inv₀ (o , r , B , β) K = GR.R zero (E.ψ [] K ∷ []) (proj₁ β)

inv₀-step : ∀ {a} (s : Stᶻ a) K → Inv₀ s K → (c : CH a) → ∀ {t x} → GR.R a t x
  → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv₀ (stepᶻ s c x) (K ++ t)
inv₀-step {nd _ _} s K bd c r q = q

module W₀ = Wire Inv₀ (λ o r B β bd → bd) inv₀-step (λ n → H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)))

ebo-end₀ : (cr : W₀.ChainRel) → W₀.ExitCondition cr → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
ebo-end₀ = W₀.ebo-end
```

## 加上各层的底不低于 Ω 树

`Inv₁`: 再记 "底在每一层不低于该层的 Ω 树" (同 `YiGIInst.Bdᵍ` 的第二项); 三条也都实填. `ChainRel Inv₀` 推出 `ChainRel Inv₁` (`chain₀→₁`), 所以 `ebo-end₁` 的前提更弱.

```agda
⊴-tr : ∀ {S : Sg} {x y z : T S} → x ⊴ y → y ⊴ z → x ⊴ z
⊴-tr ⊴r     e       = e
⊴-tr (⊴◃ d) ⊴r      = ⊴◃ d
⊴-tr (⊴◃ d) (⊴◃ d′) = ⊴◃ (◃t d d′)

Inv₁ : ∀ {a} → Stᶻ a → E.T → Set
Inv₁ (o , r , B , β) K = GR.R zero (E.ψ [] K ∷ []) (proj₁ β) × (∀ i u → proj₁ (O.Ωt i) ⊴ proj₁ (B i u))

inv₁-step : ∀ {a} (s : Stᶻ a) K → Inv₁ s K → (c : CH a) → ∀ {t x} → GR.R a t x
  → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv₁ (stepᶻ s c x) (K ++ t)
inv₁-step {nd s′ h} (o , r , B , β) K (_ , bs) c {x = x} _ q =
  q , λ i u → ⊴-tr (bs i (inc c u)) (ψ-⊵ᴮ (nd s′ h) o r B i (inc c u) (B i (inc c u)) x)

module W₁ = Wire Inv₁ (λ o r B β bd → proj₁ bd) inv₁-step
  (λ n → H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)) , λ i u → ψ-⊵ᴮ Λ Ok-Λ rbΛ (B₀ Λ) i (inc n u) (O.Ωt i) (pre n))

chain₀→₁ : W₀.ChainRel → W₁.ChainRel
chain₀→₁ cr s K bd = cr s K (proj₁ bd)

ebo-end₁ : (cr : W₁.ChainRel) → W₁.ExitCondition cr → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
ebo-end₁ = W₁.ebo-end
```
