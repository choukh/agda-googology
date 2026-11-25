# 对照表判定件 1: 下标侧槽位与目标在 Ω 形状结点上分叉

> 判决: 编译定理 (形状档), 不读记号, 不改树、折叠、合法性. 对一切 Ω 形状层号: 下标侧槽位沿地板路径推进孩子 c′ 的层号, 目标沿另一条路径进同一层号, 两条路径在某个 Ω 形状结点上分到孩子一侧 (`Cross`) 时, 保留判定给 `nothing` (`drop-idx`); 塔第 n+1 项的顶结点对一切 n 是实例 (`drop-tw`, 审查 E 路 `drop₂` 的一般形式), 此时槽位层 `tw n` 有到目标的字面路径 (`below-tw`).
> 后果: 三个折叠 (现行两个, 换基一个) 的结点行共用 `kp`, 这一格上输出都是 ℕ 极限 (`chainᴿ`, `chainᵀ`, `chainᴮ`). 换基证据给出的保留 (`keepS`, 搬自留档附件 AuditEKeepFix, 改成对一切参数) 在目标是地板加非零偏移时确实保留 (`keepS-lift`).
> 不否定什么: 没有值的定理; 这一格在终点归约的实际链上是否被问到是判断. 入口: `drop-idx`, `drop-tw`, `keepS`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCMCross where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; mapK; kp; kp⁼; node⁺; nodeLe)
import OCF.Lean.YiRWFold as RW
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBSBase using (Schema; floor; offsets; index-floor; rb-tw)
```

## 分叉

`Cross a u v`: 槽位的推进路径 u 与目标路径 v 都进层号 a, 先一起下行 (后继形状, 一致目标), 然后在一个 Ω 形状结点上 u 走孩子一侧 (`inc` 或 `inu`), v 走指定孩子. 不含 ℕ 极限形状与下标层侧的共同下行 (那两种要层号证据, 这里不用).

```agda
data Cross {k j : L} : (a : L) → k ≤ a → j ≤ a → Set where
  xcc : ∀ {k′ h′} c (u : k ≤ h′ c) c″ (v : j ≤ h′ c″) → Cross (nd (sΩ k′) h′) (inc c u) (inc c″ v)
  xuc : ∀ {k′ h′} (us : (c : Tr k′) → k ≤ h′ c) c″ (v : j ≤ h′ c″) → Cross (nd (sΩ k′) h′) (inu us) (inc c″ v)
  xS  : ∀ {h} {u : k ≤ h tt} {v : j ≤ h tt} → Cross (h tt) u v → Cross (nd sS h) (inc tt u) (inc tt v)
  xSu : ∀ {h} {us : (c : ⊤) → k ≤ h c} {v : j ≤ h tt} → Cross (h tt) (us tt) v → Cross (nd sS h) (inu us) (inc tt v)
  xU  : ∀ {s h} c {u : k ≤ h c} {vs : (c : Ch s) → j ≤ h c} → Cross (h c) u (vs c) → Cross (nd s h) (inc c u) (inu vs)
  xUu : ∀ {s h} {us : (c : Ch s) → k ≤ h c} {vs : (c : Ch s) → j ≤ h c}
      → Cross (h (c₀ s)) (us (c₀ s)) (vs (c₀ s)) → Cross (nd s h) (inu us) (inu vs)

cross-drop : ∀ {k j a} {u : k ≤ a} {v : j ≤ a} → Cross a u v → (o : Ok a) (t : Pos⁼ k) → kp⁼ a o (psh u t) v ≡ nothing
cross-drop (xcc c u c″ v)  o t = refl
cross-drop (xuc us c″ v)   o t = refl
cross-drop (xS x)          o t = cross-drop x (proj₂ o tt) t
cross-drop (xSu x)         o t = cross-drop x (proj₂ o tt) t
cross-drop (xU c x)        o t = cross-drop x (proj₂ o c) t
cross-drop (xUu {s = s} x) o t = cross-drop x (proj₂ o (c₀ s)) t
```

顶上一步: Ω 形状层号的下标侧槽位, 目标经指定孩子 c′. 行 `kp … (inj₁ t) (inc c v)` 把槽位沿 `k ≤ h c′` 推进孩子再判定.

```agda
drop-idx : ∀ k h (o : Ok (nd (sΩ k) h)) (t : Pos⁼ k) c′ {j} (v : j ≤ h c′)
  → Cross (h c′) (proj₂ (proj₁ o) c′) v → kp (nd (sΩ k) h) o (inj₁ t) (inc c′ v) ≡ nothing
drop-idx k h ((ok , kh) , oc) t c′ v x =
  cong (mapK (pshBr (kh c′) t) (pshFirst (kh c′) t)) (cross-drop x (oc c′) t)
```

## 塔各项

塔第 n+1 项, 孩子 c′ 是 Ω 结点 `Ω p g` (偏移的顶是 Ω 形状), 目标经偏移顶结点的任一孩子 c″. n = 0 时 `Pos (tw 0)` 为空, 陈述空真; n ≥ 1 时 `Ωt (tw n)` 是这样的孩子 (`c′-inst`).

```agda
drop-tw : ∀ n (p : Pos (tw n)) (g : Br (tw n) p → Tr (tw n)) (t : Pos⁼ (tw n))
  (c″ : Tr (at (tw n) p)) {j} (v : j ≤ tw n ⊕ ↑ (tw n) (g (fromBr (tw n) p c″)))
  → kp (tw (suc n)) (Ok-tw (suc n)) (inj₁ t) (inc (Ω p g) (inc c″ v)) ≡ nothing
drop-tw n p g t c″ v = drop-idx (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) t (Ω p g) (inc c″ v) (xuc _ c″ v)

c′-inst : ∀ n → Σ (Pos (tw (suc n))) λ p → Σ (Br (tw (suc n)) p → Tr (tw (suc n))) λ g → proj₁ (Ωt (tw (suc n))) ≡ Ω p g
c′-inst n = _ , _ , refl

below-tw : ∀ n (b : L) → tw n ≤ tw n ⊕ b
below-tw n b = lift (tw n) b
```

## 后果: 三个折叠在这一格上都是 ℕ 极限

```agda
data IsL {S : Sg} : T S → Set where
  isL : ∀ f a → IsL (lim f a)

nodeL : ∀ {j X x₀} (m : Keep j X x₀) → m ≡ nothing → (G : X → Tr⁺ j) (s : X → X) → IsL (proj₁ (node⁺ m G s))
nodeL .nothing refl G s = isL _ _

chainᴿ : ∀ ℓ o (B : Base ℓ) j (w : j ≤ ℓ) β p g → kp ℓ o p w ≡ nothing → IsL (proj₁ (RW.ψ ℓ o B j w β (Ω p g)))
chainᴿ ℓ o B j w β p g e = nodeL (kp ℓ o p w) e _ _

chainᵀ : ∀ ℓ o r (B : Base ℓ) j (w : j ≤ ℓ) β p g → kp ℓ o p w ≡ nothing → IsL (proj₁ (TB.ψ ℓ o r B j w β (Ω p g)))
chainᵀ ℓ o r B j w β p g e = nodeL (kp ℓ o p w) e _ _

chainᴮ : ∀ ℓ o r (B : Base ℓ) j (w : j ≤ ℓ) β p g → kp ℓ o p w ≡ nothing → IsL (proj₁ (BS.ψ ℓ o r B j w β (Ω p g)))
chainᴮ ℓ o r B j w β p g e = nodeL (kp ℓ o p w) e _ _

chain-twᴮ : ∀ n p g c″ {j} (v : j ≤ tw n ⊕ ↑ (tw n) (g (fromBr (tw n) p c″))) (B : Base (tw (suc n))) β
  → IsL (proj₁ (BS.ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B j (inc (Ω p g) (inc c″ v)) β (proj₁ (Ωt (tw (suc n))))))
chain-twᴮ n p g c″ v B β = chainᴮ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B _ _ β _ _ (drop-tw n p g (inj₁ tt) c″ v)
```

## 换基证据给出的保留

对一切换基证据, 一切下标层槽位, 一切地板之上的目标: 沿 `index-floor ∙ u` 把槽位推进目标. 落在目标的真槽位上就保留, 落在目标自身 (同层) 就不保留. 没有接进折叠.

```agda
toKeep : ∀ {j X x₀} (r : Pos⁼ j) (cv : Br⁼ j r → X) → cv (bz⁼ j r) ≡ x₀ → Keep j X x₀
toKeep (inj₁ _) cv e = nothing
toKeep (inj₂ q) cv e = just (q , cv , e)

keepS : ∀ {k h} (S : Schema k h) (t : Pos⁼ k) {j} → floor S ≤ j
      → Keep j (Br (nd (sΩ k) h) (inj₁ t)) (fromBr (nd (sΩ k) h) (inj₁ t) zero)
keepS S t u = toKeep (psh (index-floor S ∙ u) t) (pshBr (index-floor S ∙ u) t) (pshFirst (index-floor S ∙ u) t)

data IsJust {A : Set} : Maybe A → Set where
  isJ : ∀ a → IsJust (just a)

keepS-lift : ∀ {k h} (S : Schema k h) (t : Pos⁼ k) s (b : Ch s → L)
  → IsJust (keepS S t (lift (floor S) (nd s b)))
keepS-lift S t s b = isJ _
```
