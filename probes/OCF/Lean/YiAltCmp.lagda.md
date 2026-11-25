# 替代写法的探针 (一): 同一层号里两条路径的比较, 路径末端的槽位

> 判决: 原型的工具, 编译定理, 无前提; 只导入精简块 (`YiRWBlock`, `YiRWOps`, `YiRWPath`, `YiRWFold` 的 `Keep`), 不读记号. `cmp a o v u`: 两条进同一层号 a 的路径 v : j ≤ a, u : k ≤ a, 部分地给出 j ≤ k; Ω 形状上两条都经指定孩子时交 `nothing` (不比较孩子下标).
> `end w`: 非自身的路径 w : a ≤ j 末端是 j 的一个槽位, 分支类型换回 `Tr a` (`Keep j (Tr a) zero`). `cmp-lift`: 经下标层再抬进 `a ⊕ b` 的路径对 `lift a b` 比较, 交回原路径 (对一切 b, 所以对塔的一切孩子).
> 不否定什么. 折叠在 `YiAltFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAltCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep)
```

## 分情形的小工具

```agda
cM : ∀ {A X : Set} → Maybe A → (A → X) → X → X
cM (just a) F d = F a
cM nothing  F d = d

cM-ind : ∀ {A X : Set} (Q : X → Set) (m : Maybe A) {F : A → X} {d : X}
       → ((a : A) → Q (F a)) → Q d → Q (cM m F d)
cM-ind Q (just a) hF hd = hF a
cM-ind Q nothing  hF hd = hd

cM-ind₂ : ∀ {A X : Set} (Q : X → X → Set) (m : Maybe A) {F F′ : A → X} {d d′ : X}
        → ((a : A) → Q (F a) (F′ a)) → Q d d′ → Q (cM m F d) (cM m F′ d′)
cM-ind₂ Q (just a) hF hd = hF a
cM-ind₂ Q nothing  hF hd = hd

sel : ∀ {X : Set} → Bool → X → X → X
sel true  a b = a
sel false a b = b

sel-ind : ∀ {X : Set} (Q : X → Set) (b : Bool) {x y : X} → Q x → Q y → Q (sel b x y)
sel-ind Q true  hx hy = hx
sel-ind Q false hx hy = hy

sel-ind₂ : ∀ {X : Set} (Q : X → X → Set) (b : Bool) {x x′ y y′ : X} → Q x x′ → Q y y′ → Q (sel b x y) (sel b x′ y′)
sel-ind₂ Q true  hx hy = hx
sel-ind₂ Q false hx hy = hy
```

## 路径下方的层号仍带证据

```agda
Ok-≤ : (ℓ : L) → Ok ℓ → ∀ {j} → j ≤ ℓ → Ok j
Ok-≤ ℓ             o              self      = o
Ok-≤ (nd s h)      (_ , oc)       (inc c v) = Ok-≤ (h c) (oc c) v
Ok-≤ (nd s h)      (_ , oc)       (inu vs)  = Ok-≤ (h (c₀ s)) (oc (c₀ s)) (vs (c₀ s))
Ok-≤ (nd (sΩ k) h) ((ok , _) , _) (ink v)   = Ok-≤ k ok v
```

## 比较

两条路径有字面的公共上界 a. 后继形状进同一个孩子; ℕ 极限形状比较孩子编号 (`way`); 一致路径取对方的那个孩子; 下标层侧的路径经证据 `k ≤ h c` 搬进孩子. Ω 形状上两条都经指定孩子: 不比较, 交 `nothing`.

```agda
cmp : (a : L) → Ok a → ∀ {j k} → j ≤ a → k ≤ a → Maybe (j ≤ k)
cmp a             o               v         self      = just v
cmp a             o               self      u         = nothing
cmp (nd sS h)     (_ , oc)        (inc _ v) (inc _ u) = cmp (h tt) (oc tt) v u
cmp (nd sL g)     (r , oc)        (inc m v) (inc n u) =
  cW (way g r m n) (λ w → cmp (g n) (oc n) (v ∙ w) u) (λ w → cmp (g m) (oc m) v (u ∙ w))
cmp (nd (sΩ k) h) _               (inc _ _) (inc _ _) = nothing
cmp (nd s h)      (_ , oc)        (inc c v) (inu us)  = cmp (h c) (oc c) v (us c)
cmp (nd s h)      (_ , oc)        (inu vs)  (inc c u) = cmp (h c) (oc c) (vs c) u
cmp (nd s h)      (_ , oc)        (inu vs)  (inu us)  = cmp (h (c₀ s)) (oc (c₀ s)) (vs (c₀ s)) (us (c₀ s))
cmp (nd (sΩ k) h) ((ok , _) , _)  (ink v)   (ink u)   = cmp k ok v u
cmp (nd (sΩ k) h) ((_ , kh) , oc) (ink v)   (inc c u) = cmp (h c) (oc c) (v ∙ kh c) u
cmp (nd (sΩ k) h) ((_ , kh) , oc) (ink v)   (inu us)  = cmp (h zero) (oc zero) (v ∙ kh zero) (us zero)
cmp (nd (sΩ k) h) ((_ , kh) , oc) (inc c v) (ink u)   = cmp (h c) (oc c) v (u ∙ kh c)
cmp (nd (sΩ k) h) ((_ , kh) , oc) (inu vs)  (ink u)   = cmp (h zero) (oc zero) (vs zero) (u ∙ kh zero)
```

`w ∙ lift a b` 对 `lift a b`: 交回 w. 塔第 n+1 项的证据里 `k ≤ h c` 就是 `lift (tw n) (↑ (tw n) c)`, 所以这条对一切孩子 c 成立, 不看 c.

```agda
∙-inu : ∀ {i j s} {h : Ch s → L} (w : i ≤ j) (vs : (c : Ch s) → j ≤ h c) → w ∙ inu vs ≡ inu (λ c → w ∙ vs c)
∙-inu w vs = refl

cmp-lift : (a b : L) (o : Ok (a ⊕ b)) {j : L} (w : j ≤ a) → cmp (a ⊕ b) o (w ∙ lift a b) (lift a b) ≡ just w
cmp-lift a zero     o        w = refl
cmp-lift a (nd s h) (_ , oc) w = cmp-lift a (h (c₀ s)) (oc (c₀ s)) w
```

## 路径末端的槽位

```agda
end⁼ : ∀ {a j} → a ≤ j → Σ (Pos⁼ j) λ t → Σ (Br⁼ j t → Tr a) λ cv → cv (bz⁼ j t) ≡ zero
end⁼ self = inj₁ tt , (λ z → z) , refl
end⁼ (inc c v) with end⁼ v
... | t , cv , e = inj₂ (inj₂ (c , t)) , cv , e
end⁼ {j = nd s h} (inu vs) with end⁼ (vs (c₀ s))
... | t , cv , e = inj₂ (inj₂ (c₀ s , t)) , cv , e
end⁼ (ink v) with end⁼ v
... | t , cv , e = inj₂ (inj₁ t) , cv , e

endK : ∀ {a j} → (Σ (Pos⁼ j) λ t → Σ (Br⁼ j t → Tr a) λ cv → cv (bz⁼ j t) ≡ zero) → Keep j (Tr a) zero
endK (inj₁ _ , _)      = nothing
endK (inj₂ q , cv , e) = just (q , cv , e)

end : ∀ {a j} → a ≤ j → Keep j (Tr a) zero
end w = endK (end⁼ w)
```
