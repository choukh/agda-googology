# 取尾部的上确界构造子 (原型): 折叠

> 判决: 原型, 合法闭项仍在 (`twᶜ`, `EBOᶜ`, 类型即合法). 同 `YiRWFold`, 多 `sup q x Y e` 的四行: 自身行逐孩子上折; 一致路径与下标层侧逐孩子折叠; 分支侧 (指定孩子 c′) 有尾部证据时取尾部 `Y (c′ + z)`, 路径是 `v ∙ 尾部路径`, 没有时回退.
> `up x c y` 的各行逐字未动 (分支侧仍回退). 单调 `mono` 补 `◃p` 的四行.
> 不否定什么; 值没有证. 验收与形状测试在 `YiSupCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSupFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiSupBlock
open import OCF.Lean.YiSupOps
open import OCF.Lean.YiSupPath
```

## 底与保留判定

底给每个经路径可达的低层一棵非零的树. 保留时交出目标层的槽位 q, 换型 cv, 以及 cv 把第一分支送到第一分支.

```agda
Base : L → Set
Base ℓ = (j : L) → j ≤ ℓ → Tr⁺ j

B₀ : (ℓ : L) → Base ℓ
B₀ ℓ j _ = Ωt j

Keep : L → (X : Set) → X → Set
Keep j X x₀ = Maybe (Σ (Pos j) λ q → Σ (Br j q → X) λ cv → cv (fromBr j q zero) ≡ x₀)

mapK : ∀ {j X Y x₀ y₀} (f : X → Y) → f x₀ ≡ y₀ → Keep j X x₀ → Keep j Y y₀
mapK f e (just (q , cv , g)) = just (q , (λ z → f (cv z)) , trans (cong f g) e)
mapK f e nothing             = nothing

mutual
  kp : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
  kp ℓ             o               p              self      = just (p , (λ z → z) , refl)
  kp (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼ (h c) (oc c) t (vs c)
  kp (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₂ (c , t)) (ink v)   = kp⁼ (h c) (oc c) t (v ∙ kh c)
  kp (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼ (h c) (oc c) t v
  kp (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (oc n) (psh u t) v))
                     (λ u → kp⁼ (g m) (oc m) t (v ∙ u))
  kp (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = nothing
  kp (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼ k ok t v
  kp (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₁ t)       (inc c v) =
    mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼ (h c) (oc c) (psh (kh c) t) v)
  kp (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₁ t)       (inu vs)  =
    mapK (pshBr (kh zero) t) (pshFirst (kh zero) t) (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼ : (a : L) → Ok a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
  kp⁼ a o (inj₁ _) w = nothing
  kp⁼ a o (inj₂ p) w = kp a o p w

node⁺ : ∀ {j X x₀} → Keep j X x₀ → (X → Tr⁺ j) → (X → X) → Tr⁺ j
node⁺ (just (q , cv , _)) G s = Ω⁺ q (λ z → G (cv z))
node⁺ {x₀ = x₀} nothing G s   = limc⁺ (λ n → G (iter s x₀ n))

nodeLe : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) → j ⊢ proj₁ (G x₀) ◃ proj₁ (node⁺ m G s)
nodeLe {j} (just (q , cv , e)) G s = subst (λ t → j ⊢ proj₁ (G t) ◃ Ω q (λ z → proj₁ (G (cv z)))) e ◃w
nodeLe nothing                 G s = ◃l zero
```

## 折叠与单调

结点: 保留则在目标层的槽位上逐分支折叠, 否则取链 (分支回灌到槽位所在层号的折叠) 的部分和极限. 嵌入 `up x c y`: 自身行上折; 一切孩子的路径, 下标层侧, 后继形状进孩子 c, 底是 x 的折叠; ℕ 极限形状比较孩子编号; Ω 形状经指定孩子的路径回退.

`sup q x Y e` (只在 Ω 形状): 四行都是顶槽位 `inj₁ (inj₁ tt)` 的结点行, 分支 z 折叠孩子树 `Y z`, 底是 x 经孩子 z 的折叠, 反馈把孩子树折到下标层 k. 分支侧一行按层号证据的尾部字段 `tlΩ o` 派发 (对孩子是常值): 有尾部路径 tl 时分支 z 取 `Y (c′ + z)`, 路径 `v ∙ tl c′ z`; 没有时回退到 x 的折叠加上可数链的部分和极限.

```agda
mutual
  ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ ℓ o B j w β zero      = β
  ψ ℓ o B j w β (suc x)   = next⁺ (ψ ℓ o B j w β x)
  ψ ℓ o B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o B j w β (f n)) (λ n → mono ℓ o B j w β (a n))
  ψ ℓ o B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ (nd s h) o B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y
  ψ (nd s h) o B j (inu ws) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y
  ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ khΩ o c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) y
  ψ (nd sS h) o B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y
  ψ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) =
    ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y

  ψ (nd (sΩ k) h) o B _ self β (sup q x Y e) =
    Ω⁺ (inj₁ (inj₁ tt)) (λ c → Up (h c) (down stop c) (ψ (nd (sΩ k) h) o B _ self β x) (Y c))
  ψ (nd (sΩ k) h) o B j (inu ws) β (sup q x Y e) = node⁺ (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (inu ws))
    (λ z → ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) j (ws z) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (Y z))
    (λ z → proj₁ (ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) k (khΩ o z) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y z)))
  ψ (nd (sΩ k) h) o B j (ink v) β (sup q x Y e) = node⁺ (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (ink v))
    (λ z → ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) j (v ∙ khΩ o z) (ψ (nd (sΩ k) h) o B j (ink v) β x) (Y z))
    (λ z → proj₁ (ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) k (khΩ o z) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y z)))
  ψ (nd (sΩ k) h) o B j (inc c′ v) β (sup q x Y e) = cW (tlΩ o)
    (λ _ → ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ limc⁺ (λ n → ψ (h (iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero n))
        (proj₂ o (iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero n))
        (B₀ (h (iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero n))) zero
        (z≤ (h (iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero n))) (Ωt zero)
        (Y (iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero n))))
    (λ tl → node⁺ (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (inc c′ v))
      (λ z → ψ (h (c′ + z)) (proj₂ o (c′ + z)) (λ i u → ψ (nd (sΩ k) h) o B i (inc (c′ + z) u) (B i (inc (c′ + z) u)) x) j (v ∙ tl c′ z) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (Y (c′ + z)))
      (λ z → proj₁ (ψ (h (c′ + z)) (proj₂ o (c′ + z)) (λ i u → ψ (nd (sΩ k) h) o B i (inc (c′ + z) u) (B i (inc (c′ + z) u)) x) k (khΩ o (c′ + z)) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y (c′ + z)))))

  mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o B j w β x) ◃ proj₁ (ψ ℓ o B j w β y)
  mono ℓ o B j w β ◃s           = ◃l zero
  mono ℓ o B j w β (◃l n)       = ◃l n
  mono ℓ o B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) e
  mono (nd s h) o B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) e
  mono (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ khΩ o c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) e
  mono (nd sS h) o B j (inc c′ v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) e
  mono (nd sL g) o B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o B j (inc n v) β x) e)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃u x c y e) =
    +-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
  mono (nd s h) o B _ self β (◃c x c r) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) r
  mono (nd s h) o B j (inu ws) β (◃c x c r) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) r
  mono (nd (sΩ k) h) o B j (ink v) β (◃c x c r) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ khΩ o c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) r
  mono (nd sS h) o B j (inc c′ v) β (◃c x c r) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) r
  mono (nd sL g) o B j (inc n v) β (◃c x m r) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u r))
      (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o B j (inc n v) β x) r)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃c x c r) =
    +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) r))
  mono (nd (sΩ k) h) o B _ self β (◃p q x Y e) = ◃t (Upm (h zero) (down stop zero) (ψ (nd (sΩ k) h) o B _ self β x) (e zero)) ◃w
  mono (nd (sΩ k) h) o B j (inu ws) β (◃p q x Y e) =
    ◃t (mono (h zero) (proj₂ o zero) (λ i u → ψ (nd (sΩ k) h) o B i (inc zero u) (B i (inc zero u)) x) j (ws zero) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (e zero)) (nodeLe (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (inu ws))
          (λ z → ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) j (ws z) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (Y z))
          (λ z → proj₁ (ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) k (khΩ o z) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y z))))
  mono (nd (sΩ k) h) o B j (ink v) β (◃p q x Y e) =
    ◃t (mono (h zero) (proj₂ o zero) (λ i u → ψ (nd (sΩ k) h) o B i (inc zero u) (B i (inc zero u)) x) j (v ∙ khΩ o zero) (ψ (nd (sΩ k) h) o B j (ink v) β x) (e zero)) (nodeLe (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (ink v))
          (λ z → ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) j (v ∙ khΩ o z) (ψ (nd (sΩ k) h) o B j (ink v) β x) (Y z))
          (λ z → proj₁ (ψ (h z) (proj₂ o z) (λ i u → ψ (nd (sΩ k) h) o B i (inc z u) (B i (inc z u)) x) k (khΩ o z) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y z))))
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃p q x Y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (tlΩ o)
      (λ _ → +-mono _ (ι-mono j (◃t (proj₂ (ψ (h zero) (proj₂ o zero) (B₀ (h zero)) zero (z≤ (h zero)) (Ωt zero) (Y zero))) (◃l zero))))
      (λ tl → ◃t (mono (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) j (v ∙ tl c′ zero) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (e c′))
                 (nodeLe (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (inc c′ v))
          (λ z → ψ (h (c′ + z)) (proj₂ o (c′ + z)) (λ i u → ψ (nd (sΩ k) h) o B i (inc (c′ + z) u) (B i (inc (c′ + z) u)) x) j (v ∙ tl c′ z) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (Y (c′ + z)))
          (λ z → proj₁ (ψ (h (c′ + z)) (proj₂ o (c′ + z)) (λ i u → ψ (nd (sΩ k) h) o B i (inc (c′ + z) u) (B i (inc (c′ + z) u)) x) k (khΩ o (c′ + z)) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y (c′ + z))))))
  mono ℓ o B j w β (◃t d d′) = ◃t (mono ℓ o B j w β d) (mono ℓ o B j w β d′)
```

## 闭项

`ψ₀(Ω_ℓ)`: 默认底, 目标第 0 层, 一致路径, 底 `Ωt zero`. 合法性是类型.

```agda
ψ₀ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ ℓ o = ψ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

twᶜ : ℕ → Tr zero
twᶜ n = proj₁ (ψ₀ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

EBOᶜ : Tr zero
EBOᶜ = proj₁ (ψ₀ Λ Ok-Λ (proj₁ (Ωt Λ)))
```
