# 原型 (a): 折叠, 统一的底

> 判决: 原型, 不替换主线. 与 `YiRWFold` 逐行相同, 只换分支侧一行 (Ω 形状, 目标经指定孩子 c′, 嵌入在孩子 c): 不再回退到第 0 层, 改为沿孩子层的证书 `Ab k (h c)` 递归的 `φ` ("以孩子 c′ 的层为锚重读孩子 c 的树"). 进孩子时的底仍是同一个式子 "x 朝该层的折叠", 它经这一行, 所以对 `up` 形, 结点形的左项与读回层号是同一条规则.
> `φ`: 证书的叶子 `here` (层号逐字是下标层 k) 处把树嵌进锚层再正常折叠; 叶子 `via` 处先折到 k 再嵌入; 中间 `ab` 处逐构造子递归, 结点只在槽位落到叶子 `here` 时按锚层判定保留, 否则取源层回灌的链. 行里不比较 c 与 c′.
> 不否定什么; 值没有定理. 闭项 `twᶜ`, `EBOᶜ` 在文末; 验收在 `YiCertCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCertFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiCertPath
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
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₂ (c , t)) (ink v)   = kp⁼ (h c) (oc c) t (v ∙ kh o c)
  kp (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼ (h c) (oc c) t v
  kp (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (oc n) (psh u t) v))
                     (λ u → kp⁼ (g m) (oc m) t (v ∙ u))
  kp (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = nothing
  kp (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼ k ok t v
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inc c v) =
    mapK (pshBr (kh o c) t) (pshFirst (kh o c) t) (kp⁼ (h c) (oc c) (psh (kh o c) t) v)
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inu vs)  =
    mapK (pshBr (kh o zero) t) (pshFirst (kh o zero) t) (kp⁼ (h zero) (oc zero) (psh (kh o zero) t) (vs zero))

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

## 以锚层判定保留, 叶子处的非零树

`kpA`: 源层 m 的槽位沿证书下行; 落到叶子 `here` (层号逐字是 k) 时沿 `k ≤ a` 推进锚层 a, 按锚层到目标的路径判定; 其余一律不保留. 不读孩子下标.

```agda
kpA : ∀ {k} (a : L) → Ok a → k ≤ a → ∀ {j} → j ≤ a → ∀ {m} → Ab k m → (t : Pos⁼ m) → Keep j (Br⁼ m t) (bz⁼ m t)
kpA a oa kk v here    t                       = mapK (pshBr kk t) (pshFirst kk t) (kp⁼ a oa (psh kk t) v)
kpA a oa kk v (via _) t                       = nothing
kpA a oa kk v (ab f)  (inj₁ _)                = nothing
kpA a oa kk v (ab f)  (inj₂ (inj₁ _))         = nothing
kpA a oa kk v (ab f)  (inj₂ (inj₂ (c , t)))   = kpA a oa kk v (f c) t

nz+ : {S : Sg} (b y : T S) → Lt S zero b → Lt S zero (b + y)
nz+ b zero         nb = nb
nz+ b (suc y)      nb = z◃ (b + y) ◃s
nz+ b (lim f a)    nb = z◃ (b + f zero) (◃l zero)
nz+ {S} b (Ω p g)  nb = z◃ (b + g (b₀ S p)) ◃w
nz+ b (up y c w e) nb = z◃ (b + y) (◃u (b + y) c w e)

s+ : ∀ {k} → Tr k → Tr⁺ k
s+ y = suc zero + y , nz+ (suc zero) y ◃s
```

## 折叠与单调

结点: 保留则在目标层的槽位上逐分支折叠, 否则取链 (分支回灌到槽位所在层号的折叠) 的部分和极限. 嵌入 `up x c y`: 自身行上折; 一切孩子的路径, 下标层侧, 后继形状进孩子 c, 底是 x 的折叠; ℕ 极限形状比较孩子编号; Ω 形状经指定孩子 c′ 的路径时走 `φ`, 锚是孩子 c′ 的层与 c′ 的底, 源是孩子 c 的层, 证书与底.

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
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ kh o c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) y
  ψ (nd sS h) o B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y
  ψ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) =
    φ (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (kh o c′) j v
      (h c) (proj₂ o c) (proj₂ (proj₁ o) c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
      (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y

  φ : ∀ {k} (a : L) (oa : Ok a) (Ba : Base a) (kk : k ≤ a) (j : L) (v : j ≤ a)
    → (m : L) → Ok m → Ab k m → Base m → Tr⁺ j → Tr m → Tr⁺ j
  φ a oa Ba kk j v m om here Bm β y = ψ a oa Ba j v β (proj₁ (emb a oa kk (s+ y)))
  φ {k} a oa Ba kk j v m om (via w) Bm β y = ψ a oa Ba j v β (proj₁ (emb a oa kk (ψ m om Bm k w (Ωt k) y)))
  φ a oa Ba kk j v m om (ab f) Bm β zero      = β
  φ a oa Ba kk j v m om (ab f) Bm β (suc x)   = next⁺ (φ a oa Ba kk j v m om (ab f) Bm β x)
  φ a oa Ba kk j v m om (ab f) Bm β (lim g r) =
    lim⁺ (λ n → φ a oa Ba kk j v m om (ab f) Bm β (g n)) (λ n → φm a oa Ba kk j v m om (ab f) Bm β (r n))
  φ a oa Ba kk j v m om (ab f) Bm β (Ω p g)   = node⁺ (kpA a oa kk v (ab f) (inj₂ p)) (λ z → φ a oa Ba kk j v m om (ab f) Bm β (g z))
    (λ z → fromBr m p (proj₁ (ψ m om Bm (at m p) (posW m p) (Bm (at m p) (posW m p)) (g z))))
  φ a oa Ba kk j v (nd s h) om (ab f) Bm β (up x c y e) =
    φ a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab f) Bm β x) y

  φm : ∀ {k} (a : L) (oa : Ok a) (Ba : Base a) (kk : k ≤ a) (j : L) (v : j ≤ a)
     (m : L) (om : Ok m) (U : Ab k m) (Bm : Base m) (β : Tr⁺ j) {x y : Tr m}
     → m ⊢ x ◃ y → j ⊢ proj₁ (φ a oa Ba kk j v m om U Bm β x) ◃ proj₁ (φ a oa Ba kk j v m om U Bm β y)
  φm a oa Ba kk j v m om here Bm β d = mono a oa Ba j v β (emb-mono a oa kk (+-mono (suc zero) d))
  φm {k} a oa Ba kk j v m om (via w) Bm β d = mono a oa Ba j v β (emb-mono a oa kk (mono m om Bm k w (Ωt k) d))
  φm a oa Ba kk j v m om (ab f) Bm β ◃s           = ◃l zero
  φm a oa Ba kk j v m om (ab f) Bm β (◃l n)       = ◃l n
  φm a oa Ba kk j v m om (ab f) Bm β (◃w {p = p}) = nodeLe (kpA a oa kk v (ab f) (inj₂ p)) _ _
  φm a oa Ba kk j v (nd s h) om (ab f) Bm β (◃u x c y e) =
    φu a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab f) Bm β x) e
  φm a oa Ba kk j v (nd s h) om (ab f) Bm β (◃c x c r) =
    φm a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab f) Bm β x) r
  φm a oa Ba kk j v m om (ab f) Bm β (◃t d d′) =
    ◃t (φm a oa Ba kk j v m om (ab f) Bm β d) (φm a oa Ba kk j v m om (ab f) Bm β d′)

  φu : ∀ {k} (a : L) (oa : Ok a) (Ba : Base a) (kk : k ≤ a) (j : L) (v : j ≤ a)
     (m : L) (om : Ok m) (U : Ab k m) (Bm : Base m) (β : Tr⁺ j) {y : Tr m}
     → m ⊢ zero ◃ y → j ⊢ proj₁ β ◃ proj₁ (φ a oa Ba kk j v m om U Bm β y)
  φu a oa Ba kk j v m om here Bm β {y} d = mono a oa Ba j v β (proj₂ (emb a oa kk (s+ y)))
  φu {k} a oa Ba kk j v m om (via w) Bm β {y} d = mono a oa Ba j v β (proj₂ (emb a oa kk (ψ m om Bm k w (Ωt k) y)))
  φu a oa Ba kk j v m om (ab f) Bm β d = φm a oa Ba kk j v m om (ab f) Bm β d

  mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o B j w β x) ◃ proj₁ (ψ ℓ o B j w β y)
  mono ℓ o B j w β ◃s           = ◃l zero
  mono ℓ o B j w β (◃l n)       = ◃l n
  mono ℓ o B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) e
  mono (nd s h) o B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) e
  mono (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ kh o c)
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
    φu (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (kh o c′) j v
      (h c) (proj₂ o c) (proj₂ (proj₁ o) c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
      (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) e
  mono (nd s h) o B _ self β (◃c x c r) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) r
  mono (nd s h) o B j (inu ws) β (◃c x c r) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) r
  mono (nd (sΩ k) h) o B j (ink v) β (◃c x c r) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ kh o c)
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
    φm (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (kh o c′) j v
      (h c) (proj₂ o c) (proj₂ (proj₁ o) c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
      (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) r
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
