# 龙骨原型: 折叠

> 判决: 候选原型 (折叠), 不替换主线. 逐行是候选 A 的 `YiKVFold`, 改两行, 都只读证书里新带的路径 q (下标层 ≤ 地板): (1) `kpA` 在源层 Ω 形状的下标侧槽位上不再一律不保留, 而是经 q 进地板, 再进锚层, 按锚层到目标的路径判定; (2) `cut` 在目标路径进入内层下标侧时交出 "到地板" 的路径 (接上 q), 走孩子自己的折叠.
> 行里不比较两个孩子, 不按存在性保留. 不否定什么; 形状在 `YiKDCheck`, 龙骨塔在 `YiKDKeel`, 值在 `YiKDTw1`, `YiKDStep`. 闭项 `twᶜ`, `EBOᶜ` 在文末.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiCertFold using (Base; B₀; Keep; mapK; node⁺; nodeLe; nz+; s+)
```

## 保留判定

`kpA`: 源层 m 的槽位沿证书下行, 落到地板时推进锚层, 按锚层到目标的路径判定; 源层 Ω 形状的下标侧槽位经证书的路径 q 进地板, 同样判定 (原型改的一行); 地板以上的孩子层本身不保留. 孩子 c 里的槽位朝经 c′ 的目标同样经 `kpA`.

```agda
mutual
  kp : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
  kp ℓ             o               p              self       = just (p , (λ z → z) , refl)
  kp (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)   = kp⁼ (h c) (oc c) t (vs c)
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₂ (c , t)) (ink v)    = kp⁼ (h c) (oc c) t (v ∙ kh o c)
  kp (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v)  = kp⁼ (h c) (oc c) t v
  kp (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v)  =
    cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (oc n) (psh u t) v))
                     (λ u → kp⁼ (g m) (oc m) t (v ∙ u))
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₂ (c , t)) (inc c′ v) = kpA (h c′) (oc c′) (ab→≤ (crt o c′)) v (crt o c) t
  kp (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)    = kp⁼ k ok t v
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inc c v)  =
    mapK (pshBr (kh o c) t) (pshFirst (kh o c) t) (kp⁼ (h c) (oc c) (psh (kh o c) t) v)
  kp (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inu vs)   =
    mapK (pshBr (kh o zero) t) (pshFirst (kh o zero) t) (kp⁼ (h zero) (oc zero) (psh (kh o zero) t) (vs zero))

  kp⁼ : (a : L) → Ok a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
  kp⁼ a o (inj₁ _) w = nothing
  kp⁼ a o (inj₂ p) w = kp a o p w

  kpA : ∀ {a₀} (a : L) → Ok a → a₀ ≤ a → ∀ {j} → j ≤ a → ∀ {m} → Ab a₀ m → (t : Pos⁼ m) → Keep j (Br⁼ m t) (bz⁼ m t)
  kpA a oa kk v here    t                     = mapK (pshBr kk t) (pshFirst kk t) (kp⁼ a oa (psh kk t) v)
  kpA a oa kk v (ab q f)  (inj₁ _)              = nothing
  kpA a oa kk v {m = nd (sΩ k) h} (ab q f) (inj₂ (inj₁ t)) =
    mapK (pshBr (q ∙ kk) t) (pshFirst (q ∙ kk) t) (kp⁼ a oa (psh (q ∙ kk) t) v)
  kpA a oa kk v {m = nd sS h} (ab q f) (inj₂ (inj₁ ()))
  kpA a oa kk v {m = nd sL h} (ab q f) (inj₂ (inj₁ ()))
  kpA a oa kk v (ab q f)  (inj₂ (inj₂ (c , t))) = kpA a oa kk v (f c) t
```

`cut`: 目标路径沿锚的证书下行, 到地板时交出 j ≤ 地板; 进入内层下标侧时接上证书的路径 q, 也交出 j ≤ 地板 (原型改的一行); 停在地板以上时交出 `tt`.

```agda
cut : ∀ {a m j} → Ab a m → j ≤ m → (j ≤ a) ⊎ ⊤
cut here                v         = inj₁ v
cut (ab q f)              self      = inj₂ tt
cut (ab q f)              (inc c v) = cut (f c) v
cut {m = nd s h} (ab q f) (inu vs)  = cut (f (c₀ s)) (vs (c₀ s))
cut (ab q f)              (ink v)   = inj₁ (v ∙ q)
```

## 折叠与单调

孩子 c 的底仍是 "x 朝该层经 c 的折叠". 分支侧一行: `cut` 交出 j ≤ 地板时走孩子 c 的折叠; 否则走 `φ`, 锚是孩子 c′ 的层与底, 源是孩子 c 的层, 证书与底.

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
  ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) = cW (cut (crt o c′) v)
    (λ u → ψ (h c) (proj₂ o c) (λ i u′ → ψ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (u ∙ ab→≤ (crt o c))
             (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y)
    (λ _ → φ (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (ab→≤ (crt o c′)) j v
             (h c) (proj₂ o c) (crt o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
             (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y)

  φ : ∀ {a₀} (a : L) (oa : Ok a) (Ba : Base a) (kk : a₀ ≤ a) (j : L) (v : j ≤ a)
    → (m : L) → Ok m → Ab a₀ m → Base m → Tr⁺ j → Tr m → Tr⁺ j
  φ a oa Ba kk j v m om here Bm β y = ψ a oa Ba j v β (proj₁ (emb a oa kk (s+ y)))
  φ a oa Ba kk j v m om (ab q f) Bm β zero      = β
  φ a oa Ba kk j v m om (ab q f) Bm β (suc x)   = next⁺ (φ a oa Ba kk j v m om (ab q f) Bm β x)
  φ a oa Ba kk j v m om (ab q f) Bm β (lim g r) =
    lim⁺ (λ n → φ a oa Ba kk j v m om (ab q f) Bm β (g n)) (λ n → φm a oa Ba kk j v m om (ab q f) Bm β (r n))
  φ a oa Ba kk j v m om (ab q f) Bm β (Ω p g)   = node⁺ (kpA a oa kk v (ab q f) (inj₂ p)) (λ z → φ a oa Ba kk j v m om (ab q f) Bm β (g z))
    (λ z → fromBr m p (proj₁ (ψ m om Bm (at m p) (posW m p) (Bm (at m p) (posW m p)) (g z))))
  φ a oa Ba kk j v (nd s h) om (ab q f) Bm β (up x c y e) =
    φ a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab q f) Bm β x) y

  φm : ∀ {a₀} (a : L) (oa : Ok a) (Ba : Base a) (kk : a₀ ≤ a) (j : L) (v : j ≤ a)
     (m : L) (om : Ok m) (U : Ab a₀ m) (Bm : Base m) (β : Tr⁺ j) {x y : Tr m}
     → m ⊢ x ◃ y → j ⊢ proj₁ (φ a oa Ba kk j v m om U Bm β x) ◃ proj₁ (φ a oa Ba kk j v m om U Bm β y)
  φm a oa Ba kk j v m om here Bm β d = mono a oa Ba j v β (emb-mono a oa kk (+-mono (suc zero) d))
  φm a oa Ba kk j v m om (ab q f) Bm β ◃s           = ◃l zero
  φm a oa Ba kk j v m om (ab q f) Bm β (◃l n)       = ◃l n
  φm a oa Ba kk j v m om (ab q f) Bm β (◃w {p = p}) = nodeLe (kpA a oa kk v (ab q f) (inj₂ p)) _ _
  φm a oa Ba kk j v (nd s h) om (ab q f) Bm β (◃u x c y e) =
    φu a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab q f) Bm β x) e
  φm a oa Ba kk j v (nd s h) om (ab q f) Bm β (◃c x c r) =
    φm a oa Ba kk j v (h c) (proj₂ om c) (f c) (λ i u → ψ (nd s h) om Bm i (inc c u) (Bm i (inc c u)) x)
      (φ a oa Ba kk j v (nd s h) om (ab q f) Bm β x) r
  φm a oa Ba kk j v m om (ab q f) Bm β (◃t d d′) =
    ◃t (φm a oa Ba kk j v m om (ab q f) Bm β d) (φm a oa Ba kk j v m om (ab q f) Bm β d′)

  φu : ∀ {a₀} (a : L) (oa : Ok a) (Ba : Base a) (kk : a₀ ≤ a) (j : L) (v : j ≤ a)
     (m : L) (om : Ok m) (U : Ab a₀ m) (Bm : Base m) (β : Tr⁺ j) {y : Tr m}
     → m ⊢ zero ◃ y → j ⊢ proj₁ β ◃ proj₁ (φ a oa Ba kk j v m om U Bm β y)
  φu a oa Ba kk j v m om here Bm β {y} d = mono a oa Ba j v β (proj₂ (emb a oa kk (s+ y)))
  φu a oa Ba kk j v m om (ab q f) Bm β d = φm a oa Ba kk j v m om (ab q f) Bm β d

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
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (cut (crt o c′) v)
      (λ u → mono (h c) (proj₂ o c) (λ i u′ → ψ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (u ∙ ab→≤ (crt o c))
               (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) e)
      (λ _ → φu (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (ab→≤ (crt o c′)) j v
               (h c) (proj₂ o c) (crt o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
               (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) e)
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
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (cut (crt o c′) v)
      (λ u → mono (h c) (proj₂ o c) (λ i u′ → ψ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (u ∙ ab→≤ (crt o c))
               (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) r)
      (λ _ → φm (h c′) (proj₂ o c′) (λ i u → ψ (nd (sΩ k) h) o B i (inc c′ u) (B i (inc c′ u)) x) (ab→≤ (crt o c′)) j v
               (h c) (proj₂ o c) (crt o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
               (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) r)
  mono ℓ o B j w β (◃t d d′) = ◃t (mono ℓ o B j w β d) (mono ℓ o B j w β d′)
```

## 闭项

```agda
ψ₀ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ ℓ o = ψ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

twᶜ : ℕ → Tr zero
twᶜ n = proj₁ (ψ₀ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

EBOᶜ : Tr zero
EBOᶜ = proj₁ (ψ₀ Λ Ok-Λ (proj₁ (Ωt Λ)))
```
