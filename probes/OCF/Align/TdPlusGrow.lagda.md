# `Tᴰ₊` 的折叠 (三): 一致世界与 `growL′`

> 不含记号. 入口 [TdPlus](TdPlus.lagda.md). 说明 [TdPlusFold](TdPlusFold.lagda.md) 的折叠为什么是 "按 `growL′` 回灌": `T⁺` 在两种种类的世界 $(a,\beta)$ 里跑, 经 `uW` 它就是 `L′ k` 的一致世界; 这里证明一致世界恰好是 `growL′` 从最小世界生成的世界 (互模拟意义下).
>
> - **`embL≡`, `embK≡`** (定理, `≡`): `TdPlusUni` 的嵌入就是 `DiagK3Grow.embL`, `embK`.
> - **`grow-uni`** (定理): 一致世界经 `growL′` (任意 $f$, 任意 $H_0$ 增量 $\delta$) 得到一致世界 `uW (f a) (β ⊞ δ)`, 互模拟意义下 (`EqL`: `A` 界相等, 高度界 `_≈_`). 这就是 `T⁺` 的世界的一步: `A` 界换成 $f\,a$, 高度界接上 $\delta$.
> - **`d-uni`** (定理): 最小世界 `dW k` 是一致世界 `uW azero hz`.
> - **`grow-cong`**, **`reach-uni`** (定理): `growL′` 保互模拟; 所以从 `dW k` 出发经任意有限次 `growL′` 到达的世界都与某个一致世界互模拟.
>
> 互模拟而不是相等: `up (a ⊞ b)` 与 `up a ⊞ up b` 在 ℕ-极限处是两个 λ, 相等要函数外延; 这里不用. 世界的单调方向 (两种种类的世界变大, 一致世界变大) 是 `Uni.uW≤`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlusGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two; dW; dWLev)
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
import OCF.Align.DiagK3Grow as G
open import OCF.Align.DiagK3Grow using (embL)
open import OCF.Align.TdPlusUni
open import OCF.Align.TdPlusVal using (≈-refl; ≈-trans)
```

## §1 互模拟的算术

```agda
≈-sym : ∀ {S} {x y : HB S} → x ≈ y → y ≈ x
≈-sym ≈z = ≈z
≈-sym (≈s p) = ≈s (≈-sym p)
≈-sym (≈l p) = ≈l (λ n → ≈-sym (p n))
≈-sym (≈Ω p) = ≈Ω (λ c → ≈-sym (p c))

≡→≈ : ∀ {S} {x y : HB S} → x ≡ y → x ≈ y
≡→≈ {x = x} refl = ≈-refl x

⊞-≈ : ∀ {S} {a a′ b b′ : HB S} → a ≈ a′ → b ≈ b′ → a ⊞ b ≈ a′ ⊞ b′
⊞-≈ p ≈z = p
⊞-≈ p (≈s q) = ≈s (⊞-≈ p q)
⊞-≈ p (≈l q) = ≈l (λ n → ⊞-≈ p (q n))
⊞-≈ p (≈Ω q) = ≈Ω (λ c → ⊞-≈ p (q c))

module _ {S : KS} where
  up-≈ : {x y : HB S} → x ≈ y → up x ≈ up y
  up-≈ ≈z = ≈z
  up-≈ (≈s p) = ≈s (up-≈ p)
  up-≈ (≈l p) = ≈l (λ n → up-≈ (p n))
  up-≈ (≈Ω p) = ≈Ω (λ c → up-≈ (p c))

  up-⊞ : ∀ (a b : HB S) → up (a ⊞ b) ≈ up a ⊞ up b
  up-⊞ a hz = ≈-refl (up a)
  up-⊞ a (hs b) = ≈s (up-⊞ a b)
  up-⊞ a (hl f) = ≈l (λ n → up-⊞ a (f n))
  up-⊞ a (hΩ κ g) = ≈Ω (λ c → up-⊞ a (g c))

module _ {I : Set} {F : I → KS} (i : I) where
  ι-≈ : {x y : HB (F i)} → x ≈ y → ι {F = F} i x ≈ ι i y
  ι-≈ ≈z = ≈z
  ι-≈ (≈s p) = ≈s (ι-≈ p)
  ι-≈ (≈l p) = ≈l (λ n → ι-≈ (p n))
  ι-≈ (≈Ω p) = ≈Ω (λ c → ι-≈ (p c))

  ι-⊞ : ∀ (a b : HB (F i)) → ι {F = F} i (a ⊞ b) ≈ ι i a ⊞ ι i b
  ι-⊞ a hz = ≈-refl (ι i a)
  ι-⊞ a (hs b) = ≈s (ι-⊞ a b)
  ι-⊞ a (hl f) = ≈l (λ n → ι-⊞ a (f n))
  ι-⊞ a (hΩ κ g) = ≈Ω (λ c → ι-⊞ a (g c))
```

## §2 嵌入: 就是 `embL`, `embK`; 对加法互模拟

```agda
embL≡ : ∀ {S} (x : HB S) h → embL x h ≡ emb (uLev x) h
embL≡ hz h = refl
embL≡ (hs x) h = cong up (embL≡ x h)
embL≡ (hl f) h = cong (ι {F = λ n → Lev (f n)} 0) (embL≡ (f 0) h)
embL≡ {S} (hΩ κ g) h = cong (ι {F = λ c → Lev (g c)} (bot S κ)) (embL≡ (g (bot S κ)) h)

embLev-⊞ : ∀ {S} (x : HB S) a b → emb (uLev x) (a ⊞ b) ≈ emb (uLev x) a ⊞ emb (uLev x) b
embLev-⊞ hz a b = ≈-refl (a ⊞ b)
embLev-⊞ (hs x) a b = ≈-trans (up-≈ (embLev-⊞ x a b)) (up-⊞ (emb (uLev x) a) (emb (uLev x) b))
embLev-⊞ (hl f) a b =
  ≈-trans (ι-≈ {F = λ n → Lev (f n)} 0 (embLev-⊞ (f 0) a b)) (ι-⊞ {F = λ n → Lev (f n)} 0 (emb (uLev (f 0)) a) (emb (uLev (f 0)) b))
embLev-⊞ {S} (hΩ κ g) a b =
  ≈-trans (ι-≈ {F = λ c → Lev (g c)} (bot S κ) (embLev-⊞ (g (bot S κ)) a b))
          (ι-⊞ {F = λ c → Lev (g c)} (bot S κ) (emb (uLev (g (bot S κ))) a) (emb (uLev (g (bot S κ))) b))

FL : ℕ → Bool → KS
FL k = two (step (L′ k)) (Lev (Ωtop (L′ k)))

embL′-⊞ : ∀ k a b → emb (uL k) (a ⊞ b) ≈ emb (uL k) a ⊞ emb (uL k) b
embL′-⊞ zero a b = ≈-refl (a ⊞ b)
embL′-⊞ (suc k) a b =
  ≈-trans (ι-≈ {F = FL k} true (≈-trans (up-≈ (embL′-⊞ k a b)) (up-⊞ (emb (uL k) a) (emb (uL k) b))))
          (ι-⊞ {F = FL k} true (up (emb (uL k) a)) (up (emb (uL k) b)))

emb-z : ∀ k → emb (uL k) hz ≈ hz
emb-z zero = ≈z
emb-z (suc k) = ι-≈ {F = FL k} true (up-≈ (emb-z k))

embLev-z : ∀ {S} (x : HB S) → emb (uLev x) hz ≈ hz
embLev-z hz = ≈z
embLev-z (hs x) = up-≈ (embLev-z x)
embLev-z (hl f) = ι-≈ {F = λ n → Lev (f n)} 0 (embLev-z (f 0))
embLev-z {S} (hΩ κ g) = ι-≈ {F = λ c → Lev (g c)} (bot S κ) (embLev-z (g (bot S κ)))
```

## §3 世界的互模拟

```agda
EqLev : ∀ {S} (x : HB S) → Wd (Lev x) → Wd (Lev x) → Set
EqLev hz a a′ = a ≡ a′
EqLev (hs x) w w′ = EqLev x (proj₁ w) (proj₁ w′) × (proj₂ w ≈ proj₂ w′)
EqLev (hl f) w w′ = ∀ n → EqLev (f n) (w n) (w′ n)
EqLev (hΩ κ g) w w′ = ∀ c → EqLev (g c) (w c) (w′ c)

EqL : ∀ k → Wd (L′ k) → Wd (L′ k) → Set
EqL zero a a′ = a ≡ a′
EqL (suc k) w w′ = (EqL k (proj₁ (w true)) (proj₁ (w′ true)) × (proj₂ (w true) ≈ proj₂ (w′ true))) × EqLev (Ωtop (L′ k)) (w false) (w′ false)

EqLev-tr : ∀ {S} (x : HB S) {u v w} → EqLev x u v → EqLev x v w → EqLev x u w
EqLev-tr hz p q = trans p q
EqLev-tr (hs x) (p , p′) (q , q′) = EqLev-tr x p q , ≈-trans p′ q′
EqLev-tr (hl f) p q = λ n → EqLev-tr (f n) (p n) (q n)
EqLev-tr (hΩ κ g) p q = λ c → EqLev-tr (g c) (p c) (q c)

EqL-tr : ∀ k {u v w} → EqL k u v → EqL k v w → EqL k u w
EqL-tr zero p q = trans p q
EqL-tr (suc k) ((p , p′) , p″) ((q , q′) , q″) = (EqL-tr k p q , ≈-trans p′ q′) , EqLev-tr (Ωtop (L′ k)) p″ q″

d-uniLev : ∀ {S} (x : HB S) → EqLev x (dWLev x) (uW (uLev x) azero hz)
d-uniLev hz = refl
d-uniLev (hs x) = d-uniLev x , ≈-sym (embLev-z x)
d-uniLev (hl f) = λ n → d-uniLev (f n)
d-uniLev (hΩ κ g) = λ c → d-uniLev (g c)

d-uni : ∀ k → EqL k (dW k) (uW (uL k) azero hz)
d-uni zero = refl
d-uni (suc k) = (d-uni k , ≈-sym (emb-z k)) , d-uniLev (Ωtop (L′ k))
```

## §4 `growL′` 在一致世界上

```agda
module _ (f : A → A) (ffst : ∀ a → a ⊲ f a) (flg : ∀ a → Lg a → Lg (f a)) (δ : H₀) (lδ : LgB δ) where
  growW = G.growW f ffst flg δ lδ
  growL′ = G.growL′ f ffst flg δ lδ
  embK = G.embK f ffst flg δ lδ

  embK≡ : ∀ k x → embK k x ≡ emb (uL k) x
  embK≡ zero x = refl
  embK≡ (suc k) x = cong (λ z → ι {F = FL k} true (up z)) (embK≡ k x)

  grow-uniLev : ∀ {S} (x : HB S) a β → EqLev x (growW x (uW (uLev x) a β)) (uW (uLev x) (f a) (β ⊞ δ))
  grow-uniLev hz a β = refl
  grow-uniLev (hs x) a β =
    grow-uniLev x a β ,
    ≈-trans (⊞-≈ (≈-refl (emb (uLev x) β)) (≡→≈ (embL≡ x δ))) (≈-sym (embLev-⊞ x β δ))
  grow-uniLev (hl g) a β = λ n → grow-uniLev (g n) a β
  grow-uniLev (hΩ κ g) a β = λ c → grow-uniLev (g c) a β

  grow-uni : ∀ k a β → EqL k (growL′ k (uW (uL k) a β)) (uW (uL k) (f a) (β ⊞ δ))
  grow-uni zero a β = refl
  grow-uni (suc k) a β =
    (grow-uni k a β , ≈-trans (⊞-≈ (≈-refl (emb (uL k) β)) (≡→≈ (embK≡ k δ))) (≈-sym (embL′-⊞ k β δ))) ,
    grow-uniLev (Ωtop (L′ k)) a β

  grow-congLev : ∀ {S} (x : HB S) {w w′} → EqLev x w w′ → EqLev x (growW x w) (growW x w′)
  grow-congLev hz p = cong f p
  grow-congLev (hs x) (p , q) = grow-congLev x p , ⊞-≈ q (≈-refl (embL x δ))
  grow-congLev (hl g) p = λ n → grow-congLev (g n) (p n)
  grow-congLev (hΩ κ g) p = λ c → grow-congLev (g c) (p c)

  grow-cong : ∀ k {w w′} → EqL k w w′ → EqL k (growL′ k w) (growL′ k w′)
  grow-cong zero p = cong f p
  grow-cong (suc k) ((p , q) , r) = (grow-cong k p , ⊞-≈ q (≈-refl (embK k δ))) , grow-congLev (Ωtop (L′ k)) r
```

## §5 从最小世界经 `growL′` 到达的世界都一致

每一步可以换 $f$ 与 $\delta$ (各自满足 `growL′` 的前提).

```agda
data Reach (k : ℕ) : Wd (L′ k) → Set where
  r-d : Reach k (dW k)
  r-g : ∀ {w} (f : A → A) (ffst : ∀ a → a ⊲ f a) (flg : ∀ a → Lg a → Lg (f a)) (δ : H₀) (lδ : LgB δ) →
        Reach k w → Reach k (G.growL′ f ffst flg δ lδ k w)

reach-uni : ∀ k {w} → Reach k w → Σ A (λ a → Σ H₀ (λ β → EqL k w (uW (uL k) a β)))
reach-uni k r-d = azero , hz , d-uni k
reach-uni k (r-g f ffst flg δ lδ r) with reach-uni k r
... | a , β , e = f a , β ⊞ δ , EqL-tr k (grow-cong f ffst flg δ lδ k e) (grow-uni f ffst flg δ lδ k a β)
```
