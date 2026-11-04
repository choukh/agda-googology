# 中间层是布劳威尔树 (一): 第 0 层的互译

> 不含记号. 入口 [BrwMid](BrwMid.lagda.md). 第 0 层的差树 `D azero W` (`SumOneTree`) 与带字面合法性的布劳威尔树 `Σ A Lg` 互译.
>
> - `toA`: 差树到布劳威尔树. 加法 `_⊞_` 对右边递归, 极限 `Σlim` 写成部分和. **合法性由形状给:** `⊞-fst` ($a\lhd a\boxplus b$, 无前提) 与 `Lg-⊞` (前提只在加数上). `toA` 的输出就是一对, 不另证.
> - `dif`: 一条第一位置的路径 (带 `Lg`) 到差树.
> - 互逆到值: `sum-toA` ($\mathrm{sum}\,b\,x\approx b\boxplus\mathrm{toA}\,x$), `dif-ok` ($a\boxplus\mathrm{toA}(\mathrm{dif}\,p)\approx b$).
> - 字面不互逆: `dif-not-id` (差树一侧不 `≡`), `sum-dif-not-≈ᴬ` (树一侧连结构等价 `≈ᴬ` 都不成立). 这是编译过的反例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwMidZero where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ; ⊲→≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
```

## §1 布劳威尔树的加法给第一位置

```agda
⊞-fst : ∀ a b → a ⊲ a ⊞ b
⊞-fst a azero = C.self
⊞-fst a (asuc b) = C.suc (⊞-fst a b)
⊞-fst a (alim f) = C.lim 0 (⊞-fst a (f 0))

⊞-⊲ : ∀ a {x y} → x ⊲ y → a ⊞ x ⊲ a ⊞ y
⊞-⊲ a C.self = C.self
⊞-⊲ a (C.suc q) = C.suc (⊞-⊲ a q)
⊞-⊲ a (C.lim n q) = C.lim n (⊞-⊲ a q)

Lg-⊞ : ∀ a b → Lg a → Lg b → Lg (a ⊞ b)
Lg-⊞ a azero u v = u
Lg-⊞ a (asuc b) u v = Lg-⊞ a b u v
Lg-⊞ a (alim f) u (st , v) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) u (v n))
```

## §2 带合法性的布劳威尔树

```agda
L₀ : Set
L₀ = Σ A Lg

𝟎 𝟏 : L₀
𝟎 = azero , tt
𝟏 = asuc azero , tt

infixl 6 _+ᴸ_
_+ᴸ_ : L₀ → L₀ → L₀
(a , u) +ᴸ (b , v) = a ⊞ b , Lg-⊞ a b u v

-- 部分和: 第 n+1 项是第 n 项加一段
pts : L₀ → (ℕ → L₀) → ℕ → L₀
pts b f zero = b
pts b f (suc n) = pts b f n +ᴸ f n

-- 极限: 部分和的极限. 步进就是 ⊞-fst, 不调用别的证明
Σlim : L₀ → (ℕ → L₀) → L₀
Σlim b f = alim (λ n → proj₁ (pts b f n)) , (λ n → ⊞-fst (proj₁ (pts b f n)) (proj₁ (f n))) , (λ n → proj₂ (pts b f n))

toA : ∀ {W} → D azero W → L₀
toA n0 = 𝟎
toA n1 = 𝟏
toA (x ⨾ y) = toA x +ᴸ toA y
toA (nl d) = Σlim 𝟎 (λ n → toA (d n))
toA (ni () u)
toA (nκ () u)
toA (nw p x) = toA x
```

## §3 `sum` 就是 `⊞`

```agda
infix 4 _≈_
_≈_ : A → A → Set
a ≈ b = (a ≤ b) × (b ≤ a)

≈-refl : ∀ a → a ≈ a
≈-refl a = ≤-refl a , ≤-refl a

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans (p , q) (p′ , q′) = ≤-trans p p′ , ≤-trans q′ q

⊞≈ : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ⊞ b) ≈ (a′ ⊞ b′)
⊞≈ (p , q) (p′ , q′) = ⊞-mono p p′ , ⊞-mono q q′

asso≈ : ∀ a b c → (a ⊞ (b ⊞ c)) ≈ ((a ⊞ b) ⊞ c)
asso≈ a b c = ⊞-asso a b c , ⊞-assoʳ a b c

z⊞ : ∀ c → c ≈ (azero ⊞ c)
z⊞ azero = z≤ , z≤
z⊞ (asuc c) = s≤ (proj₁ (z⊞ c)) , s≤ (proj₂ (z⊞ c))
z⊞ (alim f) = l≤ (λ n → ≤l n (proj₁ (z⊞ (f n)))) , l≤ (λ n → ≤l n (proj₂ (z⊞ (f n))))

lim≈ : ∀ {f g : ℕ → A} → (∀ n → f n ≈ g n) → alim f ≈ alim g
lim≈ h = l≤ (λ n → ≤l n (proj₁ (h n))) , l≤ (λ n → ≤l n (proj₂ (h n)))

sum-toA : ∀ {W} b (x : D azero W) → sum b x ≈ (b ⊞ proj₁ (toA x))
pt-toA  : ∀ {W} b (d : ℕ → D azero W) n → pt b d n ≈ (b ⊞ proj₁ (pts 𝟎 (λ m → toA (d m)) n))
sum-toA b n0 = ≈-refl b
sum-toA b n1 = ≈-refl (asuc b)
sum-toA b (x ⨾ y) =
  ≈-trans (sum-toA (sum b x) y)
  (≈-trans (⊞≈ (sum-toA b x) (≈-refl _))
           (asso≈ b (proj₁ (toA x)) (proj₁ (toA y)) .proj₂ , asso≈ b (proj₁ (toA x)) (proj₁ (toA y)) .proj₁))
sum-toA b (nl d) = lim≈ (pt-toA b d)
sum-toA b (ni () u)
sum-toA b (nκ () u)
sum-toA b (nw p x) = sum-toA b x
pt-toA b d zero = ≈-refl b
pt-toA b d (suc n) =
  ≈-trans (sum-toA (pt b d n) (d n))
  (≈-trans (⊞≈ (pt-toA b d n) (≈-refl _))
           (asso≈ b (proj₁ (pts 𝟎 (λ m → toA (d m)) n)) (proj₁ (toA (d n))) .proj₂ , asso≈ b _ _ .proj₁))

-- 从 0 起: sum 就是 toA
sum₀ : ∀ {W} (x : D azero W) → sum azero x ≈ proj₁ (toA x)
sum₀ x = ≈-trans (sum-toA azero x) (proj₂ (z⊞ _) , proj₁ (z⊞ _))
```

## §4 `dif`

```agda
dif : ∀ {W} b {a} → a ⊲ b → Lg b → D azero W
dif b C.self w = n0
dif (asuc c) (C.suc p) w = dif c p w ⨾ n1
dif (alim f) (C.lim n p) (st , w) = dif (f n) p (w n) ⨾ nl (λ m → dif (f (suc (m + n))) (st (m + n)) (w (suc (m + n))))

steps≤ : ∀ (f : ℕ → A) → (∀ n → f n ⊲ f (suc n)) → ∀ k n → f k ≤ f (k + n)
steps≤ f st k zero = subst (λ i → f k ≤ f i) (sym (+-identityʳ k)) (≤-refl (f k))
steps≤ f st k (suc n) = subst (λ i → f k ≤ f i) (sym (+-suc k n)) (≤-trans (steps≤ f st k n) (⊲→≤ (st (k + n))))

dif-ok : ∀ {W} b {a} (p : a ⊲ b) (w : Lg b) → (a ⊞ proj₁ (toA {W} (dif b p w))) ≈ b
dif-ok b C.self w = ≈-refl b
dif-ok (asuc c) {a} (C.suc p) w = s≤ (proj₁ (dif-ok c p w)) , s≤ (proj₂ (dif-ok c p w))
dif-ok {W} (alim f) {a} (C.lim n p) (st , w) =
  ≈-trans (asso≈ a X (proj₁ Σd))
  (lim≈′ (λ m → R m))
  where
  X = proj₁ (toA {W} (dif (f n) p (w n)))
  Dm : ℕ → L₀
  Dm m = toA {W} (dif (f (suc (m + n))) (st (m + n)) (w (suc (m + n))))
  Σd = Σlim 𝟎 Dm
  R : ∀ m → ((a ⊞ X) ⊞ proj₁ (pts 𝟎 Dm m)) ≈ f (m + n)
  R zero = dif-ok {W} (f n) {a = a} p (w n)
  R (suc m) =
    ≈-trans (asso≈ (a ⊞ X) (proj₁ (pts 𝟎 Dm m)) (proj₁ (Dm m)))
    (≈-trans (⊞≈ (R m) (≈-refl _)) (dif-ok {W} (f (suc (m + n))) {a = f (m + n)} (st (m + n)) (w (suc (m + n)))))
  lim≈′ : (∀ m → ((a ⊞ X) ⊞ proj₁ (pts 𝟎 Dm m)) ≈ f (m + n)) → alim (λ m → (a ⊞ X) ⊞ proj₁ (pts 𝟎 Dm m)) ≈ alim f
  lim≈′ h = l≤ (λ m → ≤l (m + n) (proj₁ (h m))) ,
            l≤ (λ k → ≤l k (≤-trans (subst (λ i → f k ≤ f i) refl (steps≤ f st k n)) (proj₂ (h k))))

-- 树 → 差 → 树: 值不变
round₁ : ∀ {W} b (w : Lg b) → proj₁ (toA {W} (dif b (z⊲ b) w)) ≈ b
round₁ {W} b w = ≈-trans (z⊞ _) (dif-ok {W} b {a = azero} (z⊲ b) w)

-- 差 → 树 → 差: sum 的值不变
round₂ : ∀ {W} (x : D azero W) → sum azero (dif {W} (sum azero x) (z⊲ (sum azero x)) (OCF.Align.SumOneTree.Lg-sum azero x tt)) ≈ sum azero x
round₂ {W} x = ≈-trans (sum₀ (dif {W} (sum azero x) (z⊲ _) _)) (round₁ {W} (sum azero x) _)
```

## §5 字面上不互逆

```agda
dif-not-id : ∀ {W} → ¬ (dif {W} (sum {W} azero n1) (sum-fst {W} azero n1) tt ≡ n1)
dif-not-id ()

natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ωA : A
ωA = alim natA

lgω : Lg ωA
lgω = (λ n → C.suc C.self) , go
  where
  go : ∀ n → Lg (natA n)
  go zero = tt
  go (suc n) = go n

sum-dif-not-≈ᴬ : ∀ {W} → ¬ (sum (asuc azero) (dif {W} ωA (C.lim 1 C.self) lgω) ≈ᴬ ωA)
sum-dif-not-≈ᴬ (l≈ h) with h 0
... | ()
```
