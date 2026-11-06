# 规范形论证对树类型抽象 (一): 第 0 层差树的签名

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). [DValCanon](DValCanon.lagda.md) 的 `Gen` 写死在 `SumOneTree.D azero` 上, 用到的只是第 0 层差树的五个构造子 (`n0`, `n1`, `⨾`, `nl`, `nw`), 对它们的归纳, 和读法 `sum` (从底 $b$ 起把树加到 $b$ 上). 这里把这些写成一个记录 `Sig`:
>
> - 世界类型 `Wd` 与 `nw` 用的世界序 `_≺_` 也是参数 (`HtTowerFTree` 的世界是一对, 序是 `≤`);
> - 归纳原理 `ind` (只有五种情形: 第 0 层没有 `ni`, `nκ`, `nμ`, 实例里是 $\bot$);
> - 读法 `sum`, `pt` (部分和) 与七条计算方程; 实例里都是 `refl`. 方程是命题相等, 因为抽象的 `sum` 不能定义性地计算; `pt` 要单列, 因为 `sum b (nl d) ≡ alim (λ n → …)` 若对通用的部分和陈述就要外延性;
> - `sum-fst`, `Lg-sum`: 读法给出第一位置与合法性 (由上面可以导出, 实例里已有, 直接取).
>
> `Ops` 是对签名通用的定义: 部分和 `pre`, 从序数造差树 `dif`, 和 `sum⊞` (`sum b x` 与 $b\oplus$ `sum 0 x` 互相 $\le$), 由它得出 `smono` (`sum` 对底与树的值单调). `sum⊞` 在 `TLRuleSpec`, `BrwMidZero` (`sum-toA`) 各写过一次, `MonoPortBridge` 经翻译又借了一次.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenAbsSig where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
```

## §1 签名

```agda
record Sig : Set₁ where
  infixl 6 _⨾_
  field
    Wd  : Set
    _≺_ : Wd → Wd → Set
    T   : Wd → Set
    n0 n1 : ∀ {W} → T W
    _⨾_ : ∀ {W} → T W → T W → T W
    nl  : ∀ {W} → (ℕ → T W) → T W
    nw  : ∀ {W₀ W} → W₀ ≺ W → T W₀ → T W
    ind : (P : ∀ {W} → T W → Set) →
          (∀ {W} → P (n0 {W})) → (∀ {W} → P (n1 {W})) →
          (∀ {W} {x y : T W} → P x → P y → P (x ⨾ y)) →
          (∀ {W} {d : ℕ → T W} → (∀ n → P (d n)) → P (nl d)) →
          (∀ {W₀ W} {p : W₀ ≺ W} {x : T W₀} → P x → P (nw p x)) →
          ∀ {W} (z : T W) → P z
    sum : ∀ {W} → A → T W → A
    pt  : ∀ {W} → A → (ℕ → T W) → ℕ → A
    pt-z   : ∀ {W} b (d : ℕ → T W) → pt b d zero ≡ b
    pt-s   : ∀ {W} b (d : ℕ → T W) n → pt b d (suc n) ≡ sum (pt b d n) (d n)
    sum-n0 : ∀ {W} b → sum b (n0 {W}) ≡ b
    sum-n1 : ∀ {W} b → sum b (n1 {W}) ≡ asuc b
    sum-⨾  : ∀ {W} b (x y : T W) → sum b (x ⨾ y) ≡ sum (sum b x) y
    sum-nl : ∀ {W} b (d : ℕ → T W) → sum b (nl d) ≡ alim (pt b d)
    sum-nw : ∀ {W₀ W} b (p : W₀ ≺ W) (x : T W₀) → sum b (nw p x) ≡ sum b x
    sum-fst : ∀ {W} b (x : T W) → b ⊲ sum b x
    Lg-sum  : ∀ {W} b (x : T W) → Lg b → Lg (sum b x)
```

## §2 与树无关的小件

`tailP` 与 `SumOneTree`, `HtFeedTree` 里的同名定义相同, 这里重写一遍是为了不导入它们.

```agda
tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))

infix 4 _≈_
_≈_ : A → A → Set
a ≈ b = (a ≤ b) × (b ≤ a)

≡≈ : ∀ {a b} → a ≡ b → a ≈ b
≡≈ refl = ≤-refl _ , ≤-refl _

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans (p , q) (p′ , q′) = ≤-trans p p′ , ≤-trans q′ q

≈-sym : ∀ {a b} → a ≈ b → b ≈ a
≈-sym (p , q) = q , p

⊞≈ : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ⊞ b) ≈ (a′ ⊞ b′)
⊞≈ (p , q) (p′ , q′) = ⊞-mono p p′ , ⊞-mono q q′

asso≈ : ∀ a b c → ((a ⊞ b) ⊞ c) ≈ (a ⊞ (b ⊞ c))
asso≈ a b c = ⊞-assoʳ a b c , ⊞-asso a b c

lim≈ : ∀ {f g : ℕ → A} → (∀ n → f n ≈ g n) → alim f ≈ alim g
lim≈ h = l≤ (λ n → ≤l n (proj₁ (h n))) , l≤ (λ n → ≤l n (proj₂ (h n)))
```

## §3 对签名通用的定义

```agda
module Ops (σ : Sig) where
  open Sig σ

  pre : ∀ {W} → (ℕ → T W) → ℕ → T W
  pre d zero = n0
  pre d (suc k) = pre d k ⨾ d k

  -- 第一位置 a ⊲ b 之间的差, 只用构造子
  dif : ∀ {W} b {a} → a ⊲ b → Lg b → T W
  dif b C.self w = n0
  dif (asuc c) (C.suc p) w = dif c p w ⨾ n1
  dif (alim f) (C.lim n p) (st , w) = dif (f n) p (w n) ⨾ nl (λ m → dif (f (suc (m + n))) (st (m + n)) (w (suc (m + n))))

  val : ∀ {W} → T W → A
  val = sum azero

  -- 从底 a 起的和就是 a ⊞ (从 0 起的和)
  S⊞ : ∀ {W} → T W → Set
  S⊞ x = ∀ a → sum a x ≈ (a ⊞ val x)

  sum⊞ : ∀ {W} (x : T W) → S⊞ x
  sum⊞ = ind S⊞ c0 c1 c⨾ cl cw
    where
    c0 : ∀ {W} → S⊞ (n0 {W})
    c0 {W} a = ≈-trans (≡≈ (sum-n0 a)) (≡≈ (sym (cong (a ⊞_) (sum-n0 {W} azero))))
    c1 : ∀ {W} → S⊞ (n1 {W})
    c1 {W} a = ≈-trans (≡≈ (sum-n1 a)) (≡≈ (sym (cong (a ⊞_) (sum-n1 {W} azero))))
    c⨾ : ∀ {W} {x y : T W} → S⊞ x → S⊞ y → S⊞ (x ⨾ y)
    c⨾ {x = x} {y} hx hy a =
      ≈-trans (≡≈ (sum-⨾ a x y))
      (≈-trans (hy (sum a x))
      (≈-trans (⊞≈ (hx a) (≡≈ refl))
      (≈-trans (asso≈ a (val x) (val y))
      (≈-trans (⊞≈ (≡≈ {a} refl) (≈-sym (hy (val x))))
               (≡≈ (sym (cong (a ⊞_) (sum-⨾ azero x y))))))))
    cl : ∀ {W} {d : ℕ → T W} → (∀ n → S⊞ (d n)) → S⊞ (nl d)
    cl {d = d} h a =
      ≈-trans (≡≈ (sum-nl a d)) (≈-trans (lim≈ E) (≡≈ (sym (cong (a ⊞_) (sum-nl azero d)))))
      where
      E : ∀ n → pt a d n ≈ (a ⊞ pt azero d n)
      E zero = ≈-trans (≡≈ (pt-z a d)) (≡≈ (sym (cong (a ⊞_) (pt-z azero d))))
      E (suc n) =
        ≈-trans (≡≈ (pt-s a d n))
        (≈-trans (h n (pt a d n))
        (≈-trans (⊞≈ (E n) (≡≈ refl))
        (≈-trans (asso≈ a (pt azero d n) (val (d n)))
        (≈-trans (⊞≈ (≡≈ {a} refl) (≈-sym (h n (pt azero d n))))
                 (≡≈ (sym (cong (a ⊞_) (pt-s azero d n))))))))
    cw : ∀ {W₀ W} {p : W₀ ≺ W} {x : T W₀} → S⊞ x → S⊞ (nw p x)
    cw {p = p} {x} hx a =
      ≈-trans (≡≈ (sum-nw a p x)) (≈-trans (hx a) (≡≈ (sym (cong (a ⊞_) (sum-nw azero p x)))))

  -- sum 对底与树的值单调
  smono : ∀ {V V′} {b b′ : A} {x : T V} {x′ : T V′} → b ≤ b′ → val x ≤ val x′ → sum b x ≤ sum b′ x′
  smono {b = b} {b′} {x} {x′} h hx = ≤-trans (proj₁ (sum⊞ x b)) (≤-trans (⊞-mono h hx) (proj₂ (sum⊞ x′ b′)))
```
