# 结构关系, 第四轮 (三): 加上部分和规则, 对齐照样生成

> 不含记号. 入口 [StrRel4](StrRel4.lagda.md).
>
> `StrRel4Walk.walk` 的 `aR`/`aRL` 两句说的是 "右边末尾多出位置". 若要把格的输出也写成结构关系 (下一格的对齐要它), 这两句的输出形如 $x\sqsubseteq x'⨾y'$, 是部分和规则 `pr`, `StrRel3Zero` 的 $\sqsubseteq^{\mathsf O}$ 没有收. 这里定义 $\sqsubseteq^{\mathsf P}$ = $\sqsubseteq^{\mathsf O}$ 加 `pr`, 证明:
>
> - **`vsᴾ`**: 值可靠;
> - **`genᴾ`**: 由 $\sqsubseteq^{\mathsf P}$ 生成对齐, 与 `StrRel4Gen.gen` 同形. `pr` 一句: 右边多出的一段由 `ext` 接上, 末端领先量只会变松 (右边剩得更多);
> - **`alSuccᴾ`**, **`alZeroᴾ`**: 两种格.
>
> 结论: 部分和规则不妨碍对齐. 不加的是左边极限截断 (`lim⊑` 一类), 它对应 `KNestAdm.¬adm-end`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel4Pr where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; sum; pt; sum-fst; Lg-sum; Lg-pt)
open import OCF.Align.BrwMidZero using (sum-toA)
open import OCF.Align.KValSem using (toV0)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel3Zero using (_⊑ᴼ_)
import OCF.Align.StrRel3Zero as O
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aL)
open import OCF.Align.StrRel4Gen using (adm-back; module Tail; Al-tr; lgsf; ext; cat; adm-self)
```

## §1 关系

```agda
infix 4 _⊑ᴾ_
data _⊑ᴾ_ : ∀ {V V′} → D azero V → D azero V′ → Set where
  z0 : ∀ {V V′} {x : D azero V′} → n0 {W = V} ⊑ᴾ x
  o1 : ∀ {V V′} → n1 {W = V} ⊑ᴾ n1 {W = V′}
  sq : ∀ {V V′} {x y : D azero V} {x′ y′ : D azero V′} → x ⊑ᴾ x′ → y ⊑ᴾ y′ → (x ⨾ y) ⊑ᴾ (x′ ⨾ y′)
  lm : ∀ {V V′} {d : ℕ → D azero V} {d′ : ℕ → D azero V′} → (∀ n → d n ⊑ᴾ d′ n) → nl d ⊑ᴾ nl d′
  wl : ∀ {V₀ V V′} {p : V₀ ⊲ V} {x : D azero V₀} {x′ : D azero V′} → x ⊑ᴾ x′ → nw p x ⊑ᴾ x′
  wr : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D azero V} {x′ : D azero V₀} → x ⊑ᴾ x′ → x ⊑ᴾ nw p x′
  tr : ∀ {V V′} {x y : D azero V} {z : D azero V′} → x ⊑ᴾ y → y ⊑ᴾ z → x ⊑ᴾ z
  pr : ∀ {V V′} {x : D azero V} {x′ y′ : D azero V′} → x ⊑ᴾ x′ → x ⊑ᴾ (x′ ⨾ y′)

fromᴼ : ∀ {V V′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴼ x′ → x ⊑ᴾ x′
fromᴼ O.z0 = z0
fromᴼ O.o1 = o1
fromᴼ (O.sq h h′) = sq (fromᴼ h) (fromᴼ h′)
fromᴼ (O.lm h) = lm (λ n → fromᴼ (h n))
fromᴼ (O.wl h) = wl (fromᴼ h)
fromᴼ (O.wr h) = wr (fromᴼ h)
fromᴼ (O.tr h h′) = tr (fromᴼ h) (fromᴼ h′)

vsᴾ : ∀ {V V′ b b′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴾ x′ → b ≤ b′ → sum b x ≤ sum b′ x′
vsᴾ {b′ = b′} {x′ = x′} z0 h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
vsᴾ o1 h = s≤ h
vsᴾ {b = b} {b′} (sq {x = x} {x′ = x′} hx hy) h = vsᴾ {b = sum b x} {sum b′ x′} hy (vsᴾ hx h)
vsᴾ {b = b} {b′} (lm {d = d} {d′} hd) h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b d n ≤ pt b′ d′ n
  go zero = h
  go (suc n) = vsᴾ {b = pt b d n} {pt b′ d′ n} (hd n) (go n)
vsᴾ {b = b} {b′} (wl {x = x} {x′} hx) h = vsᴾ {b = b} {b′} {x} {x′} hx h
vsᴾ {b = b} {b′} (wr {x = x} {x′} hx) h = vsᴾ {b = b} {b′} {x} {x′} hx h
vsᴾ {b = b} {b′} (tr {x = x} {y} {z} hx hy) h = ≤-trans (vsᴾ {b = b} {b} {x} {y} hx (≤-refl b)) (vsᴾ {b = b} {b′} {y} {z} hy h)
vsᴾ {b = b} {b′} (pr {x = x} {x′} {y′} hx) h = ≤-trans (vsᴾ {b = b} {b′} {x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
```

## §2 生成对齐

```agda
genᴾ : ∀ {L L′ V V′ b b′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴾ x′ → (w : Lg b) (w′ : Lg b′) → b ≤ b′ →
       Adm (sum b x) (sum b′ x′) L L′ → Al L L′ (sum-fst b x) (Lg-sum b x w) (sum-fst b′ x′) (Lg-sum b′ x′ w′)
genᴾ {b′ = b′} {x′ = x′} z0 w w′ h ad = aS (sum-fst b′ x′) (Lg-sum b′ x′ w′)
genᴾ {b = b} {b′} o1 w w′ h ad = aP (aS C.self w′) h (adm-back ad (≤-refl (asuc b)) (≤-refl (asuc b′)) (≤-refl _))
genᴾ {b = b} {b′} (sq {x = x} {y} {x′} {y′} hx hy) w w′ h ad =
  cat (genᴾ hx w w′ h adx) (genᴾ hy (Lg-sum b x w) (Lg-sum b′ x′ w′) (vsᴾ hx h) ad)
      (sym (lgsf (sum b x) y (Lg-sum b x w))) (sym (lgsf (sum b′ x′) y′ (Lg-sum b′ x′ w′)))
  where
  adx = adm-back ad (proj₁ (sum-toA (sum b x) y)) (proj₂ (sum-toA (sum b′ x′) y′)) (toV0 y y′ (vsᴾ hy z≤))
genᴾ {b = b} {b′} (lm {d = d} {d′} hd) w w′ h ad =
  aL (aS C.self w′) (λ m → genᴾ (hd (m + 0)) (Lg-pt b d (m + 0) w) (Lg-pt b′ d′ (m + 0) w′) (ptle (m + 0)) (pos (suc (m + 0))))
  where
  module T = Tail b d
  module T′ = Tail b′ d′
  ptle : ∀ n → pt b d n ≤ pt b′ d′ n
  ptle zero = h
  ptle (suc n) = vsᴾ {b = pt b d n} {pt b′ d′ n} (hd n) (ptle n)
  pos : ∀ m → Adm (pt b d m) (pt b′ d′ m) _ _
  pos m = adm-back ad (≤-trans (T.up m) (proj₁ (sum-toA (pt b d m) (T.tl m))))
                      (≤-trans (proj₂ (sum-toA (pt b′ d′ m) (T′.tl m))) (T′.dn m))
                      (toV0 (T.tl m) (T′.tl m) (vsᴾ (lm (λ j → hd (j + m))) z≤))
genᴾ {b = b} {b′} (wl {x = x} {x′} hx) w w′ h ad = genᴾ {b = b} {b′} {x} {x′} hx w w′ h ad
genᴾ {b = b} {b′} (wr {x = x} {x′} hx) w w′ h ad = genᴾ {b = b} {b′} {x} {x′} hx w w′ h ad
genᴾ {L = L} {L′} {b = b} {b′} (tr {y = y} hx hy) w w′ h (δ , h₁ , h₂) =
  Al-tr (genᴾ {L′ = sum b y ⊞ δ} hx w w (≤-refl b) (δ , h₁ , ≤-refl _)) (genᴾ {L = sum b y ⊞ δ} hy w w′ h (δ , ≤-refl _ , h₂))
-- 右边多出的一段: 对齐由 ext 接上, 末端领先量变松
genᴾ {b = b} {b′} (pr {x = x} {x′} {y′} hx) w w′ h (δ , h₁ , h₂) =
  ext (sum-fst (sum b′ x′) y′) (Lg-sum (sum b′ x′) y′ (Lg-sum b′ x′ w′)) (sym (lgsf (sum b′ x′) y′ (Lg-sum b′ x′ w′)))
      (genᴾ {b = b} {b′} {x} {x′} hx w w′ h (δ , h₁ , ≤-trans (⊞-mono (⊲→≤ (sum-fst (sum b′ x′) y′)) (≤-refl δ)) h₂))
```

## §3 两种格

```agda
alSuccᴾ : ∀ {V V′ v v′} {d : D azero V} {d′ : D azero V′} → d ⊑ᴾ d′ → (lv : Lg v) (lv′ : Lg v′) → v ≤ v′ →
          Al (sum v d) (sum v′ d′) (sum-fst v d) (Lg-sum v d lv) (sum-fst v′ d′) (Lg-sum v′ d′ lv′)
alSuccᴾ {v = v} {v′} {d} {d′} h lv lv′ le = genᴾ h lv lv′ le (adm-self (sum v d) (sum v′ d′))

alZeroᴾ : ∀ {V V′ W₀ W₀′ W W′} {z : D azero V} {z′ : D azero V′} {q₀ : W₀ ⊲ W} {q₀′ : W₀′ ⊲ W′} (lW : Lg W) (lW′ : Lg W′) →
          Al (sum W z) (sum W′ z′) q₀ lW q₀′ lW′ → z ⊑ᴾ z′ → W ≤ W′ →
          Al (sum W z) (sum W′ z′) (⊲-tr q₀ (sum-fst W z)) (Lg-sum W z lW) (⊲-tr q₀′ (sum-fst W′ z′)) (Lg-sum W′ z′ lW′)
alZeroᴾ {W = W} {W′} {z} {z′} lW lW′ Hq h le =
  cat Hq (genᴾ h lW lW′ le (adm-self (sum W z) (sum W′ z′))) (sym (lgsf W z lW)) (sym (lgsf W′ z′ lW′))
```
