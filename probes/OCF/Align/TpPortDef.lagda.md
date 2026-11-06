# 两种种类的单调 (三): 第 0 层的结构关系

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [StrRelDef](StrRelDef.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 只取原文 §1 (`_⊑₀_`, `refl₀`, `nwd`, `preL₀`, `val₀`), 模块不带参数 (原文的参数只给 §2 以后用); `preL` 从原文的头部抄来.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPortDef where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtTowerTy using (hz)
open import OCF.Align.HtTowerFTree using (D; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; sum; pt; sum-fst) renaming (_≤_ to _≤ʷ_)

preL : ∀ {ly V} → (ℕ → D ly V) → ℕ → D ly V
preL d zero = n0
preL d (suc k) = preL d k ⨾ d k

infix 4 _⊑₀_
data _⊑₀_ : ∀ {V V′} → D hz V → D hz V′ → Set where
  z0  : ∀ {V V′} {x : D hz V′} → n0 {W = V} ⊑₀ x
  o1  : ∀ {V V′} → n1 {W = V} ⊑₀ n1 {W = V′}
  sq  : ∀ {V V′} {x y : D hz V} {x′ y′ : D hz V′} → x ⊑₀ x′ → y ⊑₀ y′ → (x ⨾ y) ⊑₀ (x′ ⨾ y′)
  lm  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → nl d ⊑₀ nl d′
  wl  : ∀ {V₀ V V′} {p : V₀ ≤ʷ V} {x : D hz V₀} {x′ : D hz V′} → x ⊑₀ x′ → nw p x ⊑₀ x′
  wr  : ∀ {V₀ V V′} {p : V₀ ≤ʷ V′} {x : D hz V} {x′ : D hz V₀} → x ⊑₀ x′ → x ⊑₀ nw p x′
  pr  : ∀ {V V′} {x : D hz V} {x′ : D hz V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} →
        x ⊑₀ x′ → (∀ n → d n ⊑₀ d′ n) → ∀ k → (x ⨾ preL d k) ⊑₀ (x′ ⨾ nl d′)
  tr  : ∀ {V V′} {x y : D hz V} {z : D hz V′} → x ⊑₀ y → y ⊑₀ z → x ⊑₀ z
  u0l : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → (n0 ⨾ x) ⊑₀ x′
  u0r : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → x ⊑₀ (n0 ⨾ x′)
  u1l : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → (x ⨾ n0) ⊑₀ x′
  u1r : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → x ⊑₀ (x′ ⨾ n0)
  al  : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → (x ⨾ (y ⨾ z)) ⊑₀ t → ((x ⨾ y) ⨾ z) ⊑₀ t
  al′ : ∀ {V V′} {x y z : D hz V} {t : D hz V′} → ((x ⨾ y) ⨾ z) ⊑₀ t → (x ⨾ (y ⨾ z)) ⊑₀ t
  ar  : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → t ⊑₀ ((x ⨾ y) ⨾ z) → t ⊑₀ (x ⨾ (y ⨾ z))
  ar′ : ∀ {V V′} {x y z : D hz V′} {t : D hz V} → t ⊑₀ (x ⨾ (y ⨾ z)) → t ⊑₀ ((x ⨾ y) ⨾ z)

-- 第 0 层一切树自比
refl₀ : ∀ {V} (x : D hz V) → x ⊑₀ x
refl₀ n0 = z0
refl₀ n1 = o1
refl₀ (x ⨾ y) = sq (refl₀ x) (refl₀ y)
refl₀ (nl d) = lm (λ n → refl₀ (d n))
refl₀ (ni () u)
refl₀ (nκ () u)
refl₀ (nμ () u)
refl₀ (nw p x) = wl (wr (refl₀ x))

-- nw 对 ⨾ 的分配 (两个方向)
nwd : ∀ {V₀ V} {q : V₀ ≤ʷ V} (x y : D hz V₀) → nw q (x ⨾ y) ⊑₀ (nw q x ⨾ nw q y)
nwd x y = wl (sq (wr (refl₀ x)) (wr (refl₀ y)))

nwd′ : ∀ {V₀ V} {q : V₀ ≤ʷ V} (x y : D hz V₀) → (nw q x ⨾ nw q y) ⊑₀ nw q (x ⨾ y)
nwd′ x y = wr (sq (wl (refl₀ x)) (wl (refl₀ y)))

preL₀ : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ k → preL d k ⊑₀ preL d′ k
preL₀ h zero = z0
preL₀ h (suc k) = sq (preL₀ h k) (h k)
```
```agda
val₀ : ∀ {V V′} {x : D hz V} {x′ : D hz V′} → x ⊑₀ x′ → ∀ {b b′} → b ≤ b′ → sum b x ≤ sum b′ x′
ptv  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ {b b′} → b ≤ b′ → ∀ n → pt b d n ≤ pt b′ d′ n
prv  : ∀ {V V′} {d : ℕ → D hz V} {d′ : ℕ → D hz V′} → (∀ n → d n ⊑₀ d′ n) → ∀ {b b′} → b ≤ b′ → ∀ k → sum b (preL d k) ≤ pt b′ d′ k
val₀ (z0 {x = x}) {b′ = b′} h = ≤-trans h (⊲→≤ (sum-fst b′ x))
val₀ o1 h = s≤ h
val₀ (sq hx hy) h = val₀ hy (val₀ hx h)
val₀ (lm hd) h = l≤ (λ n → ≤l n (ptv hd h n))
val₀ (wl hx) h = val₀ hx h
val₀ (wr hx) h = val₀ hx h
val₀ (pr hx hd k) h = ≤l k (prv hd (val₀ hx h) k)
val₀ (tr hx hy) {b′ = b′} h = ≤-trans (val₀ hx h) (val₀ hy (≤-refl b′))
val₀ (u0l hx) h = val₀ hx h
val₀ (u0r hx) h = val₀ hx h
val₀ (u1l hx) h = val₀ hx h
val₀ (u1r hx) h = val₀ hx h
val₀ (al hx) h = val₀ hx h
val₀ (al′ hx) h = val₀ hx h
val₀ (ar hx) h = val₀ hx h
val₀ (ar′ hx) h = val₀ hx h
ptv hd h zero = h
ptv hd h (suc n) = val₀ (hd n) (ptv hd h n)
prv hd h zero = h
prv hd h (suc k) = val₀ (hd k) (prv hd h k)
```
