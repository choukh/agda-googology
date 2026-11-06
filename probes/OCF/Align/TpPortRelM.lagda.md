# 两种种类的单调 (五): 一般层上的结构关系 `RelM`

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort5Rel](MonoPort5Rel.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 只取原文的 `RelM` (原文其余是实例 $\Lambda=3$ 的特例); `OkRf` 多 `nμ` 一句.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerFTree using (Wd₂; LgW₂)
module OCF.Align.TpPortRelM {W : Wd₂} (lW : LgW₂ W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Data.Unit using (tt)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (hz; hs; hself; hsuc; _⊲[_]_)
open import OCF.Align.HtTowerFTree using (Ht; D; ss; StH; Vs; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortDef using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀) public

module RelM (ly : Ht) (Low : ∀ {k} (r : StH W k ly) → Vs ly r W → Vs ly r W → Set) where
  infix 4 _⊑_
  data _⊑_ : D ly W → D ly W → Set where
    n0⊑ : ∀ {x} → n0 ⊑ x
    n1⊑ : n1 ⊑ n1
    ⨾⊑  : ∀ {x y x′ y′} → x ⊑ x → x′ ⊑ x′ → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)
    nl⊑ : ∀ {d d′ : ℕ → D ly W} → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
    ni⊑ : ∀ {k} (r : StH W k ly) {u u′ : ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′} →
          (∀ z z′ → Low r z z′ → u ≤rf lW z ⊑ u ≤rf lW z′) →
          (∀ z z′ → Low r z z′ → u′ ≤rf lW z ⊑ u′ ≤rf lW z′) →
          (∀ z z′ → Low r z z′ → u ≤rf lW z ⊑ u′ ≤rf lW z′) → ni r u ⊑ ni r u′
    nwˡ : ∀ {x x′} → x ⊑ x′ → nw ≤rf x ⊑ x′
    nwʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ nw ≤rf x′
    nwᵉ : ∀ {x x′} → nw ≤rf x ⊑ nw ≤rf x′ → x ⊑ x′
    tr  : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    u0ˡ : ∀ {x x′} → x ⊑ x′ → (n0 ⨾ x) ⊑ x′
    u0ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (n0 ⨾ x′)
    u1ˡ : ∀ {x x′} → x ⊑ x′ → (x ⨾ n0) ⊑ x′
    u1ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (x′ ⨾ n0)
    asˡ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → (x ⨾ (y ⨾ z)) ⊑ t → ((x ⨾ y) ⨾ z) ⊑ t
    asˡ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → ((x ⨾ y) ⨾ z) ⊑ t → (x ⨾ (y ⨾ z)) ⊑ t
    asʳ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ ((x ⨾ y) ⨾ z) → t ⊑ (x ⨾ (y ⨾ z))
    asʳ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ (x ⨾ (y ⨾ z)) → t ⊑ ((x ⨾ y) ⨾ z)
    pre⊑ : ∀ {x x′} {d d′ : ℕ → D ly W} → x ⊑ x → x′ ⊑ x′ → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) →
           x ⊑ x′ → (∀ n → d n ⊑ d′ n) → ∀ k → (x ⨾ preL d k) ⊑ (x′ ⨾ nl d′)

  Rf : D ly W → Set
  Rf x = x ⊑ x

  rPre : ∀ {e : ℕ → D ly W} → (∀ n → Rf (e n)) → ∀ k → Rf (preL e k)
  rPre r zero = n0⊑
  rPre r (suc k) = ⨾⊑ (rPre r k) (rPre r k) (rPre r k) (r k)

  rnw : ∀ {x} → Rf x → Rf (nw ≤rf x)
  rnw r = nwˡ (nwʳ r)

  -- nw 对 ⨾ 的分配 (两个方向), 只在 self
  nwd : ∀ {x y} → Rf x → Rf y → nw ≤rf (x ⨾ y) ⊑ (nw ≤rf x ⨾ nw ≤rf y)
  nwd rx ry = nwˡ (⨾⊑ rx (rnw rx) (nwʳ rx) (nwʳ ry))

  nwd′ : ∀ {x y} → Rf x → Rf y → (nw ≤rf x ⨾ nw ≤rf y) ⊑ nw ≤rf (x ⨾ y)
  nwd′ rx ry = nwʳ (⨾⊑ (rnw rx) rx (nwˡ rx) (nwˡ ry))

  -- 上下文的自比, 沿 ⨾ 的左脊记下每一段 (对树的形状计算, 不对推导反演)
  Ok : D ly W → Set
  Ok (a ⨾ b) = Ok a × Rf b
  Ok x = Rf x

  OkRf : ∀ {x} → Ok x → Rf x
  OkRf {x = n0} o = o
  OkRf {x = n1} o = o
  OkRf {x = a ⨾ b} (oa , rb) = ⨾⊑ (OkRf oa) (OkRf oa) (OkRf oa) rb
  OkRf {x = nl d} o = o
  OkRf {x = ni r u} o = o
  OkRf {x = nκ z v} o = o
  OkRf {x = nμ z v} o = o
  OkRf {x = nw p x} o = o
```
