# 层号由回灌给出 (W3): 外延相等当关系, 第一位置与合法性是否尊重 ≈

> 不含记号. 入口 [LvFb](LvFb.lagda.md). 作者选定原话: "A3 提前探路". 本篇是三种不需要外延的写法里的第三种 (W3): 需要逐点相等的地方用互模拟 `_≈_` (`DiagK3Zero`), 律写到 ≈ 为止. 决定性的问题是: 第一位置 `_⊲[_]_` 与合法性 `LgB` 是否尊重 ≈. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; `Funext` 只在 §4 作模块参数 (条件).
>
> **结论.**
>
> 1. **到 ≈ 为止地尊重 (定理, 无条件).** `⊲≈`: 若 $a\lhd b$ 且 $b\approx b'$, 则有 $a'\approx a$ 使 $a'\lhd b'$. 沿 ≈ 的搬运对路径结构递归, 不沿 ≡ 搬.
> 2. **字面地尊重 = 一条外延原理 (定理).** `≈→¬<`: 互模拟的两棵树不互为严格子项 (对 `Acc` 归纳). 由它: `resp⊲→ext`: 若第一位置字面地尊重 ≈ (左端换成互模拟的树仍是第一位置), 则逐点互模拟的两个 ℕ-极限**相等** (`hl f ≡ hl g`); `respLg→ext`: 若合法性尊重 ≈, 同样的结论. 这两条前提在函数外延之下成立 (`FE.fe→resp⊲`, `FE.fe→respLg`, 条件定理), 所以前提可满足 (有外延的模型里); 在 `--safe --without-K` 不加外延时它们证不出 (判断, 元层: 结论 `hl f ≡ hl g` 对逐点互模拟而内涵不同的 $f, g$ 是函数外延的一个实例).
>
> **对 W3 的判决: 未走通 (只对本仓库的 `LgB`).** 证书 (第 3 层) 里的合法性是字面的 `LgB`; 要它尊重 ≈ 就要一条外延原理 (第 2 条). 换成 "到 ≈ 为止的合法性" (第一位置换成 `⊲≈` 的形状) 可以尊重 ≈ (第 1 条是它的第一块), 但那是第 3 层的新定义, 两种种类的折叠 `T⁺` 与它的合法性证书都要对新合法性重证; 本篇没有做. 这一条只否定 "字面合法性尊重 ≈ 而不加外延", 不否定到 ≈ 为止的合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvFbSet where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; Acc; acc; down; wf; toLt)
open import OCF.Align.AdmWCmp using (<ᴮ-tr)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
```

## §1 互模拟的基本性质

```agda
module _ {S : KS} where
  ≈-rf : ∀ (x : HB S) → x ≈ x
  ≈-rf hz = ≈z
  ≈-rf (hs x) = ≈s (≈-rf x)
  ≈-rf (hl f) = ≈l (λ n → ≈-rf (f n))
  ≈-rf (hΩ κ g) = ≈Ω (λ c → ≈-rf (g c))

  ≈-sym : ∀ {x y : HB S} → x ≈ y → y ≈ x
  ≈-sym ≈z = ≈z
  ≈-sym (≈s e) = ≈s (≈-sym e)
  ≈-sym (≈l e) = ≈l (λ n → ≈-sym (e n))
  ≈-sym (≈Ω e) = ≈Ω (λ c → ≈-sym (e c))

  -- 反演: 与后继 / 极限 / Ω-节点互模拟的树的形状
  inv-s : ∀ {z y : HB S} → z ≈ hs y → Σ (HB S) (λ z′ → (z ≡ hs z′) × (z′ ≈ y))
  inv-s (≈s e) = _ , refl , e

  inv-l : ∀ {z : HB S} {g : ℕ → HB S} → z ≈ hl g → Σ (ℕ → HB S) (λ f → (z ≡ hl f) × (∀ n → f n ≈ g n))
  inv-l (≈l e) = _ , refl , e

  inv-Ω : ∀ {z : HB S} {κ} {g : E S κ → HB S} → z ≈ hΩ κ g → Σ (E S κ → HB S) (λ f → (z ≡ hΩ κ f) × (∀ c → f c ≈ g c))
  inv-Ω (≈Ω e) = _ , refl , e
```

## §2 到 ≈ 为止地尊重第一位置

```agda
  ⊲≈ : ∀ {a b b′ : HB S} {w} → a ⊲[ w ] b → b ≈ b′ → Σ (HB S) (λ a′ → (a ≈ a′) × (a′ ⊲[ w ] b′))
  ⊲≈ {b′ = b′} hself e = b′ , e , hself
  ⊲≈ (hsuc p) (≈s e) with ⊲≈ p e
  ... | a′ , ea , q = a′ , ea , hsuc q
  ⊲≈ (hlim n p) (≈l e) with ⊲≈ p (e n)
  ... | a′ , ea , q = a′ , ea , hlim n q
  ⊲≈ (hLim {c = c} d p) (≈Ω e) with ⊲≈ p (e c)
  ... | a′ , ea , q = a′ , ea , hLim d q
```

## §3 互模拟的树不互为严格子项; 字面尊重推出外延

```agda
  private
    no< : ∀ {y : HB S} → Acc y → ∀ {x} → x ≈ y → x <ᴮ y → ⊥
    no< (acc r) e (<s₀ {b}) with inv-s e
    ... | z′ , refl , e′ = no< (r <s₀) e′ <s₀
    no< (acc r) e (<s {b = b} q) with inv-s e
    ... | z′ , refl , e′ = no< (r <s₀) e′ (<ᴮ-tr <s₀ q)
    no< (acc r) e (<l₀ {f = g} n) with inv-l e
    ... | f , eq , e′ = no< (r (<l₀ n)) (e′ n) (subst (λ t → f n <ᴮ t) (sym eq) (<l₀ n))
    no< (acc r) e (<l {f = g} n q) with inv-l e
    ... | f , refl , e′ = no< (r (<l₀ n)) (e′ n) (<ᴮ-tr (<l₀ n) q)
    no< (acc r) e (<Ω₀ {g = g} c) with inv-Ω e
    ... | f , eq , e′ = no< (r (<Ω₀ c)) (e′ c) (subst (λ t → f c <ᴮ t) (sym eq) (<Ω₀ c))
    no< (acc r) e (<Ω {g = g} c q) with inv-Ω e
    ... | f , refl , e′ = no< (r (<Ω₀ c)) (e′ c) (<ᴮ-tr (<Ω₀ c) q)

  ≈→¬< : ∀ {x y : HB S} → x ≈ y → x <ᴮ y → ⊥
  ≈→¬< {y = y} = no< (wf y)

  -- 互模拟且为第一位置 ⇒ 相等
  ≈⊲→≡ : ∀ {x y : HB S} {w} → x ≈ y → x ⊲[ w ] y → x ≡ y
  ≈⊲→≡ e p with toLt p
  ... | inj₁ eq = eq
  ... | inj₂ lt = ⊥-elim (≈→¬< e lt)

  -- 字面地尊重: 左端换成互模拟的树仍是第一位置
  Resp⊲ : Wd S → Set
  Resp⊲ w = ∀ {a a′ b : HB S} → a ≈ a′ → a ⊲[ w ] b → a′ ⊲[ w ] b

  resp⊲→ext : ∀ w → Resp⊲ w → ∀ (f g : ℕ → HB S) → (∀ n → f n ≈ g n) → hl f ≡ hl g
  resp⊲→ext w R f g e = ≈⊲→≡ (≈l e) (R {a = hl g} (≈-sym (≈l e)) (hself {w = w}))

  -- 合法性尊重 ≈
  RespLg : Set
  RespLg = ∀ {x y : HB S} → x ≈ y → LgB x → LgB y

  -- 两步链 hl g, hs (hl g), hs (hl g), …; 第 0 格换成互模拟的 hl f
  ch : HB S → HB S → ℕ → HB S
  ch x y zero = x
  ch x y (suc n) = hs y

  Lg-ch : ∀ (g : ℕ → HB S) → LgB (hl g) → LgB (hl (ch (hl g) (hl g)))
  Lg-ch g lg = st , lc
    where
    st : ∀ {w} n → ch (hl g) (hl g) n ⊲[ w ] ch (hl g) (hl g) (suc n)
    st zero = hsuc hself
    st (suc n) = hself
    lc : ∀ n → LgB (ch (hl g) (hl g) n)
    lc zero = lg
    lc (suc n) = lg

  ≈-ch : ∀ (f g : ℕ → HB S) → (∀ n → f n ≈ g n) → hl (ch (hl g) (hl g)) ≈ hl (ch (hl f) (hl g))
  ≈-ch f g e = ≈l h
    where
    h : ∀ n → ch (hl g) (hl g) n ≈ ch (hl f) (hl g) n
    h zero = ≈-sym (≈l e)
    h (suc n) = ≈-rf (hs (hl g))

  hs-inv : ∀ {x y : HB S} {w} → x ≈ y → x ⊲[ w ] hs y → x ≡ y
  hs-inv e hself = ⊥-elim (≈→¬< (≈-sym e) <s₀)
  hs-inv e (hsuc p) = ≈⊲→≡ e p

  respLg→ext : RespLg → Wd S → ∀ (f g : ℕ → HB S) → LgB (hl g) → (∀ n → f n ≈ g n) → hl f ≡ hl g
  respLg→ext R w f g lg e = hs-inv (≈l e) (proj₁ (R (≈-ch f g e) (Lg-ch g lg)) {w} 0)
```

前提实例: `Lg-ch` 的 `LgB (hl g)` 由 $g = \lambda\_\,.\,0$ 给出 (`lg-const`). `Resp⊲`, `RespLg` 在外延之下成立 (§4).

```agda
  lg-const : LgB {S} (hl (λ _ → hz))
  lg-const = (λ n → hself) , (λ n → tt)
```

## §4 前提在外延之下可满足 (条件)

```agda
module FE (fe : ∀ {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g) {S : KS} where
  ≈→≡ : ∀ {x y : HB S} → x ≈ y → x ≡ y
  ≈→≡ ≈z = refl
  ≈→≡ (≈s e) = cong hs (≈→≡ e)
  ≈→≡ (≈l e) = cong hl (fe (λ n → ≈→≡ (e n)))
  ≈→≡ (≈Ω {κ = κ} e) = cong (hΩ κ) (fe (λ c → ≈→≡ (e c)))

  fe→resp⊲ : ∀ w → Resp⊲ {S} w
  fe→resp⊲ w {b = b} e p = subst (λ t → t ⊲[ w ] b) (≈→≡ e) p

  fe→respLg : RespLg {S}
  fe→respLg e l = subst LgB (≈→≡ e) l
```

## §5 结论 (按档)

- **[定理]** `≈-rf`, `≈-sym`, `inv-s`, `inv-l`, `inv-Ω`, **`⊲≈`** (到 ≈ 为止地尊重第一位置), **`≈→¬<`**, `≈⊲→≡`.
- **[定理]** **`resp⊲→ext`**, **`respLg→ext`**: 字面地尊重 ≈ ⇒ 逐点互模拟的 ℕ-极限相等.
- **[定理, 条件 Funext]** `FE.fe→resp⊲`, `FE.fe→respLg` (前提可满足).
- **[判断]** 不加外延, `Resp⊲`, `RespLg` 在 `--safe --without-K` 证不出 (`hl f ≡ hl g` 对内涵不同的 $f, g$ 是函数外延的实例; 有不满足函数外延的 MLTT 模型).
- **[判断]** 把证书换成 "到 ≈ 为止的合法性" 要重写 `LgB` 与 `T⁺` 的合法性证书 (第 3 层); "尊重 ≈" 的引理那时会进证书. 本篇的 `⊲≈` 是第 4 层也可用的工具, 本身不进任何证书.
