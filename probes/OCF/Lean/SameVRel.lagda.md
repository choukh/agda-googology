# SameV (一): 跨层的值关系 (沿层号的配对)

> 不含记号. 入口 [SameV](SameV.lagda.md), 接口 [SameVIf](SameVIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValCRel`, `OCF.Lean.ValCBase` (只用, 不改).
>
> **配对 `Match`.** 接口的 `LvMor` 是位置上的函数, 带限制与搬运. 证明里用不到函数, 只用它的图: 层号上的一个二元关系 `_~_` (左边的层配右边的层), 三条律: 单值 (`~fun`, 这是协调性), 后继位置保持 (`~s`), 真第一位置保持 (`~pp`). 这三条使折叠的决定在配对下不变 (留 / 同层 / 在上). 记录里没有 "配对的层值相关" 这一条: 证明不用它. (从 `LvMor` 得到 `Match` 见入口 [SameV](SameV.lagda.md) `lv→match`.)
>
> **关系 `LE m m′`.** 左边第 $m$ 层, 右边第 $m'$ 层, $m,m'$ 不要求有任何关系. 形状同 ValC 的关系, 差两处:
>
> 1. **`Ω≼Ω`.** 左边种类的层与右边种类的层配对. 没有坐标的搬运 (反方向的映射不存在), 分支写成逻辑关系: 对一切相关的坐标 $d\preceq d'$ (右边值合法), $g\,d\preceq g'\,d'$.
> 2. **`≼Ω`.** 右边取一支, 坐标在右边的地板之下, 同 ValC.
>
> 坐标关系由 `LL` 对左边的层结构递归给出 (同 ValC 的 `lowT`). 左边不要求值合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.SameVRel (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (<⇒<′)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
```

## §1 配对

```agda
record Match : Set₁ where
  field
    _~_  : Cd → Cd → Set
    ~fun : ∀ {a b b′} → a ~ b → a ~ b′ → b ≡ b′
    ~s   : ∀ {j j′ u u′} → j ~ j′ → u ~ u′ → hs j ⊲ u → hs j′ ⊲ u′
    ~pp  : ∀ {t t′ u u′} → t ~ t′ → u ~ u′ → Pp t u → Pp t′ u′
```

## §2 关系

```agda
module X (Mt : Match) where
  open Match Mt public

  module R2 (m : Cd) (lw : ∀ (κ : K (T m)) k′ → H (lvK m κ) → H k′ → Set) (m′ : Cd) where
    infix 4 _≼_
    data _≼_ : H m → H m′ → Set where
      z≼  : ∀ {b} → hz ≼ b
      s≼s : ∀ {a b} → a ≼ b → hs a ≼ hs b
      ≼s  : ∀ {a b} → a ≼ b → a ≼ hs b
      l≼l : ∀ {f g} (σ : ℕ → ℕ) → Inc σ → (∀ n → f n ≼ g (σ n)) → hl f ≼ hl g
      ≼l  : ∀ {a g} n → a ≼ g n → a ≼ hl g
      ≼Ω  : ∀ {a κ′ g′} c → LeAt (lvK m′ κ′) c (top b⊥ (lvK m′ κ′)) → MoAt (lvK m′ κ′) c →
            a ≼ g′ (toK m′ κ′ c) → a ≼ hΩ κ′ g′
      Ω≼Ω : ∀ {κ κ′ g g′} → lvK m κ ~ lvK m′ κ′ →
            (∀ d d′ → MoAt (lvK m′ κ′) d′ → lw κ (lvK m′ κ′) d d′ → g (toK m κ d) ≼ g′ (toK m′ κ′ d′)) →
            hΩ κ g ≼ hΩ κ′ g′

  LL : ∀ m (κ : K (T m)) k′ → H (lvK m κ) → H k′ → Set
  LL hz ()
  LL (hs x) (inj₁ κ) = LL x κ
  LL (hs x) (inj₂ _) k′ = R2._≼_ x (LL x) k′
  LL (hl f) (n , κ) = LL (f n) κ
  LL (hΩ () _) _

  LE : ∀ m m′ → H m → H m′ → Set
  LE m m′ = R2._≼_ m (LL m) m′

  ll→ : ∀ m κ k′ {d d′} → LL m κ k′ d d′ → LE (lvK m κ) k′ d d′
  ll→ hz ()
  ll→ (hs x) (inj₁ κ) k′ p = ll→ x κ k′ p
  ll→ (hs x) (inj₂ _) k′ p = p
  ll→ (hl f) (n , κ) k′ p = ll→ (f n) κ k′ p
  ll→ (hΩ () _) _

  →ll : ∀ m κ k′ {d d′} → LE (lvK m κ) k′ d d′ → LL m κ k′ d d′
  →ll hz ()
  →ll (hs x) (inj₁ κ) k′ p = →ll x κ k′ p
  →ll (hs x) (inj₂ _) k′ p = p
  →ll (hl f) (n , κ) k′ p = →ll (f n) κ k′ p
  →ll (hΩ () _) _

  LE-tr : ∀ {k k₁ k₂} (e : k₁ ≡ k₂) {d : H k} (d₂ : H k₂) → LE k k₂ d d₂ → LE k k₁ d (subst H (sym e) d₂)
  LE-tr refl d₂ p = p

  ssy : ∀ {a b : Cd} (e : a ≡ b) (x : H b) → subst H e (subst H (sym e) x) ≡ x
  ssy refl x = refl
```

## §3 右边接上同层的关系

```agda
  module Lm (m m′ : Cd) where
    open R2 m (LL m) m′ public
    private module Lʳ = L m′

    tr≼ : ∀ {a b c} → a ≼ b → LeAt m′ b c → a ≼ c
    tr≼ z≼ q = z≼
    tr≼ p (Rel.≤s q) = ≼s (tr≼ p q)
    tr≼ p (Rel.≤l n q) = ≼l n (tr≼ p q)
    tr≼ p (Rel.≤Ω {κ = κ} c e mc q) = ≼Ω c (lle→ m′ κ c _ e) (lmo→ m′ κ c mc) (tr≼ p q)
    tr≼ (s≼s p) (Rel.s≤s q) = s≼s (tr≼ p q)
    tr≼ (≼s p) (Rel.s≤s q) = ≼s (tr≼ p q)
    tr≼ (l≼l σ i h) (Rel.l≤l τ j h′) = l≼l (λ n → τ (σ n)) (Lʳ.inc∘ i j) (λ n → tr≼ (h n) (h′ (σ n)))
    tr≼ (≼l n p) (Rel.l≤l τ j h′) = ≼l (τ n) (tr≼ p (h′ n))
    tr≼ (≼Ω {κ′ = κ′} c bd mc p) (Rel.Ω≤Ω {κ′ = κ″} e′ h′) =
      ≼Ω (subst H e′ c) (subst (λ z → LeAt _ (subst H e′ c) z) (top-tr e′) (LeAt-tr e′ c _ bd)) (MoAt-tr e′ c mc)
         (tr≼ p (h′ c (→lmo m′ κ′ c mc)))
    tr≼ {hΩ κ g} (Ω≼Ω {κ′ = κ′} ev h) (Rel.Ω≤Ω {κ′ = κ″} {g′ = g″} e′ h′) =
      Ω≼Ω (subst (lvK m κ ~_) e′ ev) (λ d d″ md″ r →
        let c = subst H (sym e′) d″
            mc = MoAt-tr (sym e′) d″ md″
        in subst (λ z → g (toK m κ d) ≼ g″ (toK m′ κ″ z)) (ssy e′ d″)
             (tr≼ (h d c mc (→ll m κ _ (LE-tr e′ d″ (ll→ m κ _ r)))) (h′ c (→lmo m′ κ′ c mc))))

    ⊞≼ : ∀ {a a′ x y} → a ≼ a′ → x ≼ y → a ⊞ x ≼ a′ ⊞ y
    ⊞≼ {a′ = a′} p (z≼ {b = y}) = tr≼ p (Lʳ.≤⊞ a′ y)
    ⊞≼ p (s≼s q) = s≼s (⊞≼ p q)
    ⊞≼ p (≼s q) = ≼s (⊞≼ p q)
    ⊞≼ p (l≼l σ i h) = l≼l σ i (λ n → ⊞≼ p (h n))
    ⊞≼ p (≼l n q) = ≼l n (⊞≼ p q)
    ⊞≼ p (≼Ω c bd mc q) = ≼Ω c bd mc (⊞≼ p q)
    ⊞≼ p (Ω≼Ω ev h) = Ω≼Ω ev (λ d d′ md r → ⊞≼ p (h d d′ md r))

    mul≼ : ∀ {a a′} → a ≼ a′ → ∀ n → mul a n ≼ mul a′ n
    mul≼ p zero = p
    mul≼ p (suc n) = ⊞≼ (mul≼ p n) p

    Σ≼ : ∀ F G σ → Inc σ → (∀ n → F n ≼ G (σ n)) → ∀ n → Σ⁺ F n ≼ Σ⁺ G (σ n)
    Σ≼ F G σ i h zero = tr≼ (h 0) (Ac0.Σ-ge m′ G (σ 0))
    Σ≼ F G σ i h (suc n) = tr≼ (⊞≼ (Σ≼ F G σ i h n) (h (suc n))) (Ac0.skip m′ G (<⇒<′ (i n)))

    one≼ : ∀ {y} → LeAt m′ (hs hz) y → hs hz ≼ y
    one≼ p = tr≼ (s≼s z≼) p
```

**链.** `Bx b b′`: 右边的界值合法, 在地板之上, 两边跨层相关.

```agda
  module Ch (t t′ : Cd) where
    open Lm t t′

    Bx : H t → H t′ → Set
    Bx b b′ = MoAt t′ b′ × LeAt t′ (top b⊥ t′) b′ × (b ≼ b′)

    chX : ∀ {b b′} (kL : H t → H t) (kR : H t′ → H t′) → Bx b b′ → Ac0.KP t′ kR →
          (∀ {b₁ b₂} → Bx b₁ b₂ → kL b₁ ≼ kR b₂) → ∀ n → chain b kL n ≼ chain b′ kR n
    chX kL kR B mR h zero = h B
    chX {b} {b′} kL kR B@(mb′ , tb , bb) mR h (suc n) =
      ⊞≼ (chX kL kR B mR h n)
        (h (L.Mo-⊞ t′ b′ _ mb′ (Ac0.chM t′ b′ kR mb′ tb mR n) ,
            L.≤-trans t′ tb (L.≤⊞ t′ b′ _) , ⊞≼ bb (chX kL kR B mR h n)))

    chX-hl : ∀ {b b′} (kL : H t → H t) (kR : H t′ → H t′) → Bx b b′ → Ac0.KP t′ kR →
             (∀ {b₁ b₂} → Bx b₁ b₂ → kL b₁ ≼ kR b₂) → hl (chain b kL) ≼ hl (chain b′ kR)
    chX-hl kL kR B mR h = l≼l (λ n → n) (L.idInc t) (chX kL kR B mR h)
```

**留下的结点.**

```agda
  keepX : ∀ {t t′ k k′} (κ₁ : K (T t)) (κ₂ : K (T t′)) (e₁ : lvK t κ₁ ≡ k) (e₂ : lvK t′ κ₂ ≡ k′)
          (fr₁ : E (T t) κ₁ → H k) (fr₂ : E (T t′) κ₂ → H k′) →
          (∀ c → fr₁ (toK t κ₁ c) ≡ subst H e₁ c) → (∀ c → fr₂ (toK t′ κ₂ c) ≡ subst H e₂ c) →
          k ~ k′ → ∀ (u₁ : H k → H t) (u₂ : H k′ → H t′) →
          (∀ d d′ → MoAt k′ d′ → LE k k′ d d′ → LE t t′ (u₁ d) (u₂ d′)) →
          LE t t′ (hΩ κ₁ (λ c → u₁ (fr₁ c))) (hΩ κ₂ (λ c → u₂ (fr₂ c)))
  keepX {t} {t′} κ₁ κ₂ refl refl fr₁ fr₂ ft₁ ft₂ ev u₁ u₂ h =
    R2.Ω≼Ω ev (λ d d′ md r → subst₂ (LE t t′) (sym (cong u₁ (ft₁ d))) (sym (cong u₂ (ft₂ d′)))
      (h d d′ md (ll→ t κ₁ _ r)))
```

## 结论 (按档)

- **[定理, 不用 UIP]** 配对的记录 `Match`; 关系 `LE`, `LL`, 搬运 `ll→`, `→ll`, `LE-tr`; `tr≼` (右边接同层的关系), `⊞≼`, `mul≼`, `Σ≼`, `one≼`, 链 `chX`, `chX-hl`, 留下的结点 `keepX`.
