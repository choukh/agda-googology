# 诊断实验: 同一合法界之下的两个坐标, 相等可判定

> 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 六路受阻的否定定理 (`DiagKLev.upd→wdec`, `CohWUpd.upd→wdec`, `CohW2Need.raise-Lc→wdec`, `ClosedReview1.find→dec`, `TelWNeg.occ-find→dec`) 的结论都是 "下标类型上相等的 (弱) 判定", 前提里的接口对**一切**下标成立, 不带字面公共上界. 本篇只证一件事: 在 `HtTowerTy.HB S` 上, 若两个高度 $a, b$ 都是同一个合法高度 $L$ 在同一个合法世界 $w$ 里的字面第一位置, 则 $a\equiv b$ 可判定 (`bdec`). 证明只用 `cmpB` 加一条 "非自反的第一位置是严格子项" (`toLt`) 与子项关系的良基 (`wf`).
>
> 它说的是: 对**可入的** (在公共界之下的) 下标, 否定定理的结论本来就是定理, 不是壁垒. 所以那些否定杀掉的是 "对不可入的下标也要求更新律" 的接口; 限制在可入下标上的选择性更新, 没有被任何一条否定覆盖. 怎么用它写世界的更新, 见诊断报告 §5 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StallDxBdec where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.HtTowerTy
```

## §1 严格子项, 良基

```agda
module _ {S : KS} where
  infix 4 _<ᴮ_
  data _<ᴮ_ : HB S → HB S → Set where
    <s₀ : ∀ {b} → b <ᴮ hs b
    <s  : ∀ {a b} → a <ᴮ b → a <ᴮ hs b
    <l₀ : ∀ {f} n → f n <ᴮ hl f
    <l  : ∀ {a f} n → a <ᴮ f n → a <ᴮ hl f
    <Ω₀ : ∀ {κ g} c → g c <ᴮ hΩ κ g
    <Ω  : ∀ {a κ g} c → a <ᴮ g c → a <ᴮ hΩ κ g

  data Acc (x : HB S) : Set where
    acc : (∀ {y} → y <ᴮ x → Acc y) → Acc x

  down : ∀ {x y} → Acc x → y <ᴮ x → Acc y
  down (acc r) p = r p

  wf : ∀ x → Acc x
  wf hz = acc (λ ())
  wf (hs x) = acc (λ { <s₀ → wf x ; (<s p) → down (wf x) p })
  wf (hl f) = acc (λ { (<l₀ n) → wf (f n) ; (<l n p) → down (wf (f n)) p })
  wf (hΩ κ g) = acc (λ { (<Ω₀ c) → wf (g c) ; (<Ω c p) → down (wf (g c)) p })

  irr : ∀ {x} → Acc x → ¬ (x <ᴮ x)
  irr (acc r) p = irr (r p) p
```

## §2 第一位置要么是相等, 要么是严格子项

```agda
  toLt : ∀ {a b w} → a ⊲[ w ] b → (a ≡ b) ⊎ (a <ᴮ b)
  toLt hself = inj₁ refl
  toLt (hsuc p) with toLt p
  ... | inj₁ refl = inj₂ <s₀
  ... | inj₂ q = inj₂ (<s q)
  toLt (hlim n p) with toLt p
  ... | inj₁ refl = inj₂ (<l₀ n)
  ... | inj₂ q = inj₂ (<l n q)
  toLt (hLim {c = c} e p) with toLt p
  ... | inj₁ refl = inj₂ (<Ω₀ c)
  ... | inj₂ q = inj₂ (<Ω c q)

  lt→≢ : ∀ {a b} → a <ᴮ b → ¬ (a ≡ b)
  lt→≢ {a} {b} q e = irr (wf b) (subst (λ z → z <ᴮ b) e q)
```

## §3 同一合法界之下, 相等可判定

```agda
  bdec : ∀ {a b L w} → a ⊲[ w ] L → b ⊲[ w ] L → LgW S w → LgB L → (a ≡ b) ⊎ ¬ (a ≡ b)
  bdec p q lw l with cmpB p q lw l
  ... | inj₁ r with toLt r
  ...   | inj₁ e = inj₁ (sym e)
  ...   | inj₂ s = inj₂ (λ e → lt→≢ s (sym e))
  bdec p q lw l | inj₂ r with toLt r
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ s = inj₂ (lt→≢ s)
```

**对照.** `DiagKLev.upd→wdec` 的结论是对**一切** `y y′ : HB S` 的 `¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)`; 这里对带公共界证据的 `a, b` 得到更强的 `(a ≡ b) ⊎ ¬ (a ≡ b)`, 而且是构造的. 两者不矛盾: 差别就在前提里有没有 `a ⊲[ w ] L`, `b ⊲[ w ] L`. 这正是 AGENTS 交替路线的那句 "被比较的两个下标必须有字面的公共上界", 用在了世界的更新上.
