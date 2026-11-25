# 验收: `Tower` 成立, 主线见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (V132, V130)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `tower : Tower` (F2); `V130 : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ` (主线精简块).
> 做法: 不经上折. `low`: 对一切第 0 层的树 x, 满足 `OKB` 的一切底, 一切路径 w 与起点 β, x 的读回不高于层号 `h₁ x` 的 Ω 树沿 w 折到第 0 层的值 (ℕ 极限层号上取编号不小于路径编号的行, 避开嵌入一行). `Main`: x 是 ℕ 极限且不低于 BTBO 的参照时, `G (suc x)` 第 1 行之下字面地有 `up (Ωt ℓ) 0 (Ωt (g 0))`, 它的孩子底满足 `YiEVReach.Hi`, 于是 `reach` 可用.
> 不涉及上界; 只用到层号 2 的一行, 所以只是下界, 不是 `G (suc E₀)` 的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTWLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; plus≽; limcum≽; ◃→≺; _⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ⊴→≼)
open import OCF.Lean.YiLSFold using (OKB; ok-B₀; ok-dS; ok-dL)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; G)
open import OCF.Lean.YiEVReach using (Hi; _⇐_; ⇐r; ⇐l; reach; preΩ)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMEAnchor using (two; module G⁰)
open import OCF.Lean.YiMWPre using (sem→M⁰)
open import OCF.Lean.YiMWLow using (rd≽)
open import OCF.Lean.YiG0Low using (zs; rowS; nzS; G-infl; E₀2◃c₁; Tower)
open import OCF.Lean.YiG0Mono using (G-mono)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiDropRW using (Vᴿ; V-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiNFOCase using (tA; hA)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Align.EboLeanDef using (HC; cof; cω; fsn)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≺→s≼)
```

## 孩子编号: 不小于路径编号的行走后向一行

ℕ 极限层号上, 路径经孩子 k, 嵌入在孩子 m: m < k 时折叠先把孩子树搬进孩子 k (`fwd`), 否则进孩子 m (`bwd`). 取 m = n + k 就总是后一种 (`nlt`, `caseB`).

```agda
add : ℕ → ℕ → ℕ
add n zero    = n
add n (suc k) = suc (add n k)

data NLt : ∀ {m n} → Cmp m n → Set where
  ne : ∀ {m} → NLt (eq {m})
  ng : ∀ {m n} (l : n <ₙ m) → NLt (gt l)

nlt-s : ∀ {m n} {c : Cmp m n} → NLt c → NLt (sC c)
nlt-s ne     = ne
nlt-s (ng l) = ng (s< l)

nlt : ∀ n k → NLt (cmp (add n k) k)
nlt zero    zero    = ne
nlt (suc n) zero    = ng (z< n)
nlt n       (suc k) = nlt-s (nlt n k)

caseB : ∀ {g m n} {X : Set} (Q : X → Set) (r : Adj g) {c : Cmp m n} → NLt c
  → {F : g m ≤ g n → X} {B : g n ≤ g m → X} → ((v : g n ≤ g m) → Q (B v)) → Q (caseW (way′ g r c) F B)
caseB         Q r ne     hB = hB self
caseB {g = g} Q r (ng l) hB = hB (rt g r l)

f≼ : (f : ℕ → Tr zero) → (∀ n → zero ⊢ f n ◃ f (suc n)) → ∀ n k → read (f n) ≼ read (f (add n k))
f≼ f s n zero    = ≼-refl (read (f n))
f≼ f s n (suc k) = ≼-trans (f≼ f s n k) (⊴→≼ (⊴◃ (s (add n k))))

cumΩ-form : (g : ℕ → LF) (m : ℕ) → cumΩ g m ≡ up (preΩ g m) m (Ωt (g m)) (Ωt-nz (g m))
cumΩ-form g zero    = refl
cumΩ-form g (suc m) = refl
```

## `low`: 沿任意路径折到第 0 层, 值不低于孩子

对 x 归纳. 后继: 结点在第 0 层没有槽位, 取链的第 1 行, 它是 `next` 作用在孩子层 `next β₁` 的折叠上, 而 `Ωt a ⊴ β₁` (`OKB`). ℕ 极限: 第 m 行是孩子 m 上的折叠 (底换成孩子的底, 仍满足 `OKB`); 量化域: 读自第 0 层的树的层号, 一切带 `OKB` 的底.

```agda
low : (x : Tr zero) (ε : Ev (h₁ x)) (ρ : Rt (h₁ x)) (B : Base (h₁ x)) → OKB (h₁ x) B
    → (w : zero ≤ h₁ x) (β : Tr zero) (nβ : zero ⊢ zero ◃ β)
    → read x ≼ read (ψs (h₁ x) ε ρ B zero w β nβ (Ωt (h₁ x)))
low zero ε ρ B ok w β nβ = z≼
low (suc x) ε ρ B ok (ins w) β nβ =
  ≼l 1 (plus≽ _ _ (DR.suc≼next Y₁ (nzs a ε ρ B′ zero w β nβ c¹)
    (≼-trans (low x ε ρ B′ (ok-dS ε ρ B ok zero) w β nβ) (⊴→≼ (⊴◃ (monos a ε ρ B′ zero w β nβ d))))))
  where
  a : LF
  a = h₁ x
  B′ : Base a
  B′ = dS a ε ρ B zero
  c¹ : Tr a
  c¹ = next (bs B a (ins self)) (ns B a (ins self))
  Y₁ : Tr zero
  Y₁ = ψs a ε ρ B′ zero w β nβ c¹
  d : a ⊢ Ωt a ◃ c¹
  d = ⊴-◃ (proj₂ ok a (ins self)) (◃l zero)
low (lim f s) ε (ρc , R) B ok (inlu ws) β nβ = l≼ (λ n → ≼l n
  (subst (λ Y → read (f n) ≼ read (ψs (lim (λ m → h₁ (f m))) ε (ρc , R) B zero (inlu ws) β nβ Y))
    (sym (cumΩ-form (λ m → h₁ (f m)) n))
    (low (f n) (ε n) (ρc n) (dL (λ m → h₁ (f m)) ε (ρc , R) B n (preΩ (λ m → h₁ (f m)) n))
      (ok-dL (λ m → h₁ (f m)) ε (ρc , R) B ok n (preΩ (λ m → h₁ (f m)) n)) (ws n) _ _)))
low (lim f s) ε (ρc , R) B ok (inl k w) β nβ = l≼ (λ n → ≼l (add n k) (≼-trans (f≼ f s n k)
  (subst (λ Y → read (f (add n k)) ≼ read (ψs (lim (λ m → h₁ (f m))) ε (ρc , R) B zero (inl k w) β nβ Y))
    (sym (cumΩ-form (λ m → h₁ (f m)) (add n k)))
    (caseB {g = λ m → h₁ (f m)} (λ Z → read (f (add n k)) ≼ read Z) R (nlt n k)
      (λ v → low (f (add n k)) (ε (add n k)) (ρc (add n k))
        (dL (λ m → h₁ (f m)) ε (ρc , R) B (add n k) (preΩ (λ m → h₁ (f m)) (add n k)))
        (ok-dL (λ m → h₁ (f m)) ε (ρc , R) B ok (add n k) (preΩ (λ m → h₁ (f m)) (add n k))) (w ∙ v) _ _)))))
low (Ω () _)
low (up _ () _ _)
```

## ℕ 极限的孩子 x: `G (suc x)` 的第 1 行

层号 ℓ = `h₁ x` 是 ℕ 极限 `lim g`. `G (suc x)` 的链第 1 项是 `next (Ωt ℓ)`, 它的第 1 项 `Ωt ℓ + Ωt ℓ` 的第 0 项字面地是 `Tu = up (Ωt ℓ) 0 (Ωt (g 0))` (`T◃`). Tu 的折叠是孩子 0 上以 `B′` 为底的折叠; `B′` 的 `b⊥` 是 `G x`, 第 0 层分量是 `Ωt ℓ` 沿经孩子 0 的路径的折叠, 两者都不低于 x (`G-infl`, `low`), 所以 `Hi` 成立.

```agda
module Main (f : ℕ → Tr zero) (s : ∀ n → zero ⊢ f n ◃ f (suc n)) (p : two ⇐ h₁ (f zero))
            (hb : D.BTBOᴵ ≼ read (lim f s)) where
  x : Tr zero
  x = lim f s

  g : ℕ → LF
  g n = h₁ (f n)

  ℓ : LF
  ℓ = lim g

  B′ : Base (g 0)
  B′ = dL g (εh x) (ρh x) (B₀ ℓ) 0 (Ωt ℓ)

  hi′ : Hi (g 0) B′
  hi′ = ≼-trans hb (G-infl x)
      , λ w → ≼-trans hb (low x (εh x) (ρh x) (B₀ ℓ) (ok-B₀ ℓ) (inl 0 w) (Ωt zero) (Ωt-nz zero))

  Tu : Tr ℓ
  Tu = up (Ωt ℓ) 0 (Ωt (g 0)) (Ωt-nz (g 0))

  rowT : (h : HC tA) → R2.Rt h ≼ read (ψ⊥ ℓ (εh x) (ρh x) (B₀ ℓ) Tu)
  rowT = reach p (εh x 0) (proj₁ (ρh x) 0) B′ (ok-dL g (εh x) (ρh x) (B₀ ℓ) (ok-B₀ ℓ) 0 (Ωt ℓ)) hi′

  T◃ : ℓ ⊢ Tu ◃ zs x 1
  T◃ = ◃t {y = Ωt ℓ + Ωt ℓ} (◃l zero) (◃l 1)

  fold◃ : zero ⊢ ψ⊥ ℓ (εh x) (ρh x) (B₀ ℓ) Tu ◃ ψ⊥ ℓ (εh x) (ρh x) (B₀ ℓ) (zs x 1)
  fold◃ = mono⊥ ℓ (εh x) (ρh x) (B₀ ℓ) T◃

  strict : (h : HC tA) → O.suc (R2.Rt h) ≼ read (G (suc x))
  strict h = limcum≽ (rowS x) (nzS x) 1 (≼l 0 (≼-trans (s≼s (rowT h)) (≺→s≼ (◃→≺ fold◃))))

  weak : (h : HC tA) → R2.Rt h ≼ read (G (suc x))
  weak h = limcum≽ (rowS x) (nzS x) 1 (≼l 0 (≼-trans (rowT h) (⊴→≼ (⊴◃ fold◃))))
```

对一般的 x 陈述 (取第 0 项的函数 `seq0`), 免得在具体闭项上解极限的形状.

```agda
seq0 : Tr zero → Tr zero
seq0 (lim f _) = f zero
seq0 _         = zero

strictX : (x : Tr zero) → two ⇐ h₁ (seq0 x) → D.BTBOᴵ ≼ read x → (h : HC tA) → O.suc (R2.Rt h) ≼ read (G (suc x))
strictX zero          () hb
strictX (suc x)       () hb
strictX (lim f s)     p  hb = Main.strict f s p hb
strictX (Ω () _)
strictX (up _ () _ _)

weakX : (x : Tr zero) → two ⇐ h₁ (seq0 x) → D.BTBOᴵ ≼ read x → (h : HC tA) → R2.Rt h ≼ read (G (suc x))
weakX zero          () hb
weakX (suc x)       () hb
weakX (lim f s)     p  hb = Main.weak f s p hb
weakX (Ω () _)
weakX (up _ () _ _)
```

## 实例: 见证的底的第 0 层分量 `E₀`

`E₀` 的第 0 项是 `1 + ω`, 它的第 0 项是 2 (`pathE`, 由类型检查确认); `E₀` 不低于 BTBO 的参照 (`YiDropRow.btbo≼E₀`).

```agda
pathE : two ⇐ h₁ (seq0 DR.E₀)
pathE = ⇐l 0 ⇐r

strictE : (h : HC tA) → O.suc (R2.Rt h) ≼ read (G (suc DR.E₀))
strictE = strictX DR.E₀ pathE DR.btbo≼E₀

weakE : (h : HC tA) → R2.Rt h ≼ read (G (suc DR.E₀))
weakE = weakX DR.E₀ pathE DR.btbo≼E₀
```

## `Tower` 与 V130

`Tower`: 值序给出第 0 层的关系 (`sem→M⁰`), 再取基本列项 (`rω⁰`). V130 直接由 `strictE`: `suc E₀ ◃ c₁`, `G` 沿字面 ◃ 单调, `G c₁` 不高于见证的值.

```agda
fsM : ∀ {t} (h : HC t) (y : Tr zero) → R2.Rt h ≼ read y → cof t ≡ cω → ∀ n → MB.M⁰ (fsn t n) y
fsM h y q e n with MB.rω⁰ (sem→M⁰ h y (≼-trans q (rd≽ y))) e n
... | y′ , m , _ , le = G⁰.m⊴ m le

tower : Tower
tower = fsM hA (G (suc DR.E₀)) (weakE hA) refl

V130ᶠ : (h : HC tA) → O.suc (R2.Rt h) ≼ read DR.V
V130ᶠ h = ≼-trans (strictE h) (≼-trans (G-mono (◃t ◃s E₀2◃c₁)) (DR.row≼V 1))

V130 : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ
V130 h = up≼ V-R (V130ᶠ h)
```
