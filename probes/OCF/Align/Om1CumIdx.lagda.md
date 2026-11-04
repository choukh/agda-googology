# 下标的账: 累加到累加不要严格性, 带基底的嵌入

> **验收文件.** 入口 [Om1Cum](Om1Cum.lagda.md). `CumVal` §5 判断 $\Omega+1$ 这一站缺三件: 带基底的嵌入, 对照树一侧的单调, 两边的值严格性. 本文只碰第一件和第三件在**下标这一层**的部分, 不碰折叠.
>
> - `V2ᶜ`: 把 [BTBOFullEb](BTBOFullEb.lagda.md) 的 `V2` 的前提 "$x\preccurlyeq y$ 且两边 `St`" 换成结构序 $x\preccurlyeq^c y$, 结论不变. **不要 `St`.** 代价是 $\preccurlyeq^c$ 必须由推导给出, 极限对极限要严格增的下标映射 (`cll`).
> - `no-V2`: 前提只留 $\preccurlyeq$ 不留 `St` 是假的. 反例是常值极限. 这是 `V2` 要 `St` 的原因, 不否定任何路线.
> - `Eb-base`, `base-id`: 加法左边的下标上映射是恒等. 这是 "带基底" 在下标这一层的形状.
> - `Fʸ-next`: 合起来, $\psi^0(\Omega_{\eta+x+1})\preccurlyeq\psi^0(\Omega_{\eta+y+1})$. **只是没有上下文的 `Ψ-emb`.** 上下文 $B$ 里的折叠单调没有做, 见 [Om1Cum](Om1Cum.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1CumIdx where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono) renaming (_+_ to _+ᴰ_)
open S using (ordᴰ)
open import OCF.Align.Level using (Ordᶜ; Ω; ψ⁰)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (τ)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.BTBOFullEb using (𝕆; module Blocks; O∘; Eb-off; Σ-lift; lt-add; inv; Inv; inl; inr; cancel<; cancel≡; add-not<)
open import OCF.Align.BTBOFullV1 using (PW₁)
open import OCF.Align.BTBOFullV3 using (Fʸ)
open Blocks 𝕆
```

## §1 结构序

`Mon M₀ d`: 严格增的下标映射. 第 $n+1$ 项一定是后继, 所以块 $n+1$ 的顶可以落在目标累加的那个 `suc` 上.

```agda
Mon : ℕ → (ℕ → ℕ) → ℕ → ℕ
Mon M₀ d zero    = M₀
Mon M₀ d (suc n) = suc (Mon M₀ d n +ᴺ d n)

infix 4 _≼ᶜ_
data _≼ᶜ_ : S.Ord₀ → S.Ord₀ → Set where
  cz  : ∀ {y} → S.zero ≼ᶜ y
  css : ∀ {x y} → x ≼ᶜ y → S.suc x ≼ᶜ S.suc y
  csr : ∀ {x y} → x ≼ᶜ y → x ≼ᶜ S.suc y
  clr : ∀ {x g} n → x ≼ᶜ g n → x ≼ᶜ S.lim g
  cll : ∀ {f g} (M₀ : ℕ) (d : ℕ → ℕ) → (∀ n → f n ≼ᶜ g (Mon M₀ d n)) → S.lim f ≼ᶜ S.lim g

≼ᶜ→≼ : ∀ {x y} → x ≼ᶜ y → tr₀ x ≼ tr₀ y
≼ᶜ→≼ cz = z≼
≼ᶜ→≼ (css d) = s≼s (≼ᶜ→≼ d)
≼ᶜ→≼ (csr d) = ≼-suc (≼ᶜ→≼ d)
≼ᶜ→≼ (clr n d) = ≼l n (≼ᶜ→≼ d)
≼ᶜ→≼ (cll M₀ d h) = l≼ (λ n → ≼l (Mon M₀ d n) (≼ᶜ→≼ (h n)))
```

## §2 `V2ᶜ`

与 `V2` 的极限子句同形. 不同只在 `eN`: `V2` 要 $f_{n+1}+1\preccurlyeq g_m$ (所以要 `St`), 这里目标块多一个 `suc`, 顶落在 `suc` 上.

```agda
V2ᶜ : ∀ {x y} → x ≼ᶜ y → Eb (ordᴰ x) (ordᴰ y)
V2ᶜ cz = Eb-zero
V2ᶜ {y = S.suc y} (css d) = Eb-suc (V2ᶜ d) (ordᴰ y) (λ p → p) B.zero
V2ᶜ (csr d) = Eb-wk (V2ᶜ d) (λ p → B.suc p)
V2ᶜ {y = S.lim g} (clr n d) = Eb-wk (Eb-off (O∘ g) n (V2ᶜ d)) (λ p → B.lim n p)
V2ᶜ {x = S.lim f} {y = S.lim g} (cll M₀ d h) = Blk.Lim (O∘ f) Bd B∞ e₀ N Nb Nm Nc fl sp
  where
  M : ℕ → ℕ
  M = Mon M₀ d
  k : ℕ → ℕ
  k n = M n +ᴺ d n
  B∞ = ordᴰ (S.lim g)
  Bd : ℕ → Ordᴰ
  Bd n = cumsum (O∘ g) (M n)
  e₀ : Eb (O∘ f 0) (Bd 0)
  e₀ = Eb-off (O∘ g) M₀ (V2ᶜ (h 0))
  eN : ∀ n → Eb (B.suc (O∘ f (suc n))) (B.suc (O∘ g (suc (k n))))
  eN n = Eb-suc (V2ᶜ (h (suc n))) (O∘ g (suc (k n))) (λ p → p) B.zero
  N : ∀ n {c} → c B.< B.suc (O∘ f (suc n)) → Ordᴰ
  N n p = cumsum (O∘ g) (k n) +ᴰ map (eN n) p
  Nb : ∀ n {c} (p : c B.< B.suc (O∘ f (suc n))) → N n p B.< Bd (suc n)
  Nb n p = B.+-mono (below (eN n) p)
  Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ B.< d₂ → N n p B.< N n q
  Nm n p q r = B.+-mono (mono (eN n) p q r)
  Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ ≡ d₂ → N n p ≡ N n q
  Nc n p q r = cong (cumsum (O∘ g) (k n) +ᴰ_) (coh (eN n) p q r)
  fl : ∀ n {x} → x B.< Bd n → ∀ {c} (p : c B.< B.suc (O∘ f (suc n))) → x B.< N n p
  fl n r p = lt-add (Σ-lift (O∘ g) (≤⇒≤′ (m≤m+n (M n) (d n))) r) _
  sp : ∀ n {x} → x B.< Bd n → x B.< B∞
  sp n r = B.lim (M n) r
```

## §3 只留 $\preccurlyeq$ 是假的

$x_0=\lim(1,1,1,\ldots)$, 值是 $1$. 累加是 $\omega$. 落不进 $1$.

```agda
x₀ y₀ : S.Ord₀
x₀ = S.lim (λ _ → S.suc S.zero)
y₀ = S.suc S.zero

x₀≼y₀ : tr₀ x₀ ≼ tr₀ y₀
x₀≼y₀ = l≼ (λ n → ≼-refl _)

no2 : ∀ {u v} → u B.< v → v B.< B.suc B.zero → ⊥
no2 () B.zero
no2 p (B.suc ())

no-V2 : ¬ (∀ x y → tr₀ x ≼ tr₀ y → Eb (ordᴰ x) (ordᴰ y))
no-V2 V = no2 (mono e p q B.zero) (below e q)
  where
  e : Eb (ordᴰ x₀) (ordᴰ y₀)
  e = V x₀ y₀ x₀≼y₀
  p : B.suc B.zero B.< ordᴰ x₀
  p = B.lim 1 (B.suc B.zero)
  q : B.suc (B.suc B.zero) B.< ordᴰ x₀
  q = B.lim 1 B.zero
```

## §4 带基底

加法左边 $\eta$ 的下标不动 (`base-id`), 右边走给定的嵌入. 比较都走 `inv` 的字面分块, 不判定值.

```agda
module Base (η : Ordᴰ) {a b : Ordᴰ} (e : Eb a b) where
  disp : ∀ {c} → Inv η a c → Ordᴰ
  disp {c} (inl q) = c
  disp (inr d r _) = η +ᴰ map e r

  m : ∀ {c} → c B.< η +ᴰ a → Ordᴰ
  m {c} p = disp (inv {η} {a} p)

  bl : ∀ {c} (p : c B.< η +ᴰ a) → m p B.< η +ᴰ b
  bl p with inv {η} {a} p
  ... | inl q = lt-add q b
  ... | inr d r _ = B.+-mono (below e r)

  mn : ∀ {c d} (p : c B.< η +ᴰ a) (q : d B.< η +ᴰ a) → c B.< d → m p B.< m q
  mn p q r with inv {η} {a} p | inv {η} {a} q
  ... | inl p′ | inl q′ = r
  ... | inl p′ | inr d t _ = lt-add p′ _
  ... | inr d t refl | inl q′ = ⊥-elim (add-not< η d (B.<-trans r q′))
  ... | inr d₁ t₁ refl | inr d₂ t₂ refl = B.+-mono (mono e t₁ t₂ (cancel< t₁ t₂ r))

  ch : ∀ {c d} (p : c B.< η +ᴰ a) (q : d B.< η +ᴰ a) → c ≡ d → m p ≡ m q
  ch p q x with inv {η} {a} p | inv {η} {a} q
  ... | inl p′ | inl q′ = x
  ... | inl p′ | inr d t ee = ⊥-elim (add-not< η d (subst (B._< _) (trans x ee) p′))
  ... | inr d t ee | inl q′ = ⊥-elim (add-not< η d (subst (B._< _) (trans (sym x) ee) q′))
  ... | inr d₁ t₁ refl | inr d₂ t₂ refl = cong (η +ᴰ_) (coh e t₁ t₂ (cancel≡ t₁ t₂ x))

  Eb-base : Eb (η +ᴰ a) (η +ᴰ b)
  Eb-base = record { map = m ; below = bl ; mono = mn ; coh = ch }

  base-id : ∀ {c} (p : c B.< η) → map Eb-base (lt-add p a) ≡ c
  base-id p with inv {η} {a} (lt-add p a)
  ... | inl q = refl
  ... | inr d r ee = ⊥-elim (add-not< η d (subst (B._< _) ee p))
```

## §5 合起来

```agda
suc-Eb : ∀ {x y} → x ≼ᶜ y → Eb (B.suc (ordᴰ x)) (B.suc (ordᴰ y))
suc-Eb {y = y} d = Eb-suc (V2ᶜ d) (ordᴰ y) (λ p → p) B.zero

next-Eb : ∀ (η : Ordᴰ) {x y} → x ≼ᶜ y → Eb (η +ᴰ B.suc (ordᴰ x)) (η +ᴰ B.suc (ordᴰ y))
next-Eb η d = Base.Eb-base η (suc-Eb d)

Fʸ-next : ∀ (η : Ordᴰ) {x y} → x ≼ᶜ y → Fʸ (τ (η +ᴰ B.suc (ordᴰ x))) ≼ Fʸ (τ (η +ᴰ B.suc (ordᴰ y)))
Fʸ-next η d = Ψ-emb (PW₁ (next-Eb η d))
```
