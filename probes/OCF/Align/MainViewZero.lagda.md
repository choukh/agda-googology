# 主线数据类型上的 View (二): `HtFeedTree` 的第 0 层, 无条件

> 不含记号. 入口 [MainView](MainView.lagda.md). 主线第 0 层的树 `HtFeedTree.D₀ W = D hz W`, 值 `HtFeedTree.sum azero` (主线闭项 `HtFeedClosed.TΛ` 就是它), 目标 `A`, 步进 `_⊲_` (字面第一位置). 用 [MainViewGen](MainViewGen.lagda.md) 的骨架实例化: 读法 `Sm q b y = sum b y`, 九条方程除 `e-nl` 外都是 `refl`; 层 `hz` 没有节点 (`StH W k hz` 空, `NZ hz = ⊥`), 两个段是空函数.
>
> - `view₀ᴴ`: 一切第 0 层主线树都有布劳威尔树的 View, 值一致对 `sum azero`. **无条件.**
> - `wf₀ᴴ`, `view₀ᴴᵂ`: 部分良基, 度量是值, 关系是 `A` 的直接子树 `SubA` (同 `BrwWfZero`). **无条件.**
> - `rd₀≈ᴴ`: 经 View 读出的 `A` 与 `sum azero` 互相 $\le$; `rd₀≅ᴴ`: 逐点字面相等.
> - `fgh₀≡ᴴ`: 经 View 算的 FGH 与 `sum azero x` 上的 FGH 逐点相等. `fgh-TΛ`: 对主线闭项 `HtFeedClosed.TΛ Λ lΛ` 的第 0 层树 `ΨΩ`, 一切合法 $\Lambda$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainViewZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtFeedTree using (H; hz; LgH; StH; Vs; NZ; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (TΛ; module At)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewZero using (Sig₀)
open import OCF.Align.BrwWfDef using (Obj; Part; p-s; p-l; p-Ω; _◁_; BrwViewᵂ)
open import OCF.Align.BrwWfRead using (rec′; module Read; Cong; module ReadOk)
open import OCF.Align.BrwWfZero using (SubA; sa-s; sa-l; SubA-wf; _≅_; z≅; s≅; l≅; ≅-trans; ≡→≅; fghA; iter; iter-cong; fgh-≅)
open import OCF.Align.MainViewGen using (ps; module Skel)
```

## §1 小件

```agda
open Sig Sig₀ using (_≈_)

≈r : ∀ a → a ≈ a
≈r a = ≤-refl a , ≤-refl a

lim≡ : ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → alim f ≈ alim g
lim≡ f g e = l≤ (λ n → ≤l n (subst (λ a → f n ≤ a) (e n) (≤-refl (f n)))) ,
             l≤ (λ n → ≤l n (subst (λ a → g n ≤ a) (sym (e n)) (≤-refl (g n))))

ps-pt : ∀ {W₀} b (d : ℕ → D₀ W₀) n → sum b (ps d n) ≡ pt b d n
ps-pt b d zero = refl
ps-pt b d (suc n) = cong (λ a → sum a (d n)) (ps-pt b d n)
```

## §2 实例

```agda
module _ (W : A) where
  open Skel {Nd = λ W k → StH W k hz} {Vv = λ R → Vs hz R} {Zz = NZ hz}
            Sig₀ (λ _ → W) (λ x → sum azero x) (λ _ → ⊤) (λ q b y → sum b y) ≈r
            (λ q b → refl) (λ q b → refl) (λ q b y z → refl) (λ r q b y → refl) (λ x q y → refl) (λ x → refl) (≈r azero)
            (λ x q d → lim≡ _ _ (λ n → sym (ps-pt (sum azero x) d n))) (λ q b y → sum-fst b y)
            tt (λ _ _ → tt) (λ _ → tt) (λ _ → tt) (λ _ _ → tt) (λ _ → tt) (λ _ → tt)
    public

  sgi₀ : SegI
  sgi₀ x hx vx q () u hy

  sgk₀ : SegK
  sgk₀ x hx vx q () u hy

  open WithSeg sgi₀ sgk₀ public

  view₀ᴴ : BrwView Sig₀ X (λ x → sum azero x) Lgx
  view₀ᴴ = view

  R-l₀ : ∀ (x : D₀ W) {W₀} (q : W₀ ⊲ W) (d : ℕ → D₀ W₀) n → SubA (sum azero (x ⨾ nw q (ps d n))) (sum (sum azero x) (nl d))
  R-l₀ x q d n = subst (λ a → SubA a (alim (pt (sum azero x) d))) (sym (ps-pt (sum azero x) d n)) (sa-l n)

  open Dec A SubA SubA-wf (λ b → b) (λ b → sa-s) R-l₀ (λ { x hx vx q () }) (λ { x hx vx q () })
    public

  wf₀ᴴ : WellFounded _◁ᴳ_
  wf₀ᴴ = wf

  view₀ᴴᵂ : BrwViewᵂ Sig₀ X (λ x → sum azero x) Lgx
  view₀ᴴᵂ = viewᵂ
```

## §3 读出 `A`: 值一致与字面相等

```agda
  Ob₀ : Set
  Ob₀ = Obj Sig₀ X (λ x → sum azero x) Lgx

  vo₀ : Ob₀ → A
  vo₀ (_ , x , _) = sum azero x

  Cong₀ : Cong view₀ᴴᵂ
  Cong₀ = record { tr = ≤-trans ; bs-m = s≤ ; bl-m = λ h → l≤ (λ n → ≤l n (h n)) ; bΩ-m = λ () }

  open Read view₀ᴴᵂ (λ c → tt) using (step; rd′; rd)

  rd₀≈ᴴ : ∀ o → (rd o ≤ vo₀ o) × (vo₀ o ≤ rd o)
  rd₀≈ᴴ = ReadOk.rd≈ view₀ᴴᵂ (λ c → tt) Cong₀

  Lit : ∀ {v} → V tt v → A → Set
  Lit w a = ∀ (r : ∀ {o} → Pt w o → A) → (∀ {o} (p : Pt w o) → r p ≅ vo₀ o) → step w r ≅ a

  lit : ∀ {W₀} (x : D₀ W) (vx : V tt (sum azero x)) (q : W₀ ⊲ W) (y : D₀ W₀) →
        Lit vx (sum azero x) → Lit (vw x tt vx q y tt) (sum (sum azero x) y)
  lit x vx q n0 h = h
  lit x vx q n1 h r e = s≅ (e p-s)
  lit x vx q (y₁ ⨾ y₂) h = lit (x ⨾ nw q y₁) (vw x tt vx q y₁ tt) q y₂ (lit x vx q y₁ h)
  lit x vx q (nl d) h r e = l≅ (λ n → ≅-trans (e (p-l n)) (≡→≅ (ps-pt (sum azero x) d n)))
  lit x vx q (ni () u) h
  lit x vx q (nκ () u) h
  lit x vx q (nw p y) h = lit x vx (C.⊲-tr p q) y h

  rd₀≅′ : ∀ o (a : Acc _◁ᴳ_ o) → rd′ o a ≅ vo₀ o
  rd₀≅′ (tt , x , tt) (acc rs) = lit n0 (vz (≈r azero)) C.self x (λ r e → z≅) _ (λ p → rd₀≅′ _ (rs p))

  rd₀≅ᴴ : ∀ o → rd o ≅ vo₀ o
  rd₀≅ᴴ o = rd₀≅′ o (wf₀ᴴ o)
```

## §4 经 View 算的 FGH

```agda
  fstep : ∀ {v} (w : V tt v) → (∀ {o} → Pt w o → ℕ → ℕ) → ℕ → ℕ
  fstep (vz _) r n = suc n
  fstep (vs y ly _) r n = iter (r p-s) n n
  fstep (vl f lf _ _) r n = r (p-l n) n
  fstep (vΩ () g lg _) r n

  fgh₀′ : ∀ o → Acc _◁ᴳ_ o → ℕ → ℕ
  fgh₀′ = rec′ view₀ᴴᵂ (λ _ → ℕ → ℕ) (λ x lx r → fstep (BrwView.view view₀ᴴ x lx) r)

  fgh₀ᴴ : Ob₀ → ℕ → ℕ
  fgh₀ᴴ o = fgh₀′ o (wf₀ᴴ o)

  fstep≡ : ∀ {v} (w : V tt v) (r : ∀ {o} → Pt w o → ℕ → ℕ) (r′ : ∀ {o} → Pt w o → A) →
           (∀ {o} (p : Pt w o) n → r p n ≡ fghA (r′ p) n) → ∀ n → fstep w r n ≡ fghA (step w r′) n
  fstep≡ (vz _) r r′ e n = refl
  fstep≡ (vs y ly _) r r′ e n = iter-cong (e p-s) n n
  fstep≡ (vl f lf _ _) r r′ e n = e (p-l n) n
  fstep≡ (vΩ () g lg _) r r′ e n

  fgh-rd′ : ∀ o (a : Acc _◁ᴳ_ o) n → fgh₀′ o a n ≡ fghA (rd′ o a) n
  fgh-rd′ (tt , x , tt) (acc rs) = fstep≡ (BrwView.view view₀ᴴ x tt) _ _ (λ p → fgh-rd′ _ (rs p))

  fgh₀≡ᴴ : ∀ (x : D₀ W) n → fgh₀ᴴ (tt , x , tt) n ≡ fghA (sum azero x) n
  fgh₀≡ᴴ x n = trans (fgh-rd′ (tt , x , tt) (wf₀ᴴ _) n) (fgh-≅ (rd₀≅ᴴ (tt , x , tt)) n)
```

## §5 主线闭项

`HtFeedClosed.TΛ Λ lΛ = sum azero ΨΩ`, $\Psi\Omega$ 是第 0 层的树. 经 View 算的 FGH 就是主线闭项上的 FGH, 对一切合法的 $\Lambda$.

```agda
fgh-TΛ : ∀ Λ (lΛ : LgH Λ) n → fgh₀ᴴ (asuc azero) (tt , At.ΨΩ Λ lΛ , tt) n ≡ fghA (TΛ Λ lΛ) n
fgh-TΛ Λ lΛ n = fgh₀≡ᴴ (asuc azero) (At.ΨΩ Λ lΛ) n
```

## §6 有限测试

下面两条由 `refl` 检查, 是**有限测试**, 不是证明.

```agda
ωd : D₀ azero
ωd = nl (λ _ → n1)

test-ω : fgh₀ᴴ azero (tt , ωd , tt) 2 ≡ 8
test-ω = refl

test-ω+1 : fgh₀ᴴ azero (tt , ωd ⨾ n1 , tt) 1 ≡ 2
test-ω+1 = refl
```
