# 沿 View 递归 (四): 第 0 层的差树, 无条件

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 第 0 层差树的 View `view₀` ([BrwViewZero](BrwViewZero.lagda.md)) 的部分是前缀 $x$ (后继) 与部分和 $x ⨾ (d_0⨾\dots⨾d_{n-1})$ ($\mathbb N$-极限), 都不是字面子项. 度量取值 `sum azero` (第 0 层布劳威尔树 `A`), 关系取 `A` 的**直接子树** `SubA`: 部分的值字面地是整体的值的直接子树 (只有 $\mathbb N$-极限一处要 `ps-pt` 的 $\equiv$). 所以:
>
> - `wf₀`: 部分良基, **无条件定理**; `view₀ᵂ : BrwViewᵂ`.
> - `rd₀≈`: 经 View 读出的 `A` 与 `sum azero` 互相 $\le$ (一般的 `rd≈` 的实例).
> - `rd₀≅`: 更强, 读出的树与 `sum azero x` **逐点字面相等** (`_≅_`: 结构相同, 极限逐项 $\equiv$). 这要看 `vw` 的构造 (它在第 0 层是字面的), 不是记录给的.
> - `fgh₀`: 经 View 算的快速增长层级 (零 $n+1$, 后继迭代 $n$ 次, 极限取第 $n$ 个部分). `fgh₀≡`: 它等于 `sum azero x` 上的 FGH, 逐点 $\equiv$. FGH 不在 $\approx$ 下不变, 所以这一条要 `rd₀≅`, 不能只用 `rd₀≈`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewZero using (Sig₀; X₀; val₀; Lgl₀; V₀; view₀; vw; ps; ps-pt; ≈r)
open import OCF.Align.BrwWfDef
open import OCF.Align.BrwWfRead
```

## §1 `A` 的直接子树

```agda
data SubA : A → A → Set where
  sa-s : ∀ {a} → SubA a (asuc a)
  sa-l : ∀ {f} n → SubA (f n) (alim f)

SubA-wf : WellFounded SubA
SubA-wf azero = acc (λ ())
SubA-wf (asuc a) = acc (λ { sa-s → SubA-wf a })
SubA-wf (alim f) = acc (λ { (sa-l n) → SubA-wf (f n) })
```

## §2 部分的值是直接子树

`dec₀`: 对 `vw` 的第二个参数 $y$ 归纳, 与 `vw` 同形. 前缀的 View $vx$ 的部分已经满足, 则整体的部分也满足.

```agda
module _ (W : A) where
  Ob₀ : Set
  Ob₀ = Obj Sig₀ (X₀ W) (val₀ W) (Lgl₀ W)

  vo₀ : Ob₀ → A
  vo₀ (_ , x , _) = sum azero x

  Pt₀ : ∀ {v} → V₀ W v → Ob₀ → Set
  Pt₀ = Part Sig₀ (X₀ W) (val₀ W) (Lgl₀ W)

  dec₀ : ∀ {W₀} (x : D azero W) (vx : V₀ W (sum azero x)) (q : W₀ ⊲ W) (y : D azero W₀) →
         (∀ {o} → Pt₀ vx o → SubA (vo₀ o) (sum azero x)) →
         ∀ {o} → Pt₀ (vw W x vx q y) o → SubA (vo₀ o) (sum (sum azero x) y)
  dec₀ x vx q n0 h p = h p
  dec₀ x vx q n1 h p-s = sa-s
  dec₀ x vx q (y₁ ⨾ y₂) h p = dec₀ (x ⨾ nw q y₁) (vw W x vx q y₁) q y₂ (dec₀ x vx q y₁ h) p
  dec₀ x vx q (nl d) h (p-l n) = subst (λ a → SubA a (alim (pt (sum azero x) d))) (sym (ps-pt W (sum azero x) d n)) (sa-l n)
  dec₀ x vx q (ni () u) h p
  dec₀ x vx q (nκ () u) h p
  dec₀ x vx q (nw r y) h p = dec₀ x vx (C.⊲-tr r q) y h p

  _◁₀_ : Ob₀ → Ob₀ → Set
  _◁₀_ = _◁_ Sig₀ (X₀ W) (val₀ W) (Lgl₀ W) (view₀ W)

  dec-top₀ : ∀ {o o′} → o′ ◁₀ o → SubA (vo₀ o′) (vo₀ o)
  dec-top₀ {_ , x , _} p = dec₀ n0 (vz (≈r W azero)) C.self x (λ ()) p

  wf₀ : WellFounded _◁₀_
  wf₀ = measure _◁₀_ SubA vo₀ SubA-wf dec-top₀

  view₀ᵂ : BrwViewᵂ Sig₀ (X₀ W) (val₀ W) (Lgl₀ W)
  view₀ᵂ = record { bv = view₀ W ; wf = wf₀ }
```

## §3 经 View 读出 `A`: 值一致

```agda
  allC₀ : ∀ {i} {k : Sig.Kd Sig₀ i} (c : Sig.Cd Sig₀ k) → Sig.LgC Sig₀ c
  allC₀ c = tt

  Cong₀ : Cong view₀ᵂ
  Cong₀ = record { tr = ≤-trans ; bs-m = s≤ ; bl-m = λ h → l≤ (λ n → ≤l n (h n)) ; bΩ-m = λ () }

  open Read view₀ᵂ allC₀ using (step; rd′; rd) public

  rd₀≈ : ∀ o → (rd o ≤ vo₀ o) Data.Product.× (vo₀ o ≤ rd o)
  rd₀≈ = ReadOk.rd≈ view₀ᵂ allC₀ Cong₀
```

## §4 字面相等

`_≅_`: 结构相同, 极限逐项 $\equiv$ (不要 `Funext`). `lit`: 对 `vw` 同形归纳; 前缀的 View 满足 "一切逐点对的读数给出 $\cong$", 则整体也满足.

```agda
infix 4 _≅_
data _≅_ : A → A → Set where
  z≅ : azero ≅ azero
  s≅ : ∀ {a b} → a ≅ b → asuc a ≅ asuc b
  l≅ : ∀ {f g} → (∀ n → f n ≅ g n) → alim f ≅ alim g

≅-refl : ∀ a → a ≅ a
≅-refl azero = z≅
≅-refl (asuc a) = s≅ (≅-refl a)
≅-refl (alim f) = l≅ (λ n → ≅-refl (f n))

≅-trans : ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
≅-trans z≅ z≅ = z≅
≅-trans (s≅ p) (s≅ q) = s≅ (≅-trans p q)
≅-trans (l≅ p) (l≅ q) = l≅ (λ n → ≅-trans (p n) (q n))

≡→≅ : ∀ {a b} → a ≡ b → a ≅ b
≡→≅ {a} refl = ≅-refl a

module _ (W : A) where
  Lit : ∀ {v} → V₀ W v → A → Set
  Lit w a = ∀ (r : ∀ {o} → Pt₀ W w o → A) → (∀ {o} (p : Pt₀ W w o) → r p ≅ vo₀ W o) → step W w r ≅ a

  lit : ∀ {W₀} (x : D azero W) (vx : V₀ W (sum azero x)) (q : W₀ ⊲ W) (y : D azero W₀) →
        Lit vx (sum azero x) → Lit (vw W x vx q y) (sum (sum azero x) y)
  lit x vx q n0 h = h
  lit x vx q n1 h r e = s≅ (e p-s)
  lit x vx q (y₁ ⨾ y₂) h = lit (x ⨾ nw q y₁) (vw W x vx q y₁) q y₂ (lit x vx q y₁ h)
  lit x vx q (nl d) h r e = l≅ (λ n → ≅-trans (e (p-l n)) (≡→≅ (ps-pt W (sum azero x) d n)))
  lit x vx q (ni () u) h
  lit x vx q (nκ () u) h
  lit x vx q (nw p y) h = lit x vx (C.⊲-tr p q) y h

  rd₀≅′ : ∀ o (a : Acc (_◁₀_ W) o) → rd′ W o a ≅ vo₀ W o
  rd₀≅′ (tt , x , tt) (acc rs) = lit n0 (vz (≈r W azero)) C.self x (λ r e → z≅) _ (λ p → rd₀≅′ _ (rs p))

  rd₀≅ : ∀ o → rd W o ≅ vo₀ W o
  rd₀≅ o = rd₀≅′ o (wf₀ W o)
```

## §5 经 View 算的 FGH

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f zero m = m
iter f (suc k) m = f (iter f k m)

fghA : A → ℕ → ℕ
fghA azero n = suc n
fghA (asuc a) n = iter (fghA a) n n
fghA (alim f) n = fghA (f n) n

iter-cong : ∀ {f g : ℕ → ℕ} → (∀ n → f n ≡ g n) → ∀ k m → iter f k m ≡ iter g k m
iter-cong e zero m = refl
iter-cong {f} {g} e (suc k) m = trans (cong f (iter-cong e k m)) (e _)

fgh-≅ : ∀ {a b} → a ≅ b → ∀ n → fghA a n ≡ fghA b n
fgh-≅ z≅ n = refl
fgh-≅ (s≅ p) n = iter-cong (fgh-≅ p) n n
fgh-≅ (l≅ p) n = fgh-≅ (p n) n

module _ (W : A) where
  F : Ob₀ W → Set
  F _ = ℕ → ℕ

  fstep : ∀ {v} (w : V₀ W v) → (∀ {o} → Pt₀ W w o → ℕ → ℕ) → ℕ → ℕ
  fstep (vz _) r n = suc n
  fstep (vs y ly _) r n = iter (r p-s) n n
  fstep (vl f lf _ _) r n = r (p-l n) n
  fstep (vΩ () g lg _) r n

  fgh₀′ : ∀ o → Acc (_◁₀_ W) o → ℕ → ℕ
  fgh₀′ = rec′ (view₀ᵂ W) F (λ x lx r → fstep (BrwView.view (view₀ W) x lx) r)

  fgh₀ : Ob₀ W → ℕ → ℕ
  fgh₀ o = fgh₀′ o (wf₀ W o)

  -- 经 View 的 FGH 就是读出的树上的 FGH
  fstep≡ : ∀ {v} (w : V₀ W v) (r : ∀ {o} → Pt₀ W w o → ℕ → ℕ) (r′ : ∀ {o} → Pt₀ W w o → A) →
           (∀ {o} (p : Pt₀ W w o) n → r p n ≡ fghA (r′ p) n) → ∀ n → fstep w r n ≡ fghA (step W w r′) n
  fstep≡ (vz _) r r′ e n = refl
  fstep≡ (vs y ly _) r r′ e n = iter-cong (e p-s) n n
  fstep≡ (vl f lf _ _) r r′ e n = e (p-l n) n
  fstep≡ (vΩ () g lg _) r r′ e n

  fgh-rd′ : ∀ o (a : Acc (_◁₀_ W) o) n → fgh₀′ o a n ≡ fghA (rd′ W o a) n
  fgh-rd′ (tt , x , tt) (acc rs) = fstep≡ (BrwView.view (view₀ W) x tt) _ _ (λ p → fgh-rd′ _ (rs p))

  fgh₀≡ : ∀ (x : D azero W) n → fgh₀ (tt , x , tt) n ≡ fghA (sum azero x) n
  fgh₀≡ x n = trans (fgh-rd′ (tt , x , tt) (wf₀ W _) n) (fgh-≅ (rd₀≅ W (tt , x , tt)) n)
```

**读法.** `fgh₀` 只经 View 递归 (零、后继、$\mathbb N$-极限三种读法, 部分是前缀与部分和), 不看 `sum`; `fgh₀≡` 说它与 `sum azero x` 上的 FGH 逐点相等. 有限测试见 §6.

## §6 有限测试

$\omega=$ `nl (λ _ → n1)` (部分和 $0,1,2,\dots$). 下面几条由 `refl` 检查, 是**有限测试**, 不是证明.

```agda
ωd : D azero azero
ωd = nl (λ _ → n1)

test-ω : fgh₀ azero (tt , ωd , tt) 2 ≡ 8
test-ω = refl

test-ω+1 : fgh₀ azero (tt , ωd ⨾ n1 , tt) 1 ≡ 2
test-ω+1 = refl
```
