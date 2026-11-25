# K2′ 续做：Legal.irr 的运输能力与范围

这里直接检验作者建议的第一步。`irr` 给出分支 **LF 树** 相等；
若其余证书沿该等式运输，任意函数的子调用确实相等。
但实际的 branch-source 从两处分别投影证书，不是自动沿等式运输。
下面用一个完全合法、Only0 的闭源证明两份实际 Source 可以不相等。
这否定“先把实际 Source 证明相等再用 cong”这一充分前提，
**不否定特定 ψ 的输出一致性，也不触发某行 ψ 失败的止损**。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2cIrr where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2bBase as B
open import OCF.Align.YiDispBase using (cp-edge; e-first)
open F using (module G)

branch-tree-irr : ∀ {k c t g} → V.Legal (F.lc k c t g) →
  ∀ η e e′ → g η e ≡ g η e′
branch-tree-irr (lk , first , mono , irr , lt , lg) = irr

pack : ∀ x → C.Carry x → V.Legal x → B.Only0 x → B.Source0
pack x r l q = B.source0 (C.source x r l) q

transported-source : ∀ {x y} (p : x ≡ y) r l q →
  pack x r l q ≡ pack y
    (subst C.Carry p r) (subst V.Legal p l) (subst B.Only0 p q)
transported-source refl r l q = refl

transported-call : ∀ (ψ : B.Source0 → A.R) {x y} (p : x ≡ y) r l q →
  ψ (pack x r l q) ≡ ψ (pack y
    (subst C.Carry p r) (subst V.Legal p l) (subst B.Only0 p q))
transported-call ψ p r l q = cong ψ (transported-source p r l q)
```

## 两个确实不同的实际分支 Source

子树列为 `1, lim(const 1), lim(const 1), …`。第一步的 CP 可以取
第 0 支或第 1 支。父结点的分支树恒定；子树的 Legal 证据读取守卫的
分支号。整个父源仍满足原 irr、Reg、Carry、Legal、Only0。

```agda
unitLF : F.LF
unitLF = F.suc F.zero

sup1 : F.LF
sup1 = F.lim (λ n → unitLF)

columns : ℕ → F.LF
columns zero = unitLF
columns (suc n) = sup1

child : F.LF
child = F.lim columns

child-carry : C.Carry child
child-carry zero = tt
child-carry (suc n) = λ m → tt

child-only : B.Only0 child
child-only zero = tt
child-only (suc n) = λ m → tt

child-legal : ℕ → V.Legal child
child-legal k = step , lawful
  where
  step : ∀ n → V.CP (columns n) (columns (suc n))
  step zero = V.lim k V.self
  step (suc n) = V.self
  lawful : ∀ n → V.Legal (columns n)
  lawful zero = tt
  lawful (suc n) = (λ m → V.self) , (λ m → tt)

mark : ∀ η → F.Gd F.zero A.one η → ℕ
mark η (inj₁ e , l) = zero
mark (G.suc η) (inj₂ p , l) = zero
mark (G.lim f) (inj₂ (n , p) , l) = n
mark (G.lc () c t g) e
mark (G.em () a) e
mark G.zero (inj₂ () , l)
mark G.top (inj₂ () , l)

parent : F.LF
parent = F.lc F.zero A.one child (λ η e → child)

parent-carry : C.Carry parent
parent-carry =
  ((cp-edge (V.lim 0 V.self) e-first , tt , C.forget child-carry ,
    (λ η e → C.forget child-carry)) ,
   tt , child-carry , (λ η e b → child-carry))

parent-legal : V.Legal parent
parent-legal = tt , (λ η e → V.self) , (λ η e η′ e′ d → V.self) ,
  (λ η e e′ → refl) , child-legal 0 , (λ η e → child-legal (mark η e))

parent-only : B.Only0 parent
parent-only = child-only , (λ η e → child-only)

parent-source : B.Source0
parent-source = pack parent parent-carry parent-legal parent-only

coordinate : A.R
coordinate = G.lim (λ n → A.one)

coordinate-B : C.LglB F.zero coordinate
coordinate-B = ((λ n → inj₁ refl) , (λ n → tt)) , (λ n → tt)

point : ℕ → C.PointB F.zero A.one
point n = C.point coordinate (inj₂ (n , inj₁ refl) , proj₁ coordinate-B) coordinate-B

actual : ℕ → B.Source0
actual n = B.branch0 parent-carry parent-legal parent-only (point n)

inspect-path : ∀ {a b} → V.CP a b → ℕ
inspect-path V.self = zero
inspect-path (V.suc p) = zero
inspect-path (V.lim n p) = n
inspect-path (V.fst p) = zero

inspect : C.Source → ℕ
inspect (C.source F.zero r l) = zero
inspect (C.source (F.suc x) r l) = zero
inspect (C.source (F.lim f) r (st , l)) = inspect-path (st zero)
inspect (C.source (F.lc k c t g) r l) = zero

inspect-actual : ∀ n → inspect (B.original (actual n)) ≡ n
inspect-actual n = refl

zero-not-one : zero ≡ suc zero → ⊥
zero-not-one ()

actual-originals-differ :
  B.original (actual zero) ≡ B.original (actual (suc zero)) → ⊥
actual-originals-differ p = zero-not-one (cong inspect p)

actual-sources-differ : actual zero ≡ actual (suc zero) → ⊥
actual-sources-differ p = actual-originals-differ (cong B.original p)

-- 两份分支的底层树则字面相同，irr 实际应用也是 refl。
actual-trees-same : C.term (B.original (actual zero)) ≡
  C.term (B.original (actual (suc zero)))
actual-trees-same = branch-tree-irr parent-legal coordinate
  (C.guard (point zero)) (C.guard (point (suc zero)))
```

## 原 irr、输出合法和正性仍不蕴涵任意子算子的证据不依赖性

`sensitive` 是明确的反面对照，读取证书，不满足 ψ 的四行。
因此本定理不否定所求 ψ；它说明证明中不能省去关于这个特定 ψ 的一致性引理。

```agda
numeral : ℕ → A.R
numeral zero = G.zero
numeral (suc n) = G.suc (numeral n)

numeral-legal : ∀ n → F.Lgl F.zero (numeral n)
numeral-legal zero = tt
numeral-legal (suc n) = numeral-legal n

numeral-zero : ∀ n → F.Cp F.zero G.zero (numeral n)
numeral-zero zero = inj₁ refl
numeral-zero (suc n) = inj₂ (numeral-zero n)

sensitive : B.Source0 → A.R
sensitive s = numeral (suc (inspect (B.original s)))

sensitive-B : ∀ s → C.LglB F.zero (sensitive s)
sensitive-B s = numeral-legal _ , C.raw0-nested _

sensitive-positive : ∀ s → F.Dn F.zero G.zero (sensitive s)
sensitive-positive s = numeral-zero _

sensitive-not-irr : sensitive (actual zero) ≡ sensitive (actual (suc zero)) → ⊥
sensitive-not-irr ()
```

本篇所有反面前提都有上面的闭实例；没有假定矛盾的完整折叠记录。
结论没有把“证书不同”误写成“正确 ψ 的输出不同”。

## 极限行要求的是整个输出函数的相等

这两条不是外延公理。第一条是构造子反演；第二条是完整目标记录的
必要推论，不给这个未实填记录冒充可满足性证明。
它们把尚缺的陈述写清：逐支相等不能直接替换成该函数相等。
本篇既没有证明后者不可得，也没有证明只能靠外延原理得到它。

```agda
lim-body : A.R → ℕ → A.R
lim-body (G.lim f) = f
lim-body _ = λ n → G.zero

lim-equality-reflects : ∀ {f g : ℕ → A.R} →
  G.lim f ≡ G.lim g → f ≡ g
lim-equality-reflects p = cong lim-body p

lim-function-equality-required : (d : B.FoldRows0) → ∀ (f : ℕ → F.LF)
  (r r′ : ∀ n → C.Carry (f n))
  (st st′ : ∀ n → V.CP (f n) (f (suc n)))
  (l l′ : ∀ n → V.Legal (f n)) (q q′ : ∀ n → B.Only0 (f n)) →
  (λ n → B.FoldRows0.ψ d (pack (f n) (r n) (l n) (q n))) ≡
  (λ n → B.FoldRows0.ψ d (pack (f n) (r′ n) (l′ n) (q′ n)))
lim-function-equality-required d f r r′ st st′ l l′ q q′ =
  lim-equality-reflects
    (trans (sym (B.FoldRows0.lim-row d f r st l q))
      (trans (B.certificate-coherence-required d (F.lim f) r r′
        (st , l) (st′ , l′) q q′)
        (B.FoldRows0.lim-row d f r′ st′ l′ q′)))
```

## 第二个建议的局部检验：确实只读树时不需要函数外延

任意只读 LF 的 run 都满足下面三条；证书消去在这里是定义性的，
不是从逐支相等拼出函数相等。这个结果**没有构造满足 gt 行的 run**。
例如恒 1 的 run 有实例，但不满足后继行，不能作为完整 ψ。

```agda
module TreeOnly (run : F.LF → A.R) where

  eval : B.Source0 → A.R
  eval s = run (C.term (B.original s))

  certificate-coherence : ∀ x r r′ l l′ q q′ →
    eval (pack x r l q) ≡ eval (pack x r′ l′ q′)
  certificate-coherence x r r′ l l′ q q′ = refl

  lim-function-coherence : ∀ (f : ℕ → F.LF)
    (r r′ : ∀ n → C.Carry (f n))
    (l l′ : ∀ n → V.Legal (f n)) (q q′ : ∀ n → B.Only0 (f n)) →
    (λ n → eval (pack (f n) (r n) (l n) (q n))) ≡
    (λ n → eval (pack (f n) (r′ n) (l′ n) (q′ n)))
  lim-function-coherence f r r′ l l′ q q′ = refl

  branch-call-irr : ∀ {c t g}
    (r : C.Carry (F.lc F.zero c t g)) (l : V.Legal (F.lc F.zero c t g))
    (q : B.Only0 (F.lc F.zero c t g)) η e e′ b b′ →
    eval (B.branch0 r l q (C.point η e b)) ≡
    eval (B.branch0 r l q (C.point η e′ b′))
  branch-call-irr r l q η e e′ b b′ = cong run (branch-tree-irr l η e e′)

tree-only-instance : ∀ x r r′ l l′ q q′ →
  TreeOnly.eval (λ _ → A.one) (pack x r l q) ≡
  TreeOnly.eval (λ _ → A.one) (pack x r′ l′ q′)
tree-only-instance = TreeOnly.certificate-coherence (λ _ → A.one)
```

直接在所有裸 LF 的 lc 行运行同一 gt 程序会另外要求裸下界有启动守卫；
旧 YiK2Stop.no-coordinate 的坏下界已否定该要求。它在 Carry 域外，
所以也不否定本轮 Source0 域上的 ψ，更不排除其他只读树的实现。
