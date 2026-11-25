# 用实际塔的良序公理同时判定 EBO 两个方向

第四层。记 tₙ、Y、R 分别为 W4 的第 n 座完整塔、整树与原 EBO 的值。W4 理论逐条加入各座塔的地址良序性，其 PTO 为 P = supₙ ε⁺(tₙ)，恰是大于等于 Y 的最小 ε 数。Agda 给出 P、Y 相对 R 的双向比较，理论的定值是文末的经典纸面证明。

```agda
{-# OPTIONS --safe --without-K #-}
module Survey.W4PTOTowerTheory where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
import Data.Bool.Base
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-suc; ≼-refl; ≼-trans; ≼l; l≼; s≼s)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import OCF.Lean.YiRVLevel using (LEM)
open import WVOne using (T₀)
import B12EboRows as Rows
import B17CellNext as Next
import B17ValueDich as Cmp
import B19IdealArithmetic as Ar
import B19IdealPowers as Pow
import B22MovingIndex as E
import B22TowerCut as Mono
import B26Names as Ref
import B26PActual as W
import B26PSums as Actual
import Survey.EboPTOSegments as Seg
import Survey.W4PTOAddresses as Address

module Scale (Y R : T₀) (t : ℕ → T₀)
  (assemble : ∀ q → (∀ n → t n ≼ q) → Y ≼ q)
  (proper : ∀ n → L.suc (t n) ≼ Y)
  (stable : ∀ x → L.suc x ≼ R → L.suc (E.above x) ≼ R)
  (strip : LEM → R ≼ E.above Y → R ≼ Y) where

  P : T₀
  P = L.lim (λ n → E.above (t n))
  covers : Y ≼ P
  covers = assemble P λ n → ≼l {f = λ i → E.above (t i)} n (≼-trans {a = t n} {b = L.suc (t n)} {c = E.above (t n)}
    (≼-suc (≼-refl (t n))) (E.strict (t n)))
  ceiling : P ≼ E.above Y
  ceiling = l≼ λ n → Mono.advance {t n} {Y} (≼-trans {b = L.suc (t n)} (≼-suc (≼-refl (t n))) (proper n))

  fixed : E.step P ≈ᵛ P
  fixed = l≼ (λ n → ≼l {f = λ i → E.above (t i)} n (proj₁ (E.fix (t n)))) , Ar.up P
  least-fixed : ∀ q → Y ≼ q → E.step q ≼ q → P ≼ q
  least-fixed q h closed = l≼ λ n → E.least (t n) q (≼-trans {b = Y} (proper n) h) closed
  exact-if-fixed : (E.step Y ≼ Y → P ≼ Y) × (P ≼ Y → E.step Y ≼ Y)
  exact-if-fixed = least-fixed Y (≼-refl Y) , λ cap → ≼-trans {b = E.step P}
    (Pow.expo Pow.omega-pos covers) (≼-trans {b = P} (proj₁ fixed) cap)

  upper : Y ≼ R → P ≼ R
  upper h = l≼ λ n → ≼-trans {a = E.above (t n)} {b = L.suc (E.above (t n))} {c = R} (≼-suc (≼-refl (E.above (t n))))
    (stable (t n) (≼-trans {b = Y} (proper n) h))
  upper-back : P ≼ R → Y ≼ R
  upper-back h = ≼-trans {b = P} covers h
  lower : R ≼ Y → R ≼ P
  lower h = ≼-trans {b = Y} h covers
  lower-back : LEM → R ≼ P → R ≼ Y
  lower-back lem h = strip lem (≼-trans {b = P} h ceiling)
  same : LEM → ((Y ≈ᵛ R → P ≈ᵛ R) × (P ≈ᵛ R → Y ≈ᵛ R))
  same lem = (λ (hi , lo) → upper hi , lower lo) , (λ (hi , lo) → upper-back hi , lower-back lem lo)

  strict-below : L.suc Y ≼ R → L.suc P ≼ R
  strict-below h = ≼-trans {b = L.suc (E.above Y)} (s≼s ceiling) (stable Y h)
  strict-above-back : LEM → L.suc R ≼ P → L.suc R ≼ Y
  strict-above-back lem h with Cmp.Classical.compare lem Y R
  ... | inj₁ cap = ⊥-elim (s≼-irrefl R (≼-trans {b = P} h (upper cap)))
  ... | inj₂ high = high

tower-domain : ℕ → Address.Node → Data.Bool.Base.Bool
tower-domain n = Address.member (Rows.child n)
module ActualScale = Scale W.Y Ref.E Rows.child
  (λ q → Next.assemble {q = q}) Actual.child-in
  (λ x → Seg.Reference.stable {x}) (λ lem → Seg.recover lem W.Y)
open ActualScale public
```

**经典纸面证明。** 令 Aₙ 为 `tower-domain n` 上按 `Address.less` 排序的线序；由地址定理，它们统一递归且 otp(Aₙ)=ω^tₙ。取 Tᵂ = ACA₀ + {WO(Aₙ) ∣ n∈ℕ}。对前 n+1 条公理取带标签的有限序数和 Dₙ=A₀+⋯+Aₙ。在 ACA₀ 内，有限族良序当且仅当其和良序：各分量是子序，反过来假想降链的有限分量号最终恒定。若使用附首次验收记录的原始递归表示，和序直接使用原记录和分量号。这一步不需要在弱理论里比较各塔的序型。

在外部，tₙ<tₙ₊₁，因此有限和的序型正是 ω^tₙ。每份 Tᵂ 证明只使用有限条附加公理。单良序公理的 PTO 公式遂给出 |Tᵂ|=supₙ ε⁺(ω^tₙ)=P。最后一个等号使用 tₙ≤ω^tₙ<ε⁺(tₙ)。非空 ε 数列的上确界仍为 ε 数。若 Y≤q 且 ω^q=q，每个 tₙ 都严格低于 q，故 ε⁺(tₙ)≤q。于是 P 是大于等于 Y 的最小 ε 数，特别有 |Tᵂ|=Y 当且仅当 ω^Y=Y。这里的最小性已由 `fixed`、`least-fixed` 验证。原记号理论 Tᴿ 已有 |Tᴿ|=R。综合上述比较，**|Tᵂ|=|Tᴿ| 当且仅当 Y=R**，两个弱不等式也分别等价。这里没有假设 Y 本身已经对 ε⁺ 封闭。[地址域与序型](W4PTOAddresses.lagda.md) · [原记号初段理论](EboPTOSegments.lagda.md) · [单良序公理公式，Aguilera–Pakhomov 定理 21 的证明](https://backoffice.biblio.ugent.be/download/01H3WWR51BSZ686FK04YGPVW1Y/01H3WWSW11Q004X3M39D6NSW9R#page=18)

由此可逐公理做两向转换。在 Tᵂ 中逐条导出原记号良序公理可得下界，在 Tᴿ 中逐条导出 WO(Aₙ) 可得上界。每份转换允许加入独立证真的算术辅助句；有限合取仍是真 Σ¹₁ 句，Kreisel 定理保持接收理论的 PTO。此处尚未构造覆盖所有 n 的转换。[Walsh 定理 1.2](https://arxiv.org/pdf/2209.09765#page=2)

也可直接比较两条反射原则。记 RFN(T) 为“每个 T 可证的 Π¹₁ 句子都真”，这是 ACA₀ 语言的一条句子。两套公理都可以递归枚举，所加的每个序在标准模型中良序，所以两理论均为算术可定义、Π¹₁ 可靠的 ACA₀ 扩张。由 Walsh 的定理 1.10 及上面的比较得到

$$
Y=R\quad\Longleftrightarrow\quad
\text{存在真 }\Sigma^1_1\text{ 句 }\sigma,\quad
\mathsf{ACA}_0+\sigma\ \vdash
\mathrm{RFN}(T^{\mathrm W})\leftrightarrow\mathrm{RFN}(T^{\mathrm R}).
$$

具体方向为：RFN(Tᵂ) ⇒ RFN(Tᴿ) 给出 R≤Y，反向蕴涵给出 Y≤R。每个方向可各取一个真辅助句，两句合取仍为 Σ¹₁。因此足以在一个共同基础上给出上述反射等价的证明。应用时需要独立给出辅助句及其真实性，或直接在 ACA₀ 内证明蕴涵。现在已经构造的降链转换覆盖第一座完整塔中已定位的记号初段；反射等价本身仍开放。[Walsh，定义 1.7、1.9 及定理 1.10](https://arxiv.org/pdf/2209.09765#page=5) · [实际的两向局部转换](W4PTODescent.lagda.md)
