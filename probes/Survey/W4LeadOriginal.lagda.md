# W4 支付的第三份 Ω₁

第四层。原名 X₃=ψ₀(P+ψ₁(Ω₁·3+ω²+1)) 严格超过上一轮的 X₂，且低于固定首主项的精确上界。原名严格比较与第四行预算分别经 Agda 检查；两种写法的对接用原基本列值公式。[整行公式](W4OriginalVeblenRows.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadOriginal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product using (proj₁)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import OCF.Align.EboLeanDef using (T; HC; fsn; _<ᵀ_; hd<; ar<; lv<; tl<; []<)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼; hω-inv)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-suc; ≼-trans; ≼-refl; l≼)
import Survey.EboPTOFinite as B
import Survey.W4OriginalVeblenRows as R
import Survey.W4OriginalIteratedBound as Old
import Survey.W4LeadIdeal as Ideal
import Survey.W4LeadVeblen as V
import Survey.W4IteratedLiftValue as Towers
import Survey.W4IteratedLiftOrdinal as O
import Survey.W4RouteTests as W
import Survey.W4RoomDerivative as G
import B18Product as M
import B20StandardInside as Std
import Survey.W4LeadCapBranch as Branch

below-unit : ∀ {b : T} → Ctbl b → ∀ s → b <ᵀ (R.letter [] ∷ s)
below-unit c[] s = []<
below-unit (c∷ _) s = hd< (lv< []<)

old-arg = R.double ++ Old.b
triple = R.letter [] ∷ old-arg
X₃ = R.name R.p triple

normal : NF X₃
normal = R.ends (n∷ (nψ (B.nf-num 1) norm guard) tt n[]) (B.cons (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)
    (R.oIx (R.with-units Old.ix)) B.empty)
  where
  old = R.atomNF Old.normal Old.count
  norm : NF triple
  norm = n∷ (nf-hd (nf-Ω (B.nf-num 1))) (inj₂ refl) (nfp-a old)
  guard : GB R.i triple triple
  guard (gp (gh _)) = []<
  guard (gp (gw _ h)) rewrite B.num-support 1 (G-mono (B.bottom _) h) = []<
  guard (gp (gc _ ()))
  guard (gtl h) = <ᵀ-trans (nfp-g old h) (lt→< old-arg triple refl)

opaque
  cert : HC X₃
  cert = hc normal (c∷ c[])

start-name = R.name R.p (R.letter [] ∷ R.double)
start-normal : NF start-name
start-normal = R.ends (n∷ (nψ (B.nf-num 1) norm guard) tt n[])
  (B.cons (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) (R.oIx (R.with-units B.empty)) B.empty)
  where
  small = R.atomNF {[]} n[] c[]
  norm = n∷ (nf-hd (nf-Ω (B.nf-num 1))) (inj₂ refl) (nfp-a small)
  guard : GB R.i (R.letter [] ∷ R.double) (R.letter [] ∷ R.double)
  guard (gp (gh _)) = []<
  guard (gp (gw _ h)) rewrite B.num-support 1 (G-mono (B.bottom _) h) = []<
  guard (gp (gc _ ()))
  guard (gtl h) = <ᵀ-trans (nfp-g small h) (lt→< _ _ refl)

opaque
  start-cert : HC start-name
  start-cert = hc start-normal (c∷ c[])

import B26PSuffix as S
-- 首个可数尾 b 决定严格比较，其后的有限和 q 可以任取。
past-row : ∀ b q → Ctbl b → let t = S.φ (R.p ++ R.letter (R.double ++ b) ∷ q) in
  (nf : NF t) (h : HC t) → L.suc (Rt h) ≼ Rt start-cert
past-row b q count nf h = mono<ⁿ nf start-normal (c∷ c[]) h start-cert
  (hd< (ar< (tl< (hd< (ar< (tl< (tl< (below-unit count []))))))))

module Row₂ = R.Diagonal R.p R.double
row-member = λ n → R.name R.p (R.double ++ Row₂.γ n)
row-eq : ∀ n → fsn start-name n ≡ row-member n
row-eq n = trans (Row₂.branch n) (Row₂.step n)

row-cofinal : ∀ {y : L.Ordᶜ L.zero} →
  (∀ b → Ctbl b → let t = R.name R.p (R.double ++ b) in
    NF t → (h : HC t) → Rt h ≼ y) → Rt start-cert ≼ y
row-cofinal {y} upper = ≼-trans {b = L.lim (λ n → Rt (child n))}
  (proj₁ (S.limit start-cert Row₂.w (λ n → Rt (child n)) (λ n → S.same refl (child n) (child n))))
  (l≼ λ n → ≼-trans {b = Rt (member-h n)} (tree-≼ (row-eq n) (child n) (member-h n))
    (upper (Row₂.γ n) (count n) (member-nf n) (member-h n)))
  where
  count : ∀ n → Ctbl (Row₂.γ n)
  count zero = c∷ c[]
  count (suc n) = c∷ c[]
  child = hω-inv start-cert Row₂.w
  member-h : ∀ n → HC (row-member n)
  member-h n = subst HC (row-eq n) (child n)
  member-nf : ∀ n → NF (row-member n)
  member-nf n = subst NF (row-eq n) (cl-fsn-NF start-normal Row₂.w n)

start<X₃ : L.suc (Rt start-cert) ≼ Rt cert
start<X₃ = mono<ⁿ start-normal normal (c∷ c[]) start-cert cert (lt→< _ _ refl)

past : L.suc (Rt Old.cert-X) ≼ Rt cert
past = mono<ⁿ Old.normal-X normal (c∷ c[]) Old.cert-X cert (lt→< _ _ refl)

below-cut : L.suc (Rt cert) ≼ Rt Ideal.cut-h
below-cut = Ideal.below-cut (R.word triple) normal cert

cut<first-return : L.suc (Rt Ideal.cut-h) ≼ Branch.v 1
cut<first-return = mono<ⁿ Ideal.nf-cut (Branch.normal 1) (c∷ c[]) Ideal.cut-h (Branch.cert 1) (lt→< _ _ refl)

first-budget : V.fourth (Rt R.d-h) ≼ Std.std 1
first-budget = ≼-trans {b = G.g L.zero} (V.fourth-at (Rt R.d-h) (G.g L.zero) R.base-strict (proj₁ (G.enumerated L.zero))) G.first

index = O.width M.· L.ωᶜ
budget : V.walk (Rt R.d-h) index ≼ W.Y
budget = ≼-trans {b = G.g index} (V.paid (Rt R.d-h) (≼-trans (≼-suc (≼-refl _)) R.base-strict) index) Towers.whole
```

**经典纸面证明。** 取 D=|ψ₀(P)|，b=ω²+1。整行公式给 |X₃|=I₄(D,ω^(ω²+1))。这里 I₄ 从 D 起步，每一步取严格在当前值上方的首个 φ₃ 不动点，极限取上确界。树运算 `V.fourth` 从 x+1 迭代正规函数 φ₃ 并取 ω 次上确界，故其值恰是该步；根据正规函数的不动点枚举，按迭代指标归纳，`V.walk` 的值就是 I₄。树侧的下标 index 读作 ω^(ω²)·ω=ω^(ω²+1)，所以 `budget` 给出 **|X₃|≤Y**。将原名参数中的 ω²+1 换为任何可数标准尾项 b，整行公式同样给 |ψ₀(P+ψ₁(Ω₁·3+b))|≤g(ω^|b|)，前提是该原名为标准形。空尾项的值是 D 上方首个 φ₃ 不动点；由 D<g(0)、h(g(0))=g(0) 及 `V.fourth-at`，这个起点已经由第一座标准塔支付。[相邻塔下标](W4IteratedLiftValue.lagda.md) · [g(0) 到首塔的比较](W4RoomDerivative.lagda.md)

**PTO 推论（经典纸面证明）。** 在 ACA₀ 上，逐个加入 X₃ 以下原可数标准项的严格初段良序公理，记所得理论为 T₃。每个证明只用有限个初段。单个初段良序公理的 PTO 公式与原秩穷尽性给 PTO(T₃)=sup{ε⁺(|b|) ∣ b<X₃}=|X₃|，末式用到 X₃ 是 ε 数的极限。令 v=ω^(ω²+1)。沿 g(v) 的地址序迭代 Π¹₁ 反射的理论 S(v) 已有 PTO(S(v))=g(v)，故 PTO(T₃)≤PTO(S(v))。沿用先前从 W4 到 S(v) 的反射比较，再为 T₃ 的可证良序一次选择到 S(v) 可证良序的嵌入，合并为一条真 Σ¹₁ 辅助句 σ，则 ACA₀+σ 证明 RFN(Tᵂ)⇒RFN(T₃)。这里 σ 可随新端点更换。[原初段与反射比较](W4IteratedReflection.lagda.md) · [Walsh 的反射比较定理](https://arxiv.org/pdf/2209.09765)

原序上的另一项严格比较是 |X₃|<|ψ₀ψ₂(Ω₂+Ω₁+1)|<|a₂[1][0]|。其中第一个上界是所有固定首主项 P 的标准名的精确上确界。由 `past-row`，此前第三行中每个以 ψ₁(Ω₁·2+b) 起头的后缀（b 可数）均严格低于新第四行的起点，后面可接任意保持标准形的有限和。反向由 `row-cofinal` 给出。新起点的第 n 枝用可数尾项 γₙ 代入前一行，余下的和为空。新起点因此恰是前一行所有这些标准项的上确界。[固定首主项的上确界](W4LeadIdeal.lagda.md) · [第 1 枝的基本列](W4LeadCapBranch.lagda.md)
