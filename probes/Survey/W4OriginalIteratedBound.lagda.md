# 相邻塔迭代给出的原 ψ 记号下界

第四层。取 P=ψ₂(Ω₂+Ω₁)，本轮单个原名为 X=ψ₀(P+ψ₁(Ω₁·2+ω²+1))。Agda 验证其标准形及它与原参照项的严格比较，X≤Y 由文末的经典值计算得出。[整行的值公式](W4OriginalVeblenRows.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4OriginalIteratedBound where

open import Data.Nat.Base using (ℕ; suc; z≤n)
open import Data.Product using (proj₁; proj₂)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Sum.Base using (inj₁)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (natT; ψ; HC; ar<; []<)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
import Survey.EboPTOFinite as B
import Survey.W4PTOFirstQuery as First
import Survey.W4OriginalVeblenRows as Row

first-nf : NF (Row.name Row.p Row.double)
first-nf = Row.ends (n∷ (Row.atomNF {[]} n[] c[]) tt n[]) (Row.atomIx B.empty B.empty)

b = ψ [] (natT 2) ∷ natT 1
normal : NF b
normal = n∷ (nψ n[] (B.nf-num 2) (λ g → small g)) (inj₁ (ar< []<)) (B.nf-num 1)
  where
  small : GB [] (natT 2) (natT 2)
  small g rewrite B.num-support 2 g = []<
count : Ctbl b
count = c∷ (c∷ c[])
ix : B.Indices 1 b
ix = B.cons z≤n (Row.num-indices 2) (Row.num-indices 1)

X = Row.name Row.p (Row.double ++ b)
normal-X : NF X
normal-X = Row.ends (n∷ (Row.atomNF normal count) tt n[]) (Row.atomIx ix B.empty)
cert-X : HC X
cert-X = hc normal-X (c∷ c[])
row₂<X : L.suc (Rt (B.row-h 1)) ≼ Rt cert-X
row₂<X = mono<ⁿ (B.nf-row 1) normal-X (c∷ c[]) (B.row-h 1) cert-X (lt→< _ _ refl)

old<X : L.suc (Rt Row.whole-h) ≼ Rt cert-X
old<X = mono<ⁿ Row.whole-nf normal-X (c∷ c[]) Row.whole-h cert-X (lt→< _ _ refl)
X<query : L.suc (Rt cert-X) ≼ Rt (proj₁ First.Names.asked)
X<query = mono<ⁿ normal-X Row.query-nf (c∷ c[]) cert-X (proj₁ First.Names.asked) (lt→< _ _ refl)
query<row₃ : L.suc (Rt (proj₁ First.Names.asked)) ≼ Rt (B.row-h 2)
query<row₃ = mono<ⁿ Row.query-nf (B.nf-row 2) (c∷ c[]) (proj₁ First.Names.asked) (B.row-h 2) (lt→< _ _ refl)
```

**经典纸面证明。** 记 θ=(ω^ω)^ω=ω^(ω²)。原可数尾项 b 的值为 ω²+1，因 ψ₀(2) 的第 n 个基本列项是 n 份 ψ₀(1)，值为 ω·n。在整行公式 (1) 中代入 m=2，有 |X|=I₃(D,ω^(ω²+1))=I₃(D,θ·ω)。公式 (2) 给 |X|≤g(θ·ω)。相邻塔定理给每个 n 的具体见证 g(θ·n)≤sₙ₊₃，故 **|X|≤g(θ·ω)≤Y**。于是由原标准项严格保序，X 的整个原记号初段以及 X 本身都被 W4 覆盖。原查询 G(1)=ψ₀(ψ₂(ψ₂(1))) 严格大于 X；已证的两个上界 X<G(1) 和 X≤Y 仍容许 G(1) 与 Y 的任一相对次序。[相邻塔值定理](W4IteratedLiftValue.lagda.md) · [原记号严格保序](../OCF/Lean/YiCFMono.lagda.md)

同一公式取空可数尾项，得到首塔能接收的原名 $\psi_0(P+\psi_1(\Omega_1\cdot2))$。其值为 $S_3(D)$，即严格高于 $D$ 的首个 ζ 枚举不动点，由 (2) 的起始比较 $D<g(0)$ 和 $g(0)$ 固定 ζ 枚举可得 $S_3(D)\le g(0)\le t_1$。这里 $t_1$ 是编号 1 的实际完整塔。[首个不动点与实际首塔](W4RoomDiagonal.lagda.md) · [g(0) 的标定](W4RoomDerivative.lagda.md)

## 同一首主项的上限

```agda
import OCF.Align.EboLeanClosure
import B26PSuffix
open import OCF.Align.EboLeanDef using (T; hd<)
open import OCF.Align.Value using (l≼; ≼-refl; ≼-suc; s≼s; ≅→≼)
import B23RShare as Q
import B17RefAllSource as Src

two = First.Names.d 0 (First.Names.d 2 (ψ (natT 2) [] ∷ ψ (natT 2) [] ∷ []))
next-branch = First.Names.d 0 (First.Names.d 2 (ψ (natT 2) [] ∷ Row.letter Row.p ∷ []))
two-at = First.Names.child refl First.Names.asked 2
next-at = First.Names.child refl two-at 1
two-h : HC two
two-h = proj₁ two-at
next-h : HC next-branch
next-h = proj₁ next-at
two-nf : NF two
two-nf = OCF.Align.EboLeanClosure.cl-fsn-NF Row.query-nf refl 2
next-nf : NF next-branch
next-nf = OCF.Align.EboLeanClosure.cl-fsn-NF two-nf refl 1

under-next : ∀ (s : T) → NF (B26PSuffix.φ (Row.p ++ s)) → (h : HC (B26PSuffix.φ (Row.p ++ s))) →
  L.suc (Rt h) ≼ Rt next-h
under-next s nf h = mono<ⁿ nf next-nf (c∷ c[]) h next-h (hd< (ar< (hd< (ar< (lt→< _ _ refl)))))

next<two : L.suc (Rt next-h) ≼ Rt two-h
next<two = mono<ⁿ next-nf two-nf (c∷ c[]) next-h two-h (lt→< _ _ refl)
native-two : Rt two-h L.≅ Q.parts 2
native-two = L.≅-trans (proj₂ two-at) (Src.part First.query-address 2)

family<two : (f : ℕ → T) (nf : ∀ n → NF (B26PSuffix.φ (Row.p ++ f n)))
  (hs : ∀ n → HC (B26PSuffix.φ (Row.p ++ f n))) → L.suc (L.lim (λ n → Rt (hs n))) ≼ Q.parts 2
family<two f nf hs = ≼-trans (s≼s (l≼ (λ n → ≼-trans (≼-suc (≼-refl _)) (under-next (f n) (nf n) (hs n)))))
  (≼-trans next<two (≅→≼ native-two))
```

记 a₂=ψ₀(ψ₂(Ω₂·2))。它在原询问 G(1) 的第 2 枝。a₂ 的第 0 枝是上述 D，第 1 枝是 B=ψ₀(ψ₂(Ω₂+ψ₁(P)))。对任意使 ψ₀(P+s) 成为可数标准形的后缀 s，原序的首异位置比较直接给 |ψ₀(P+s)|<|B|。因此任取可数多个这样的后缀，全部值的上确界仍 ≤|B|<|a₂|。这个 Agda 定理给固定首主项 P 的读法划出了界限。要用原名覆盖 a₂，需要改变首主项或另证整条实际反馈的支配定理；已由实际塔支付的 g(θ·ω) 与 a₂ 的相对次序仍待证。
