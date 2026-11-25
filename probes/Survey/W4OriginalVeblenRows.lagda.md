# 原 ψ₁ 的三种基本列与一族可命名的 W4 下界

第四层。Agda 验证任意前缀的三种基本列展开，以及文末具体原名的标准形。依这些方程作经典超限归纳，可以按可数序数一次计算整行。[起始 ε 步](W4OriginalEpsilonStep.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4OriginalVeblenRows where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_; replicate)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Empty
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import OCF.Align.EboLeanDef using (T; PT; ψ; natT; Ωt; γT; HC; cof; cω; c1; cΩ; fsT; fsn; pred; hd<; lv<; tl<; []<)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiMENote using (cof++1; pred++; cof++ω; fsn++; cofψ1; fsnψ1; cofψω; fsnψω; cofψΩ; fsnψΩ; fsTψΩ)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiRefTw2 using (Rt)
import B26PSuffix as Low
import Survey.EboPTOFinite as B
import Survey.W4PTOFirstQuery as First
open import Survey.W4OriginalEpsilonStep using (unit)

i = natT 1
letter = ψ i
word = λ a → letter a ∷ []
name = λ p a → Low.φ (p ++ word a)

successor : ∀ p u b n → cof b ≡ c1 →
  fsn (name p (u ++ b)) n ≡ Low.φ (p ++ replicate n (letter (u ++ pred b)))
successor p u b n w = trans (fsnψω [] _ n (cof++ω p _ inner)) (cong Low.φ
  (trans (fsn++ p _ n inner) (cong (p ++_) (trans (fsnψ1 i _ n s)
    (cong (λ t → replicate n (letter t)) (pred++ u b w))))))
  where
  s = cof++1 u b w
  inner = cofψ1 i _ s

limit : ∀ p u b n → cof b ≡ cω →
  fsn (name p (u ++ b)) n ≡ name p (u ++ fsn b n)
limit p u b n w = trans (fsnψω [] _ n (cof++ω p _ inner)) (cong Low.φ
  (trans (fsn++ p _ n inner) (cong (p ++_) (trans (fsnψω i _ n s)
    (cong word (fsn++ u b n w))))))
  where
  s = cof++ω u b w
  inner = cofψω i _ s

module Diagonal (p u : T) where
  arg = p ++ word (u ++ unit)
  γ = γT arg []
  s = cof++Ω u unit refl
  inner : cof (word (u ++ unit)) ≡ cΩ []
  inner = cofψΩ i _ s
  outer = cof++Ω p _ inner
  w : cof (Low.φ arg) ≡ cω
  w = cofψΩ [] arg outer
  branch : ∀ n → fsn (Low.φ arg) n ≡ γ (suc n)
  branch n = fsnψΩ [] arg n outer
  step : ∀ n → γ (suc n) ≡ name p (u ++ γ n)
  step n = cong Low.φ (trans (fsT++ p _ (γ n) inner)
    (cong (p ++_) (trans (fsTψΩ i _ (γ n) s) (cong word (fsT++ u unit (γ n) refl)))))

-- p 为原参照第三层沿 (2,0,0,2,0) 抵达的名字的参数。
p = First.Names.d 2 (ψ (natT 2) [] ∷ ψ i [] ∷ [])
d = Low.φ p
nd : NF d
nd = cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (B.nf-row 2) refl 2) refl 0) refl 0) refl 2) refl 0

-- 标准形只需检查新后缀的支撑。所有用到的 ψ 下标至多为 1。
num-indices : ∀ k → B.Indices 1 (natT k)
num-indices zero = B.empty
num-indices (suc k) = B.cons Data.Nat.Base.z≤n B.empty (num-indices k)

support : ∀ {z t u} → B.Indices 1 t → InG u z t → B.Indices 1 z
support (B.cons le a ts) (gp (gh _)) = a
support (B.cons {j} le a ts) (gp (gw _ g)) rewrite B.num-support j (G-mono (B.bottom _) g) = B.empty
support (B.cons le a ts) (gp (gc _ g)) = support a g
support (B.cons le a ts) (gtl g) = support ts g

ends : ∀ {q qs} → NF (q ∷ qs) → B.Indices 1 (q ∷ qs) → NF (Low.φ (p ++ q ∷ qs))
ends {q = ψ .(natT j) a} {qs} nt ix@(B.cons {j} le _ _) =
  nf-ψ n[] (n∷ (nf-hd (nfp-a (nf-hd nd))) (inj₁ (lv< (B.numeral-strict (Data.Nat.Base.s≤s le)))) nt) guard
  where
  guard : GB [] (p ++ ψ (natT j) a ∷ qs) (p ++ ψ (natT j) a ∷ qs)
  guard (gp g) = <ᵀ-trans (nfp-g (nf-hd nd) (gp g)) (tl< []<)
  guard (gtl g) = <ᵀ-trans (B.small (support ix g)) (hd< (OCF.Align.EboLeanDef.ar< []<))

-- 所选内参数为 Ω₁·2+ω 或 Ω₁·2+k，其中 ω=ψ₀(1)。
ω = Low.φ i
double = unit ++ unit
tail = double ++ ω
ωNF = B.nf-collapsed 0 1
ωIx : B.Indices 1 ω
ωIx = B.cons Data.Nat.Base.z≤n (num-indices 1) B.empty
oIx : ∀ {ts} → B.Indices 1 ts → B.Indices 1 (letter [] ∷ ts)
oIx = B.cons (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) B.empty
with-units : ∀ {t} → B.Indices 1 t → B.Indices 1 (double ++ t)
with-units ix = oIx (oIx ix)
units-nf : ∀ {t} → NF t → Ctbl t → NF (double ++ t)
units-nf n c = n∷ card (inj₂ refl) (n∷ card (sort c) n)
  where
  card = nf-hd (nf-Ω (B.nf-num 1))
  sort : ∀ {t} → Ctbl t → HdLe (letter []) t
  sort c[] = tt
  sort (c∷ _) = inj₁ (lv< []<)

atomNF : ∀ {t} → NF t → Ctbl t → NFP (letter (double ++ t))
atomNF {t} nt ct = nψ (B.nf-num 1) (units-nf nt ct) guard
  where
  guard : GB i (double ++ t) (double ++ t)
  guard (gp (gh _)) = []<
  guard (gp (gw _ g)) rewrite B.num-support 1 (G-mono (B.bottom i) g) = []<
  guard (gp (gc _ ()))
  guard (gtl (gp (gh _))) = []<
  guard (gtl (gp (gw _ g))) rewrite B.num-support 1 (G-mono (B.bottom i) g) = []<
  guard (gtl (gp (gc _ ())))
  guard (gtl (gtl g)) = Data.Empty.⊥-elim (below nt ct g)
    where
    below : ∀ {t z} → NF t → Ctbl t → InG i z t → Data.Empty.⊥
    below n[] c[] ()
    below n@(n∷ _ _ _) (c∷ _) g = noG∷ n []< g

atomIx : ∀ {t ts} → B.Indices 1 t → B.Indices 1 ts → B.Indices 1 (letter (double ++ t) ∷ ts)
atomIx ix = B.cons (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) (with-units ix)

second = name p tail
second-nf : NF second
second-nf = ends (n∷ (atomNF ωNF (c∷ c[])) tt n[]) (atomIx ωIx B.empty)
second-h : HC second
second-h = hc second-nf (c∷ c[])

whole = Low.φ (p ++ letter tail ∷ letter (double ++ natT 2) ∷ [])
whole-nf : NF whole
whole-nf = ends (n∷ (atomNF ωNF (c∷ c[])) (inj₁ (lt→<ᴾ _ _ refl))
  (n∷ (atomNF (B.nf-num 2) (c∷ (c∷ c[]))) tt n[])) (atomIx ωIx (atomIx (num-indices 2) B.empty))
whole-h : HC whole
whole-h = hc whole-nf (c∷ c[])

```

```agda
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; s≼s; ≼l; ≼-refl; ≅→≼)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import Survey.W4FourthLiftValue as I
import Survey.W4PTOSeededQuery as H
import Survey.W4RoomDerivative as G

d-h = proj₁ First.Names.reached
base-value : Rt d-h ≼ I.h L.zero
base-value = ≼-trans (≅→≼ (L.≅-trans (proj₂ First.Names.reached) First.start-address)) (proj₁ I.start)

base-strict : L.suc (Rt d-h) ≼ G.g L.zero
base-strict = ≼-trans (s≼s base-value) (≼l 1 (H.above (I.h L.zero)))

query-nf : NF First.Names.query
query-nf = cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (B.nf-row 2) refl 2) refl 0) refl 0
under-query : L.suc (Rt whole-h) ≼ Rt (proj₁ First.Names.asked)
under-query = mono<ⁿ whole-nf query-nf (c∷ c[]) whole-h (proj₁ First.Names.asked)
  (lt→< _ _ refl)
```

## 按整个可数下标计算

**经典纸面证明。** 以 $\varphi_0(x)=\omega^x$，$\varphi_{j+1}$ 递增连续枚举 $\varphi_j$ 的不动点。记 $S_j(v)$ 为严格大于 $v$ 的第一个 $\varphi_j$ 值。令 $I_j(v,0)=v$，后继指标施 $S_j$，非零极限指标取先前各项的上确界。于是 $I_j(v,\xi+\eta)=I_j(I_j(v,\xi),\eta)$，由对 $\eta$ 的归纳即得。这里均取经典序数值。[Marcone–Montalbán，§1](https://math.berkeley.edu/~antonio/papers/veblen.pdf#page=2)

令 $P$ 为前缀，要求 $\psi_0(P)$ 是带遗传可数证书的标准形，$v=|\psi_0(P)|\ge1$。$M_m$ 表示连续 $m$ 份 $\Omega_1$。对可数标准尾项 $b$，设下式的左端也是标准形，则
\[
 |\psi_0(P+\psi_1(M_m+b))|=I_{m+1}(v,\omega^{|b|}).
 \tag{1}
\]
此处的加号拼接原语法中的项，空尾项表示零。对 $(m,|b|)$ 按字典序归纳，并对前缀同时陈述。$m=0,b=0$ 时为已编译的 `Step.exact`。当 $b$ 为后继时，`successor` 的第 $n$ 枝有 $n$ 份前一主项。对份数归纳，每加一份便由外层归纳假设从当前前缀值继续，因此其指标为 $\omega^{|b|-1}\cdot n$，取上确界即得 (1)。每个部分前缀也出现在同一基本列中；遗传证书及标准形对子项和基本列的封闭给出各次使用的前提。$b$ 为非零极限时，`limit` 保留左右前缀。基本列在 $|b|$ 中共尾，应用右指数及 $I_{m+1}$ 对非零极限的连续性。

剩下 $b=0$、$m=k+1$。由 `Diagonal.branch` 与 `Diagonal.step`，左端的值为从 $1$ 起反复施 $F(x)=I_{k+1}(v,\omega^x)$ 的上确界。每个下一输入正是前一基本列项，从而有标准形和可数证书。下面说明对任意 $j\ge1$，该 $F$ 的首个不动点为 $S_{j+1}(v)$（其中 $F$ 用 $I_j$）。$F$ 严格递增且在非零极限处连续，$F(0)>v\ge1$。若 $F(\lambda)=\lambda$，则 $\lambda>v$，且它是 $\varphi_j$ 的值，故 $\omega^\lambda=\lambda$。对每个 $\eta<\lambda$，有 $\varphi_j(\eta)\le I_j(v,\eta+1)$，由枚举次序归纳即得。因此 $\varphi_j(\lambda)\le I_j(v,\lambda)=\lambda$，反向由正规性得出。反过来若 $\varphi_j(\lambda)=\lambda>v$，可取 $\delta<\lambda$ 使 $v\le\varphi_j(\delta)$。对 $\eta<\lambda$ 有 $I_j(v,\eta)\le\varphi_j(\delta+\eta)<\lambda$，因为 $\lambda$ 对较小序数的和封闭。取上确界并用 $\omega^\lambda=\lambda$ 得 $F(\lambda)\le\lambda$；正规性给另一向。于是所求上确界恰是 $v$ 以上首个 $\varphi_j$ 不动点。这证明了系数 $m$ 增加一份时的情形，也完成了 (1)。[原记号的基本列](../OCF/Align/EboLeanDef.lagda.md) · [标准形基本列的封闭](../OCF/Align/EboLeanClosure.lagda.md)

**应用到 W4。** 专取 $P=\psi_2(\Omega_2+\Omega_1)$、$D=|\psi_0(P)|$。沿原第三层的地址 $(2,0,0,2,0)$ 即得这个值。`base-strict` 给 $D<g(0)$，且 $D=h(0)>0$。先前的 `zeta-index` 给每个 $g(\eta)$ 都固定 $\varphi_2$，即它是 $\varphi_3$ 的一个值。由 $g$ 在后继处严格增长、极限处连续，对所有可数 $\eta$ 归纳得
\[
 I_3(D,\eta)\le g(\eta).
 \tag{2}
\]
因此 $m=2$ 的任意有限主项串，设第 $i$ 个可数尾项为 $b_i$，且全项及各部分前缀的塌缩均有上述证书，就把已证的 $g$ 指标 $\eta=\omega^{|b_1|}+\cdots+\omega^{|b_k|}$ 变为原 ψ 记号下界。各部分前缀在这里也有标准形：截短一个降序和保持降序，各余下支撑在这组具体前缀下由 `ends` 检查；一般有限串的应用以上述各前缀有证书为域。[各个 g 值固定 ζ 枚举](W4ReflectionFixed.lagda.md) · [原始地址](W4PTOFirstQuery.lagda.md)

取第一项 $b_1=\omega$ 得 `second` 的值 $I_3(D,\omega^\omega)\le s_2$。再接 $b_2=2$ 得 `whole` 的值 $I_3(D,\omega^\omega+\omega^2)\le Y$。这两个下界和 (1)、(2) 的推导属经典纸面证明。两原名的标准形、遗传证书和 `whole` 严格低于原询问 $\psi_0(\psi_2(\psi_2(1)))$ 的比较属于 Agda 定理。[对应的 W4 值](W4NextLiftValue.lagda.md)
