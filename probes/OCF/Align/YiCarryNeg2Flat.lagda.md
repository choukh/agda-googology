# YiCarryNeg2：常 1 的 lc 读法在 output-step 与 OutputB 处失败

**部分否定，未否定 K2′⁺。** 本篇导入 README 已标定稿且已编译的
YiCarryPlus。检验用函数 flat 保留零、后继、ℕ 极限三行，把 lc 项
一律送到 1。它是本篇反例中的具体函数，不是提出或实现修补方案。
同一函数在 Carry⁺ 且 Legal 的闭源上没有 GtGenerator⁺，失败字段是
output-step；另一个 Carry⁺ 且 Legal 的闭源否定其 OutputB⁺。
没有得到对任意 ψ 的 K2′⁺ → ⊥。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryNeg2Flat where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as Y
import OCF.Align.YiCarryPlus as P
import OCF.Align.YiK2Base as A
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (one; e-first)

flat : F.LF → F.Raw F.zero
flat F.zero = A.one
flat (F.suc x) = A.successor (flat x)
flat (F.lim f) = G.lim (λ n → flat (f n))
flat (F.lc k c t g) = A.one

flatψ : P.Source⁺ → F.Raw F.zero
flatψ s = flat (P.term s)

flat-zero-row : ∀ r l → flatψ (P.source⁺ F.zero r l) ≡ A.one
flat-zero-row r l = refl

flat-suc-row : ∀ x (r : P.Carry⁺ x) (l : V.Legal x) →
  flatψ (P.source⁺ (F.suc x) r l) ≡ A.successor (flatψ (P.source⁺ x r l))
flat-suc-row x r l = refl

flat-lim-row : ∀ f (r : ∀ n → P.Carry⁺ (f n))
  (st : ∀ n → V.CP (f n) (f (suc n))) (l : ∀ n → V.Legal (f n)) →
  flatψ (P.source⁺ (F.lim f) r (st , l)) ≡
  G.lim (λ n → flatψ (P.source⁺ (f n) (r n) (l n)))
flat-lim-row f r st l = refl
```

## 1. 两个闭值及其源证据

first=1；node 是下界 raw1、第一支 1、全部分支恒 1 的 lc。
first 到 node 有原 CP 第一支路径，两个源各自的输出合法且正。
具体的不相容在输出之间：successor one 不能是 one 的第一位置。

```agda
first : F.LF
first = F.suc F.zero

node : F.LF
node = F.lc F.zero A.one first (λ _ _ → first)

node-reg : Reg node
node-reg = one e-first , tt , tt , (λ _ _ → tt)

node-carry : P.Carry⁺ node
node-carry = node-reg , tt , tt , tt , (λ _ _ _ → tt)

node-legal : V.Legal node
node-legal = tt , (λ _ _ → V.self) , (λ _ _ _ _ _ → V.self) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

first-source node-source : P.Source⁺
first-source = P.source⁺ first tt tt
node-source = P.source⁺ node node-carry node-legal

first-to-node : V.CP first node
first-to-node = V.fst V.self

first-output-B : P.LglB F.zero (flatψ first-source)
first-output-B = A.ψᶜ-legal (G.suc G.zero) tt ,
  Y.raw0-nested (A.successor A.one)

node-output-B : P.LglB F.zero (flatψ node-source)
node-output-B = tt , tt

first-output-positive : F.Dn F.zero G.zero (flatψ first-source)
first-output-positive = 0 , inj₁ refl

node-output-positive : F.Dn F.zero G.zero (flatψ node-source)
node-output-positive = inj₁ refl

no-wide-to-one : F.Cp F.zero (A.successor A.one) A.one → ⊥
no-wide-to-one (inj₁ ())
no-wide-to-one (inj₂ (inj₁ ()))
no-wide-to-one (inj₂ (inj₂ ()))
```

## 2. OutputB 的闭反例

取列 1,node,node,…。相邻原 CP、逐项 Carry⁺、逐项 Legal 全部成立，
所以这是原块中的合法闭源。flatψ 输出列是 successor one,one,one,…，
第一步的 Cp 不存在；失败精确在 Lgl 的相邻步字段，非 Nested。

```agda
columns : ℕ → F.LF
columns zero = first
columns (suc n) = node

column-carry : ∀ n → P.Carry⁺ (columns n)
column-carry zero = tt
column-carry (suc n) = node-carry

column-legal : ∀ n → V.Legal (columns n)
column-legal zero = tt
column-legal (suc n) = node-legal

column-step : ∀ n → V.CP (columns n) (columns (suc n))
column-step zero = first-to-node
column-step (suc n) = V.self

limit-source : P.Source⁺
limit-source = P.source⁺ (F.lim columns) column-carry (column-step , column-legal)

no-flat-limit-B : P.LglB F.zero (flatψ limit-source) → ⊥
no-flat-limit-B ((st , ls) , nested) = no-wide-to-one (st 0)

no-flat-output-B : P.OutputB⁺ flatψ → ⊥
no-flat-output-B output = no-flat-limit-B (output limit-source)
```

否定的背景前提由 limit-source 同时实填；OutputB⁺ 是被否定的目标。
flat-zero-row、flat-suc-row、flat-lim-row 的前提分别可取零源、first
的前驱零源，以及本节整个 columns 证书包。没有把 PsiRows⁺ 当成
可满足的背景前提；flat 只满足它的前三行。

## 3. output-step 的闭反例：grow 无论选哪一点都失败

源的守卫下界仍是 raw1。g 在守卫的等号支取 first，严格支取 node。
合法性与证明无关性逐项编译；等号与严格支重叠或严格返回 raw1
都会推出 Dn raw1 raw1，直接构造子反演排除。
这不是在裸下标上判等：只读原守卫已经提供的 Cp 证据。

```agda
no-one-cycle : F.Dn F.zero A.one A.one → ⊥
no-one-cycle (inj₁ ())
no-one-cycle (inj₂ ())

no-return : ∀ η → F.Dn F.zero A.one η → F.Cp F.zero η A.one → ⊥
no-return η p (inj₁ refl) = no-one-cycle p
no-return η p (inj₂ q) = no-one-cycle (F.Dn-tr F.zero p q)

gate : (η : F.Raw F.zero) → F.Gd F.zero A.one η → F.LF
gate η (inj₁ eq , l) = first
gate η (inj₂ p , l) = node

gate-first : ∀ η e → V.CP first (gate η e)
gate-first η (inj₁ eq , l) = V.self
gate-first η (inj₂ p , l) = first-to-node

gate-reg : ∀ η e → Reg (gate η e)
gate-reg η (inj₁ eq , l) = tt
gate-reg η (inj₂ p , l) = node-reg

gate-carry : ∀ η e → P.LglB F.zero η → P.Carry⁺ (gate η e)
gate-carry η (inj₁ eq , l) b = tt
gate-carry η (inj₂ p , l) b = node-carry

gate-legal : ∀ η e → V.Legal (gate η e)
gate-legal η (inj₁ eq , l) = tt
gate-legal η (inj₂ p , l) = node-legal

gate-mono : ∀ η e η′ e′ → F.Gd F.zero η η′ → V.CP (gate η e) (gate η′ e′)
gate-mono η (inj₁ eq , l) η′ e′ d = gate-first η′ e′
gate-mono η (inj₂ p , l) .A.one (inj₁ refl , l′) d =
  ⊥-elim (no-return η p (proj₁ d))
gate-mono η (inj₂ p , l) η′ (inj₂ q , l′) d = V.self

gate-irr : ∀ η e e′ → gate η e ≡ gate η e′
gate-irr η (inj₁ eq , l) (inj₁ eq′ , l′) = refl
gate-irr .A.one (inj₁ refl , l) (inj₂ p , l′) = ⊥-elim (no-one-cycle p)
gate-irr .A.one (inj₂ p , l) (inj₁ refl , l′) = ⊥-elim (no-one-cycle p)
gate-irr η (inj₂ p , l) (inj₂ q , l′) = refl

gate-source-term : F.LF
gate-source-term = F.lc F.zero A.one first gate

gate-source-reg : Reg gate-source-term
gate-source-reg = one e-first , tt , tt , gate-reg

gate-source-carry : P.Carry⁺ gate-source-term
gate-source-carry = gate-source-reg , tt , tt , tt , gate-carry

gate-source-legal : V.Legal gate-source-term
gate-source-legal = tt , gate-first , gate-mono , gate-irr , tt , gate-legal

gate-source : P.Source⁺
gate-source = P.source⁺ gate-source-term gate-source-carry gate-source-legal

p₀ p₁ : P.PointB F.zero A.one
p₀ = P.point A.one (inj₁ refl , tt) (tt , tt)
p₁ = P.point (G.suc A.one) (inj₂ (inj₁ refl) , tt) (tt , tt)

one-step-growth : F.Dn F.zero (P.coordinate p₀) (P.coordinate p₁)
one-step-growth = inj₁ refl

-- 只用下一点的原 guard 与 grow；无需假定 seed 固定在 p₀。
no-grown-output-step : ∀ (p : P.PointB F.zero A.one) →
  F.Dn F.zero A.one (P.coordinate p) →
  F.Cp F.zero (A.successor A.one) (flat (gate (P.coordinate p) (P.guard p))) → ⊥
no-grown-output-step (P.point .A.one (inj₁ refl , l) b) grow step =
  no-one-cycle grow
no-grown-output-step (P.point η (inj₂ p , l) b) grow step = no-wide-to-one step

no-flat-generator :
  P.GtGenerator⁺ flatψ F.zero A.one first gate gate-source-carry gate-source-legal → ⊥
no-flat-generator d = no-grown-output-step (P.GtGenerator⁺.next d p₀)
  (P.GtGenerator⁺.grow d p₀)
  (Y.RawStep.path (P.GtGenerator⁺.output-step d p₀))

no-flat-rows : P.PsiRows⁺ flatψ → ⊥
no-flat-rows rows = no-flat-generator
  (P.PsiRows⁺.gt-generator rows F.zero A.one first gate gate-source-carry gate-source-legal)
```

seed 不空：P.seed⁺ gate-source-carry 可用，p₀ 也是闭证据。
p₁ 说明合法且带 LglB 的严格下一点确实存在。grow 一旦成立，下一点
的守卫必须走严格支，分支源便由 first 变成 node；两支各自的输出
已有合法与正性证据，但没有所需输出 Cp。no-flat-generator 不使用
gt-additive0、gt-seed0 或 seed；它对任何 next 的 grow 都检查 p₀，
不是只否定所列 p₀→p₁ 这一条有限测试。

no-return 的 Dn 与反向 Cp 的合取本来就是被排除的环，不当作可满足
背景。主否定所需 gate-source 的 Carry⁺、Legal、Reg、PointB 与一次
严格增长均已给出同一源的闭实例。GtGenerator⁺、PsiRows⁺、OutputB⁺
在 flatψ 上正是被否定的目标，不将它们假装作背景实例。

## 三档、范围与翻译账

**编译定理。** no-flat-generator 与 no-flat-rows
否定这个具体 ψ 的生成器与行记录；失败在 output-step 的 path 字段，
不是源证书、seed、next 返回域或坐标增长。no-flat-output-B 在另一
合法闭源否定同一个 ψ 的输出证书，失败在 Lgl 的极限相邻 Cp。
两个源的全部输入证据均实填。

**有限测试。** 无；虽使用具体闭源，否定任意 next 的结论是定理，
没有把一个计算样本说成全域结论。

**判断／未完成。** 以上仅说明前三行加上这种常 1 的 lc 读法不足以
满足增补接口。它没有证明任何已经满足 gt 行的 ψ 会失败；flatψ
未满足完整行记录，故不可由此推出 K2′⁺ → ⊥。未找到与 ψ 无关的
next／grow／output-step 反例，也未找到针对完整 K2′⁺ 的 OutputB
反例。高层源的证书增补排除了旧 seed 反例；尚无新的全接口否定。
不据此关闭 K2′⁺ 或乙路线。不实施修补。

没有新增比较器。gate-mono 的源分支对以右分支为字面公共界，
gate-legal 给其 Legal；limit 的相邻项以 node 为合法公共界；
输出的被否定 Cp 以右输出 one 为合法公共界。反演不索取无界三歧。
翻译账：只有闭源、检验函数和字段反例；没有新树构造子、证书字段、
记号规则、阶段专属前提、值界或 FGH 比较。第 4 层逼出：无。

冷编与依赖审计见本轮入口 [YiCarryNeg2](YiCarryNeg2.lagda.md)。
