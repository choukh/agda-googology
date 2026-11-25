# 回灌的结果成为新下标

第四层。裸 Ω 叶的正次回灌可统一使用 W4 已覆盖的一个序数区间。将输出送入新下标时，一步合法回灌即排除了保留两处单调性的统一计分。文末分别给出实际地址的经典存在性与这份计分失效的范围。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4CriticalIndexReturn where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.EboLeanDef hiding (lt; eq)
open import OCF.Align.EboLeanView using (VΩ; ωs; ωr; ωl; ωp; Vω; ws; wl; w4; w5; w6; γ; fω-eq; vω)
open import OCF.Align.EboLeanBase using (NF)
open import OCF.Align.EboLeanTree using (nf-tower)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans)
open import OCF.Align.TightValBase using (s≼-irrefl)
import OCF.Align.Level as L
open import WVOne using (T₀)
import Survey.W4CriticalDescent as C

wrap : T → T
wrap a = ψ [] a ∷ []

context : T → T
context x = wrap (Ωt x)

a = Ωt (natT 1)

index-step : C.Jump (context a) (context (wrap a))
index-step = C.fire (C.at refl 1)

index-strict : context (wrap a) <ᵀ context a
index-strict = C.strict (nf-tower 2) index-step

index-normal : NF (context (wrap a))
index-normal = C.normal (nf-tower 2) (C.at refl 1)

no-monotone-score : (score : T → T₀) →
  score a ≼ score (wrap a) →
  (score a ≼ score (wrap a) → score (context a) ≼ score (context (wrap a))) →
  L.suc (score (context (wrap a))) ≼ score (context a) → ⊥
no-monotone-score score inside outside down = s≼-irrefl (score (context (wrap a)))
  (≼-trans {b = score (context a)} down (outside inside))

flat : T → T₀
flat _ = L.zero

flat-inside : flat a ≼ flat (wrap a)
flat-inside = ≼-refl _

flat-outside : flat a ≼ flat (wrap a) → flat (context a) ≼ flat (context (wrap a))
flat-outside h = h

orbit : ℕ → T
orbit zero = natT 1
orbit (suc n) = context (orbit n)

orbit-eq : ∀ n → γT (Ωt a) [] n ≡ orbit n
orbit-eq zero = refl
orbit-eq (suc n) = cong context (orbit-eq n)

all-branches : ∀ n → fsn (EBOψ 2) n ≡ orbit (suc n)
all-branches n = cong context (orbit-eq n)

chain : T → ℕ → T
chain ν zero = Ωt ν
chain ν (suc k) = ψ ν (chain ν k) ∷ []

bare-chain : ∀ {u} (e : cof u ≡ c1) n → γ (ωr e) n ≡ chain (pred u) n
bare-chain e zero = refl
bare-chain {u} e (suc n) = cong (λ z → ψ (pred u) z ∷ []) (bare-chain e n)

bare-fs : ∀ {u i} (e : cof u ≡ c1) (b : cof (Ωt u) ≡ cΩ (pred u))
  (p : cmpᵀ (sucT (pred u)) i ≡ gt) n →
  fsn (ψ i (Ωt u) ∷ []) n ≡ (ψ i (chain (pred u) n) ∷ [])
bare-fs {u} {i} e b p n = trans (fω-eq (w6 b p (ωr e)) n)
  (cong (λ x → ψ i x ∷ []) (bare-chain e n))

nested : ∀ {t ν} → VΩ t ν → Bool
nested (ωr _) = false
nested (ωs _) = true
nested (ωl _ _) = true
nested (ωp _ _ _) = true

charge : ∀ {t} → Vω t → ℕ → Bool
charge (ws v) n = charge v n
charge (wl _ v) n = charge v n
charge (w4 _) n = false
charge (w5 _ v) n = charge v n
charge (w6 _ _ _) zero = false
charge (w6 _ _ v) (suc n) = nested v

bare-free : ∀ n → charge (vω (C.epsilon ∷ []) refl) n ≡ false
bare-free zero = refl
bare-free (suc n) = refl

index-charged : ∀ n → charge (vω (EBOψ 2) refl) (suc n) ≡ true
index-charged n = refl
```

## 哪些正次回灌能由同一个真实返回接收

**经典纸面证明。** 在原可数标准项的前驱与基本列分支中，允许全部普通步、任意规则 6 的第零枝，以及活动参数的 Ω 视图恰为 `ωr` 时的全部正次分支。外面可有任意多个和前缀、下标和参数上下文。给有限项赋分 $m$。空列取零，非空列取各主项权重的自然和 $\#$，置
$$
w(\psi_u a)=\varphi_{m(u)}\big((m(u)\mathbin{\#}m(a))+1\big).
$$
取 $\varphi_0(\xi)=\omega^\xi$，正下标枚举所有较低函数的共同不动点。按有限语法归纳，所有分数都小于 $\Gamma_0$。主项权重是正的加法主序数，在两项分数上各自严格递增。这里用到自然和对每个变量严格递增，Veblen 函数对自变量严格递增，对下标逐点弱增（高层枚举的类包含于低层枚举的类）。[Marcone–Montalbán 的 Veblen 函数定义](https://math.berkeley.edu/~antonio/papers/veblen.pdf)

对有限分裂编辑归纳。删除一项使自然和下降，在任意前缀后仍严格下降。减少主项的下标或参数后，即便复制任意有限份，较小权重的有限自然和仍小于原权重。由 `predecessor` 与 `actual-fs`，这已经处理了全部普通步和任意深处的第零次回灌。[编辑与实际分支](W4CriticalFrames.lagda.md)

再看裸叶上的正次回灌。由 `pred-suc` 写叶为 $\Omega_{\nu+1}$，置 $i=m(\nu)$、$j=m(\nu+1)>i$（语法后继追加一个正权重）。原叶分数为 $\kappa=\varphi_j(j+1)>j$。因为 $0<j$，$\kappa$ 是 ε 数，严格初段对自然和与后继封闭，且 $\varphi_i(\kappa)=\kappa$。初值 $m(\Omega_\nu)=\varphi_i(i+1)<\kappa$。若 $m(z)<\kappa$，则 $m(\psi_\nu z)<\kappa$。沿 `bare-chain` 归纳得任意次迭代的分数均严格小于原叶。由 `bare-fs` 与上下文的严格单调性，整个分支下降。可连续提出任意多个这样的请求，允许中间更换叶、改变外层深度或穿插普通步。

已有一个具体的 W4 三级返回值严格大于 $\Gamma_0$。从这个返回起步，维持“当前实际地址的值至少为当前分数”。给定一个允许的分支，新分数严格低于当前地址值。由实际一步前驱的秩公式，至少有一个真实下降地址的值覆盖新分数，取可用地址中编码最小者即可继续。这给出了经典地址策略，对允许的分支没有深度或迭代次数上限。此处比较的是分数，未要求原项的值事先已被 W4 覆盖。[三级返回的独立下界](W4PTOGamma.lagda.md#整个区间的序型) · [实际一步前驱](W4PTOAddresses.lagda.md)

## 一步就能检验的边界

取 $D(x)=\psi_0(x)$、$A(x)=D(\Omega_x)$、$a=\Omega_1$。原标准项 $A(a)$ 的第 1 枝恰为 $A(D(a))$，两端标准，右端严格小于左端。若 $D$ 在 $a$ 处不降低某个分数，且 $A$ 保留这一次比较，整个右端分数就至少等于左端。`no-monotone-score` 证明这样的打分无法给此真实参照分支严格下降；两条单调前提共同有实例（常零打分）。这定位到“一次塌缩的结果被当作下标”的那一步。W4 自身已有返回值参与下一轮选下标的动作；将两边这种动作在任意位置对齐，仍是待证的比较。[实际回灌与选枝](Reports-2026-11-18/attachments/B12Terminal.agda.txt)

对上面的特定 $m$，甚至同一项的各枝分数都在 $\Gamma_0$ 内共尾。由 `all-branches`，令 $x_0=1$、$x_{n+1}=A(x_n)$，各枝恰为 $x_{n+1}$。置 $a_n=m(x_n)$，有 $a_{n+1}>\varphi_{a_n}(0)$ 且 $a_{n+1}>a_n$，直接展开 $\Omega_{x_n}$ 的权重即得。故 $\sup_n a_n$ 至少为从零反复施加 $\alpha\mapsto\varphi_\alpha(0)$ 的上确界，即 $\Gamma_0$，反向由所有分数小于 $\Gamma_0$。在同一分数域内仅抬高该父项的分数也无法覆盖所有分支。[Veblen 对角迭代](https://math.berkeley.edu/~antonio/slides/NotreDameASL_H.pdf)

**余下关系的高度（经典纸面证明）。** 允许先走有限多个上述已处理步，再计一次活动 Ω 视图非裸叶的正次回灌。写 $r(t)$ 为这样跳转的秩，$v(t)$ 为原可数标准项的值，$R$ 为原 EBO。每个计数步严格降低 $r$；每个已处理步可接在以后任何跳转之前，故不会增加 $r$。因此 $\Gamma_0\cdot r(t)+m(t)$ 在每条原分支上严格下降。用原树的前驱秩公式归纳得
$$
r(t)\le v(t)\le\Gamma_0\cdot r(t)+m(t).
$$
左端来自每次跳转都确实降低原值。若所有 $r(t)+1$ 的上确界小于 $R$，在它与 $\Gamma_0$ 之上、$R$ 之下取一个 ε 数。该 ε 数的严格初段对加法与乘法封闭，右侧就会把全部 $v(t)$ 限在这个真初段，与共尾性矛盾。故余下跳转的总高度恰为 $R$。这里用了原 EBO 高于 $\Gamma_0$ 且是较小 ε 数的极限；$\Gamma_0<R$ 也由上述强临界阶段严格落在原有限塔项下得到。这个高度计算属于参照一侧；在 W4 上接收所有余下跳转的策略仍开放。[原初段与 ε 数](EboPTOSegments.lagda.md) · [只计回灌的秩论证](W4CriticalDescent.lagda.md)
