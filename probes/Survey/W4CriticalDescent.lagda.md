# 只在规则 6 上下降的 EBO 验收

第四层。原可数标准项中，略去普通步、只数触发 γ 回灌的步，所得关系的高度仍恰为原 EBO（经典纸面证明）。Agda 判别实际基本列使用哪条规则，并把任意多个普通步接一次回灌压成一次真实地址下降。在已获值比较的初段可执行这一转换。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4CriticalDescent where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef hiding (lt; eq)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω)
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; <ᵀ-trans; c∷; c[])
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn)
open import OCF.Align.EboLeanTrian using (T-pred; t<)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
open import Survey.W4MultisetDescent using (Token; Step; start; choose)
open import WVOne using (T₀)

data Kind : Set where plain feedback : Kind

kind : ∀ {t} → Vω t → Kind
kind (ws v) = kind v
kind (wl _ v) = kind v
kind (w4 _) = plain
kind (w5 _ v) = kind v
kind (w6 _ _ _) = feedback

data Edge : Kind → T → T → Set where
  prev : ∀ {t} → cof t ≡ c1 → Edge plain t (pred t)
  at : ∀ {t} (e : cof t ≡ cω) n → Edge (kind (vω t e)) t (fsn t n)

smaller : ∀ {k t s} → NF t → Edge k t s → s <ᵀ t
smaller nt (prev e) = t< (T-pred _ e)
smaller nt (at e n) = t< (trian-fsn nt e n)

normal : ∀ {k t s} → NF t → Edge k t s → NF s
normal nt (prev e) = nf-pred nt
normal nt (at e n) = cl-fsn-NF nt e n

data Jump : T → T → Set where
  fire : ∀ {t s} → Edge feedback t s → Jump t s
  skip : ∀ {t u s} → Edge plain t u → Jump u s → Jump t s

strict : ∀ {t s} → NF t → Jump t s → s <ᵀ t
strict nt (fire e) = smaller nt e
strict nt (skip e j) = <ᵀ-trans (strict (normal nt e) j) (smaller nt e)

execute : ∀ {root t s} (nt : NF t) (ns : NF s) (ct : Ctbl t)
  (ht : HC t) (hs : HC s) → Jump t s → (p : Token root) → Rt ht ≼ proj₁ p →
  Σ (Token root) λ q → Step p q × Rt hs ≼ proj₁ q
execute nt ns ct ht hs j = choose nt ns ct ht hs (strict nt j)

import B12XRef as Ref
import B12EboRows as Rows
open import OCF.Align.EboLeanTree using (nf-tower)

first-tower : ∀ {s} (ns : NF s) (hs : HC s) → Jump (EBOψ 1) s →
  Σ (Token (Rows.child 1)) λ q → Step (_ , start) q × Rt hs ≼ proj₁ q
first-tower ns hs j = execute (nf-tower 1) ns (c∷ c[]) (Ref.H 1) hs j
  (_ , start) (proj₂ Rows.one)

-- 同一个 Ω₁ 回灌在不同的和前缀中连续被问到。
epsilon = ψ [] (Ωt (natT 1))
omega = ψ [] (natT 1)
once : Jump (epsilon ∷ epsilon ∷ []) (epsilon ∷ omega ∷ [])
once = fire (at refl 0)
again : Jump (epsilon ∷ omega ∷ []) (omega ∷ [])
again = skip (at refl 0) (fire (at refl 0))
```

**经典纸面证明。** 对原可数标准项 $t$，写 $v(t)$ 为参照树的值，$c(t)$ 为以 $t$ 起步、每次走一个 `Jump` 的良基关系秩。上文的 `strict` 和标准形保序定理保证此秩存在，且 $c(t)\le v(t)$。每个普通步 $t\to s$ 满足 $c(s)\le c(t)$，因为从 $s$ 开始的任一次跳转都能加上这个前缀。回灌步则满足 $c(s)<c(t)$。

给每个有限语法项赋一个独立的次要度量 $m<\varepsilon_0$。空列取零，列取各主项权重的有限自然和，$\psi_u(a)$ 的权重为 $\omega^{m(u)\mathbin{\#}m(a)+1}$。后继项取前驱会删去末尾的 $1$（`pred-suc`）。规则 4 因参数减小而降低指数，有限份较小幂之和仍小于原幂。和前缀、下标位置、参数位置都是严格单调的上下文，所以 `ws`、`wl`、`w5` 逐层传递下降。沿 `Vω` 归纳即知所有普通步都严格降低 $m$；`fω-eq` 将这些子句对应到原基本列。这也说明为何回灌必须在内部触发时计数。[基本列的视图](../OCF/Align/EboLeanView.lagda.md)

于是 $\varepsilon_0\cdot c(t)+m(t)$ 在原基本列的每条边上严格下降。参照树的后继值为前驱值加一，极限值为各枝值的上确界。沿其证书归纳得到
$$
c(t)\ \le\ v(t)\ \le\ \varepsilon_0\cdot c(t)+m(t).
$$
取 $C=\sup_t(c(t)+1)$。所有可数标准项的值严格低于 $R$ 且对 $R$ 共尾，故 $C\le R$。若 $C<R$，在 $R$ 以下取一个 ε 数 $e>\max(C,\varepsilon_0)$。这样的 $e$ 存在，因为 $R$ 是严格较小 ε 数的极限，且 $\varepsilon_0<R$。$e$ 的严格初段对加法与乘法封闭，故全部 $v(t)<e$，与共尾性矛盾。于是 **$C=R$**。[原初段与 ε 封闭](EboPTOSegments.lagda.md)

由此得到整树的单一充分条件。给每个起始项一个 W4 可达地址，每当对方指定从当前项出发的一次 `Jump`，可依历史选一次真实地址下降，继续应对以后所有跳转。对跳转秩归纳即有 $c(t)\le Y$。由 $R$ 为极限得到 $R\le Y$。也可为每个起始项选定一个有限深度的分裂状态，得到 $C\le\varepsilon^+(Y)$，同样推出 $R\le Y$。条件在参照树上有实例，起始时用 $v(t)<R$ 的已知比较，随后沿 `choose` 传递。W4 的局部实例见上文及下节；全域所需的是在尚无 $v(t)\le Y$ 证据时选择回灌地址。

**第零座塔的直接实例。** 令 $e=\psi_0(\Omega_1)$，$b=\psi_0(\Omega_1+1)$。从 $b$ 出发的第一步是普通步，选取 $k$ 份 $e$。以后每个可达项形为 $e^k$（并列 $k$ 份）接一个仅含零下标的尾项。尾项非空时，后继删末项，极限只从末项进入。对这样的尾项沿视图归纳，正下标叶和 Ω 共尾视图均无实例，规则 4 的复制与规则 5 的递归都保持零下标。尾项为空时，末一个 $e$ 的每个分支都消耗一次回灌，并产生仅含零下标的尾项。因而每次跳转恰好消耗一份 $e$。反向，反复选择第零枝，$e$ 先变为 $\omega$，再经一次普通步消失；有非空零下标尾项时，反复取零枝或前驱，由 $m$ 的严格下降终会清空。因此从 $k$ 份 $e$ 接这种尾项出发的跳转秩恰为 $k$，从 $b$ 出发恰为 $\omega$。

W4 整树第零枝的值为 $\omega$，其第 $j$ 枝为 $j+1$。从 $b$ 出发第一次回灌后若剩 $j$ 份，选择该枝并取前驱，后续每消耗一份就取一次自然数前驱。这给出覆盖 $b$ 全部可达跳转的策略。原值 $v(b)=\varepsilon_0\cdot\omega$（规则 4 对 $e$ 取有限份，$e$ 的基本列为有限 ω 幂塔），严格大于所用的整座塔。这里用到的分支选择无需先有 $v(b)\le\omega$。两条基本列公式与实际地址族如下。对任意跳转的可执行策略见[逐步更新证书](W4CriticalStrategy.lagda.md)。

```agda
open import Data.Nat.Base using (zero; suc)
open import Data.List.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong; trans)
import OCF.Align.Level as L
import Survey.W4PTOAddresses as A
open import WVOne using (read)
import W4Fold as Fold
import W4Block as W
import W4Ops as O

copies-entry : ∀ n → fsn (ψ [] (sucT (Ωt (natT 1))) ∷ []) n ≡ replicate n epsilon
copies-entry n = refl

pureTower : ℕ → T
pureTower zero = natT 1
pureTower (suc n) = ψ [] (pureTower n) ∷ []

gamma-one : ∀ n → γT (Ωt (natT 1)) [] n ≡ pureTower n
gamma-one zero = refl
gamma-one (suc n) = cong (λ t → ψ [] t ∷ []) (gamma-one n)

spent : ∀ n → fsn (epsilon ∷ []) n ≡ pureTower (suc n)
spent n = cong (λ t → ψ [] t ∷ []) (gamma-one n)

finite : ℕ → W.Tr W.zero
finite zero = W.zero
finite (suc n) = W.suc (finite n)

add-one : ∀ n → finite 1 O.+ finite n ≡ finite (suc n)
add-one zero = refl
add-one (suc n) = cong W.suc (add-one n)

iter-one : ∀ n → W.iter (finite 1 O.+_) (finite 1) n ≡ finite (suc n)
iter-one zero = refl
iter-one (suc n) = trans (cong (finite 1 O.+_) (iter-one n)) (add-one (suc n))

numeral : ∀ n → read (finite n) ≡ L.natᶜ n
numeral zero = refl
numeral (suc n) = cong L.suc (numeral n)

zero-tower : ∀ j → A.Hop (Rows.child 0) (L.natᶜ j)
zero-tower j = A.via j (subst (λ x → A.Hop x (L.natᶜ j))
  (sym (trans (cong read (iter-one j)) (numeral (suc j)))) A.pred)

enter : ∀ j → A.Hop (read Fold.EBOᶜ) (L.natᶜ j)
enter j = A.via 0 (zero-tower j)

consume : ∀ j → A.Hop (L.natᶜ (suc j)) (L.natᶜ j)
consume j = A.pred
```

## 每一个可数标准项的精确秩

```agda
open import Data.Empty using (⊥; ⊥-elim)
import Survey.EboPTOFinite as Fin
open import OCF.Align.EboLeanView using (VΩ; ωs; ωr; ωl; ωp)

no-omega : ∀ {t μ} → Fin.Indices 0 t → VΩ t μ → ⊥
no-omega (Fin.cons {j = suc _} () _ _)
no-omega (Fin.cons _ _ tail) (ωs v) = no-omega tail v
no-omega (Fin.cons {j = zero} _ _ _) (ωr ())
no-omega (Fin.cons {j = zero} _ _ _) (ωl () v)
no-omega (Fin.cons _ arg _) (ωp _ _ v) = no-omega arg v

quiet : ∀ {t} → Fin.Indices 0 t → (v : Vω t) → kind v ≡ plain
quiet (Fin.cons {j = suc _} () _ _)
quiet (Fin.cons _ _ tail) (ws v) = quiet tail v
quiet (Fin.cons {j = zero} _ _ _) (wl () v)
quiet _ (w4 _) = refl
quiet (Fin.cons _ arg _) (w5 _ v) = quiet arg v
quiet (Fin.cons _ arg _) (w6 _ _ v) = ⊥-elim (no-omega arg v)

below-epsilon : ∀ {t} → NF t → Ctbl t → t <ᵀ (epsilon ∷ []) →
  (v : Vω t) → kind v ≡ plain
below-epsilon nt ct small = quiet (Fin.recover 0 nt ct small)
```

**经典纸面证明。** 唯一写 $v(t)=\varepsilon_0\cdot q(t)+r(t)$，其中 $r(t)<\varepsilon_0$。前文的上界与 $m(t)<\varepsilon_0$ 已给出 $q(t)\le c(t)$。反向只须查一次回灌为何严格降低商。

设 $J$ 是正规零下标主项按原主项序组成的良序。可数标准项恰为 $J$ 的有限非增列。标准形的守卫逐个检查主项，列上仅要求相邻有序。按每个主项在 $J$ 内的位次 $\delta$ 赋幂 $\omega^\delta$，再按原次序求和；由康托标准形，这给出到 $\omega^{\mathrm{otp}(J)}$ 的序同构。原值等于前驱初段序型，因此上述赋值逐项就是 $v$。特别地，单主项的值一定是 ω 的幂。[标准形定义](../OCF/Align/EboLeanBase.lagda.md) · [前驱初段标定](EboPTOSegments.lagda.md)

若 $t$ 发生回灌，沿和的末尾进入的最后一个主项单独求值时也发生回灌（`ws`）。由 `below-epsilon`，它的值至少为 $\varepsilon_0$。其值是一个 $\omega^\delta\ge\varepsilon_0=\omega^{\varepsilon_0}$，因而是 $\varepsilon_0$ 的左倍数（写 $\delta=\varepsilon_0+\eta$）。前面所有主项的值都至少与它相等，同样是左倍数。故回灌发生时 $r(t)=0$。每个原基本列分支严格小于 $t$，于是这一步严格降低 $q$。先走的普通步至多保持 $q$。沿跳转归纳得到 $c(t)\le q(t)$，合并即得 **$c(t)=q(t)$**。

在经典集合论中，$c(t)\le Y$ 也足以从 W4 根应对 $t$ 的每次跳转。若已在值为 $y\ge c(t)$ 的地址，对方跳到 $s$，则 $c(s)<y$，由真实一步子秩加一的上确界公式可选一个子地址，其值至少为 $c(s)$。同一推理在新地址继续。此处从序数比较选地址是经典存在性；以 `choose` 输入实际比较证据时才已有可执行程序。

这给出 W4 单地址模拟的精确范围。以 $K$ 记独立标准塔的上确界，已有 $\omega<K$，且 $K$ 的严格初段对取下一个 ε 数封闭，故 $\varepsilon_0<K$。已有的左乘定理在排中律下给 $\varepsilon_0\cdot Y=Y$。于是对每个原可数标准项，W4 根能够应对它的全部跳转，当且仅当 **$v(t)<Y+\varepsilon_0$**。在高于 $\varepsilon_0$ 的 ε 数处，商就是原数，因此这些值上的难点完整保留。整树验收现在可以集中于回灌之间的可达路径，仍须构造在全部起始项上成立的实际策略。[标准塔的严格内点](Reports-2026-11-19/attachments/B26PPart.agda.txt) · [ε 封闭](Reports-2026-11-18/attachments/B22TowerCut.agda.txt) · [W4 的左乘定理](Reports-2026-11-19/attachments/B29Left.agda.txt)

**直接按回灌红式派地址的检验。** 若只读被展开的主项和共尾下标，就会在连续两次回灌上给出同一秩。下面的否定包括任意以这两项为自变量的零层树值函数。带剩余和前缀或带运行历史的策略仍可使用第零塔的自然数前驱。

```agda
open import Data.Maybe.Base using (Maybe; just; nothing)
open import OCF.Align.TightValBase using (s≼-irrefl)

redex : ∀ {t} → Vω t → Maybe (PT × T)
redex (ws v) = redex v
redex (wl _ v) = redex v
redex (w4 _) = nothing
redex (w5 _ v) = redex v
redex (w6 {u = u} {b} {ν} _ _ _) = just (ψ u b , ν)

edge-redex : ∀ {k s t} → Edge k s t → Maybe (PT × T)
edge-redex (prev _) = nothing
edge-redex (at {t} e n) = redex (vω t e)

event : ∀ {s t} → Jump s t → Maybe (PT × T)
event (fire e) = edge-redex e
event (skip _ j) = event j

same-event : event once ≡ event again
same-event = refl

no-redex-rank : (rank : Maybe (PT × T) → T₀) →
  (∀ {t s u} (p : Jump t s) (q : Jump s u) →
    L.suc (rank (event q)) ≼ rank (event p)) → ⊥
no-redex-rank rank law = s≼-irrefl (rank (event once)) (law once again)
```
