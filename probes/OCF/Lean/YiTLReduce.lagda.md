# 同步对象上的 Tail：归约到孩子层号上的一条保持，与它在现有框架里挡住的地方
验收文件（读记号）；编译定理：Leaf 在每个孩子层号 `a₁ c` 上无前提（`leaf-a₁`，前缀 `tw 1` 读作空）；`Tail`、`FirstMissing`、`Kᴱ′ 2` 归约到对孩子 c 一致的保持 `KeepOut`、`KeepFeed`，不对 m 归纳（`tail-fromᴱ`、`first-from-keep`、`k2′-from-keep`；单点形式 `first-fromᴱ`）；`FirstMissing` 是 `YiGTIndex.PresAt (a₁ c)` 的实例（`from-presᴱ`；经 `YiGTFold.pres` 归到 `Kit (a₁ (chain 2))`，`from-kitᴱ`；余下底的 `OK`、`PrefixU` 与出口条件）；槽位底高过链下标时链免费（`chain-below`）。
编译否定（只否定证据域）：`LowKeepˣ` 在每个 `a₁ c` 上为空（`no-lbl-a₁`）；最小表下 `IndexOK` 从任何 `tw 1 ⊕ Y` 到任何不含 Ω 的非零层号都为空（`no-index-⊕`、`no-index-a₁`、`no-index-top`）；第一个不可数槽位结点的孩子 `hh d z` 上下界读法的框架只在下标为空时有居民（`block-frame`），精确标签不存在（`no-lbl-hh`）。
不否定 `KeepOut`、`KeepFeed`、`FirstMissing`、`StepU′`、`SlotPres` 或别的比较表上的路线。入口：`first-from-keep`、`no-index-top`、`block-frame`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTLReduce where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiRWFold as F
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; tbᶻ)
open import OCF.Lean.YiSYReduce using (S; γ; a₁; h₁; oᴱ; Bᴱ)
open import OCF.Lean.YiSYFrame using (Kᴱ′)
open import OCF.Lean.YiGIInst using (betaᴱ)
open import OCF.Lean.YiNLCtx using (prefix; Top)
open import OCF.Lean.YiGLDom using (dz; dC; dom-top)
open import OCF.Lean.YiGLFrame using (Lbl)
open import OCF.Lean.YiGLOmega using (lt1)
open import OCF.Lean.YiGTNode using (NodeFrame; ChainAt)
open import OCF.Lean.YiGTGen using (weakenᴿ; closeᴿ)
open import OCF.Lean.YiLKSlot using (low-from)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLKIface using () renaming (feed to feedᴸ)
open import OCF.Lean.YiGTIndex using (PresAt; Kit; index-zero; IndexOK; CWReq; DWReq)
open import OCF.Lean.YiGTFold using (pres)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiHCCheck using (of⁰)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; tri; <→lt; cmpᵀ-refl)
import OCF.Lean.YiSYSmall as SM
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
```

## 对变量的归约

`Keep c w b`：孩子 c 的层号上，目标第 0 层、路径 w、起点 b 的折叠把 `GR.R` 的参照 s 送到 ψ₀(s) 的值下界。输出与回灌只差路径与起点（`out-form`、`feed-form` 是 `refl`）。`KeepOut`、`KeepFeed` 只对 Ω 树陈述。

```agda
LeafAt : (Tr zero → L) → Set
LeafAt a = ∀ {ν c} → GR.R zero ν c → Top (a c) (E.Ωt ν)

-- perf: C-9/C-1，层号、底、起点、Leaf 都是模块变量；链点 chain 2 只经本模块的名字出现（另写一个拼法与之比较会把 chain 2 化到弱头范式，8G 堆耗尽）。
module Gv (a : Tr zero → L) (o : Ok (nd (sΩ zero) a)) (B : Base (nd (sΩ zero) a)) (β : Tr⁺ zero) (lf : LeafAt a) where
  open SM.Gen a o B β public

  Fz : (c : Tr zero) → zero ≤ a c → Tr⁺ zero → Tr (a c) → Tr zero
  Fz c w b x = proj₁ (ψ (a c) (proj₂ o c) (rbᶻ (a c)) (D.dn B c) zero w b x)

  out-form : ∀ c → proj₁ (out c) ≡ Fz c (z≤ (a c)) β (proj₁ (Ωt (a c)))
  out-form c = refl

  feed-form : ∀ c → feed c ≡ Fz c (self ∙ proj₂ (proj₁ o) c) (B zero (ink self)) (proj₁ (Ωt (a c)))
  feed-form c = refl

  Keep : (c : Tr zero) → zero ≤ a c → Tr⁺ zero → Set
  Keep c w b = ∀ {s x} → GR.R (a c) s x → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (Fz c w b x)

  KeepOut KeepFeed : Tr zero → Set
  KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))
  KeepFeed c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (feed c)

  keep-out : ∀ c → Keep c (z≤ (a c)) β → KeepOut c
  keep-out c k m h = k m h

  keep-feed : ∀ c → Keep c (self ∙ proj₂ (proj₁ o) c) (B zero (ink self)) → KeepFeed c
  keep-feed c k m h = k m h

  out-low : (∀ c → KeepOut c) → ∀ γ′ → SM.Low-at γ′ (λ e → proj₁ (out e))
  out-low ko γ′ e m h = ko e (lf (of⁰ m)) h

  feed-low : (∀ c → KeepFeed c) → ∀ γ′ → SM.Low-at γ′ feed
  feed-low kf γ′ e m h = kf e (lf (of⁰ m)) h

  tail-from : (∀ c → KeepOut c) → (∀ c → KeepFeed c) → Tail
  tail-from ko kf m = feed-low kf _ , out-low ko _

  FirstFrom : Set
  FirstFrom = KeepOut (chain 2) → FirstMissing

  first-from : Two → FirstFrom
  first-from two ko h = ko (lf (of⁰ two)) h

  deriv-at : (c : Tr zero) → PresAt (a c) → OK (D.dn B c) → PrefixU (D.dn B c) []
    → GR.R zero (E.ψ [] [] ∷ []) (proj₁ β)
    → ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → GR.R zero (E.ψ [] s ∷ []) (proj₁ (out c))
  deriv-at c P gb pf mb m = P (proj₂ o c) (rbᶻ (a c)) (D.dn B c) gb [] pf zero (z≤ (a c)) []
    (index-zero (a c) (proj₂ o c) (rbᶻ (a c))) β mb m

  FromPres : Two → GR.R zero (E.ψ [] [] ∷ []) (proj₁ β) → Set
  FromPres two mb = (P : PresAt (a (chain 2))) (gb : OK (D.dn B (chain 2))) (pf : PrefixU (D.dn B (chain 2)) [])
    → H.Exᴴ (deriv-at (chain 2) P gb pf mb (lf (of⁰ two))) → FirstMissing

  from-pres : (two : Two) (mb : GR.R zero (E.ψ [] [] ∷ []) (proj₁ β)) → FromPres two mb
  from-pres two mb P gb pf ex h = H.exitᴴ (deriv-at (chain 2) P gb pf mb (lf (of⁰ two))) ex h

  FromKit : Two → GR.R zero (E.ψ [] [] ∷ []) (proj₁ β) → Set
  FromKit two mb = (kit : Kit (a (chain 2))) (gb : OK (D.dn B (chain 2))) (pf : PrefixU (D.dn B (chain 2)) [])
    → H.Exᴴ (deriv-at (chain 2) (pres (a (chain 2)) kit) gb pf mb (lf (of⁰ two))) → FirstMissing

  from-kit : (two : Two) (mb : GR.R zero (E.ψ [] [] ∷ []) (proj₁ β)) → FromKit two mb
  from-kit two mb kit = from-pres two mb (pres (a (chain 2)) kit)
```

## 同步对象：Leaf 与实例

孩子 c 的层号是 `tw 1 ⊕ ↑ (tw 1) (upz c (Ωt (h₁ c)))`；读回域 `YiGLDom.Dom` 里前缀 `tw 1` 取空读法 `dz`，于是 `GR.R zero ν c` 给出 Ω_{Ω_ν} 不高于孩子层号的 Ω 树。`S ν` 逐字就是 ψ₀(Ω_{Ω_ν})。

```agda
a₁-form : ∀ c → a₁ c ≡ tw 1 ⊕ ↑ (tw 1) (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c))))
a₁-form c = refl

S-form : ∀ ν → S ν ≡ E.ψ [] (E.Ωt (E.Ωt ν)) ∷ []
S-form ν = refl

leaf-a₁ : LeafAt a₁
leaf-a₁ {ν} {c} r = dom-top (dC (prefix (tw 1)) (tw 1) {t = []} {ν = E.Ωt ν}
  {y = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))} (dz (tw 1))
  (H.mU {t = []} {s = E.Ωt ν} {x = zero} {c = c} {y = proj₁ (Ωt (h₁ c))} {e = proj₂ (Ωt (h₁ c))} H.mz
    (dom-top (dC (prefix zero) zero {t = []} {ν = ν} {y = c} (dz zero) r))))

module Gvᴱ = Gv a₁ oᴱ Bᴱ (betaᴱ 2) leaf-a₁

-- perf: C-1，第 2 个链点的关系在本模块的拷贝里重建（与 `YiSYSmall.chain-two` 同一证明），不与 `Gᴱ.Two` 换写。
two′ : Gvᴱ.Two
two′ = Gvᴱ.chain₁ (Gvᴱ.sf-from-base SM.base-row₂)

first-fromᴱ : Gvᴱ.FirstFrom
first-fromᴱ = Gvᴱ.first-from two′

-- 同一模块对同一参数的两份拷贝：整个命题换写是便宜的，只是不能把 chain 2 单独换写。
same-first : Gvᴱ.FirstMissing → SM.Gᴱ.FirstMissing
same-first f = f

tail-fromᴱ : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → SM.Gᴱ.Tail
tail-fromᴱ = Gvᴱ.tail-from

k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2
k2′-from-keep ko kf = SM.k2′-from-tail (tail-fromᴱ ko kf)

first-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → SM.Gᴱ.FirstMissing
first-from-keep ko kf = SM.first-missingᴱ (tail-fromᴱ ko kf)
```

`FirstMissing` 作为 `PresAt` 的实例：目标第 0 层、一致路径、目标下标与前缀都为空，`IndexOK` 由 `index-zero` 给出；剩下底的 `OK`、`PrefixU`，以及出口条件 `Exᴴ`（对实例给出的推导）。

```agda
mb₂ : GR.R zero (E.ψ [] [] ∷ []) (proj₁ (betaᴱ 2))
mb₂ = H.pos⁰ (proj₁ (betaᴱ 2)) (proj₂ (betaᴱ 2))

from-presᴱ : Gvᴱ.FromPres two′ mb₂
from-presᴱ = Gvᴱ.from-pres two′ mb₂

from-kitᴱ : Gvᴱ.FromKit two′ mb₂
from-kitᴱ = Gvᴱ.from-kit two′ mb₂
```

## 精确标签在这些层号上不存在

`tw 1 ⊕ X` 的每条孩子链都落到 Ω 形状的 `tw 1`，所以没有 `Lbl`；`LowKeepˣ ℓ` 要 `Lbl ℓ λ′`，在一切 `a₁ c` 上为空。

```agda
no-lbl-tw1 : ∀ X {ν} → Lbl (tw 1 ⊕ X) ν → ⊥
no-lbl-tw1 zero ()
no-lbl-tw1 (nd sS h) (_ , q) = no-lbl-tw1 (h tt) q
no-lbl-tw1 (nd sL g) (_ , _ , _ , f) = no-lbl-tw1 (g 0) (proj₁ (proj₂ (f 0)))
no-lbl-tw1 (nd (sΩ k) h) ()

no-lbl-a₁ : ∀ c {ν} → Lbl (a₁ c) ν → ⊥
no-lbl-a₁ c = no-lbl-tw1 (↑ (tw 1) (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))))
```

## 第一个不可数槽位：孩子 c = d + 1 的顶结点

`a₁ (suc d)` 是 Ω 形状，下标层 `h₁ d`（d ≥ 1 时不可数）；目标第 0 层没有槽位，什么都不保留（`keep-zero`），输出与回灌的顶结点都走 `h₁ d` 上的链，链的一步把分支折到 `h₁ d`。分支所在的孩子 `hh d z` 是后继形状，唯一槽位是它的孩子 `tw 1 ⊕ …`（Ω 形状）。

```agda
keep-zero : ∀ {X x₀} (k : F.Keep zero X x₀) → k ≡ nothing
keep-zero nothing = refl

hh : (d : Tr zero) → Tr (h₁ d) → L
hh d z = tw 1 ⊕ (zero ⊕ nd sS (λ _ → zero ⊕ ↑ (h₁ d) z))

succ-shape : ∀ d → a₁ (suc d) ≡ nd (sΩ (h₁ d)) (hh d)
succ-shape d = refl

hh-shape : ∀ d z → hh d z ≡ nd sS (λ _ → tw 1 ⊕ (zero ⊕ (zero ⊕ ↑ (h₁ d) z)))
hh-shape d z = refl

no-lbl-hh : ∀ d z {ν} → Lbl (hh d z) ν → ⊥
no-lbl-hh d z (_ , q) = no-lbl-tw1 (zero ⊕ (zero ⊕ ↑ (h₁ d) z)) q

-- 顶槽位上链的一步：`YiSUIface.StepU′ (a₁ (suc d))` 在实际层号证据、最小表、继承底与顶槽位处的实例。
TightStep : Tr zero → Set
TightStep d = OK (D.dn Bᴱ (suc d)) → (t : E.T) → PrefixU (D.dn Bᴱ (suc d)) t
  → (a κ : E.T) → GR.Nu (a₁ (suc d)) (inj₁ (inj₁ tt)) κ → E.cof a ≡ E.cΩ κ
  → (g : Tr (h₁ d) → Tr (a₁ (suc d))) (n : ℕ) (z : Tr (h₁ d))
  → GR.R (h₁ d) (E.γT (t ++ a) κ n) z → GR.R (a₁ (suc d)) (E.fsT a (E.γT (t ++ a) κ n)) (g z)
  → GR.R (h₁ d) (E.γT (t ++ a) κ (suc n))
      (feedᴸ (a₁ (suc d)) (proj₂ oᴱ (suc d)) (rbᶻ (a₁ (suc d))) (D.dn Bᴱ (suc d)) (inj₁ (inj₁ tt)) g z)

tight-from : ∀ d → StepU′ (a₁ (suc d)) → TightStep d
tight-from d st gb t pf a κ nu e g n z = st (proj₂ oᴱ (suc d)) (rbᶻ (a₁ (suc d))) (D.dn Bᴱ (suc d)) gb t pf a (inj₁ (inj₁ tt)) κ nu e g n z
```

下界读法的框架：后继形状层号经任一非 `self` 路径折到 j 时，孩子槽位不保留，空读法 `[]` 是它的读法，框架要 `cmpᵀ 1 ν ≡ gt`，所以 ν 只能是空。`YiGLFrame.no-frame-S` 是 j 为孩子、路径 `inc tt self` 的情形。

```agda
gt1 : ∀ {ν} → E.cmpᵀ (E.sucT []) ν ≡ E.gt → ν ≡ []
gt1 {ν} e with tri ν (E.sucT [])
... | inj₁ lt = lt1 lt
... | inj₂ (inj₁ refl) = ⊥-elim (eq≢ (trans (sym (cmpᵀ-refl (E.sucT []))) e))
  where
  eq≢ : E.eq ≡ E.gt → ⊥
  eq≢ ()
... | inj₂ (inj₂ gt) = ⊥-elim (lt≢ (trans (sym (<→lt gt)) e))
  where
  lt≢ : E.lt ≡ E.gt → ⊥
  lt≢ ()

NotSelf : ∀ {b j ℓ} → Pth b j ℓ → Set
NotSelf self = ⊥
NotSelf _ = ⊤

succ-frame : (h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (w : j ≤ nd sS h) (ν : E.T) → NotSelf w
  → NodeFrame (nd sS h) o j w ν → ν ≡ []
succ-frame h o (inc tt v) ν _ fr = gt1 (fr (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl))
succ-frame h o (inu vs) ν _ fr = gt1 (fr (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl))
```

目标是不含 Ω 形状的层号（如 `h₁ d`）时，任何路径都不是 `self`，所以对实际路径（`oᴱ` 给出的）不必展开。

```agda
NoΩ : L → Set
NoΩ zero = ⊤
NoΩ (nd sS h) = NoΩ (h tt)
NoΩ (nd sL g) = ∀ n → NoΩ (g n)
NoΩ (nd (sΩ k) h) = ⊥

noΩ-z⊕ : ∀ X → NoΩ X → NoΩ (zero ⊕ X)
noΩ-z⊕ zero n = n
noΩ-z⊕ (nd sS h) n = noΩ-z⊕ (h tt) n
noΩ-z⊕ (nd sL g) n = λ m → noΩ-z⊕ (g m) (n m)
noΩ-z⊕ (nd (sΩ k) h) ()

noΩ-↑ : ∀ (x : Tr zero) → NoΩ (↑ zero x)
noΩ-↑ zero = tt
noΩ-↑ (suc x) = noΩ-↑ x
noΩ-↑ (lim f _) = λ n → noΩ-↑ (f n)

noΩ-h₁ : ∀ d → NoΩ (h₁ d)
noΩ-h₁ d = noΩ-z⊕ (↑ zero d) (noΩ-↑ d)

no-tw1 : ∀ X → NoΩ (tw 1 ⊕ X) → ⊥
no-tw1 zero ()
no-tw1 (nd sS h) n = no-tw1 (h tt) n
no-tw1 (nd sL g) n = no-tw1 (g 0) (n 0)
no-tw1 (nd (sΩ k) h) ()

not-self : ∀ {K} X → NoΩ K → (w : K ≤ nd sS (λ _ → tw 1 ⊕ X)) → NotSelf w
not-self X n self = no-tw1 X n
not-self X n (inc c v) = tt
not-self X n (inu vs) = tt

block-frame : ∀ d z (o : Ok (hh d z)) (w : h₁ d ≤ hh d z) (ν : E.T)
  → NodeFrame (hh d z) o (h₁ d) w ν → ν ≡ []
block-frame d z o w ν = succ-frame (λ _ → tw 1 ⊕ (zero ⊕ (zero ⊕ ↑ (h₁ d) z))) o w ν
  (not-self (zero ⊕ (zero ⊕ ↑ (h₁ d) z)) (noΩ-h₁ d) w)
```

## 链的一步经 `tw 1` 的指定孩子：最小比较表缺项

不含 Ω 形状、非零的目标层号（如 d ≠ 0 时的 `h₁ d`）在 `tw 1 ⊕ Y` 里只能经某个 `tw 1` 叶子的非零孩子到达；最小表 `rbᶻ` 在两个孩子都不是字面零时没有条目，`IndexOK` 的路线要条目，所以对任何路径、任何下标为空。于是 `pres` 不能给出顶结点那一步（`no-index-top`）。只否定这一证据域，不否定链的一步本身。

```agda
le-zero : ∀ {b j} → Pth b j zero → j ≡ zero
le-zero self = refl

cw-none : ∀ {A C : Set} (W : A ⊎ C) {F : A → Set} {G : C → Set}
  → (∀ x → F x → ⊥) → (∀ y → G y → ⊥) → CWReq W F G → ⊥
cw-none (inj₁ x) nf ng q = nf x q
cw-none (inj₂ y) nf ng q = ng y q

no-index-tw1 : ∀ {K} → NoΩ K → (K ≡ zero → ⊥) → (o : Ok (tw 1)) (w : K ≤ tw 1) (ν : E.T)
  → IndexOK (tw 1) o (rbᶻ (tw 1)) K w ν → ⊥
no-index-tw1 nK nz o self ν idx = nK
no-index-tw1 nK nz o (inc zero v) ν idx = nz (le-zero v)
no-index-tw1 nK nz o (inc (suc c) v) ν (_ , route) = route (suc c)
no-index-tw1 nK nz o (inc (lim f a) v) ν (_ , route) = route (lim f a)
no-index-tw1 nK nz o (inu vs) ν idx = nz (le-zero (vs zero))
no-index-tw1 nK nz o (ink v) ν idx = nz (le-zero v)

no-index-⊕ : ∀ Y {K} → NoΩ K → (K ≡ zero → ⊥) → (o : Ok (tw 1 ⊕ Y)) (w : K ≤ tw 1 ⊕ Y) (ν : E.T)
  → IndexOK (tw 1 ⊕ Y) o (rbᶻ (tw 1 ⊕ Y)) K w ν → ⊥
no-index-⊕ zero nK nz o w ν idx = no-index-tw1 nK nz o w ν idx
no-index-⊕ (nd s h) {K} nK nz o self ν idx = no-tw1 (nd s h) nK
no-index-⊕ (nd sS h) nK nz o (inu vs) ν (_ , route) =
  no-index-⊕ (h tt) nK nz (proj₂ o tt) (vs tt) ν (route tt)
no-index-⊕ (nd sL h) nK nz o (inu vs) ν (_ , route) =
  no-index-⊕ (h zero) nK nz (proj₂ o zero) (vs zero) ν (route zero)
no-index-⊕ (nd (sΩ k) h) nK nz o (inu vs) ν (_ , route) =
  no-index-⊕ (h zero) nK nz (proj₂ o zero) (vs zero) ν (route zero)
no-index-⊕ (nd sS h) nK nz o (inc tt v) ν (_ , route) = no-index-⊕ (h tt) nK nz (proj₂ o tt) v ν route
no-index-⊕ (nd sL h) nK nz o (inc n v) ν (_ , route) =
  cw-none (way (λ m → tw 1 ⊕ h m) (proj₁ o) n n)
    (λ u → no-index-⊕ (h n) nK nz (proj₂ o n) v ν)
    (λ u → no-index-⊕ (h n) nK nz (proj₂ o n) (v ∙ u) ν)
    (route n)
no-index-⊕ (nd (sΩ k) h) {K} nK nz o (inc c′ v) ν (_ , route) = at-diag c′ v (route c′)
  where
  at-diag : ∀ (d : Tr k) (v′ : K ≤ tw 1 ⊕ h d)
    → DWReq (tbᶻ k (λ c → tw 1 ⊕ h c) d d)
        (λ u → IndexOK (tw 1 ⊕ h d) (proj₂ o d) (rbᶻ (tw 1 ⊕ h d)) K (v′ ∙ u) ν)
        (λ u → IndexOK (tw 1 ⊕ h d) (proj₂ o d) (rbᶻ (tw 1 ⊕ h d)) K v′ ν) → ⊥
  at-diag zero v′ q = no-index-⊕ (h zero) nK nz (proj₂ o zero) (v′ ∙ self) ν q
  at-diag (suc x) v′ ()
  at-diag (lim f a) v′ ()
  at-diag (Ω p g) v′ ()
  at-diag (up x c y e) v′ ()
no-index-⊕ (nd (sΩ k) h) nK nz o (ink v) ν (_ , route) =
  no-index-⊕ (h zero) nK nz (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) ν (route zero)

no-index-a₁ : ∀ c {K} → NoΩ K → (K ≡ zero → ⊥) → (o : Ok (a₁ c)) (w : K ≤ a₁ c) (ν : E.T)
  → IndexOK (a₁ c) o (rbᶻ (a₁ c)) K w ν → ⊥
no-index-a₁ c = no-index-⊕ (↑ (tw 1) (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))))

no-index-top : ∀ d → (h₁ d ≡ zero → ⊥) → (o : Ok (a₁ (suc d))) (ν : E.T)
  → IndexOK (a₁ (suc d)) o (rbᶻ (a₁ (suc d))) (h₁ d) (ink self) ν → ⊥
no-index-top d nz o ν (_ , route) =
  no-index-⊕ (zero ⊕ nd sS (λ _ → zero ⊕ ↑ (h₁ d) zero)) (noΩ-h₁ d) nz (proj₂ o zero)
    (self ∙ proj₂ (proj₁ o) zero) ν (route zero)
```

## 不紧的链免费

链在槽位层上的点都不低于槽位的底（`ψ-⊵`）；底若不低于 Ω_ρ 且链的下标 κ 在项序上低于 ρ，γ 链的每一项都低于 Ω_ρ，`ChainAt` 无需 `StepU′`。所以要另证的只剩紧的链：κ 不低于槽位底能对上的读法。判断（未编译）：`a₁ (d+1)` 顶结点的链是紧的，κ 是 d 的读法，第 `h₁ d` 层的树低于 Ω_{d+1}；继承底若带更大的 ψ_κ 参照也能给出这条链，但那要实际站折到 `h₁ d` 的保持，仍是整体引理的实例。来源：`YiS2Chain.gamma-bound`、`actual-chain` 的一般形式。

```agda
γT-below : ∀ b μ ρ n → μ E.<ᵀ ρ → E.γT b μ n ≤ᵀ E.Ωt ρ
γT-below b μ ρ zero lt = inj₁ (E.hd< (E.lv< lt))
γT-below b μ ρ (suc n) lt = inj₁ (E.hd< (E.lv< lt))

chain-below : ∀ ℓ (o : Ok ℓ) r (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) (t a κ ρ : E.T) → κ E.<ᵀ ρ
  → GR.R (at ℓ p) (E.Ωt ρ) (proj₁ (B (at ℓ p) (posW ℓ p)))
  → ChainAt ℓ o r B t a p κ g
chain-below ℓ o r B p g t a κ ρ lt base n = low-from ℓ p
  (closeᴿ (at ℓ p) (γT-below (t ++ a) κ ρ n lt)
    (weakenᴿ (at ℓ p) base (ψ-⊵ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p))
      (g (iter (feedᴸ ℓ o r B p g) (fromBr ℓ p zero) n)))))
```

