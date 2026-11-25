# 候选原型在 `no-stepU′-tw1` 那一点上的值

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 编译定理: `YiTFTw1` 否定 `StepU′ (tw 1)` 所用的那一点 (塔第 1 项孩子 2 朝第 1 层回灌), 原折叠与候选 (A) 的输出都不承载 ψ₁(Ω₁) (`no-out₀`, `no-outᴬ`), 候选 (A)+(B) 的输出承载 ψ₁(Ω₁) (`out-ab`).
> 另: `YiKTSlot` 的实际证据 `oᴱ` 下, (A) 让 `p*` 保留 (`kp*ᴱ`), `p₀` 不变 (`kp₀ᴱ`), `p*` 处 `KeepSpec′` 有居民 (`spec*ᴬ`, 对照 `YiKTSlot.no-spec*`).
> 不否定什么; 只是一点上的定理, 不给出 `StepU′ (tw 1)`, 也不涉及 `Cand` 与同步对象的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDXValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiDXFold
open import OCF.Lean.YiDXTest using (h₁; n1; c₂; p₁; g₁; z*; IsJust; module T₀; module Tᴬ; module Tᴬᴮ)
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiTFTw1 as TF
open import OCF.Lean.YiTFBound using (bS)
import OCF.Lean.YiSYReduce as SY
import OCF.Lean.YiKTSlot as KT
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-irrefl; <ᵀ-trans)
```

## 实际证据下的保留判定

```agda
kp*ᴱ : IsJust (kpᴬ (SY.a₁ (suc KT.one)) (proj₂ SY.oᴱ (suc KT.one)) KT.p* (ink self))
kp*ᴱ = tt

kp₀ᴱ : kpᴬ (SY.a₁ (suc KT.one)) (proj₂ SY.oᴱ (suc KT.one)) KT.p₀ (ink self) ≡ kp (SY.a₁ (suc KT.one)) (proj₂ SY.oᴱ (suc KT.one)) KT.p₀ (ink self)
kp₀ᴱ = refl
```

`YiKTSlot.no-spec*` 说原折叠在 `p*` (κ = 0, ν = 1) 处的证据为空; (A) 下同一个谓词有居民.

```agda
spec*ᴬ : KT.KeepSpec′ (SY.a₁ (suc KT.one)) (SY.h₁ KT.one) (E.𝟏 ∷ []) KT.p* []
  (kpᴬ (SY.a₁ (suc KT.one)) (proj₂ SY.oᴱ (suc KT.one)) KT.p* (ink self))
spec*ᴬ = inj₂ refl , GR.c0 refl , λ η c l → l
```

## 原折叠与 (A): 输出是 Ω₁ 树加可数尾巴

```agda
lv1 : L
lv1 = nd sS (λ _ → zero)

γ₁ : E.T
γ₁ = E.ψ (E.natT 1) (E.Ωt (E.natT 1)) ∷ []

γ₁-same : TF.γ₁ ≡ γ₁
γ₁-same = refl

out₀-same : T₀.out₁ ≡ TF.out₁
out₀-same = refl

no-out₀ : GR.R lv1 γ₁ T₀.out₁ → ⊥
no-out₀ = TF.no-out

Yᴬ : Tr⁺ zero
Yᴬ = FA.ψ (h₁ c₂) (proj₂ (Ok-tw 1) c₂) (proj₂ (rbᶻ (tw 1)) c₂) (B₀ (h₁ c₂)) zero (z≤ (h₁ c₂)) (Ωt zero)
  (up zero tt (suc z*) (z◃ z* ◃s))

outᴬ-form : Tᴬ.out₁ ≡ proj₁ (Ωt lv1 ⊞ Yᴬ)
outᴬ-form = refl

no-outᴬ : GR.R lv1 γ₁ Tᴬ.out₁ → ⊥
no-outᴬ r = <ᵀ-irrefl (<ᵀ-trans (bS r (TF.S-⊞ Yᴬ)) TF.ΩΩ<γ₁)
```

## (A)+(B): 输出承载 ψ₁(Ω₁)

`carry`: 对变量 Φ 陈述 (C-9): Φ 在零处是 Ω₁ 树, 后继处是 `next⁺`, 且单调, 则第 0 层树 c 承载 η 时 Φ c 承载 ψ₁(η). 对 `M⁰` 的推导归纳; `ar≤` 照搬 `YiKTSlot.ar≤`.

```agda
ψ1 : E.T → E.T
ψ1 η = E.ψ (E.natT 1) η ∷ []

q₁ : Pos lv1
q₁ = inj₂ (tt , inj₁ tt)

module M1 = H.Gen {Sig lv1} {GR.Low lv1} {λ _ → GR.R zero} {GR.Nu lv1}

cof-s : ∀ t → E.cof t ≡ E.c1 → E.cof (ψ1 t) ≡ E.cω
cof-s []       ()
cof-s (y ∷ ys) e rewrite e = refl

fsn-s : ∀ t → E.cof t ≡ E.c1 → ∀ n → E.fsn (ψ1 t) n ≡ replicate n (E.ψ (E.natT 1) (E.pred t))
fsn-s []       () n
fsn-s (y ∷ ys) e n rewrite e = refl

cof-l : ∀ t → E.cof t ≡ E.cω → E.cof (ψ1 t) ≡ E.cω
cof-l []       ()
cof-l (y ∷ ys) e rewrite e = refl

fsn-l : ∀ t → E.cof t ≡ E.cω → ∀ n → E.fsn (ψ1 t) n ≡ ψ1 (E.fsn t n)
fsn-l []       () n
fsn-l (y ∷ ys) e n rewrite e = refl

ar≤ : ∀ {a b} → a ≤ᵀ b → ψ1 a ≤ᵀ ψ1 b
ar≤ (inj₁ p)    = inj₁ (E.hd< (E.ar< p))
ar≤ (inj₂ refl) = inj₂ refl

carry : (Φ : Tr zero → Tr⁺ lv1) → proj₁ (Φ zero) ≡ proj₁ (Ωt lv1) → (∀ c → Φ (suc c) ≡ next⁺ (Φ c))
  → (∀ {x y} → zero ⊢ x ◃ y → lv1 ⊢ proj₁ (Φ x) ◃ proj₁ (Φ y))
  → ∀ {η c} → H.M⁰ η c → GR.R lv1 (ψ1 η) (proj₁ (Φ c))
carry Φ z s m (H.mz {x = x}) = M1.m-zl (λ c → proj₁ (Φ c)) m (subst (GR.R lv1 (ψ1 [])) (sym z) TF.low0) x
carry Φ z s m (H.m1 {t = t} {x = x} e r) =
  subst (λ Z → GR.R lv1 (ψ1 t) (proj₁ Z)) (sym (s x)) (M1.m-next (Φ x) (cof-s t e) (fsn-s t e) (carry Φ z s m r))
carry Φ z s m (H.mL {t = t} {x = x} e h) =
  H.mL (cof-l t e) (λ n → subst (λ u → GR.R lv1 u (proj₁ (Φ x))) (sym (fsn-l t e n)) (carry Φ z s m (h n)))
carry Φ z s m (H.mΩ {p = ()} _ _ _)
carry Φ z s m (H.mU {c = ()} _ _)
carry Φ z s m (H.mw r d)  = H.mw (carry Φ z s m r) (m d)
carry Φ z s m (H.mc le r) = H.mc (ar≤ le) (carry Φ z s m r)

node-ab : (Φ : Tr zero → Tr⁺ lv1) → proj₁ (Φ zero) ≡ proj₁ (Ωt lv1) → (∀ c → Φ (suc c) ≡ next⁺ (Φ c))
  → (∀ {x y} → zero ⊢ x ◃ y → lv1 ⊢ proj₁ (Φ x) ◃ proj₁ (Φ y))
  → GR.R lv1 γ₁ (proj₁ (next⁺ (Ω⁺ {S = Sig lv1} q₁ (λ c → next⁺ (Φ c)))))
node-ab Φ z s m = H.mw (H.mΩ refl (GR.c0 refl) (λ η c l → H.mw (carry Φ z s m l) (◃l zero))) (◃l zero)
```

实际的 Φ: (A)+(B) 的退路把孩子 2 的树 `up zero tt (suc z*)` 上折后, `z*` 的结点在第 1 层的地板槽位保留, 第 c 个分支是 `next⁺ (Φ c)`.

```agda
module Inst where
  o₁ : Ok (tw 1)
  o₁ = Ok-tw 1

  j₁ : L
  j₁ = at (tw 1) p₁

  w₁ : j₁ ≤ tw 1
  w₁ = posW (tw 1) p₁

  β₁ : Tr⁺ j₁
  β₁ = B₀ (tw 1) j₁ w₁

  d₁ : Dn (tw 1) (h₁ n1)
  d₁ = down (down stop c₂) tt

  X X₁ X₂ : Base (tw 1)
  X  i u = FAB.ψ (tw 1) o₁ (rbᶻ (tw 1)) (B₀ (tw 1)) i u (B₀ (tw 1) i u) zero
  X₁ i u = FAB.ψˡ (tw 1) o₁ X i u (X i u) (h₁ c₂) (down stop c₂) zero
  X₂ i u = FAB.ψˡ (tw 1) o₁ X₁ i u (X₁ i u) (h₁ n1) d₁ zero

  Φ : Tr zero → Tr⁺ lv1
  Φ c = FAB.ψˡ (tw 1) o₁ X₂ j₁ w₁ β₁ zero (down d₁ tt) c

  shape : Tᴬᴮ.out₁ ≡ proj₁ (next⁺ (Ω⁺ {S = Sig lv1} q₁ (λ c → next⁺ (Φ c))))
  shape = refl

out-ab : GR.R lv1 γ₁ Tᴬᴮ.out₁
out-ab = subst (GR.R lv1 γ₁) (sym Inst.shape)
  (node-ab Inst.Φ refl (λ c → refl) (FAB.monoˡ (tw 1) Inst.o₁ Inst.X₂ Inst.j₁ Inst.w₁ Inst.β₁ zero (down Inst.d₁ tt)))
```
