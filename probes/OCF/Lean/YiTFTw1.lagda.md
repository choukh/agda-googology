# 塔第 1 项上链的一步: 表缺项的退路把孩子 2 的读法折没了
验收文件 (读记号); 编译否定: `no-stepU′-tw1 : StepU′ (tw 1) → ⊥`, `no-wholeU-tw1 : WholeU (tw 1) → ⊥`; 前提全部实填 (最小表 `rbᶻ`, 标准底, `PrefixU` 由 `leafC` 给出).
位置: tw 1 孩子 2 里第 1 层的槽位, 分支是孩子 2 的直接嵌入 c+1; 折到第 1 层时表在 (2, 2) 缺项走退路, 输出是 Ω₁ 树加可数尾巴 (`out-form`), 读法低于 Ω₁+Ω₁ (`YiTFBound.bS`), 记号要 ψ₁(Ω₁).
第 0 步的局部事实: tw 1 叶子上槽位在孩子里时, 任何证据、任何非零无 Ω 目标的路径都走链 (`kp-leaf`); 同步对象参照的第 1 项在第 1 层保留 (`ref₁-keep`).
否定的是 GR.R 量化分支的接口, 不是实际对象的值. 实际继承底上的 `TightStep` 见 `YiTFTight`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTFTw1 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ₀ʳ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiSUIface using (StepU′; PrefixU; WholeU)
open import OCF.Lean.YiLKIface using (feed; OK)
open import OCF.Lean.YiLLCheck using (leafC)
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ≤)
open import OCF.Lean.YiKVRel using (one; ⊴r)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (<ᵀ-irrefl; <ᵀ-trans)
open import OCF.Lean.YiTFBound

open import Data.Maybe using (nothing)
open import OCF.Lean.YiRWFold using (kp)
open import OCF.Lean.YiTLReduce using () renaming (NoΩ to NoΩᵀ)
```

## 第 0 步: 树走链, 记号保留

```agda
le-zero : ∀ {b j} → Pth b j zero → j ≡ zero
le-zero self = refl

kp-leaf : ∀ {K} → NoΩᵀ K → (K ≡ zero → ⊥) → (o : Ok (tw 1)) (c : Tr zero) (t : Pos⁼ (zero ⊕ ↑ zero c))
  (w : K ≤ tw 1) → kp (tw 1) o (inj₂ (c , t)) w ≡ nothing
kp-leaf nK nz o c t self = ⊥-elim nK
kp-leaf nK nz o c t (inc c′ v) = refl
kp-leaf nK nz o c t (inu vs) = ⊥-elim (nz (le-zero (vs zero)))
kp-leaf nK nz o c t (ink v) = ⊥-elim (nz (le-zero v))

ref₁ : E.T
ref₁ = E.γT (E.Ωt (E.Ωt (E.natT 2))) (E.natT 1) 1

ref₁-form : ref₁ ≡ E.ψ (E.natT 1) (E.Ωt (E.Ωt (E.natT 1))) ∷ []
ref₁-form = refl

ref₁-cof : E.cof ref₁ ≡ E.cΩ []
ref₁-cof = refl

ref₁-keep : ∀ η → E.fsT ref₁ η ≡ E.ψ (E.natT 1) (E.Ωt η) ∷ []
ref₁-keep η = refl
```

## 前提: 标准底在 tw 1 的一切槽位层号上满足 `PrefixU`

槽位层号不含 Ω 形状, Leaf 用 `YiLLCheck.leafC`.

```agda
noΩ-z⊕ : ∀ X → NoΩ X → NoΩ (zero ⊕ X)
noΩ-z⊕ zero n = n
noΩ-z⊕ (nd sS h) n = noΩ-z⊕ (h tt) n
noΩ-z⊕ (nd sL g) n = λ m → noΩ-z⊕ (g m) (n m)
noΩ-z⊕ (nd (sΩ k) h) ()

noΩ-↑ : ∀ (x : Tr zero) → NoΩ (↑ zero x)
noΩ-↑ zero = tt
noΩ-↑ (suc x) = noΩ-↑ x
noΩ-↑ (lim f _) = λ n → noΩ-↑ (f n)

mutual
  nu-rd : ∀ ℓ (p : Pos ℓ) {ν} → GR.Nu ℓ p ν → GR.Rd (at ℓ p) ν
  nu-rd (nd s h) (inj₂ (c , t)) r = nu-rd⁼ (h c) t r
  nu-rd (nd (sΩ k) h) (inj₁ t) r = nu-rd⁼ k t r

  nu-rd⁼ : ∀ a (t : Pos⁼ a) {ν} → GR.Nu⁼ a t ν → GR.Rd (proj₁ (sl⁼ a t)) ν
  nu-rd⁼ a (inj₁ _) r = r
  nu-rd⁼ a (inj₂ p) r = nu-rd a p r

noΩ-at : (p : Pos (tw 1)) → NoΩ (at (tw 1) p)
noΩ-at (inj₁ (inj₁ tt)) = tt
noΩ-at (inj₂ (c , t)) = NoΩ≤ (posW⁼ (zero ⊕ ↑ zero c) t) (noΩ-z⊕ (↑ zero c) (noΩ-↑ c))

pf : PrefixU (B₀ (tw 1)) []
pf p ν nu = leafC (at (tw 1) p) (noΩ-at p) (nu-rd (tw 1) p nu)

okB : OK (B₀ (tw 1))
okB i u = ⊴r
```

## 实例与否定

```agda
c₂ : Tr zero
c₂ = suc (suc zero)

p₁ : Pos (tw 1)
p₁ = inj₂ (c₂ , inj₂ (inj₂ (tt , inj₁ tt)))

g₁ : Tr one → Tr (tw 1)
g₁ c = up zero c₂ (up zero tt (suc c) (z◃ c ◃s)) (◃u zero tt (suc c) (z◃ c ◃s))

cΩ₁ : Tr one
cΩ₁ = proj₁ (Ωt one)

rd1 : GR.Rd one (E.natT 1)
rd1 = GR.ca (inj₂ (refl , GR.c0 refl))

low0 : GR.R one (E.Ωt (E.natT 1)) cΩ₁
low0 = leafC one tt rd1

rg : ∀ {η c} → GR.R one η c → GR.R (tw 1) η (g₁ c)
rg r = H.mU H.mz (H.mU H.mz (H.mw r ◃s))

a₂ : E.T
a₂ = E.Ωt (E.natT 2)

γ₁ : E.T
γ₁ = E.ψ (E.natT 1) (E.Ωt (E.natT 1)) ∷ []

ΩΩ<γ₁ : ΩΩ <ᵀ γ₁
ΩΩ<γ₁ = hd< (ar< []<)

S-⊞ : (Y : Tr⁺ zero) → S (proj₁ (Ωt one ⊞ Y))
S-⊞ (y , _) = S-plus y

out₁ : Tr one
out₁ = feed (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) p₁ g₁ cΩ₁

out-form : out₁ ≡ proj₁ (Ωt one ⊞ ψ₀ʳ (zero ⊕ ↑ zero c₂) (proj₂ (Ok-tw 1) c₂) (proj₂ (rbᶻ (tw 1)) c₂)
  (up zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s)))
out-form = refl

s-out : S out₁
s-out = S-⊞ (ψ₀ʳ (zero ⊕ ↑ zero c₂) (proj₂ (Ok-tw 1) c₂) (proj₂ (rbᶻ (tw 1)) c₂) (up zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s)))

no-out : GR.R one γ₁ out₁ → ⊥
no-out r = <ᵀ-irrefl (<ᵀ-trans (bS r s-out) ΩΩ<γ₁)

no-stepU′-tw1 : StepU′ (tw 1) → ⊥
no-stepU′-tw1 st = no-out (st (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) okB [] pf a₂ p₁ (E.natT 1) rd1 refl g₁ 0 cΩ₁ low0 (rg low0))

no-wholeU-tw1 : WholeU (tw 1) → ⊥
no-wholeU-tw1 wh = no-out (wh (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) okB [] a₂ p₁ (E.natT 1) rd1 refl g₁ (λ η c r → rg r) 0 cΩ₁ low0)
```
