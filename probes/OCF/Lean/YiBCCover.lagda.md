# 换基证据对同步对象与真实链孩子的覆盖
编译定理，形状档，不读记号：同步对象 `nd (sΩ zero) a₁`（逐字是 `tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）与它的一切孩子 `a₁ c`（含真实链点 `Real.chain m` 与换基折叠自己的链 `chainᴮ m`）上，`rbO` 给的证据在每个 Ω 形状结点上都是 `just`（`full-sync`、`full-child`、`full-chain`）；任意树 t 读回的层号 `a ⊕ ↑ k t` 同样（`full-↑`），所以各站 `kl n` 与任意链点孩子都有（`full-kl`、`full-kl-child`）。
证据只读层号：`Rb` 是层号上的正递归，树只经 `↑` 进入，不变换任何树；同步对象顶上那一份证据在 `Fd` 与回灌里用不到（`top-idle`）；换基行走 `seen` 时，重建的层号 `j ⊕ offsets S c` 的满证据可由外层证据沿目标路径降下构造（`rb-row`、`full-row`；`YiBSFold` 那里现用 `rb-no`）。
不否定什么，不涉及值；变量 a 上给不出与换基行收到的块，见 `YiBCNeg`；与原定义的相等见 `YiBCSync`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBCCover where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiRKChain using (a₁; module Real)
```

## 满证据

`Full ℓ r`：r 在 ℓ 的每个 Ω 形状结点上是 `just`（换基行在那里不退回原行）。

```agda
IsJust : {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥

FullS : (s : Sh) (h : Ch s → L) → RbS s h → Set
FullS sS     h m = ⊤
FullS sL     h m = ⊤
FullS (sΩ k) h m = IsJust m

Full : (ℓ : L) → Rb ℓ → Set
Full zero     r = ⊤
Full (nd s h) r = FullS s h (proj₁ r) × ((c : Ch s) → Full (h c) (proj₂ r c))

full-rbO : (a b : L) (ra : Rb a) (oa : Ok a) (ob : OkO a b) → Full a ra → Full (a ⊕ b) (rbO a b ra oa ob)
full-rbO a zero          ra oa ob fa = fa
full-rbO a (nd sS h)     ra oa ob fa = tt , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa
full-rbO a (nd sL h)     ra oa ob fa = tt , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa
full-rbO a (nd (sΩ k) h) ra oa ob fa = tt , λ c → full-rbO a (h c) ra oa (proj₂ ob c) fa

full-tw : (n : ℕ) → Full (tw n) (rb-tw n)
full-tw zero    = tt
full-tw (suc n) = tt , λ c →
  full-rbO (tw n) (↑ (tw n) c) (rb-tw n) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c) (full-tw n)
```

任意树 t 读回的偏移：t 可以是折叠输出、上折或嵌入的树，证据都只经 `OkO↑` 读它的层号。

```agda
rb↑ : (a k : L) → Rb a → Ok a → Ok k → k ≤ a → (t : Tr k) → Rb (a ⊕ ↑ k t)
rb↑ a k ra oa ok v t = rbO a (↑ k t) ra oa (OkO↑ a k ok v t)

ok↑ : (a k : L) → Ok a → Ok k → k ≤ a → (t : Tr k) → Ok (a ⊕ ↑ k t)
ok↑ a k oa ok v t = Ok⊕ a (↑ k t) oa (OkO↑ a k ok v t)

full-↑ : (a k : L) (ra : Rb a) (oa : Ok a) (ok : Ok k) (v : k ≤ a) (t : Tr k) → Full a ra
  → Full (a ⊕ ↑ k t) (rb↑ a k ra oa ok v t)
full-↑ a k ra oa ok v t fa = full-rbO a (↑ k t) ra oa (OkO↑ a k ok v t) fa
```

## 同步对象与它的孩子

顶结点的证据地板是 `tw 1`，偏移是 `↑ (tw 1) (gₛ c)`；孩子 `a₁ c` 对一切 c（变量）有满证据。

```agda
gₛ : Tr zero → Tr (tw 1)
gₛ c = proj₁ (upz {s = sΩ zero} {h = h₁} c (Ωt (h₁ c)))

ℓₛ : L
ℓₛ = nd (sΩ zero) a₁

shape-s : tw 1 ⊕ ↑ (tw 1) (proj₁ (Ωt (tw 1))) ≡ ℓₛ
shape-s = refl

Sₛ : Schema zero a₁
Sₛ = schema (tw 1) (λ c → ↑ (tw 1) (gₛ c)) (Ok-tw 1) (ink self)
  (λ c → OkO↑ (tw 1) (tw 1) (Ok-tw 1) self (gₛ c)) (λ c → refl)

oₛ : Ok ℓₛ
oₛ = ok↑ (tw 1) (tw 1) (Ok-tw 1) (Ok-tw 1) self (proj₁ (Ωt (tw 1)))

rbₛ : Rb ℓₛ
rbₛ = rb↑ (tw 1) (tw 1) (rb-tw 1) (Ok-tw 1) (Ok-tw 1) self (proj₁ (Ωt (tw 1)))

top-s : proj₁ rbₛ ≡ just Sₛ
top-s = refl

floor-s : floor Sₛ ≡ tw 1
floor-s = refl

full-sync : Full ℓₛ rbₛ
full-sync = full-↑ (tw 1) (tw 1) (rb-tw 1) (Ok-tw 1) (Ok-tw 1) self (proj₁ (Ωt (tw 1))) (full-tw 1)

full-child : ∀ c → Full (a₁ c) (proj₂ rbₛ c)
full-child c = proj₂ full-sync c

child-form : ∀ c → a₁ c ≡ tw 1 ⊕ (zero ⊕ ↑ (h₁ c) (proj₁ (Ωt (h₁ c))))
child-form c = refl

top-L : ∀ f r → proj₁ (proj₂ rbₛ (lim f r)) ≡ tt
top-L f r = refl
```

`top-L`：ℕ 极限孩子（真实链点的顶就是 ℕ 极限，`Real.L₁`）的顶是 ℕ 极限形状，那里不要证据；证据在它里面的 Ω 形状结点上。

## 真实链点与换基折叠自己的链

`Real`（`YiRKChain`）的链用现行行；`Sync` 用换基折叠回灌。两条链的点都只作孩子编号进入层号。

```agda
module Chain (o : Ok ℓₛ) (B : Base ℓₛ) where
  open Real o B using (chain; chain₁)

  full-chain : ∀ m → Full (a₁ (chain m)) (proj₂ rbₛ (chain m))
  full-chain m = full-child (chain m)

  full-chain₁ : Full (a₁ chain₁) (proj₂ rbₛ chain₁)
  full-chain₁ = full-child chain₁

module Sync (o : Ok ℓₛ) (B : Base ℓₛ) (β : Tr⁺ zero) where
  g : Tr zero → Tr ℓₛ
  g z = proj₁ (upz {s = sΩ zero} {h = a₁} z (Ωt (a₁ z)))

  feedᴮ : Tr zero → Tr zero
  feedᴮ z = proj₁ (BS.ψ ℓₛ o rbₛ B zero (ink self) (B zero (ink self)) (g z))

  chainᴮ : ℕ → Tr zero
  chainᴮ = iter feedᴮ zero

  outᴮ : Tr zero → Tr⁺ zero
  outᴮ z = BS.ψ ℓₛ o rbₛ B zero (z≤ ℓₛ) β (g z)

  Fdᴮ : Tr⁺ zero
  Fdᴮ = BS.ψ ℓₛ o rbₛ B zero (z≤ ℓₛ) β (proj₁ (Ωt ℓₛ))

  full-chainᴮ : ∀ m → Full (a₁ (chainᴮ m)) (proj₂ rbₛ (chainᴮ m))
  full-chainᴮ m = full-child (chainᴮ m)
```

顶上那一份证据换成 `nothing`，`Fd` 与回灌逐字不变：这两处的路径在顶结点是 `inu` 与 `ink`，换基行只在 `inc` 路径上触发，而 Ω 树顶下的左加项是零。

```agda
  rb⁻ : Rb ℓₛ
  rb⁻ = nothing , proj₂ rbₛ

  top-idle : BS.ψ ℓₛ o rb⁻ B zero (z≤ ℓₛ) β (proj₁ (Ωt ℓₛ)) ≡ Fdᴮ
  top-idle = refl

  top-idle-feed : ∀ z → proj₁ (BS.ψ ℓₛ o rb⁻ B zero (ink self) (B zero (ink self)) (g z)) ≡ feedᴮ z
  top-idle-feed z = refl

syncᴮ : Tr⁺ zero
syncᴮ = BS.ψ₀ ℓₛ oₛ rbₛ (proj₁ (Ωt ℓₛ))
```

## 各站

`kl n` 照 `YiKSDesc.kl` 重写（为导入闭包干净）。第 n+1 站的孩子编号是第 `tw n` 层的任意树。

```agda
kl : ℕ → L
kl n = tw n ⊕ ↑ (tw n) (proj₁ (Ωt (tw n)))

ok-kl : (n : ℕ) → Ok (kl n)
ok-kl n = ok↑ (tw n) (tw n) (Ok-tw n) (Ok-tw n) self (proj₁ (Ωt (tw n)))

rb-kl : (n : ℕ) → Rb (kl n)
rb-kl n = rb↑ (tw n) (tw n) (rb-tw n) (Ok-tw n) (Ok-tw n) self (proj₁ (Ωt (tw n)))

full-kl : (n : ℕ) → Full (kl n) (rb-kl n)
full-kl n = full-↑ (tw n) (tw n) (rb-tw n) (Ok-tw n) (Ok-tw n) self (proj₁ (Ωt (tw n))) (full-tw n)

klc : (n : ℕ) → Tr (tw n) → L
klc n c = tw (suc n) ⊕ ↑ (tw (suc n))
  (proj₁ (upz {s = sΩ (tw n)} {h = λ d → tw n ⊕ ↑ (tw n) d} c (Ωt (tw n ⊕ ↑ (tw n) c))))

kl-shape : (n : ℕ) → kl (suc n) ≡ nd (sΩ (tw n)) (klc n)
kl-shape n = refl

kl-one : kl 1 ≡ ℓₛ
kl-one = refl

full-kl-child : (n : ℕ) (c : Tr (tw n)) → Full (klc n c) (proj₂ (rb-kl (suc n)) c)
full-kl-child n c = proj₂ (full-kl (suc n)) c

klᴮ : ℕ → Tr⁺ zero
klᴮ n = BS.ψ₀ (kl n) (ok-kl n) (rb-kl n) (proj₁ (Ωt (kl n)))
```

## 换基行里重建的层号

`route` 给 `inj₂` 时，目标 j 经孩子（不经下标层）落在偏移部分的结点上（`split⊑`），所以 j 的证据从外层证据沿路径降下（`rb⊑`），重建层号 `j ⊕ offsets S c` 的证据由 `rbO` 给出。

```agda
rb⊑ : (ℓ : L) → Rb ℓ → ∀ {j} → j ⊑ ℓ → Rb j
rb⊑ ℓ        r self      = r
rb⊑ (nd s h) r (inc c v) = rb⊑ (h c) (proj₂ r c) v
rb⊑ (nd s h) r (inu vs)  = rb⊑ (h (c₀ s)) (proj₂ r (c₀ s)) (vs (c₀ s))

full⊑ : (ℓ : L) (r : Rb ℓ) → Full ℓ r → ∀ {j} (v : j ⊑ ℓ) → Full j (rb⊑ ℓ r v)
full⊑ ℓ        r f self      = f
full⊑ (nd s h) r f (inc c v) = full⊑ (h c) (proj₂ r c) (proj₂ f c) v
full⊑ (nd s h) r f (inu vs)  = full⊑ (h (c₀ s)) (proj₂ r (c₀ s)) (proj₂ f (c₀ s)) (vs (c₀ s))

IsInj₂ : {A B : Set} → A ⊎ B → Set
IsInj₂ (inj₁ _) = ⊥
IsInj₂ (inj₂ _) = ⊤

split⊑ : (a b : L) (ob : OkO a b) {j : L} (v : j ≤ a ⊕ b) → IsInj₂ (split a b ob v) → j ⊑ a ⊕ b
split⊑ a zero          ob v         ()
split⊑ a (nd s h)      ob self      t = self
split⊑ a (nd s h)      ob (inc c v) t = inc c (split⊑ a (h c) (proj₂ ob c) v t)
split⊑ a (nd s h)      ob (inu vs)  t = inc (c₀ s) (split⊑ a (h (c₀ s)) (proj₂ ob (c₀ s)) (vs (c₀ s)) t)
split⊑ a (nd (sΩ k) h) ob (ink v)   ()

route⊑ : ∀ {k h} (S : Schema k h) j c′ (v : j ≤ h c′) → IsInj₂ (route S j c′ v) → j ⊑ h c′
route⊑ {h = h} S j c′ v t = subst (λ b → j ⊑ b) (sym (shape S c′))
  (split⊑ (floor S) (offsets S c′) (ok-offsets S c′) (subst (λ b → j ≤ b) (shape S c′) v) t)

rb-row : ∀ {k h} (r : (c : Tr k) → Rb (h c)) (S : Schema k h) j c′ (v : j ≤ h c′) → IsInj₂ (route S j c′ v)
  → Ok j → floor S ≤ j → (c : Tr k) → Rb (j ⊕ offsets S c)
rb-row r S j c′ v t oj u c = rbO j (offsets S c) (rb⊑ _ (r c′) (route⊑ S j c′ v t)) oj
  (raiseO (floor S) j (offsets S c) u (ok-offsets S c))

full-row : ∀ {k h} (r : (c : Tr k) → Rb (h c)) → ((c : Tr k) → Full (h c) (r c)) → ∀ (S : Schema k h) j c′ (v : j ≤ h c′)
  (t : IsInj₂ (route S j c′ v)) (oj : Ok j) (u : floor S ≤ j) (c : Tr k) → Full (j ⊕ offsets S c) (rb-row r S j c′ v t oj u c)
full-row r f S j c′ v t oj u c = full-rbO j (offsets S c) _ oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c))
  (full⊑ _ (r c′) (f c′) (route⊑ S j c′ v t))
```
