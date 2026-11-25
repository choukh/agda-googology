# `kp` 的出口换成证据形式; 一致路径没有分叉; R80 落在哪个出口

> 判决: 编译定理, 无前提, 不读记号, 不改树、折叠、合法性. `kexit`: `YiCMExit.kp-exit` 换成以 "kp 返回保留" 为证据的三种出口 (`KExit`), 保留时层号不变 (`kp-lvl`, 由 `YiQDFold.kp-good`). 目标路径一致 (只由 `self`, `inu` 组成, 如 `lift`, `z≤`) 时出口只有保留与同层或高于 (`kp-uni`, `uni-notX`).
> R80 (下标侧槽位, 一致路径, 推进孩子 zero): 塔各项上推进是恒等, 即下标层上的判定 (`r80-tw`); 一般 Ω 形状层号上推进与目标在孩子 zero 里分叉时给 `nothing` (`drop-r80`); 读回域里的实例在塔第 3 项的一个孩子层号上 (`r80-cross`), 槽位层号是目标的真槽位层号 (`r80-lit`). 目标到自己真槽位的层号没有字面路径 (`no-cyc`, `apart`).
> 不否定什么: 没有值的定理; 实际折叠是否走到 `r80-cross` 的路径没有查. 入口: `kexit`, `kp-uni`, `apart`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXTKp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep; mapK; kp; kp⁼; node⁺)
import OCF.Lean.YiCMExit as CM
open import OCF.Lean.YiCMCross using (Cross; xuc; cross-drop)
open import OCF.Lean.YiQDFold using (GoodK; kp-good)
open import OCF.Lean.YiGIBlock using (slTᵍ)
```

## 证据形式的出口

`EvK j a o p w` 与 `YiBLFold.Main.Evᴮ`, `YiBLFold.Aux.Evᴬ` (`rbs` 状态), `YiQDFold.QDPack.Kept` 逐字同形.

```agda
EvK : (j a : L) → Ok a → Pos a → j ≤ a → Set
EvK j a o p w = Σ (Pos j) λ q → Σ (Br j q → Br a p) λ cv → Σ (cv (fromBr j q zero) ≡ fromBr a p zero) λ e
  → kp a o p w ≡ just (q , cv , e)

data KExit (j a : L) (o : Ok a) (p : Pos a) (w : j ≤ a) : Set where
  kept  : EvK j a o p w → KExit j a o p w
  high  : (EvK j a o p w → ⊥) → j ≤ at a p → KExit j a o p w
  cross : (EvK j a o p w → ⊥) → ∀ {k′} {h′ : Tr k′ → L} (c c′ : Tr k′) → at a p ≤ h′ c → j ≤ h′ c′ → KExit j a o p w

jn : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
jn ()

conv : ∀ {j} a o p (w : j ≤ a) (m : Keep j (Br a p) (fromBr a p zero)) → kp a o p w ≡ m → CM.Exit (at a p) m → KExit j a o p w
conv a o p w _ eq (CM.kept q cv e _)  = kept (q , cv , e , eq)
conv a o p w _ eq (CM.high u)         = high (λ { (_ , _ , _ , eq′) → jn (trans (sym eq′) eq) }) u
conv a o p w _ eq (CM.cross c c′ u v) = cross (λ { (_ , _ , _ , eq′) → jn (trans (sym eq′) eq) }) c c′ u v

kexit : ∀ {j} a o p (w : j ≤ a) → KExit j a o p w
kexit a o p w = conv a o p w (kp a o p w) refl (CM.kp-exit a o p w)

kp-lvl : ∀ {j} a o p (w : j ≤ a) q cv e → kp a o p w ≡ just (q , cv , e) → at j q ≡ at a p
kp-lvl a o p w q cv e eq = proj₁ (subst (GoodK (at a p) (slTᵍ a p)) eq (kp-good a o p w))
```

无证据时结点的输出是链的部分和极限; 给定链点到极限的支配 (`YiQDFold.AddR.chain-dom` 一类), 得到 `YiQDIface.Chain` 的形状. 对任何关系 `Rj`.

```agda
chainK : ∀ {j} {Tᵣ : Set} (Rj : Tᵣ → Tr j → Set) {X : Set} {x₀ : X} (m : Keep j X x₀) (G′ : X → Tr⁺ j) (S′ : X → X)
  → (∀ k {τ} → Rj τ (proj₁ (G′ (iter S′ x₀ k))) → Rj τ (proj₁ (node⁺ {x₀ = x₀} nothing G′ S′)))
  → ((Σ (Pos j) λ q → Σ (Br j q → X) λ cv → Σ (cv (fromBr j q zero) ≡ x₀) λ e → m ≡ just (q , cv , e)) → ⊥)
  → Σ (ℕ → X) λ z → ∀ k {τ} → Rj τ (proj₁ (G′ (z k))) → Rj τ (proj₁ (node⁺ m G′ S′))
chainK Rj (just (q , cv , e)) G′ S′ cd ne = ⊥-elim (ne (q , cv , e , refl))
chainK Rj {x₀ = x₀} nothing G′ S′ cd ne = (λ k → iter S′ x₀ k) , cd
```

## 一致路径

`Uni w`: w 只由 `self` 与 `inu` 组成. 这时 `kp` 的递归只走 `self`, `inu` 两种路径的子句, 不到 R77 (`inc`) 与 R79, 出口没有分叉 (`Exit₂`).

```agda
data Uni {j : L} : {a : L} → j ≤ a → Set where
  u-self : Uni {j} {j} self
  u-inu  : ∀ {s} {h : Ch s → L} {vs : (c : Ch s) → j ≤ h c} → ((c : Ch s) → Uni (vs c)) → Uni (inu vs)

uni-lift : (a b : L) → Uni (lift {true} a b)
uni-lift a zero     = u-self
uni-lift a (nd s h) = u-inu (λ c → uni-lift a (h c))

uni-z≤ : (ℓ : L) → Uni (z≤ ℓ)
uni-z≤ zero     = u-self
uni-z≤ (nd s h) = u-inu (λ c → uni-z≤ (h c))

data Exit₂ (a₀ : L) {j : L} {X : Set} {x₀ : X} : Keep j X x₀ → Set where
  kept₂ : ∀ q cv e → at j q ≡ a₀ → Exit₂ a₀ (just (q , cv , e))
  high₂ : j ≤ a₀ → Exit₂ a₀ nothing

map₂ : ∀ {a₀ a₁ j X Y} {x₀ : X} {y₀ : Y} (f : X → Y) (e : f x₀ ≡ y₀) → a₀ ≡ a₁
  → {m : Keep j X x₀} → Exit₂ a₀ m → Exit₂ a₁ (mapK f e m)
map₂ f e refl (kept₂ q cv e′ eq) = kept₂ q _ _ eq
map₂ f e refl (high₂ w)          = high₂ w

mutual
  kp-uni : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Uni w → Exit₂ (at ℓ p) (kp ℓ o p w)
  kp-uni ℓ             o               p              self      u-self    = kept₂ p _ _ refl
  kp-uni (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  (u-inu U) = kp⁼-uni (h c) (oc c) t (vs c) (U c)
  kp-uni (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  (u-inu U) =
    map₂ (pshBr (kh zero) t) (pshFirst (kh zero) t) (CM.psh-at (kh zero) t)
      (kp⁼-uni (h zero) (oc zero) (psh (kh zero) t) (vs zero) (U zero))
  kp-uni ℓ             o               p              (inc c v) ()
  kp-uni ℓ             o               p              (ink v)   ()

  kp⁼-uni : (a : L) (o : Ok a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → Uni w → Exit₂ (proj₁ (sl⁼ a t)) (kp⁼ a o t w)
  kp⁼-uni a o (inj₁ _) w _ = high₂ w
  kp⁼-uni a o (inj₂ p) w U = kp-uni a o p w U

conv₂ : ∀ {j} a o p (w : j ≤ a) (m : Keep j (Br a p) (fromBr a p zero)) → kp a o p w ≡ m → Exit₂ (at a p) m → KExit j a o p w
conv₂ a o p w _ eq (kept₂ q cv e _) = kept (q , cv , e , eq)
conv₂ a o p w _ eq (high₂ u)        = high (λ { (_ , _ , _ , eq′) → jn (trans (sym eq′) eq) }) u

kexit-uni : ∀ {j} a o p (w : j ≤ a) → Uni w → KExit j a o p w
kexit-uni a o p w U = conv₂ a o p w (kp a o p w) refl (kp-uni a o p w U)

NotX : ∀ {j a o p w} → KExit j a o p w → Set
NotX (cross _ _ _ _ _) = ⊥
NotX (kept _)          = ⊤
NotX (high _ _)        = ⊤

notX₂ : ∀ {j} a o p (w : j ≤ a) m (eq : kp a o p w ≡ m) (x : Exit₂ (at a p) m) → NotX (conv₂ a o p w m eq x)
notX₂ a o p w _ eq (kept₂ _ _ _ _) = tt
notX₂ a o p w _ eq (high₂ _)       = tt

uni-notX : ∀ {j} a o p (w : j ≤ a) (U : Uni w) → NotX (kexit-uni a o p w U)
uni-notX a o p w U = notX₂ a o p w (kp a o p w) refl (kp-uni a o p w U)
```

## 两条参照前提的作用点互不相交

目标到自己某个真槽位的层号没有字面路径 (`no-cyc`): 路径给出层号的 "后代或自身" (`p→b`), 真槽位的层号是严格后代 (`pos-below`), 严格后代关系良基 (`wfᴸ`). 所以 "目标有与槽位同层的真槽位" (`Below` 的作用点) 与 "目标到槽位层号有字面路径" (`AboveL` 的作用点) 不同时成立 (`apart`).

```agda
mutual
  Lo⁺ : L → L → Set
  Lo⁺ x zero     = ⊥
  Lo⁺ x (nd s h) = (Σ (Ch s) λ c → Lo x (h c)) ⊎ LoK x s

  LoK : L → Sh → Set
  LoK x (sΩ k) = Lo x k
  LoK x sS     = ⊥
  LoK x sL     = ⊥

  Lo : L → L → Set
  Lo x y = (x ≡ y) ⊎ Lo⁺ x y

p→b : ∀ {b i j} → Pth b i j → Lo i j
p→b self                 = inj₁ refl
p→b (inc c v)            = inj₂ (inj₁ (c , p→b v))
p→b {j = nd s h} (inu vs) = inj₂ (inj₁ (c₀ s , p→b (vs (c₀ s))))
p→b (ink v)              = inj₂ (inj₂ (p→b v))

mutual
  tr⁺ : ∀ {x y} z → Lo x y → Lo⁺ y z → Lo⁺ x z
  tr⁺ (nd s h)      d (inj₁ (c , e)) = inj₁ (c , trE (h c) d e)
  tr⁺ (nd (sΩ k) h) d (inj₂ e)       = inj₂ (trE k d e)

  trE : ∀ {x y} z → Lo x y → Lo y z → Lo x z
  trE z (inj₁ refl) e           = e
  trE z (inj₂ d)    (inj₁ refl) = inj₂ d
  trE z (inj₂ d)    (inj₂ e)    = inj₂ (tr⁺ z (inj₂ d) e)

data AccL (a : L) : Set where
  acc : (∀ x → Lo⁺ x a → AccL x) → AccL a

downL : ∀ {x y} → AccL y → Lo x y → AccL x
downL a       (inj₁ refl) = a
downL (acc f) (inj₂ d)    = f _ d

wfᴸ : (a : L) → AccL a
wfᴸ zero          = acc (λ x ())
wfᴸ (nd sS h)     = acc (λ { x (inj₁ (c , d)) → downL (wfᴸ (h c)) d ; x (inj₂ ()) })
wfᴸ (nd sL h)     = acc (λ { x (inj₁ (c , d)) → downL (wfᴸ (h c)) d ; x (inj₂ ()) })
wfᴸ (nd (sΩ k) h) = acc (λ { x (inj₁ (c , d)) → downL (wfᴸ (h c)) d ; x (inj₂ d) → downL (wfᴸ k) d })

irrᴸ : ∀ {a} → AccL a → Lo⁺ a a → ⊥
irrᴸ (acc f) d = irrᴸ (f _ d) d

pos-below : (j : L) (q : Pos j) → Lo⁺ (at j q) j
pos-below (nd s h)      (inj₂ (c , t)) = inj₁ (c , p→b (posW⁼ (h c) t))
pos-below (nd (sΩ k) h) (inj₁ t)       = inj₂ (p→b (posW⁼ k t))

no-cyc : (j : L) (q : Pos j) → j ≤ at j q → ⊥
no-cyc j q u = irrᴸ (wfᴸ j) (tr⁺ j (p→b u) (pos-below j q))

apart : ∀ {j a} (p : Pos a) (q : Pos j) → at j q ≡ at a p → j ≤ at a p → ⊥
apart {j} p q eq u = no-cyc j q (subst (λ b → j ≤ b) (sym eq) u)
```

## R80: 下标侧槽位, 一致路径, 推进孩子 zero

塔各项上孩子 zero 的层号就是下标层, 推进路径是 `self`, 所以 R80 就是下标层上的判定.

```agda
r80-tw : ∀ n (t : Pos⁼ (tw n)) {j} (vs : (c : Tr (tw n)) → j ≤ tw n ⊕ ↑ (tw n) c)
  → kp (tw (suc n)) (Ok-tw (suc n)) (inj₁ t) (inu vs) ≡ mapK (λ z → z) refl (kp⁼ (tw n) (Ok-tw n) t (vs zero))
r80-tw n t vs = refl
```

一般的 Ω 形状层号: 推进路径 `kh zero` 与目标路径 `vs zero` 在孩子 zero 里分叉 (同 `YiCMCross.Cross`) 时给 `nothing` (`drop-r80`). 读回域里的实例: 塔第 3 项在孩子 `Ωt (tw 2)` 上的层号 `L′` (下标层 `tw 1`), 目标 `tw 2`, 路径在 `L′` 顶上一致, 在孩子 zero 的顶结点 (Ω 形状) 上进孩子 2; 推进经孩子 zero, 两者分叉. 槽位层号 `tw 1` 是目标 `tw 2` 的真槽位 (下标侧) 的层号 (`r80-lit`). 路径是手写的, 实际折叠是否走到这条路径没有查.

```agda
drop-r80 : ∀ k h (o : Ok (nd (sΩ k) h)) (t : Pos⁼ k) {j} (vs : (c : Tr k) → j ≤ h c)
  → Cross (h zero) (proj₂ (proj₁ o) zero) (vs zero) → kp (nd (sΩ k) h) o (inj₁ t) (inu vs) ≡ nothing
drop-r80 k h ((ok , kh) , oc) t vs x = cong (mapK (pshBr (kh zero) t) (pshFirst (kh zero) t)) (cross-drop x (oc zero) t)

c₃ : Tr (tw 2)
c₃ = proj₁ (Ωt (tw 2))

X₃ : Tr (tw 1) → L
X₃ c = ↑ (tw 2) (up zero c (proj₁ (Ωt (tw 1 ⊕ ↑ (tw 1) c))) (proj₂ (Ωt (tw 1 ⊕ ↑ (tw 1) c))))

L′ : L
L′ = nd (sΩ (tw 1)) (λ c → tw 2 ⊕ X₃ c)

L′≡ : tw 2 ⊕ ↑ (tw 2) c₃ ≡ L′
L′≡ = refl

o′ : Ok L′
o′ = proj₂ (Ok-tw 3) c₃

vs′ : (c : Tr (tw 1)) → tw 2 ≤ tw 2 ⊕ X₃ c
vs′ zero = inc (suc (suc zero)) (lift (tw 2) _)
vs′ c    = lift (tw 2) (X₃ c)

IsCrossK : ∀ {j a o p w} → KExit j a o p w → Set
IsCrossK (cross _ _ _ _ _) = ⊤
IsCrossK (kept _)          = ⊥
IsCrossK (high _ _)        = ⊥

r80-drop : kp L′ o′ (inj₁ (inj₁ tt)) (inu vs′) ≡ nothing
r80-drop = drop-r80 (tw 1) (λ c → tw 2 ⊕ X₃ c) o′ (inj₁ tt) vs′ (xuc _ (suc (suc zero)) (lift (tw 2) _))

r80-cross : IsCrossK (kexit L′ o′ (inj₁ (inj₁ tt)) (inu vs′))
r80-cross = tt

r80-lit : at (tw 2) (inj₁ (inj₁ tt)) ≡ at L′ (inj₁ (inj₁ tt))
r80-lit = refl
```
