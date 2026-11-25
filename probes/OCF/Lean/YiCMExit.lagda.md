# 对照表判定件 2: 保留判定的三个出口, 嵌入行的分叉出口

> 判决: 编译定理, 无前提, 不读记号, 不改树、折叠、合法性. 对一切层号、证据、槽位、目标路径, `kp` 的结果属于三种之一 (`kp-exit`): 保留在目标的一个槽位上, 该槽位的层号字面等于原槽位的层号 (`kept`); 不保留, 且目标有到槽位层号的字面路径 (`high`, 即同层或高于目标); 不保留, 且在某个 Ω 形状结点上槽位层号在孩子 c 之下, 目标在孩子 c′ 之下 (`cross`, 分叉).
> 嵌入行在同一种上下文 (Ω 形状, 目标经指定孩子) 的输出: 现行折叠在两个孩子都非零时对一切 Ω 形状层号回退 (`fallᶻ`), 换基折叠无证据时回退 (`fallᴮ`), 有证据时按 `route` 二分 (`rebᴮ-lo`, `rebᴮ-hi`).
> 不否定什么: `cross` 出口上槽位与目标的真实关系没有判定 (三种都可能); 没有值的定理. 入口: `kp-exit`, `fallᶻ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCMExit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; kp; kp⁼)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiMTTab using (tbᶻ; rbᶻ)
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiBSBase as BB
```

## 三个出口

`Exit a₀ m`: a₀ 是原槽位的层号, m 是保留判定的结果.

```agda
data Exit (a₀ : L) {j : L} {X : Set} {x₀ : X} : Keep j X x₀ → Set where
  kept  : ∀ q cv e → at j q ≡ a₀ → Exit a₀ (just (q , cv , e))
  high  : j ≤ a₀ → Exit a₀ nothing
  cross : ∀ {k′} {h′ : Tr k′ → L} (c c′ : Tr k′) → a₀ ≤ h′ c → j ≤ h′ c′ → Exit a₀ nothing

psh-at : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → proj₁ (sl⁼ a (psh v t)) ≡ proj₁ (sl⁼ k t)
psh-at self                  t = refl
psh-at (inc c v)             t = psh-at v t
psh-at {a = nd s h} (inu vs) t = psh-at (vs (c₀ s)) t
psh-at (ink v)               t = psh-at v t

map-exit : ∀ {a₀ a₁ j X Y} {x₀ : X} {y₀ : Y} (f : X → Y) (e : f x₀ ≡ y₀) → a₀ ≡ a₁
  → {m : Keep j X x₀} → Exit a₀ m → Exit a₁ (mapK f e m)
map-exit f e refl (kept q cv e′ eq) = kept q _ _ eq
map-exit f e refl (high w)          = high w
map-exit f e refl (cross c c′ u v)  = cross c c′ u v

mutual
  kp-exit : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → Exit (at ℓ p) (kp ℓ o p w)
  kp-exit ℓ             o               p              self      = kept p _ _ refl
  kp-exit (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼-exit (h c) (oc c) t (vs c)
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼-exit (h c) (oc c) t (v ∙ kh c)
  kp-exit (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼-exit (h c) (oc c) t v
  kp-exit (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (Exit (proj₁ (sl⁼ (g m) t))) (way g r m n)
      (λ u → map-exit (pshBr u t) (pshFirst u t) (psh-at u t) (kp⁼-exit (g n) (oc n) (psh u t) v))
      (λ u → kp⁼-exit (g m) (oc m) t (v ∙ u))
  kp-exit (nd (sΩ k) h) _               (inj₂ (c , t)) (inc c′ v) = cross c c′ (posW⁼ (h c) t) v
  kp-exit (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼-exit k ok t v
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    map-exit (pshBr (kh c) t) (pshFirst (kh c) t) (psh-at (kh c) t) (kp⁼-exit (h c) (oc c) (psh (kh c) t) v)
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    map-exit (pshBr (kh zero) t) (pshFirst (kh zero) t) (psh-at (kh zero) t)
      (kp⁼-exit (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼-exit : (a : L) (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → Exit (proj₁ (sl⁼ a t)) (kp⁼ a o t w)
  kp⁼-exit a o (inj₁ _) w = high w
  kp⁼-exit a o (inj₂ p) w = kp-exit a o p w
```

保留时槽位层号在目标之下有字面路径; 这是 `kept` 的直接读法.

```agda
kept-below : ∀ {a₀ j X} {x₀ : X} {q : Pos j} {cv : Br j q → X} {e : cv (fromBr j q zero) ≡ x₀}
  → Exit a₀ {j} {X} {x₀} (just (q , cv , e)) → a₀ ≤ j
kept-below {j = j} (kept q cv e eq) = subst (λ a → a ≤ j) eq (posW j q)
```

`cross` 出口不区分槽位与目标的关系. 同一个孩子的对角上 (槽位在孩子 c 里, 目标就是孩子 c 的层号), 对一切 Ω 形状层号: 槽位是孩子层号自身时 (同层, 按规则走链) 与槽位字面就是目标的槽位 p′ 时 (低于目标) 结果相同. 前提可满足: 塔第 1 项的非零孩子层号有槽位 (`YiFINeg.lit₃` 一格).

```agda
diag-same : ∀ k h (o : Ok (nd (sΩ k) h)) c
  → (kp (nd (sΩ k) h) o (inj₂ (c , inj₁ tt)) (inc c self) ≡ nothing) × (at (nd (sΩ k) h) (inj₂ (c , inj₁ tt)) ≡ h c)
diag-same k h o c = refl , refl

diag-slot : ∀ k h (o : Ok (nd (sΩ k) h)) c (p′ : Pos (h c))
  → (kp (nd (sΩ k) h) o (inj₂ (c , inj₂ p′)) (inc c self) ≡ nothing)
  × (Br (h c) p′ ≡ Br (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))
  × (at (h c) p′ ≡ at (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))
diag-slot k h o c p′ = refl , refl , refl
```

## 嵌入行的分叉出口

上下文: Ω 形状层号, 嵌入在孩子 c, 目标经指定孩子 c′. 现行折叠 (`YiTBRow.ψ` 配 `rbᶻ`): 表只看孩子的顶构造子, 两个孩子都非零时没有条目, 行回退.

```agda
data NZ {S : Sg} : T S → Set where
  nzs : ∀ x → NZ (suc x)
  nzl : ∀ f a → NZ (lim f a)
  nzΩ : ∀ p g → NZ (Ω p g)
  nzu : ∀ x c y e → NZ (up x c y e)

tb-nz : ∀ k (h : Tr k → L) {c c′ : Tr k} → NZ c → NZ c′ → tbᶻ k h c c′ ≡ nothing
tb-nz k h (nzs _)       (nzs _)       = refl
tb-nz k h (nzs _)       (nzl _ _)     = refl
tb-nz k h (nzs _)       (nzΩ _ _)     = refl
tb-nz k h (nzs _)       (nzu _ _ _ _) = refl
tb-nz k h (nzl _ _)     (nzs _)       = refl
tb-nz k h (nzl _ _)     (nzl _ _)     = refl
tb-nz k h (nzl _ _)     (nzΩ _ _)     = refl
tb-nz k h (nzl _ _)     (nzu _ _ _ _) = refl
tb-nz k h (nzΩ _ _)     (nzs _)       = refl
tb-nz k h (nzΩ _ _)     (nzl _ _)     = refl
tb-nz k h (nzΩ _ _)     (nzΩ _ _)     = refl
tb-nz k h (nzΩ _ _)     (nzu _ _ _ _) = refl
tb-nz k h (nzu _ _ _ _) (nzs _)       = refl
tb-nz k h (nzu _ _ _ _) (nzl _ _)     = refl
tb-nz k h (nzu _ _ _ _) (nzΩ _ _)     = refl
tb-nz k h (nzu _ _ _ _) (nzu _ _ _ _) = refl

dW-no : {A B X : Set} (m : Maybe (A ⊎ B)) → m ≡ nothing → {F : A → X} {G : B → X} {H : X} → TB.dW m F G H ≡ H
dW-no .nothing refl = refl

fallᶻ : ∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j {c c′} (v : j ≤ h c′) β x (y : Tr (h c)) e
  → NZ c → NZ c′
  → TB.ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc c′ v) β (up x c y e)
  ≡ TB.ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc c′ v) β x ⊞ TB.ψ₀ʳ (h c) (proj₂ o c) (rbᶻ (h c)) y
fallᶻ k h o B j {c} {c′} v β x y e nc nc′ = dW-no (tbᶻ k h c c′) (tb-nz k h nc nc′)
```

换基折叠 (`YiBSFold.ψ`): 无证据时回退; 有证据时按 `route` 二分, 地板之下进孩子 c 朝原目标折 (不比较 c 与 c′), 地板之上是替身加第 0 层尾项.

```agda
fallᴮ : ∀ k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → BB.Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → BS.ψ (nd (sΩ k) h) o (nothing , rc) B j (inc c′ v) β (up x c y e)
  ≡ BS.ψ (nd (sΩ k) h) o (nothing , rc) B j (inc c′ v) β x ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
fallᴮ k h o rc B j c′ v β x c y e = refl

rebᴮ-lo : ∀ k h (o : Ok (nd (sΩ k) h)) (S : BB.Schema k h) (rc : (c : Tr k) → BB.Rb (h c)) (B : Base (nd (sΩ k) h)) j c′
  (v : j ≤ h c′) β x c y e (u : j ≤ BB.floor S) → BB.route S j c′ v ≡ inj₁ u
  → BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β (up x c y e)
  ≡ BS.ψ (h c) (proj₂ o c) (rc c) (λ i u′ → BS.ψ (nd (sΩ k) h) o (just S , rc) B i (inc c u′) (B i (inc c u′)) x)
      j (BB.back S c u) (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) y
rebᴮ-lo k h o S rc B j c′ v β x c y e u eq =
  cong (λ W → cW W
    (λ u → BS.ψ (h c) (proj₂ o c) (rc c) (λ i u′ → BS.ψ (nd (sΩ k) h) o (just S , rc) B i (inc c u′) (B i (inc c u′)) x)
             j (BB.back S c u) (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) y)
    (λ u → BB.seen S j (BB.downOk (h c′) (proj₂ o c′) j v) u (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) c
             ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)) eq

rebᴮ-hi : ∀ k h (o : Ok (nd (sΩ k) h)) (S : BB.Schema k h) (rc : (c : Tr k) → BB.Rb (h c)) (B : Base (nd (sΩ k) h)) j c′
  (v : j ≤ h c′) β x c y e (u : BB.floor S ≤ j) → BB.route S j c′ v ≡ inj₂ u
  → BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β (up x c y e)
  ≡ BB.seen S j (BB.downOk (h c′) (proj₂ o c′) j v) u (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) c
      ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
rebᴮ-hi k h o S rc B j c′ v β x c y e u eq =
  cong (λ W → cW W
    (λ u → BS.ψ (h c) (proj₂ o c) (rc c) (λ i u′ → BS.ψ (nd (sΩ k) h) o (just S , rc) B i (inc c u′) (B i (inc c u′)) x)
             j (BB.back S c u) (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) y)
    (λ u → BB.seen S j (BB.downOk (h c′) (proj₂ o c′) j v) u (BS.ψ (nd (sΩ k) h) o (just S , rc) B j (inc c′ v) β x) c
             ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)) eq
```
