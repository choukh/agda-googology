# 龙骨原型: 形状

> 编译定理 (`refl` 或对一切参数): 候选 A 的形状测试在原型折叠上逐条照旧成立 (其余各行逐字保住, 分支侧一行对一切 Ω 形状层号同式, 最小见证的各个底的形状); 原型改的两行: 源层 Ω 形状的下标侧槽位经地板推进锚层判定 (`kpA-idx`), 目标落在内层下标侧时交出到地板的路径 (`cut-idx`).
> 有限测试: `tw 2` 上孩子 `Ωt (tw 1)` 的下标侧槽位, 朝孩子 `suc zero` 那一层, 原型保留 (`keep-new`), 候选 A 不保留 (`keep-old`). 不否定什么; 值在 `YiKDTw1`, `YiKDStep`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiKDFold
open import OCF.Lean.YiCertFold using (Base; B₀; node⁺; s+; mapK)
open import Data.Maybe using (Maybe; just; nothing)
import OCF.Lean.YiKVPath as AP
import OCF.Lean.YiKVFold as A
import OCF.Lean.YiRWPath as RP
import OCF.Lean.YiRWFold as R
```

## 其余各行

```agda
cb : ∀ {s h} (o : Ok (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cb {s} {h} o B c x i u = ψ (nd s h) o B i (inc c u) (B i (inc c u)) x

J2-u : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (j : L) (ws : (c : Ch s) → j ≤ h c)
  (β : Tr⁺ j) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B j (inu ws) β (up x c y e) ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y
J2-u s h o B j ws β x c y e = refl

J2⊥ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ zero) (x : Tr (nd s h))
  (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B zero (z≤ (nd s h)) β (up x c y e)
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) zero (z≤ (h c)) (ψ (nd s h) o B zero (z≤ (nd s h)) β x) y
J2⊥ s h o B β x c y e = refl

J2-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (v : j ≤ k)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e)
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ kh o c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
J2-k k h o B j v β x c y e = refl

J2-s : (h : ⊤ → L) (o : Ok (nd sS h)) (B : Base (nd sS h)) (j : L) (v : j ≤ h tt)
  (β : Tr⁺ j) (x : Tr (nd sS h)) (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → ψ (nd sS h) o B j (inc tt v) β (up x tt y e) ≡ ψ (h tt) (proj₂ o tt) (cb o B tt x) j v (ψ (nd sS h) o B j (inc tt v) β x) y
J2-s h o B j v β x y e = refl

way-refl : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (n : ℕ) → way g r n n ≡ inj₂ self
way-refl g r zero    = refl
way-refl g r (suc n) = way-refl (λ i → g (suc i)) (λ i → r (suc i)) n

J2-lim : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
  → ψ (nd sL g) o B j (inc n v) β (up x n y e) ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) y
J2-lim g o B n j v β x y e rewrite way-refl g (proj₁ o) n = refl

J2-lim-fwd : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (m n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g m ≤ g n) → way g (proj₁ o) m n ≡ inj₁ u
  → ψ (nd sL g) o B j (inc n v) β (up x m y e)
  ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e)))
J2-lim-fwd g o B m n j v β x y e u eq rewrite eq = refl

J2-lim-bwd : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (m n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g n ≤ g m) → way g (proj₁ o) m n ≡ inj₂ u
  → ψ (nd sL g) o B j (inc n v) β (up x m y e) ≡ ψ (g m) (proj₂ o m) (cb o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y
J2-lim-bwd g o B m n j v β x y e u eq rewrite eq = refl

self-up : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h)) (x : Tr (nd s h))
  (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (ψ (nd s h) o B (nd s h) self β x) y
self-up s h o B β x c y e = refl
```

## 分支侧一行

对一切 Ω 形状层号, 一切 c, c′ 是同一个式子; `cut` 交出 j ≤ 地板时是孩子 c 自己的折叠 (路径: 到地板, 再沿 c 的证书上去), 否则是 `φ`.

```agda
module _ (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) where

  J2-Ω : ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
       ≡ cW (cut (crt o c′) v)
            (λ u → ψ (h c) (proj₂ o c) (cb o B c x) j (u ∙ ab→≤ (crt o c)) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y)
            (λ _ → φ (h c′) (proj₂ o c′) (cb o B c′ x) (ab→≤ (crt o c′)) j v (h c) (proj₂ o c) (crt o c) (cb o B c x)
                     (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y)
  J2-Ω = refl

  J2-floor : (u : j ≤ flr o) → cut (crt o c′) v ≡ inj₁ u
    → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
    ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (u ∙ ab→≤ (crt o c)) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y
  J2-floor u eq rewrite eq = refl

  J2-φ : cut (crt o c′) v ≡ inj₂ tt
    → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
    ≡ φ (h c′) (proj₂ o c′) (cb o B c′ x) (ab→≤ (crt o c′)) j v (h c) (proj₂ o c) (crt o c) (cb o B c x)
        (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y
  J2-φ eq rewrite eq = refl

kp-side : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (c c′ : Tr k) (t : Pos⁼ (h c)) {j : L} (v : j ≤ h c′)
  → kp (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ kpA (h c′) (proj₂ o c′) (ab→≤ (crt o c′)) v (crt o c) t
kp-side k h o c c′ t v = refl
```

`φ` 的各行: 地板叶子处树 (前面加一) 嵌进锚层正常折叠; 中间逐构造子下行, 源层的底是源层自己的 "x 朝该层的折叠"; 结点按 `kpA`, 不保留时链在源层回灌.

```agda
module _ {a₀ : L} (a : L) (oa : Ok a) (Ba : Base a) (kk : a₀ ≤ a) (j : L) (v : j ≤ a) where

  φ-here : (om : Ok a₀) (Bm : Base a₀) (β : Tr⁺ j) (y : Tr a₀)
    → φ a oa Ba kk j v a₀ om here Bm β y ≡ ψ a oa Ba j v β (proj₁ (emb a oa kk (s+ y)))
  φ-here om Bm β y = refl

  φ-up : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (q : AbS a₀ s) (f : (c : Ch s) → Ab a₀ (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → φ a oa Ba kk j v (nd s h) om (ab q f) Bm β (up x c y e)
    ≡ φ a oa Ba kk j v (h c) (proj₂ om c) (f c) (cb om Bm c x) (φ a oa Ba kk j v (nd s h) om (ab q f) Bm β x) y
  φ-up s h om q f Bm β x c y e = refl

  φ-node : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (q : AbS a₀ s) (f : (c : Ch s) → Ab a₀ (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (p : Pos (nd s h)) (g : Br (nd s h) p → Tr (nd s h))
    → φ a oa Ba kk j v (nd s h) om (ab q f) Bm β (Ω p g)
    ≡ node⁺ (kpA a oa kk v (ab q f) (inj₂ p)) (λ z → φ a oa Ba kk j v (nd s h) om (ab q f) Bm β (g z))
        (λ z → fromBr (nd s h) p (proj₁ (ψ (nd s h) om Bm (at (nd s h) p) (posW (nd s h) p) (Bm (at (nd s h) p) (posW (nd s h) p)) (g z))))
  φ-node s h om q f Bm β p g = refl
```

## 地板

塔第 n+1 项的地板是下标层 `tw n`; 塔第 2 项里左项 βΩ 读回的孩子层号 (下标层是第 0 层的 Ω 形状) 的地板是 `tw 1` (`YiCertPath` 在那里是 `via` 叶子: 先折到第 0 层).

```agda
flr-tw : (n : ℕ) → flr (Ok-tw (suc n)) ≡ tw n
flr-tw n = refl

βΩ : Tr (tw 1)
βΩ = proj₁ (Ωt (tw 1))

lvβ : Σ (Tr zero → L) λ h → tw 1 ⊕ ↑ (tw 1) βΩ ≡ nd (sΩ zero) h
lvβ = _ , refl

flr-β : flr {zero} {proj₁ lvβ} (proj₂ (Ok-tw 2) βΩ) ≡ tw 1
flr-β = refl
```

## 最小见证

塔第 1 项, 左项 βΩ, 孩子 two. `br c′ j v z`: 左项第 z 支的孩子树 (孩子 z 的 Ω 树) 以孩子 c′ 的层为锚朝 j 的 `φ`.

```agda
o¹ : Ok (tw 1)
o¹ = Ok-tw 1

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

c1 c2 : Tr zero
c1 = suc zero
c2 = suc c1

one two : L
one = nd sS (λ _ → zero)
two = nd sS (λ _ → one)

q1 : Pos one
q1 = inj₂ (tt , inj₁ tt)

q2 : Pos two
q2 = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

Wt : Tr (tw 1)
Wt = up βΩ c2 (proj₁ (Ωt two)) (proj₂ (Ωt two))

BW : Base two
BW = cb o¹ (B₀ (tw 1)) c2 βΩ

g₁ : Tr zero → Tr⁺ one
g₁ c = ψ (tw 1) o¹ (B₀ (tw 1)) one (inc c2 (inc tt self)) (Ωt one) (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c))))

A0f : (c : Tr zero) → zero ≤ h₁ c → Tr⁺ zero
A0f c w = ψ (h₁ c) (proj₂ o¹ c) (B₀ (h₁ c)) zero w (Ωt zero) (proj₁ (Ωt (h₁ c)))

cc : ℕ → Tr zero
cc = iter (λ c → proj₁ (A0f c (self ∙ kh o¹ c))) zero

br : (j : L) → j ≤ two → Tr zero → Tr⁺ j
br j v z = φ two (proj₂ o¹ c2) (B₀ two) (ab→≤ (crt o¹ c2)) j v (h₁ z) (proj₂ o¹ z) (crt o¹ z) (B₀ (h₁ z)) (Ωt j) (proj₁ (Ωt (h₁ z)))

wit : proj₁ (ψ₀ (tw 1) o¹ Wt) ≡ proj₁ (ψ two (proj₂ o¹ c2) BW zero (z≤ two) (ψ₀ (tw 1) o¹ βΩ) (proj₁ (Ωt two)))
wit = refl

b2-form : proj₁ (BW two self) ≡ Ω q2 (λ z → proj₁ (br two self z))
b2-form = refl

β₁-form : proj₁ (BW one (inc tt self)) ≡ Ω q1 (λ c → proj₁ (g₁ c))
β₁-form = refl

b1-form : (c : Tr zero) → g₁ c ≡ br one (inc tt self) c
b1-form c = refl

g₁0-form : proj₁ (g₁ zero) ≡ proj₁ (next⁺ (next⁺ (Ωt one)))
g₁0-form = refl

cut-0 : cut (crt o¹ c2) (inc tt (inc tt self)) ≡ inj₁ self
cut-0 = refl

cut-1 : cut (crt o¹ c2) (inc tt self) ≡ inj₂ tt
cut-1 = refl

β₀-form : proj₁ (ψ₀ (tw 1) o¹ βΩ) ≡ proj₁ (limc⁺ (λ n → A0f (cc n) (z≤ (h₁ (cc n)))))
β₀-form = refl

b′-form : proj₁ (BW zero (inc tt (inc tt self))) ≡ proj₁ (limc⁺ (λ n → A0f (cc n) (self ∙ ab→≤ (crt o¹ (cc n)))))
b′-form = refl
```

精简块上的同一支 (左项第 c 支经孩子 two 朝第 1 层): 对一切 c, 是 Ω₁ 树加上孩子 c 的 Ω 树在第 0 层的折叠 (嵌进第 1 层).

```agda
old-any : (c : Tr zero)
  → proj₁ (R.ψ (tw 1) (RP.Ok-tw 1) (R.B₀ (tw 1)) one (inc c2 (inc tt self)) (Ωt one) (up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))))
  ≡ proj₁ (Ωt one) + ι one (proj₁ (R.ψ (h₁ c) (proj₂ (RP.Ok-tw 1) c) (R.B₀ (h₁ c)) zero (z≤ (h₁ c)) (Ωt zero) (proj₁ (Ωt (h₁ c)))))
old-any c = refl

isΩ isLim : {ℓ : L} → Tr ℓ → Set
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥
isLim (lim _ _) = ⊤
isLim _         = ⊥

new-1-Ω : isΩ (proj₁ (g₁ c1))
new-1-Ω = tt

new-2-lim : isLim (proj₁ (g₁ c2))
new-2-lim = tt

tw1ᶜ-lim : isLim (twᶜ 1)
tw1ᶜ-lim = tt

EBOᶜ-lim : isLim EBOᶜ
EBOᶜ-lim = tt
```

## 原型改的两行

证书在 Ω 形状上带 "下标层 ≤ 地板" 的路径 q. 源层的下标侧槽位: 经 q 进地板, 再进锚层, 按锚层到目标的路径判定. 目标路径进入内层下标侧: 接上 q 就是到地板的路径, 走孩子自己的折叠.

```agda
kpA-idx : ∀ {a₀} (a : L) (oa : Ok a) (kk : a₀ ≤ a) {j : L} (v : j ≤ a) (k : L) (h : Tr k → L)
          (q : k ≤ a₀) (f : (c : Tr k) → Ab a₀ (h c)) (t : Pos⁼ k)
        → kpA a oa kk v {m = nd (sΩ k) h} (ab q f) (inj₂ (inj₁ t))
        ≡ mapK (pshBr (q ∙ kk) t) (pshFirst (q ∙ kk) t) (kp⁼ a oa (psh (q ∙ kk) t) v)
kpA-idx a oa kk v k h q f t = refl

cut-idx : ∀ {a k j} (h : Tr k → L) (q : k ≤ a) (f : (c : Tr k) → Ab a (h c)) (v : j ≤ k)
        → cut {m = nd (sΩ k) h} (ab q f) (ink v) ≡ inj₁ (v ∙ q)
cut-idx h q f v = refl

isJ isN : {X : Set} → Maybe X → Set
isJ (just _) = ⊤
isJ nothing  = ⊥
isN (just _) = ⊥
isN nothing  = ⊤

cΩᴰ c1ᴰ : Tr (tw 1)
cΩᴰ = proj₁ (Ωt (tw 1))
c1ᴰ = suc zero

keep-new : isJ (kp (tw 2) (Ok-tw 2) (inj₂ (cΩᴰ , inj₂ (inj₁ (inj₁ tt)))) (inc c1ᴰ self))
keep-new = tt

keep-old : isN (A.kp (tw 2) (AP.Ok-tw 2) (inj₂ (cΩᴰ , inj₂ (inj₁ (inj₁ tt)))) (inc c1ᴰ self))
keep-old = tt
```
