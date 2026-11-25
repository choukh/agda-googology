# 候选 A: 形状

> 编译定理 (`refl` 或对一切参数): 精简块的其余各行逐字保住 (`J2-u`, `J2⊥`, `J2-k`, `J2-s`, `J2-lim` 三条, `self-up`); 分支侧一行对一切 Ω 形状层号是同一个式子 (`J2-Ω`), 按 `cut` 分成孩子自己的折叠 (`J2-floor`) 与 `φ` (`J2-φ`); 孩子里的槽位朝经别的孩子的目标经 `kpA` (`kp-side`); 塔的地板是下标层, 读回层号的地板是被加的层 (`flr-tw`, `flr-β`).
> 有限测试 (`refl`): 塔第 1 项上最小见证 `Wt` 的折叠就是孩子 two 里以 `BW` 为底的折叠 (`wit`); 孩子 two 的第 2, 1 层底是保留的结点, 各支是左项该支的 `φ` (`b2-form`, `β₁-form`); 第 0 层底与起点是孩子自己的标准折叠的链 (`b′-form`, `β₀-form`); 精简块上同一支是 Ω₁ 加一个可数树 (`old-any`). 不否定什么; 值在 `YiKVValue`, `YiKVInst`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKVCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base; B₀; node⁺; s+)
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

  φ-up : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (f : (c : Ch s) → Ab a₀ (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (up x c y e)
    ≡ φ a oa Ba kk j v (h c) (proj₂ om c) (f c) (cb om Bm c x) (φ a oa Ba kk j v (nd s h) om (ab f) Bm β x) y
  φ-up s h om f Bm β x c y e = refl

  φ-node : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (f : (c : Ch s) → Ab a₀ (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (p : Pos (nd s h)) (g : Br (nd s h) p → Tr (nd s h))
    → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (Ω p g)
    ≡ node⁺ (kpA a oa kk v (ab f) (inj₂ p)) (λ z → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (g z))
        (λ z → fromBr (nd s h) p (proj₁ (ψ (nd s h) om Bm (at (nd s h) p) (posW (nd s h) p) (Bm (at (nd s h) p) (posW (nd s h) p)) (g z))))
  φ-node s h om f Bm β p g = refl
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
