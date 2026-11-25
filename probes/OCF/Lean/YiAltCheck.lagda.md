# 替代写法的探针 (三): 行律与 "不依赖孩子的比较"

> 编译定理, 无前提, 对两个候选同时成立 (`lv` 任意): 嵌入一致的其余各行逐字保住 (`J2-u`, `J2⊥`, `J2-k`, `J2-s`, `J2-lim`, `self-up`, `node`, `kstep`); 非零是折叠值的类型, 单调是 `YiAltFold.Fold.mono`.
> 新行的律: 目标路径经下标层时对一切孩子 c 交接 (`J2-b-k`), 结点按孩子层判定 (`kp-b-k`); 在下一站 `Nx a` 上, 形如 `w ∙ lift` 的指定孩子路径对一切 c, c′ 交接 (`hand-all`, `kp-all`), x 是零时输出与 c′ 无关 (`const`), 所以这族探针上任何观察对 c′ 是常值 (`no-sep`): `branch→sep` 的 `on` 与 `off` 不能同时成立 (`on→not-off`).
> 不否定什么: `no-sep` 只对 `w ∙ lift` 这一族路径陈述 (`YiLNBranch.wc` 是这个形状); 层号比较的两条 (`kp-lev`, `J2-b-lev`) 只陈述形状.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAltCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; node⁺)
open import OCF.Lean.YiRWCheck using (way-refl; Nx; Ok-Nx)
open import OCF.Lean.YiAltCmp
open import OCF.Lean.YiAltFold

module Laws (lv : Bool) where
  open Fold lv
```

## 保住的各行 (与 `YiRWCheck` 同陈述)

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
    ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
  J2-k k h o B j v β x c y e = refl

  J2-s : (h : ⊤ → L) (o : Ok (nd sS h)) (B : Base (nd sS h)) (j : L) (v : j ≤ h tt)
    (β : Tr⁺ j) (x : Tr (nd sS h)) (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
    → ψ (nd sS h) o B j (inc tt v) β (up x tt y e) ≡ ψ (h tt) (proj₂ o tt) (cb o B tt x) j v (ψ (nd sS h) o B j (inc tt v) β x) y
  J2-s h o B j v β x y e = refl

  J2-lim : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (n : ℕ) (j : L) (v : j ≤ g n)
    (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
    → ψ (nd sL g) o B j (inc n v) β (up x n y e) ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) y
  J2-lim g o B n j v β x y e rewrite way-refl g (proj₁ o) n = refl

  self-up : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h)) (x : Tr (nd s h))
    (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → ψ (nd s h) o B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (ψ (nd s h) o B (nd s h) self β x) y
  self-up s h o B β x c y e = refl

  step : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
  step ℓ o B p g z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))

  node : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
    → ψ ℓ o B j w β (Ω p g) ≡ node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z)) (step ℓ o B p g)
  node ℓ o B j w β p g = refl

  keep0 : ∀ {X : Set} {x₀ : X} (m : Keep zero X x₀) → m ≡ nothing
  keep0 nothing = refl

  node⊥ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (w : zero ≤ ℓ) (β : Tr⁺ zero) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
    → ψ ℓ o B zero w β (Ω p g) ≡ limc⁺ (λ n → ψ ℓ o B zero w β (g (iter (step ℓ o B p g) (fromBr ℓ p zero) n)))
  node⊥ ℓ o B w β p g rewrite keep0 (kp ℓ o p w) = refl

  kstep : (a : L) (oa : Ok a) (B : Base (Nx a)) (β : Tr⁺ a) (x : Tr (Nx a)) (p : Pos a) (g : Br a p → Tr a)
    (e : a ⊢ zero ◃ Ω p g)
    → ψ (Nx a) (Ok-Nx a oa) B a (ink self) β (up x zero (Ω p g) e)
    ≡ Ω⁺ p (λ z → ψ a (proj₂ (Ok-Nx a oa) zero) (cb (Ok-Nx a oa) B zero x) a self (ψ (Nx a) (Ok-Nx a oa) B a (ink self) β x) (g z))
  kstep a oa B β x p g e = refl
```

## 新行: 目标路径经下标层

前提 `q` 是 `cmp` 在孩子 c′ 的层号里的一次计算结果, 不含 c. 交接对一切孩子 c 成立, 路径是 `u ∙ (k ≤ h c)`.

```agda
  J2-b-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
    (u : j ≤ k) → cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′) ≡ just u
    → (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
    ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (u ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y
  J2-b-k k h o B j c′ v u q β x c y e rewrite q = refl

  kp-b-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
    (u : j ≤ k) → cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′) ≡ just u
    → (c : Tr k) (t : Pos⁼ (h c))
    → kp (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ kp⁼ (h c) (proj₂ o c) t (u ∙ proj₂ (proj₁ o) c)
  kp-b-k k h o j c′ v u q c t rewrite q = refl
```

下一站 `Nx a` (塔第 n+1 项是 `Nx (tw n)`): 指定孩子的路径 `w ∙ lift a (↑ a c′)` 对一切 c′ 被认出经下标层 (`cmp-lift`), 所以对一切 c, c′ 交接.

```agda
  wL : (a : L) {j : L} → j ≤ a → (c : Tr a) → j ≤ a ⊕ ↑ a c
  wL a w c = w ∙ lift a (↑ a c)

  hand-all : (a : L) (oa : Ok a) (B : Base (Nx a)) (j : L) (w : j ≤ a) (β : Tr⁺ j) (x : Tr (Nx a))
    (c′ c : Tr a) (y : Tr (a ⊕ ↑ a c)) (e : (a ⊕ ↑ a c) ⊢ zero ◃ y)
    → ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β (up x c y e)
    ≡ ψ (a ⊕ ↑ a c) (proj₂ (Ok-Nx a oa) c) (cb (Ok-Nx a oa) B c x) j (wL a w c)
        (ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β x) y
  hand-all a oa B j w β x c′ c y e =
    J2-b-k a (λ c → a ⊕ ↑ a c) (Ok-Nx a oa) B j c′ (wL a w c′) w
      (cmp-lift a (↑ a c′) (proj₂ (Ok-Nx a oa) c′) w) β x c y e

  kp-all : (a : L) (oa : Ok a) (j : L) (w : j ≤ a) (c′ c : Tr a) (t : Pos⁼ (a ⊕ ↑ a c))
    → kp (Nx a) (Ok-Nx a oa) (inj₂ (c , t)) (inc c′ (wL a w c′)) ≡ kp⁼ (a ⊕ ↑ a c) (proj₂ (Ok-Nx a oa) c) t (wL a w c)
  kp-all a oa j w c′ c t =
    kp-b-k a (λ c → a ⊕ ↑ a c) (Ok-Nx a oa) j c′ (wL a w c′) w (cmp-lift a (↑ a c′) (proj₂ (Ok-Nx a oa) c′) w) c t
```

## 这族探针上没有分离

x 是零时 (`YiLNBranch` 的探针取 x = zero, 路径 `wc c = ink self ∙ lift …`), 输出与目标所在的孩子 c′ 无关; 任何布尔观察对 c′ 是常值, 所以 `YiAbsFrame.branch→sep` 的两条前提 (`on`: c₀ 处为真; `off`: 字面不同处为假) 在有一个字面不同的孩子时不能同时成立.

```agda
  const : (a : L) (oa : Ok a) (B : Base (Nx a)) (j : L) (w : j ≤ a) (β : Tr⁺ j)
    (c′ c″ c : Tr a) (y : Tr (a ⊕ ↑ a c)) (e : (a ⊕ ↑ a c) ⊢ zero ◃ y)
    → ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β (up zero c y e)
    ≡ ψ (Nx a) (Ok-Nx a oa) B j (inc c″ (wL a w c″)) β (up zero c y e)
  const a oa B j w β c′ c″ c y e = trans (hand-all a oa B j w β zero c′ c y e) (sym (hand-all a oa B j w β zero c″ c y e))

  no-sep : (a : L) (oa : Ok a) (B : Base (Nx a)) (j : L) (w : j ≤ a) (β : Tr⁺ j) (hd : Tr j → Bool)
    (c′ c″ c : Tr a) (y : Tr (a ⊕ ↑ a c)) (e : (a ⊕ ↑ a c) ⊢ zero ◃ y)
    → hd (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β (up zero c y e)))
    ≡ hd (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc c″ (wL a w c″)) β (up zero c y e)))
  no-sep a oa B j w β hd c′ c″ c y e = cong (λ Z → hd (proj₁ Z)) (const a oa B j w β c′ c″ c y e)

  t≢f : true ≡ false → ⊥
  t≢f ()

  on→not-off : (a : L) (oa : Ok a) (B : Base (Nx a)) (j : L) (w : j ≤ a) (β : Tr⁺ j) (hd : Tr j → Bool)
    (c₁ c : Tr a) (y : Tr (a ⊕ ↑ a c)) (e : (a ⊕ ↑ a c) ⊢ zero ◃ y) (c′ : Tr a) → (c₁ ≡ c′ → ⊥)
    → hd (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc c₁ (wL a w c₁)) β (up zero c y e))) ≡ true
    → ((d : Tr a) → (c₁ ≡ d → ⊥) → hd (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc d (wL a w d)) β (up zero c y e))) ≡ false)
    → ⊥
  on→not-off a oa B j w β hd c₁ c y e c′ ne on off =
    t≢f (trans (sym on) (trans (no-sep a oa B j w β hd c₁ c′ c y e) (off c′ ne)))
```

## 候选二另加的两条 (只陈述形状)

结点: 目标不经下标层 (`q₁`), 槽位层号经下标层 (`q₂`), 且在目标层号之下 (`q₃`), 就取路径 w 末端的槽位. 嵌入: 目标不经下标层, 下标层在目标之下 (`q₂`), 就把孩子树折到下标层再嵌进目标层. 三个前提都不含 c 与 c′ 的比较.

```agda
module LawsLev where
  open Fold true
  open Laws true using (cb)

  kp-lev : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′) (c : Tr k) (t : Pos⁼ (h c))
    (u : proj₁ (sl⁼ (h c) t) ≤ k) (w : proj₁ (sl⁼ (h c) t) ≤ j)
    → cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′) ≡ nothing
    → cmp (h c) (proj₂ o c) (posW⁼ (h c) t) (proj₂ (proj₁ o) c) ≡ just u
    → cmp (h c′) (proj₂ o c′) (u ∙ proj₂ (proj₁ o) c′) v ≡ just w
    → kp (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ mapK (proj₂ (sl⁼ (h c) t)) refl (end w)
  kp-lev k h o j c′ v c t u w q₁ q₂ q₃ rewrite q₁ | q₂ | q₃ = refl

  J2-b-lev : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
    (u : k ≤ j)
    → cmp (h c′) (proj₂ o c′) v (proj₂ (proj₁ o) c′) ≡ nothing
    → cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v ≡ just u
    → (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
    ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x
      ⊹ emb j (Ok-≤ (h c′) (proj₂ o c′) v) u (ψ (h c) (proj₂ o c) (cb o B c x) k (proj₂ (proj₁ o) c) (B k (ink self)) y)
  J2-b-lev k h o B j c′ v u q₁ q₂ β x c y e rewrite q₁ | q₂ = refl
```
