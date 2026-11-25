# `Ωt` 的值单调: 归结到树类型的值支配

> 判决: 条件定理 (排中律 + `Tp`). `Tp` 指值低的层号的每棵树都被值高的层号的某棵树按值支配 (只对合法层号 `Ok`); 在它与排中律之下 `Ωt` 对右侧正规的层号按值单调 (`Mono.M`), 同值正规层号的 `Ωt` 同值 (`Mono.M≈`).
> 反过来 `Ωt` 的值单调推出 `Tp` (`nec`, 无前提), 所以两者等价. `Tp` 的唯一难点在 Ω 结点: 由 `Reg` (Ω 结点分支族在高层有上界) 推出 `Tp` (`tpR`). `Tp` 与 `Reg` 是否成立未判.
> 值与 `≼` 用 `YiVWVal`; 层号值序与正规在 `YiRVLevel`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRVOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Ok)
import OCF.Lean.YiVWVal as W
open W using (V; val; _≼_; _≈_; _⊹_)
open import OCF.Lean.YiRVLevel
```

## 值的辅助引理

```agda
infixr 5 _⊙_
_⊙_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → b ≼ c → a ≼ c
d ⊙ e = W.≼-trans d e

≼s : ∀ {ℓ} (v : V ℓ) → v ≼ W.suc v
≼s v = W.≼-suc (W.≼-refl v)

≼⊹r : ∀ {ℓ} (a b : V ℓ) → b ≼ a ⊹ b
≼⊹r a W.zero    = W.z≼
≼⊹r a (W.suc b) = W.s≼s (≼⊹r a b)
≼⊹r a (W.lim f) = W.l≼ (λ n → W.≼l n (≼⊹r a (f n)))
≼⊹r a (W.Ω p g) = W.Ω≼ (λ z → W.≼Ω z (≼⊹r a (g z)))

z⊹≼ : ∀ {ℓ} (b : V ℓ) → W.zero ⊹ b ≼ b
z⊹≼ W.zero    = W.z≼
z⊹≼ (W.suc b) = W.s≼s (z⊹≼ b)
z⊹≼ (W.lim f) = W.l≼ (λ n → W.≼l n (z⊹≼ (f n)))
z⊹≼ (W.Ω p g) = W.Ω≼ (λ z → W.≼Ω z (z⊹≼ (g z)))

⊹-mono₂ : ∀ {ℓ₁ ℓ₂} {a b : V ℓ₁} {a′ b′ : V ℓ₂} → a ≼ a′ → b ≼ b′ → a ⊹ b ≼ a′ ⊹ b′
⊹-mono₂ {a′ = a′} {b′ = b′} d W.z≼ = d ⊙ W.≼⊹ a′ b′
⊹-mono₂ d (W.s≼s e)  = W.s≼s (⊹-mono₂ d e)
⊹-mono₂ d (W.≼l n e) = W.≼l n (⊹-mono₂ d e)
⊹-mono₂ d (W.l≼ h)   = W.l≼ (λ n → ⊹-mono₂ d (h n))
⊹-mono₂ d (W.≼Ω z e) = W.≼Ω z (⊹-mono₂ d e)
⊹-mono₂ d (W.Ω≼ h)   = W.Ω≼ (λ z → ⊹-mono₂ d (h z))
```

`Ωt` 的分支都是 `up zero c y e`; 它与孩子树 y 同值.

```agda
br≼ : ∀ {s h} (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → val (nd s h) (up zero c y e) ≼ val (h c) y
br≼ {s} {h} c y e = z⊹≼ _ ⊙ W.emb-≼ (nd s h) c (val (h c) y)

≼br : ∀ {s h} (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → val (h c) y ≼ val (nd s h) (up zero c y e)
≼br {s} {h} c y e = W.≼-emb (nd s h) c (val (h c) y) ⊙ ≼⊹r W.zero _

F≼cum : (ℓ : L) (F : ℕ → Tr ℓ) (m : ℕ) → val ℓ (F m) ≼ val ℓ (cum F m)
F≼cum ℓ F zero    = W.≼-refl _
F≼cum ℓ F (suc m) = ≼⊹r (val ℓ (cum F m)) (val ℓ (F (suc m))) ⊙ proj₂ (W.val-+ (cum F m) (F (suc m)))

Fl : (g : ℕ → L) → ℕ → Tr (nd sL g)
Fl g n = proj₁ (upz {sL} {g} n (Ωt (g n)))

CPL : (g : ℕ → L) (m : ℕ) → val (g m) (proj₁ (Ωt (g m))) ≼ val (nd sL g) (proj₁ (Ωt (nd sL g)))
CPL g m = W.≼l m (≼br m (proj₁ (Ωt (g m))) (proj₂ (Ωt (g m))) ⊙ F≼cum (nd sL g) (Fl g) m)
```

类型界的值版 (无前提): `Tr ℓ` 的树都严格低于 `Ωt (sc ℓ)`.

```agda
tbV : (ℓ : L) (x : Tr ℓ) → W.suc (val ℓ x) ≼ val (sc ℓ) (proj₁ (Ωt (sc ℓ)))
tbV ℓ x = W.≼Ω x (≼br tt (suc x) (z◃ x ◃s))
```

## 条件: 值支配 `Tp`

`K`: 严格低于正规层号 ℓ′ 的合法层号上的树, 值都严格低于 `Ωt ℓ′` (一般的类型界). 极限形状换到更高的正规孩子, 后继形状用一次 `Tp`.

```agda
Tp : Set
Tp = ∀ {a a′} → Ok a → Ok a′ → a ≼ᴸ a′ → (x : Tr a) → Σ (Tr a′) λ x′ → val a x ≼ val a′ x′

module _ (tp : Tp) where
  K : (ℓ′ : L) → Ok ℓ′ → Nm ℓ′ → ∀ {j} → Ok j → j ≺ᴸ ℓ′ → (x : Tr j)
    → W.suc (val j x) ≼ val ℓ′ (proj₁ (Ωt ℓ′))
  K zero          o nm oj () x
  K (nd sS h)     o nm oj (tt , d) x with tp oj (proj₂ o tt) d x
  ... | x′ , e = W.≼Ω x′ (W.s≼s e ⊙ ≼br tt (suc x′) (z◃ x′ ◃s))
  K (nd sL g)     o nm oj (n , d) x with nm n
  ... | m , lt , nm′ = K (g m) (proj₂ o m) nm′ oj (≼≺ (g m) d lt) x ⊙ CPL g m
  K (nd (sΩ k) h) o nm oj (c , d) x with nm c
  ... | c′ , lt , nm′ =
    W.≼Ω c′ (K (h c′) (proj₂ o c′) nm′ oj (≼≺ (h c′) d lt) x ⊙ ≼br c′ (proj₁ (Ωt (h c′))) (proj₂ (Ωt (h c′))))
```

`M`: 左侧任意合法层号, 右侧合法且正规. ℕ 极限的左侧是部分和, 用排中律取前 n+1 个孩子里值最大的一个, 把各项经 `Tp` 搬进它的树里求和, 再用 `K`.

```agda
module Mono (lem : LEM) (tp : Tp) where
  open Cl lem

  M : (ℓ ℓ′ : L) → Ok ℓ → Ok ℓ′ → Nm ℓ′ → ℓ ≼ᴸ ℓ′ → val ℓ (proj₁ (Ωt ℓ)) ≼ val ℓ′ (proj₁ (Ωt ℓ′))
  M zero          zero        o o′ nm d = W.≼-refl _
  M zero          (nd s′ h′)  o o′ nm d = K tp (nd s′ h′) o′ nm {zero} tt (c₀ s′ , z≼) zero
  M (nd sS h)     ℓ′          o o′ nm (n≼ f) =
    W.Ω≼ (λ z → br≼ tt (suc z) (z◃ z ◃s) ⊙ K tp ℓ′ o′ nm (proj₂ o tt) (f tt) z)
  M (nd (sΩ k) h) ℓ′          o o′ nm (n≼ f) =
    W.Ω≼ (λ c → br≼ c (proj₁ (Ωt (h c))) (proj₂ (Ωt (h c))) ⊙ ≼s _ ⊙ K tp ℓ′ o′ nm (proj₂ o c) (f c) (proj₁ (Ωt (h c))))
  M (nd sL g)     ℓ′          o o′ nm (n≼ f) = W.l≼ step
    where
    Acc′ : ℕ → Set
    Acc′ n = Σ L λ j → Ok j × (j ≺ᴸ ℓ′) × Σ (Tr j) λ S → val (nd sL g) (cum (Fl g) n) ≼ val j S

    grow : (n : ℕ) → Acc′ n → Acc′ (suc n)
    grow n (j , oj , lt , S , e) = pick (Dk j (g (suc n)))
      where
      Ωg : Tr (g (suc n))
      Ωg = proj₁ (Ωt (g (suc n)))
      eg : val (nd sL g) (Fl g (suc n)) ≼ val (g (suc n)) Ωg
      eg = br≼ (suc n) Ωg (proj₂ (Ωt (g (suc n))))
      pick : (j ≼ᴸ g (suc n)) ⊎ (g (suc n) ≺ᴸ j) → Acc′ (suc n)
      pick (inj₁ jg) = let r = tp oj (proj₂ o (suc n)) jg S in
        g (suc n) , proj₂ o (suc n) , f (suc n) , proj₁ r + Ωg ,
        (proj₁ (W.val-+ (cum (Fl g) n) (Fl g (suc n))) ⊙ ⊹-mono₂ (e ⊙ proj₂ r) eg ⊙ proj₂ (W.val-+ (proj₁ r) Ωg))
      pick (inj₂ gj) = let r = tp (proj₂ o (suc n)) oj (≺→≼ j gj) Ωg in
        j , oj , lt , S + proj₁ r ,
        (proj₁ (W.val-+ (cum (Fl g) n) (Fl g (suc n))) ⊙ ⊹-mono₂ e (eg ⊙ proj₂ r) ⊙ proj₂ (W.val-+ S (proj₁ r)))

    acc : (n : ℕ) → Acc′ n
    acc zero    = g zero , proj₂ o zero , f zero , proj₁ (Ωt (g zero)) , br≼ zero (proj₁ (Ωt (g zero))) (proj₂ (Ωt (g zero)))
    acc (suc n) = grow n (acc n)

    step : (n : ℕ) → val (nd sL g) (cum (Fl g) n) ≼ val ℓ′ (proj₁ (Ωt ℓ′))
    step n with acc n
    ... | j , oj , lt , S , e = e ⊙ ≼s _ ⊙ K tp ℓ′ o′ nm oj lt S

  M≈ : (ℓ ℓ′ : L) → Ok ℓ → Ok ℓ′ → Nm ℓ → Nm ℓ′ → ℓ ≈ᴸ ℓ′ → val ℓ (proj₁ (Ωt ℓ)) ≈ val ℓ′ (proj₁ (Ωt ℓ′))
  M≈ ℓ ℓ′ o o′ n n′ (d , d′) = M ℓ ℓ′ o o′ n′ d , M ℓ′ ℓ o′ o n d′
```

## 反方向: `Ωt` 的值单调推出 `Tp`

只用后继层号: `sc a ≼ sc a′`, 比较两个 Ω 结点时每个分支 x 都要在对面找到分支 x′, 那就是 `Tp` 的见证.

```agda
OmMono : Set
OmMono = ∀ {ℓ ℓ′} → Ok ℓ → Ok ℓ′ → Nm ℓ′ → ℓ ≼ᴸ ℓ′ → val ℓ (proj₁ (Ωt ℓ)) ≼ val ℓ′ (proj₁ (Ωt ℓ′))

invΩ : ∀ {ℓ₁ ℓ₂} {u : V ℓ₁} {p : Pos ℓ₂} {G : Br ℓ₂ p → V ℓ₂} → W.suc u ≼ W.Ω p G → Σ (Br ℓ₂ p) λ z → W.suc u ≼ G z
invΩ (W.≼Ω z d) = z , d

invS : ∀ {ℓ₁ ℓ₂} {u : V ℓ₁} {w : V ℓ₂} → W.suc u ≼ W.suc w → u ≼ w
invS (W.s≼s d) = d

nec : OmMono → Tp
nec mm {a} {a′} oa oa′ d x
  with invΩ (W.Ω⁻ x (mm {sc a} {sc a′} (tt , λ _ → oa) (tt , λ _ → oa′) tt (n≼ (λ _ → tt , d))))
... | x′ , e = x′ , (W.≼-emb (sc a) tt (val a x) ⊙ ≼⊹r W.zero _ ⊙ invS e ⊙ z⊹≼ _ ⊙ W.emb-≼ (sc a′) tt (val a′ x′))

suf : LEM → Tp → OmMono
suf lem tp {ℓ} {ℓ′} = Mono.M lem tp ℓ ℓ′
```

## `Tp` 的难点只在 Ω 结点

`Reg`: 值低的层号 a 的一个槽位上, 任何以其分支类型为下标、取值在高层 a′ 的树族, 在 `Tr a′` 里有一棵按值支配全族的树. 零, 后继, ℕ 极限, 嵌入四种构造子不需要它. 对角 (a′ 就是 a) 时由 Ω 结点自身给出 (`regSelf`).

```agda
Reg : Set
Reg = ∀ {a a′} → Ok a → Ok a′ → a ≼ᴸ a′ → (p : Pos a) (φ : Br a p → Tr a′)
    → Σ (Tr a′) λ x′ → (z : Br a p) → val a′ (φ z) ≼ val a′ x′

regSelf : (a : L) (p : Pos a) (φ : Br a p → Tr a) → Σ (Tr a) λ x′ → (z : Br a p) → val a (φ z) ≼ val a x′
regSelf a p φ = Ω p φ , λ z → W.≼Ω z (W.≼-refl _)

module _ (rg : Reg) where
  tpR : Tp
  tpR oa oa′ d zero    = zero , W.z≼
  tpR oa oa′ d (suc x) = suc (proj₁ (tpR oa oa′ d x)) , W.s≼s (proj₂ (tpR oa oa′ d x))
  tpR {a} {a′} oa oa′ d (lim f m) =
    let P = λ n → proj₁ (tpR oa oa′ d (f n)) in
    lim (cum (λ n → suc (P n))) (λ n → +-mono (cum (λ i → suc (P i)) n) (z◃ (P (suc n)) ◃s)) ,
    W.l≼ (λ n → W.≼l n (proj₂ (tpR oa oa′ d (f n)) ⊙ ≼s _ ⊙ F≼cum a′ (λ i → suc (P i)) n))
  tpR oa oa′ d (Ω p g) with rg oa oa′ d p (λ z → proj₁ (tpR oa oa′ d (g z)))
  ... | x′ , e = x′ , W.Ω≼ (λ z → proj₂ (tpR oa oa′ d (g z)) ⊙ e z)
  tpR {a = nd s h} {a′ = zero}      oa oa′ (n≼ f) (up x c y e) = ⊥-elim (f c)
  tpR {a = nd s h} {a′ = nd s′ h′}  oa oa′ (n≼ f) (up x c y e) with f c
  ... | c′ , dc =
    let X = tpR oa oa′ (n≼ f) x
        Y = tpR (proj₂ oa c) (proj₂ oa′ c′) dc y in
    up (proj₁ X) c′ (suc (proj₁ Y)) (z◃ (proj₁ Y) ◃s) ,
    ⊹-mono₂ (proj₂ X) (W.emb-≼ (nd s h) c (val (h c) y) ⊙ proj₂ Y ⊙ ≼s _ ⊙ W.≼-emb (nd s′ h′) c′ (W.suc (val (h′ c′) (proj₁ Y))))
```
