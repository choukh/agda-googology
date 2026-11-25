# 原型 (a): 与精简块的对照, 否定的前提

> 验收文件, 编译定理与有限测试, 无前提. 对照: 塔第 1 项上孩子 two 在 Ω 树之后的第 1 层底, 新块与精简块不是同一棵树 (`new≢old`): 第 1 支在新块是结点, 在精简块是 ℕ 极限 (`old1-form`, `old-br1-lim`).
> `base-same` 的对应物: 孩子 two 下行一步后的第 1 层底与孩子 one 的, 在闭的分支 0, 1 上逐点 `refl` 相等 (`same-0`, `same-1`, 有限测试); 整条不再是 `refl` (分支变量下锚层不同, 临时试验), 也没有 `≢`.
> 否定的前提: 孩子层为常值的 Ω 形状层号上, 分支侧一行在 x 为零时与指定孩子无关 (`const`), 任何布尔观察不分离 (`no-sep`, `on→not-off`); 保留不按存在性 (`kpA-via`, `kpA-top`, `kpA-side`). 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCertNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiCertPath
open import OCF.Lean.YiCertFold
open import OCF.Lean.YiCertCheck
import OCF.Lean.YiRWPath as RP
import OCF.Lean.YiRWFold as R
```

## 与精简块对照

精简块上同一个底 (`R.ψ`, 证据 `RP.Ok-tw 1`): 各支是 `Ωt L1` 加孩子树对第 0 层的折叠.

```agda
BWᵒ : R.Base L2
BWᵒ i u = R.ψ (tw 1) (RP.Ok-tw 1) (R.B₀ (tw 1)) i (inc c2 u) (Ωt i) βΩ

old1-form : proj₁ (BWᵒ L1 (inc tt self))
          ≡ Ω q1 (λ z → proj₁ (Ωt L1 ⊞ R.ψ₀ (h₁ z) (proj₂ (RP.Ok-tw 1) z) (proj₁ (Ωt (h₁ z)))))
old1-form = refl

old-br1-lim : isLim (proj₁ (Ωt L1 ⊞ R.ψ₀ (h₁ c1) (proj₂ (RP.Ok-tw 1) c1) (proj₁ (Ωt (h₁ c1)))))
old-br1-lim = tt

hdΩ : {ℓ : L} → Tr ℓ → Bool
hdΩ (Ω _ _) = true
hdΩ _       = false

at1 : Tr L1 → Tr L1
at1 (Ω (inj₂ (tt , inj₁ tt)) g) = g c1
at1 _                           = zero

t≢f : true ≡ false → ⊥
t≢f ()

new≢old : proj₁ (BW L1 (inc tt self)) ≡ proj₁ (BWᵒ L1 (inc tt self)) → ⊥
new≢old e = t≢f (cong (λ t → hdΩ (at1 t)) e)
```

## `base-same` 的对应物 (有限测试)

```agda
same-0 : proj₁ (br c2 L1 (inc tt self) zero) ≡ proj₁ (br c1 L1 self zero)
same-0 = refl

same-1 : proj₁ (br c2 L1 (inc tt self) c1) ≡ proj₁ (br c1 L1 self c1)
same-1 = refl
```

## 否定的前提

孩子层为常值 a 的 Ω 形状层号 (证书 u 任意): 分支侧一行只经锚层的数据读指定孩子, 所以 x 为零时输出与指定孩子无关. `branch→wdec` 的 `on` 与 `off` 在这族探针上不能同时成立.

```agda
module Const (k : L) (ok : Ok k) (a : L) (oa : Ok a) (u : Ab k a) where

  ℓc : L
  ℓc = nd (sΩ k) (λ _ → a)

  oc : Ok ℓc
  oc = (ok , λ _ → u) , λ _ → oa

  const : (j : L) (v : j ≤ a) (β : Tr⁺ j) (c′ c″ c : Tr k) (y : Tr a) (e : a ⊢ zero ◃ y)
    → ψ ℓc oc (B₀ ℓc) j (inc c′ v) β (up zero c y e) ≡ ψ ℓc oc (B₀ ℓc) j (inc c″ v) β (up zero c y e)
  const j v β c′ c″ c y e = refl

  no-sep : (j : L) (v : j ≤ a) (β : Tr⁺ j) (hd : Tr j → Bool) (c′ c″ c : Tr k) (y : Tr a) (e : a ⊢ zero ◃ y)
    → hd (proj₁ (ψ ℓc oc (B₀ ℓc) j (inc c′ v) β (up zero c y e)))
    ≡ hd (proj₁ (ψ ℓc oc (B₀ ℓc) j (inc c″ v) β (up zero c y e)))
  no-sep j v β hd c′ c″ c y e = refl

  on→not-off : (j : L) (v : j ≤ a) (β : Tr⁺ j) (hd : Tr j → Bool) (c₁ c : Tr k) (y : Tr a) (e : a ⊢ zero ◃ y)
    (c′ : Tr k) → (c₁ ≡ c′ → ⊥)
    → hd (proj₁ (ψ ℓc oc (B₀ ℓc) j (inc c₁ v) β (up zero c y e))) ≡ true
    → ((d : Tr k) → (c₁ ≡ d → ⊥) → hd (proj₁ (ψ ℓc oc (B₀ ℓc) j (inc d v) β (up zero c y e))) ≡ false)
    → ⊥
  on→not-off j v β hd c₁ c y e c′ ne on off = t≢f (trans (sym on) (off c′ ne))
```

前提可满足: k 取第 0 层, a 取 `L1`, 证书 `ab (λ _ → here)`; 两个字面不同的孩子下标 `zero`, `c1`.

```agda
module C¹ = Const zero tt L1 (tt , λ _ → tt) (ab (λ _ → here))

z≢1 : _≡_ {A = Tr zero} zero c1 → ⊥
z≢1 ()

inst : (j : L) (v : j ≤ L1) (β : Tr⁺ j) (hd : Tr j → Bool) (c : Tr zero) (y : Tr L1) (e : L1 ⊢ zero ◃ y)
  → hd (proj₁ (ψ C¹.ℓc C¹.oc (B₀ C¹.ℓc) j (inc zero v) β (up zero c y e))) ≡ true
  → ((d : Tr zero) → (zero ≡ d → ⊥) → hd (proj₁ (ψ C¹.ℓc C¹.oc (B₀ C¹.ℓc) j (inc d v) β (up zero c y e))) ≡ false)
  → ⊥
inst j v β hd c y e = C¹.on→not-off j v β hd zero c y e c1 z≢1
```

保留不按存在性: 证书的叶子是 `via` 时一律不保留; 源层自己那个槽位与内层 Ω 形状的下标层侧槽位一律不保留, 不论目标里有没有同层号的槽位.

```agda
kpA-via : ∀ {k} (a : L) (oa : Ok a) (kk : k ≤ a) {j} (v : j ≤ a) {m} (w : k ≤ m) (t : Pos⁼ m)
  → kpA a oa kk v (via w) t ≡ nothing
kpA-via a oa kk v w t = refl

kpA-top : ∀ {k} (a : L) (oa : Ok a) (kk : k ≤ a) {j} (v : j ≤ a) (s : Sh) (h : Ch s → L) (f : (c : Ch s) → Ab k (h c))
  → kpA a oa kk v {m = nd s h} (ab f) (inj₁ tt) ≡ nothing
kpA-top a oa kk v s h f = refl

kpA-side : ∀ {k} (a : L) (oa : Ok a) (kk : k ≤ a) {j} (v : j ≤ a) (k′ : L) (h : Tr k′ → L)
  (f : (c : Tr k′) → Ab k (h c)) (t : Pos⁼ k′)
  → kpA a oa kk v {m = nd (sΩ k′) h} (ab f) (inj₂ (inj₁ t)) ≡ nothing
kpA-side a oa kk v k′ h f t = refl
```
