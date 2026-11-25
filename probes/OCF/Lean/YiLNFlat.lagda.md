# 冻结接口的配对否定 (二): 自身行摊平的结点在 Ω 结点层号上保留同支

> 验收文件 (否定), 编译定理. 候选字段 `FlatKeep` (摊平进 Ωₗ 层分支 c 的结点, 以同支目标 `inb c w` 折叠时, 以孩子层保留判定给出的槽位为根) 加 `FlatOff` (异支不以任何槽位为根, `legI` 满足), 对 `Iface` 的任何实例弱判定塔第 3 项的下标 c₀ 与一切 c′ 的字面相等 (`flat→wdec`, 经 `branch→wdec`); 加 ℕ → Bool 上的函数外延得 WLPO (`flat→wlpo`, 条件定理); 经同支证据派发 (`FlatE`, `legI` 满足) 则判等 (`flatE→dec`, 经 `diag→dec`). `legI` 不满足 `FlatKeep` (`legI-not-flatKeep`).
> 探针结点是 `legI` 的自身行对塔第 3 项的输入 `up zero c₀ y₀ e₀` 的输出 (`probe-self`); 合法块自己的链步里就有 "同支目标遇到摊平结点而回退" (`chain-flat` 对 `chain-emb`, 有限测试, 单个样本).
> 不否定什么: 接口本身. 重推 `YiUpNegFlat.flat→wdec`, `flat→wlpo`, `flatE→dec` 到合法块与冻结接口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLNFlat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (Ωt; Ωt-nz; Upc)
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; B₀)
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiLPIface using (Iface; Kept)
open import OCF.Lean.YiLPInst using (legI)
open import OCF.Lean.YiAbsObs using (WDec; Dec′; Sep; WLPO; IsJust; sep→wlpo; diag→dec)
open import OCF.Lean.YiAbsFrame using (module Fold)
open import OCF.Lean.YiAbsLeg using (hdΩ)
open import OCF.Lean.YiLNBranch using (c₀; h₃; wc; top₁; y₀; e₀; b₃; β₁; cantor; Funext₀; allF→eq; module Frame)
```

## 候选字段

`root⁼`: 孩子层上合法块的保留判定 (`YiLegFold.kp⁼`) 交出的槽位, 不保留时 `nothing`.

```agda
root⁼ : (a : L) → Ev a → Rt a → Pos⁼ a → {j : L} → j ≤ a → Maybe (Pos j)
root⁼ a ε ρ t w = F.kp⁼ a ε ρ t w (λ q _ → just q) nothing

FlatKeep : Iface → Set
FlatKeep I = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k)
  (w : j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (b : Tr (Ωₗ k h)) (nb : Ωₗ k h ⊢ zero ◃ b)
  (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → root⁼ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (inj₂ p) w ≡ just q
  → Kept q (Iface.ψs I (Ωₗ k h) ε ρ B j (inb c w) β nβ (Upc (Ωₗ k h) c b nb (Ω p G)))

FlatOff : Iface → Set
FlatOff I = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (b : Tr (Ωₗ k h)) (nb : Ωₗ k h ⊢ zero ◃ b)
  (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) → (c ≡ c′ → ⊥)
  → (q : Pos j) → Kept q (Iface.ψs I (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (Upc (Ωₗ k h) c b nb (Ω p G))) → ⊥

FlatE : Iface → Set
FlatE I = Σ ((k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) λ E →
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (b : Tr (Ωₗ k h)) (nb : Ωₗ k h ⊢ zero ◃ b)
  (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) → E k c c′ ≡ nothing
  → (q : Pos j) → Kept q (Iface.ψs I (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (Upc (Ωₗ k h) c b nb (Ω p G))) → ⊥
```

## `legI`: 摊平进分支的结点在分支侧目标下从不保留

对一切 c, c′ (不要求不等): 保留判定在 `inj₂ (c , …)` 对 `inb c′ …` 一行走默认 (ℕ 极限).

```agda
leg-never : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (b : Tr (Ωₗ k h)) (nb : Ωₗ k h ⊢ zero ◃ b)
  (p : Pos (h c)) (G : Br (h c) p → Tr (h c)) (q : Pos j)
  → Kept q (F.ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (Upc (Ωₗ k h) c b nb (Ω p G))) → ⊥
leg-never k h ε ρ B j c c′ w β nβ b nb p G q (G′ , ())

off-legI : FlatOff legI
off-legI k h ε ρ B j c c′ w β nβ b nb p G ne = leg-never k h ε ρ B j c c′ w β nβ b nb p G

flatE-legI : FlatE legI
flatE-legI = (λ _ _ _ → nothing) , λ k h ε ρ B j c c′ w β nβ b nb p G r → leg-never k h ε ρ B j c c′ w β nβ b nb p G
```

## 探针

`p₀` 是 `y₀` 里那个结点 (tw 1 的顶槽位) 在孩子层 h₃ c₀ 里的槽位; `node b nb` 是它摊平进 tw 3 后的样子.

```agda
p₀ : Pos (h₃ c₀)
p₀ = zero , inj₂ (inj₂ (zero , inj₂ top₁))

node : (b : Tr (tw 3)) → tw 3 ⊢ zero ◃ b → Tr (tw 3)
node b nb = Upc (tw 3) c₀ b nb (Ω p₀ (λ _ → zero))

O : Iface → Tr (tw 2) → Tr (tw 1)
O I c′ = Iface.ψs I (tw 3) (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ (wc c′)) (Ωt (tw 1)) (Ωt-nz (tw 1))
           (node (Ωt (tw 3)) (Ωt-nz (tw 3)))

root-p₀ : root⁼ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (proj₂ (Rt-tw 3) c₀) (inj₂ p₀) (wc c₀) ≡ just top₁
root-p₀ = refl

probe-self : (B : Base (tw 3)) (β : Tr (tw 3)) (nβ : tw 3 ⊢ zero ◃ β)
  → F.ψs (tw 3) (Ev-tw 3) (Rt-tw 3) B (tw 3) self β nβ (up zero c₀ y₀ e₀) ≡ node β nβ
probe-self B β nβ = refl
```

## 两侧的头部; 否定

```agda
kept-hd : ∀ {j} {q : Pos j} (o : Tr j) → Kept q o → hdΩ o ≡ true
kept-hd o (G′ , e) = cong hdΩ e

none-hd : ∀ {j} (o : Tr j) → ((q : Pos j) → Kept q o → ⊥) → hdΩ o ≡ false
none-hd zero          f = refl
none-hd (suc o)       f = refl
none-hd (lim g s)     f = refl
none-hd (Ω q G)       f = ⊥-elim (f q (G , refl))
none-hd (up x c y e)  f = refl

keep₀ : (I : Iface) → FlatKeep I → Kept top₁ (O I c₀)
keep₀ I K = K (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c₀ (wc c₀) (Ωt (tw 1)) (Ωt-nz (tw 1))
              (Ωt (tw 3)) (Ωt-nz (tw 3)) p₀ (λ _ → zero) top₁ root-p₀

off₀ : (I : Iface) → FlatOff I → (c′ : Tr (tw 2)) → (c₀ ≡ c′ → ⊥) → hdΩ (O I c′) ≡ false
off₀ I F c′ ne = none-hd _ (F (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c₀ c′ (wc c′) (Ωt (tw 1)) (Ωt-nz (tw 1))
                             (Ωt (tw 3)) (Ωt-nz (tw 3)) p₀ (λ _ → zero) ne)

flat-sep : (I : Iface) → FlatKeep I → FlatOff I → Sep c₀
flat-sep I K F = Fold.branch→sep (Frame.foldI I) (tw 3) b₃ (tw 1) β₁ c₀ wc (node (Ωt (tw 3)) (Ωt-nz (tw 3)))
                   (kept-hd _ (keep₀ I K)) (off₀ I F)

flat→wdec : (I : Iface) → FlatKeep I → FlatOff I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
flat→wdec I K F = Fold.branch→wdec (Frame.foldI I) (tw 3) b₃ (tw 1) β₁ c₀ wc (node (Ωt (tw 3)) (Ωt-nz (tw 3)))
                    (kept-hd _ (keep₀ I K)) (off₀ I F)

flat→wlpo : Funext₀ → (I : Iface) → FlatKeep I → FlatOff I → WLPO
flat→wlpo fe I K F = sep→wlpo (flat-sep I K F) cantor (allF→eq fe)

flatE→dec : (I : Iface) → FlatKeep I → FlatE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)
flatE→dec I K (E , V) = diag→dec (E (tw 2) c₀) (go (E (tw 2) c₀ c₀) refl)
  where
  go : (m : Maybe (c₀ ≡ c₀)) → E (tw 2) c₀ c₀ ≡ m → IsJust (E (tw 2) c₀ c₀)
  go (just e) r = subst IsJust (sym r) tt
  go nothing  r = ⊥-elim (V (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c₀ c₀ (wc c₀) (Ωt (tw 1)) (Ωt-nz (tw 1))
                            (Ωt (tw 3)) (Ωt-nz (tw 3)) p₀ (λ _ → zero) r top₁ (keep₀ I K))

legI-not-flatKeep : FlatKeep legI → ⊥
legI-not-flatKeep K = leg-never (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c₀ c₀ (wc c₀) (Ωt (tw 1)) (Ωt-nz (tw 1))
                        (Ωt (tw 3)) (Ωt-nz (tw 3)) p₀ (λ _ → zero) top₁ (keep₀ legI K)
```

## 合法块自己的链步 (有限测试, 单个样本, 对一切底与偏移)

层号 tw 1, 孩子 c₂ = 2 (孩子层是 2). 自身行把 `yS` 的两个结点摊平到 `s₁`, `s₂`; 外结点的链步以 `posW (tw 1) s₁ = inb c₂ (ins self)` 折分支, 内结点走默认 (`chain-flat`). 摊平前, 孩子层里同一链步保留内结点 (`chain-emb`).

```agda
two : L
two = suc (suc zero)

c₂ : Tr zero
c₂ = suc (suc zero)

yS : Tr two
yS = Ω (inj₁ tt) (λ z → up zero tt (Ω (inj₁ tt) (λ _ → zero)) ◃w)

eS : two ⊢ zero ◃ yS
eS = ◃t (◃u zero tt (Ω (inj₁ tt) (λ _ → zero)) ◃w) ◃w

s₁ s₂ : Pos (tw 1)
s₁ = inj₂ (c₂ , inj₂ (inj₁ tt))
s₂ = inj₂ (c₂ , inj₂ (inj₂ (inj₁ tt)))

chain-self : (B : Base (tw 1)) (β : Tr (tw 1)) (nβ : tw 1 ⊢ zero ◃ β)
  → F.ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B (tw 1) self β nβ (up zero c₂ yS eS) ≡ Ω s₁ (λ _ → Ω s₂ (λ _ → β))
chain-self B β nβ = refl

chain-path : posW (tw 1) s₁ ≡ inb c₂ (ins self)
chain-path = refl

chain-flat : (B : Base (tw 1)) (β : Tr (tw 1)) (β′ : Tr (at (tw 1) s₁)) (nβ′ : at (tw 1) s₁ ⊢ zero ◃ β′)
  → hdΩ (F.ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B (at (tw 1) s₁) (posW (tw 1) s₁) β′ nβ′ (Ω s₂ (λ _ → β))) ≡ false
chain-flat B β β′ nβ′ = refl

chain-emb : (B : Base two) (β′ : Tr (at two (inj₁ tt))) (nβ′ : at two (inj₁ tt) ⊢ zero ◃ β′)
  → hdΩ (F.ψs two tt tt B (at two (inj₁ tt)) (posW two (inj₁ tt)) β′ nβ′
             (up zero tt (Ω (inj₁ tt) (λ _ → zero)) ◃w)) ≡ true
chain-emb B β′ nβ′ = refl
```
