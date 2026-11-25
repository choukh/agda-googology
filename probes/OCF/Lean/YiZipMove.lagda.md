# 层号之间的结构搬运: 保第一位置, 保合法

非验收文件. 编译定理, 无前提: 对一切两个层号 `a b` 定义树的搬运 `mv a b : Raw a → Raw b` (停机由检查器保证), `mv-cp` 保第一位置, `mv-lgl` 保合法, `mv-br` 分支族与搬运复合仍是 `Br`.
零, 后继, ℕ 极限层号之间按结构对齐位置与孩子; 对不上 (含 Ω 结点层号) 时位置上的结点取 `top` 那一支的值 (照 `YiLamFold` 的 `Kfk` 的 `lc` 子句), 孩子按源的孩子层直接搬. 值正确的情形在 [YiZipSim](YiZipSim.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZipMove where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (Br; DnB; LgB; dnLc; lgLc)
```

## 1 搬运

`mvN a b B r h`: 源层 `a` 的位置 `r` 上的结点 (分支已搬成 `h`) 在目标层 `b` 里的像, `B` 造目标的结点 (同 `add` 的 `Bld`).
两个位置在后继的根处对上时, 分支的输入要反向搬: `mv k′ k`. 停机度量: 两个层号互换且都严格下降, 或树下降.

```agda
mv  : (a b : LF) → Raw a → Raw b
mvN : ∀ {M} (a b : LF) → Bld M b → (r : Pre a) → (Lay.A (Lo a r) → Raw M) → Raw M

mv a b G.zero = G.zero
mv a b (G.suc x) = G.suc (mv a b x)
mv a b (G.lim f) = G.lim (λ n → mv a b (f n))
mv a b (G.lc r g) = mvN a b G.lc r (λ η → mv a b (g η))
mv a b G.top = G.top
mv zero b (G.em () y)
mv (suc k) (suc k′) (G.em _ y) = G.em tt (mv k k′ y)
mv (suc k) zero (G.em _ y) = mv k zero y
mv (suc k) (lim f′) (G.em _ y) = mv k (lim f′) y
mv (suc k) (lc k′ g′) (G.em _ y) = mv k (lc k′ g′) y
mv (lim f) (lim f′) (G.em n y) = G.em n (mv (f n) (f′ n) y)
mv (lim f) zero (G.em n y) = mv (f n) zero y
mv (lim f) (suc k′) (G.em n y) = mv (f n) (suc k′) y
mv (lim f) (lc k′ g′) (G.em n y) = mv (f n) (lc k′ g′) y
mv (lc k g) b (G.em (η , _) y) = mv (g η) b y

mvN zero b B () h
mvN (suc k) (suc k′) B (inj₁ _) h = B (inj₁ tt) (λ η → h (mv k′ k η))
mvN (suc k) zero B (inj₁ _) h = h G.top
mvN (suc k) (lim f′) B (inj₁ _) h = h G.top
mvN (suc k) (lc k′ g′) B (inj₁ _) h = h G.top
mvN (suc k) (suc k′) B (inj₂ r) h = mvN k k′ (λ r′ → B (inj₂ r′)) r h
mvN (suc k) zero B (inj₂ r) h = mvN k zero B r h
mvN (suc k) (lim f′) B (inj₂ r) h = mvN k (lim f′) B r h
mvN (suc k) (lc k′ g′) B (inj₂ r) h = mvN k (lc k′ g′) B r h
mvN (lim f) (lim f′) B (n , r) h = mvN (f n) (f′ n) (λ r′ → B (n , r′)) r h
mvN (lim f) zero B (n , r) h = mvN (f n) zero B r h
mvN (lim f) (suc k′) B (n , r) h = mvN (f n) (suc k′) B r h
mvN (lim f) (lc k′ g′) B (n , r) h = mvN (f n) (lc k′ g′) B r h
mvN (lc k g) b B (η , _ , r) h = mvN (g η) b B r h

mv-top : ∀ a b → mv a b G.top ≡ G.top
mv-top a b = refl
```

## 2 保第一位置

```agda
em1 : ∀ {k u v} → Cp k u v → Cp (suc k) (G.em tt u) (G.em tt v)
em1 (inj₁ refl) = inj₁ refl
em1 (inj₂ p) = inj₂ (refl , p)

emω : ∀ {f : ℕ → LF} n {u v} → Cp (f n) u v → Cp (lim f) (G.em n u) (G.em n v)
emω n (inj₁ refl) = inj₁ refl
emω n (inj₂ p) = inj₂ (refl , p)

mvN-dn : ∀ {M} a b (B : Bld M b) → DnB B → (r : Pre a) (h : Lay.A (Lo a r) → Raw M) {z : Raw M} →
  Cp M z (h (Lay.tp (Lo a r))) → Cp M z (mvN a b B r h)
mvN-dn zero b B hB () h q
mvN-dn (suc k) (suc k′) B hB (inj₁ _) h q = inj₂ (hB (inj₁ tt) _ q)
mvN-dn (suc k) zero B hB (inj₁ _) h q = q
mvN-dn (suc k) (lim f′) B hB (inj₁ _) h q = q
mvN-dn (suc k) (lc k′ g′) B hB (inj₁ _) h q = q
mvN-dn (suc k) (suc k′) B hB (inj₂ r) h q = mvN-dn k k′ (λ r′ → B (inj₂ r′)) (λ r′ → hB (inj₂ r′)) r h q
mvN-dn (suc k) zero B hB (inj₂ r) h q = mvN-dn k zero B hB r h q
mvN-dn (suc k) (lim f′) B hB (inj₂ r) h q = mvN-dn k (lim f′) B hB r h q
mvN-dn (suc k) (lc k′ g′) B hB (inj₂ r) h q = mvN-dn k (lc k′ g′) B hB r h q
mvN-dn (lim f) (lim f′) B hB (n , r) h q = mvN-dn (f n) (f′ n) (λ r′ → B (n , r′)) (λ r′ → hB (n , r′)) r h q
mvN-dn (lim f) zero B hB (n , r) h q = mvN-dn (f n) zero B hB r h q
mvN-dn (lim f) (suc k′) B hB (n , r) h q = mvN-dn (f n) (suc k′) B hB r h q
mvN-dn (lim f) (lc k′ g′) B hB (n , r) h q = mvN-dn (f n) (lc k′ g′) B hB r h q
mvN-dn (lc k g) b B hB (η , _ , r) h q = mvN-dn (g η) b B hB r h q

mv-cp : ∀ a b {x y : Raw a} → Cp a x y → Cp b (mv a b x) (mv a b y)
mv-dn : ∀ a b {x : Raw a} (y : Raw a) → Dn a x y → Cp b (mv a b x) (mv a b y)

mv-cp a b (inj₁ refl) = inj₁ refl
mv-cp a b (inj₂ p) = mv-dn a b _ p

mv-dn a b (G.suc y) p = inj₂ (mv-cp a b p)
mv-dn a b (G.lim f) (n , p) = inj₂ (n , mv-cp a b p)
mv-dn a b (G.lc r g) p = mvN-dn a b G.lc dnLc r (λ η → mv a b (g η)) (mv-cp a b p)
mv-dn (suc k) (suc k′) {G.em _ x} (G.em _ y) (refl , p) = em1 (mv-dn k k′ y p)
mv-dn (suc k) zero {G.em _ x} (G.em _ y) (refl , p) = mv-dn k zero y p
mv-dn (suc k) (lim f′) {G.em _ x} (G.em _ y) (refl , p) = mv-dn k (lim f′) y p
mv-dn (suc k) (lc k′ g′) {G.em _ x} (G.em _ y) (refl , p) = mv-dn k (lc k′ g′) y p
mv-dn (lim f) (lim f′) {G.em n x} (G.em _ y) (refl , p) = emω n (mv-dn (f n) (f′ n) y p)
mv-dn (lim f) zero {G.em n x} (G.em _ y) (refl , p) = mv-dn (f n) zero y p
mv-dn (lim f) (suc k′) {G.em n x} (G.em _ y) (refl , p) = mv-dn (f n) (suc k′) y p
mv-dn (lim f) (lc k′ g′) {G.em n x} (G.em _ y) (refl , p) = mv-dn (f n) (lc k′ g′) y p
mv-dn (lc k g) b {G.em (η , _) x} (G.em _ y) (refl , p) = mv-dn (g η) b y p
```

## 3 保合法, 与分支族的复合

```agda
mv-lgl  : ∀ a b (x : Raw a) → Lgl a x → Lgl b (mv a b x)
mvN-lgl : ∀ {M} a b (B : Bld M b) → LgB B → (r : Pre a) (h : Lay.A (Lo a r) → Raw M) →
  Br (Lo a r) M h → Lgl M (mvN a b B r h)
mv-br   : ∀ c d {M} (h : Raw d → Raw M) → Br (layer d) M h → Br (layer c) M (λ η → h (mv c d η))

mv-lgl a b G.zero l = tt
mv-lgl a b (G.suc x) l = mv-lgl a b x l
mv-lgl a b (G.lim f) (st , lf) = (λ n → mv-cp a b (st n)) , (λ n → mv-lgl a b (f n) (lf n))
mv-lgl a b (G.lc r g) (lg , mo) = mvN-lgl a b G.lc lgLc r (λ η → mv a b (g η))
  ((λ η l → mv-lgl a b (g η) (lg η l)) , (λ η η′ l e l′ → mv-cp a b (mo η η′ l e l′)))
mv-lgl a b G.top l = tt
mv-lgl (suc k) (suc k′) (G.em _ y) l = mv-lgl k k′ y l
mv-lgl (suc k) zero (G.em _ y) l = mv-lgl k zero y l
mv-lgl (suc k) (lim f′) (G.em _ y) l = mv-lgl k (lim f′) y l
mv-lgl (suc k) (lc k′ g′) (G.em _ y) l = mv-lgl k (lc k′ g′) y l
mv-lgl (lim f) (lim f′) (G.em n y) l = mv-lgl (f n) (f′ n) y l
mv-lgl (lim f) zero (G.em n y) l = mv-lgl (f n) zero y l
mv-lgl (lim f) (suc k′) (G.em n y) l = mv-lgl (f n) (suc k′) y l
mv-lgl (lim f) (lc k′ g′) (G.em n y) l = mv-lgl (f n) (lc k′ g′) y l
mv-lgl (lc k g) b (G.em (η , _) y) l = mv-lgl (g η) b y l

mvN-lgl (suc k) (suc k′) B hB (inj₁ _) h hb = hB (inj₁ tt) _ (mv-br k′ k h hb)
mvN-lgl (suc k) zero B hB (inj₁ _) h hb = proj₁ hb G.top tt
mvN-lgl (suc k) (lim f′) B hB (inj₁ _) h hb = proj₁ hb G.top tt
mvN-lgl (suc k) (lc k′ g′) B hB (inj₁ _) h hb = proj₁ hb G.top tt
mvN-lgl (suc k) (suc k′) B hB (inj₂ r) h hb =
  mvN-lgl k k′ (λ r′ → B (inj₂ r′)) (λ r′ → hB (inj₂ r′)) r h hb
mvN-lgl (suc k) zero B hB (inj₂ r) h hb = mvN-lgl k zero B hB r h hb
mvN-lgl (suc k) (lim f′) B hB (inj₂ r) h hb = mvN-lgl k (lim f′) B hB r h hb
mvN-lgl (suc k) (lc k′ g′) B hB (inj₂ r) h hb = mvN-lgl k (lc k′ g′) B hB r h hb
mvN-lgl (lim f) (lim f′) B hB (n , r) h hb =
  mvN-lgl (f n) (f′ n) (λ r′ → B (n , r′)) (λ r′ → hB (n , r′)) r h hb
mvN-lgl (lim f) zero B hB (n , r) h hb = mvN-lgl (f n) zero B hB r h hb
mvN-lgl (lim f) (suc k′) B hB (n , r) h hb = mvN-lgl (f n) (suc k′) B hB r h hb
mvN-lgl (lim f) (lc k′ g′) B hB (n , r) h hb = mvN-lgl (f n) (lc k′ g′) B hB r h hb
mvN-lgl (lc k g) b B hB (η , _ , r) h hb = mvN-lgl (g η) b B hB r h hb

mv-br c d h (lg , mo) = (λ η l → lg (mv c d η) (mv-lgl c d η l)) ,
  (λ η η′ l e l′ → mo _ _ (mv-lgl c d η l) (mv-cp c d e) (mv-lgl c d η′ l′))
```
