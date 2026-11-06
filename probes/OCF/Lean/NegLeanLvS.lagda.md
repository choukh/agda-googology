# 头按自己的级读回, 否定一路 (七): 对主候选 `TVs` (沿 `Sim⁺` 的读回) 的检查

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 对着接口 [LeanLvIf](LeanLvIf.lagda.md) §6 (22:20 "只增": `Sim⁺`, `RdS⁺Ty`) 与构造一路的 [LeanLvRdS](LeanLvRdS.lagda.md), [LeanLvTmS](LeanLvTmS.lagda.md) (22:21 版, 只读导入, 不改) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> 构造一路按 [NegLeanLvInst](NegLeanLvInst.lagda.md) 的对照 (`succK-co`) 改了读回: 过 $\Omega$-极限一支本身的结点, 在 `Sim⁺` 给出后继种类的嵌入时读成那个种类的 $\Omega$-结点. 本篇:
>
> 1. **边界不变 (§1, 定理 `fromSim⁺`, `no-sim⁺`).** `Sim⁺` 忘掉后继种类就是 `Sim`; 所以 `NegLeanLvBlind.no-sim` 对 `Sim⁺` 同样成立: 头 $3+n$ 在 $\Lambda_F$ 里没有与 `st (3+n)` 的 `Sim⁺`. 反方向 `toSim⁺` (一切 `Sim` 都是不带后继种类的 `Sim⁺`): 接口 §6 不逼读回用后继种类 (盲).
> 2. **读回只产出像里的种类 (§2, 定理 `img-readS⁺`, `no-top3⁺`, `no-top3-RLs`).** 同 `NegLeanLvInst.img-readS`, 对 `readS⁺` (后继种类的嵌入与 `Em` 复合, 仍在 `j Em` 的像里). 所以主候选 `TVs` 的头 3 的读回仍不产出 `kTop3` (坐标为 `HB (Lv (st 2))` 的种类).
> 3. **改动生效 (§3, 定理 `rd-Ωd⁺`, `exec-TVs2`).** `Ωd (Sg 1)` (状态里 `Stp` 发出的 $\Omega_{S_1}$ 的数据) 现在读成后继种类 `(inj₂ (β+1) , inj₂ tt)` 的 $\Omega$-结点再加一 ($\beta$ = 世界里头 0 的界), 不再是 `NegLeanLvTm.rd-Ωd` 的有限 $b+2$. 头 2 的回灌行在 `TVs` 的计算里出现 (`exec-TVs2`, 同 `exec-TF2` 的路径).
>
> **只否定什么.** `no-sim⁺` 只否定 $\Lambda_F$ 里的 `Sim⁺` 级层与 `st (3+n)`; `no-top3-RLs` 只说头 3 的读回的种类. 不说值, 不否定路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvS where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (bkS; toFb)
open import OCF.Lean.LeanLvIf renaming (inS to hinS; inL to hinL; inΩ to hinΩ; here to hhere)
open import OCF.Lean.LeanLvEmb using (emb2; _∘E_; stepE; supE)
open import OCF.Lean.LeanLvTm using (Sg)
open import OCF.Lean.LeanLvTmS using (σ₂⁺; RLs; feedLs; fbS; ΨVs)
import OCF.Lean.LeanLvRdS as RdM
import OCF.Lean.LeanTFold as Fold
open import OCF.Lean.NegLeanFbInst using (Dir; dL; dR; dN; nav)
open import OCF.Lean.NegLeanLvPre using () renaming (L₀ to L₀ˢ)
open import OCF.Lean.NegLeanLvBlind using (no-sim)
open import OCF.Lean.NegLeanLvEmb using (kTop3; miss-top; E1)
open import OCF.Lean.NegLeanLvInst using (AllK; allK-has; all-nbJ)
```

## §1 `Sim⁺` 与 `Sim`

```agda
module _ {T : KS} where
  fromSim⁺ : ∀ {a x} → Sim⁺ T a x → Sim T a x
  fromSim⁺ sz⁺ = sz
  fromSim⁺ (ss⁺ σ) = ss (fromSim⁺ σ)
  fromSim⁺ (sl⁺ σf sk) = sl (λ n → fromSim⁺ (σf n))
  fromSim⁺ (sΩ⁺ cv σg sk) = sΩ cv (λ e → fromSim⁺ (σg e))

  toSim⁺ : ∀ {a x} → Sim T a x → Sim⁺ T a x
  toSim⁺ sz = sz⁺
  toSim⁺ (ss σ) = ss⁺ (toSim⁺ σ)
  toSim⁺ (sl σf) = sl⁺ (λ n → toSim⁺ (σf n)) (λ _ → inj₂ tt)
  toSim⁺ (sΩ cv σg) = sΩ⁺ cv (λ e → toSim⁺ (σg e)) (λ _ → inj₂ tt)

no-sim⁺ : ∀ n {ℓ} → ℓ ⊲[ w₀ L₀ˢ ] ΛF → ¬ Sim⁺ SLs ℓ (stL (suc (suc (suc n))))
no-sim⁺ n p σ = no-sim n p (fromSim⁺ σ)
```

## §2 读回只产出像里的种类

```agda
module Img⁺ (T : KS) where
  open Tree T
  open RdM T

  MP : ∀ {X} (P : K X → Set) {x} → Emb (Lv (ls x)) X ⊎ ⊤ → Set
  MP P (inj₁ Ep) = ∀ κ → P (j Ep κ)
  MP P (inj₂ _) = ⊤

  mp-map : ∀ {Y X} (Em : Emb Y X) (P : K X → Set) → (∀ κ → P (j Em κ)) → ∀ {x} (s : Emb (Lv (ls x)) Y ⊎ ⊤) → MP P (map₁ (Em ∘E_) s)
  mp-map Em P pj (inj₁ E′) = λ κ → pj (j E′ κ)
  mp-map Em P pj (inj₂ _) = tt

  readS-P  : ∀ {a x} (σ : Sim⁺ T a x) {X} (Em : Emb (Lv x) X) (P : K X → Set) → (∀ κ → P (j Em κ)) →
             ∀ {W} (lW : LgW L₀ W) b (d : D a W) → AllK P b → AllK P (readS σ Em lW b d)
  readSp-P : ∀ {a x} (σ : Sim⁺ T a x) {X} (Em : Emb (Lv x) X) (P : K X → Set) → (∀ κ → P (j Em κ)) →
             ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D a W) → AllK P b → ∀ n → AllK P (readSp σ Em lW b d n)
  rdN-P    : ∀ {a₀ x₀} (σ₀ : Sim⁺ T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) → AllK P b → AllK P (rdN σ₀ E₀ lW b r₀ u)
  rdP-P    : ∀ {a₀ x₀} (σ₀ : Sim⁺ T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {a x} (σ : Sim⁺ T a x) (Em : Emb (Lv x) X) → (∀ κ → P (j Em κ)) → (m : Emb (Lv (ls x)) X ⊎ ⊤) → MP P m →
             ∀ {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) (Q : k ⊲[ W ] a) → AllK P b → AllK P (rdP σ₀ E₀ σ Em m lW b r₀ u Q)
  slf-P    : ∀ {a₀ x₀} (σ₀ : Sim⁺ T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {a x} (σ : Sim⁺ T a x) (m : Emb (Lv (ls x)) X ⊎ ⊤) → MP P m →
             ∀ {W} (lW : LgW L₀ W) b (r₀ : StH W a a₀) (u : Br r₀) → AllK P b → AllK P (slf σ₀ E₀ σ m lW b r₀ u)
  readS-P σ Em P pj lW b n0 ab = ab
  readS-P σ Em P pj lW b n1 ab = ab
  readS-P σ Em P pj lW b (x ⨾ y) ab = readS-P σ Em P pj lW (readS σ Em lW b x) y (readS-P σ Em P pj lW b x ab)
  readS-P σ Em P pj lW b (nl d) ab = readSp-P σ Em P pj lW b d ab
  readS-P σ Em P pj lW b (ni r u) ab = rdN-P σ Em P pj lW b r u ab
  readS-P σ Em P pj lW b (nc κ z u) ab = readS-P σ Em P pj lW b (u ≤rf lW) ab
  readS-P σ Em P pj lW b (nw p x) ab = readS-P σ Em P pj (lgDn L₀ p lW) b x ab
  readSp-P σ Em P pj lW b d ab zero = ab
  readSp-P σ Em P pj lW b d ab (suc n) = readS-P σ Em P pj lW (readSp σ Em lW b d n) (d n) (readSp-P σ Em P pj lW b d ab n)

  rdN-P (ss⁺ σ₁) Em P pj lW b (ss Q) u ab =
    rdP-P (ss⁺ σ₁) Em P pj σ₁ (Em ∘E stepE) (λ κ → pj (inj₁ κ)) (inj₁ Em) pj lW b (ss Q) u Q ab
  rdN-P (sl⁺ σf sk) Em P pj lW b (sl n Q) u ab =
    rdP-P (sl⁺ σf sk) Em P pj (σf n) (Em ∘E supE n) (λ κ → pj (n , κ)) (map₁ (Em ∘E_) (sk n)) (mp-map Em P pj (sk n)) lW b (sl n Q) u Q ab
  rdN-P (sΩ⁺ cv′ σg sk) Em P pj lW b (sL {c = e} bd Q) u ab =
    rdP-P (sΩ⁺ cv′ σg sk) Em P pj (σg e) (Em ∘E supE (inj₂ (cv′ e))) (λ κ → pj (inj₂ (cv′ e) , κ))
      (map₁ (Em ∘E_) (sk e)) (mp-map Em P pj (sk e)) lW b (sL bd Q) u Q ab

  rdP-P σ₀ E₀ P p₀ σ Em pj m pm lW b r₀ u hself ab = slf-P σ₀ E₀ P p₀ σ m pm lW b r₀ u ab
  rdP-P σ₀ E₀ P p₀ (ss⁺ σ₁) Em pj m pm lW b r₀ u (hsuc Q) ab =
    rdP-P σ₀ E₀ P p₀ σ₁ (Em ∘E stepE) (λ κ → pj (inj₁ κ)) (inj₁ Em) pj lW b r₀ u Q ab
  rdP-P σ₀ E₀ P p₀ (sl⁺ σf sk) Em pj m pm lW b r₀ u (hlim n Q) ab =
    rdP-P σ₀ E₀ P p₀ (σf n) (Em ∘E supE n) (λ κ → pj (n , κ)) (map₁ (Em ∘E_) (sk n)) (mp-map Em P pj (sk n)) lW b r₀ u Q ab
  rdP-P σ₀ E₀ P p₀ (sΩ⁺ cv′ σg sk) Em pj m pm lW b r₀ u (hLim {c = e} bd Q) ab =
    rdP-P σ₀ E₀ P p₀ (σg e) (Em ∘E supE (inj₂ (cv′ e))) (λ κ → pj (inj₂ (cv′ e) , κ))
      (map₁ (Em ∘E_) (sk e)) (mp-map Em P pj (sk e)) lW b r₀ u Q ab

  slf-P σ₀ E₀ P p₀ σ (inj₁ Ep) pm lW b r₀ u ab =
    pm (inj₂ tt) ,
    (λ e → all-nbJ (Ep ∘E stepE) P (λ κ → pm (inj₁ κ)) b _ ab
             (λ y h ah → readS-P σ₀ E₀ P p₀ lW h (u ≤rf lW (inS r₀ (wrS σ y))) ah) (cv Ep e))
  slf-P σ₀ E₀ P p₀ σ (inj₂ _) pm lW b r₀ u ab = readS-P σ₀ E₀ P p₀ lW b (u ≤rf lW (inS r₀ n0)) ab

  InImg : ∀ {S′ S : KS} → Emb S′ S → K S → Set
  InImg {S′} Em κ = Σ (K S′) (λ κ′ → j Em κ′ ≡ κ)

  img-readS⁺ : ∀ {a x} (σ : Sim⁺ T a x) {X} (Em : Emb (Lv x) X) {W} (lW : LgW L₀ W) b (d : D a W) →
    AllK (InImg Em) b → AllK (InImg Em) (readS σ Em lW b d)
  img-readS⁺ σ Em lW b d = readS-P σ Em (InImg Em) (λ κ → κ , refl) lW b d

  no-top3⁺ : ∀ {a} (σ : Sim⁺ T a (stL 2)) {W} (lW : LgW L₀ W) (d : D a W) → ¬ HasK kTop3 (readS σ E1 lW hz d)
  no-top3⁺ σ lW d h with allK-has (InImg E1) (img-readS⁺ σ E1 lW hz d tt) h
  ... | κ , e = miss-top κ e

open Tree SLs
open RdM SLs using (readS)

no-top3-RLs : ∀ {W} (lW : LgW L₀ W) (x : D (Sg 1) W) → ¬ HasK kTop3 (LvRd.δ (RLs 1) lW x)
no-top3-RLs lW x = Img⁺.no-top3⁺ SLs σ₂⁺ lW x
```

## §3 改动生效

$\beta$ = 世界 $W$ 里头 0 的界 (`top L₀ (inj₁ (νS 0)) W`). `Ωd (Sg 1)` 读成后继种类 `(inj₂ (β+1) , inj₂ tt)` 的 $\Omega$-结点.

```agda
rd-Ωd⁺ : ∀ m {W} (lW : LgW L₀ W) b →
  Σ (_ → HB (Lv (stL (suc (suc m))))) (λ g →
    readS σ₂⁺ (emb2 m) lW b (Ωd (Sg 1)) ≡ hΩ (Emb.j (emb2 m) (inj₂ (hs (top L₀ (inj₁ (νS 0)) W)) , inj₂ tt)) g)
rd-Ωd⁺ m lW b = _ , refl
```

**回灌行在 `TVs` 里出现.**

```agda
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fbS

fbS-head2 : fbS (νS 2) ≡ inj₁ (toFb (feedLs 0))
fbS-head2 = refl

exec-TVs2 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 3 ∷ dN 0 ∷ dL ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨVs ≡ RKa _ (fbS (νS 2)) _ _ _ _ _ _ _ Tq
exec-TVs2 Tq = refl
```

## §4 结论 (按档)

- **[定理]** `fromSim⁺`, `toSim⁺`, **`no-sim⁺`** (头 $3+n$ 在 $\Lambda_F$ 里没有 `Sim⁺` 级层). **`img-readS⁺`**, **`no-top3⁺`**, **`no-top3-RLs`** (主候选的头 3 的读回不产出 `kTop3`). **`rd-Ωd⁺`** (`refl`; $\Omega_{S_1}$ 的数据现在读成 $\Omega$-结点), `fbS-head2`, **`exec-TVs2`** (`refl`).
- **[定理, 盲]** `toSim⁺`: 接口 §6 不逼后继种类 (一切 `Sim` 给出不带后继种类的 `Sim⁺`); `lvSims` 的 `σ` 字段是 `σ₂` (`Sim`), 读回走的是 `σ₂⁺`, 两者是否一致由构造一路判断 (逐构造子对照), 接口不管 (盲区第 1 条).
