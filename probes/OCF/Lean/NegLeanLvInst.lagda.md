# 头按自己的级读回, 否定一路 (五): 对构造一路读回 `LeanLvRd` 的检查

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 只读导入构造一路的 [LeanLvRd](LeanLvRd.lagda.md), [LeanLvEmb](LeanLvEmb.lagda.md) (22:17 版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **三个检查.**
>
> 1. **读回产出哪些种类 (§1, 定理 `readS-P`, `img-readS`).** 对一切 $T$, 一切同形 $\sigma$, 一切嵌入 `Em : Emb (Lv x) X`: 起点的 $\Omega$-结点都在 `j Em` 的像里时, `readS σ Em` 的输出的一切 $\Omega$-结点都在 `j Em` 的像里. (更一般: 对任一性质 $P$, `j Em` 的像都满足 $P$ 时, 输出保持 $P$.)
> 2. **头 3 读不出 `kTop3` (§2, 定理 `no-top3`).** 与 [NegLeanLvEmb](NegLeanLvEmb.lagda.md) 的 `miss-top` 合起来: 对一切 $T$, 一切 `σ : Sim T a (st 2)`, 一切数据, 经 `emb2 1` 的读回 (起点 $0$ 或任一像内的起点) 的输出里**没有** `kTop3` (`Lv (st 3)` 里坐标为 `HB (Lv (st 2))` 的种类) 的 $\Omega$-结点. 这是 `NegLeanFbInst.rdX-one-kind` 高一层的版本: 构造一路计划里头 $n\ge3$ 的界只按 `Lv (st 2)` 的那份拷贝里的种类增长.
> 3. **停在 $\Omega$-极限一支本身的结点有损, 但不是被 `Lv` 的形状逼的 (§3).** **`rdΩ-top-lossy`** (定理, `refl`, 对一切 $T$ 与一切 $\Omega$-头的同形, 头 2 的 `sim2` 是一例): 级层 $S_1$ 上, 过分支 $c$ 本身的结点 (`ni (sL bd hself) u`) 读成 "分支在输入 $0$ 处的读回", 与 $c$ 和数据无关的那部分丢掉. 构造一路文件头的判断是 "这是 `Lv` 的形状". **对照 `NegLeanLvPre.succK-co`** (定理): `Lv (st 2)` 有一个坐标字面是 `HB (Lv (g₂ c))` 的种类 `succK c` (分支 $c+1$ 处的新种类), 恰是这个结点的子层沿 `sim2` 的读回类型. 所以头 2 处的这一处有损**不是** `Lv` 的形状逼出的; 读成 `succK c` 的 $\Omega$-结点在类型上可行 (是否保持合法未查, 判断). `Ωd` 的 $\Omega$-行发出的结点恰好是这种 (`ni (sL top hself) _`, `LeanTTree` §4), 所以这一处有损落在 $\Omega_{S_1}$ 的主结点上 (判断, 依据 `Ωd` 的定义).
>
> **只否定什么.** `no-top3` 只说经 `emb2 1` 的 `readS` 不产出 `kTop3`; 不说值, 不否定嵌入链, 不否定计划. `rdΩ-top-lossy` 是定义相等, 不是否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanLvIf renaming (inS to hinS; inL to hinL; inΩ to hinΩ; here to hhere)
open import OCF.Lean.LeanLvEmb
open import OCF.Lean.LeanFbSt using (st; SLs; ιS)
import OCF.Lean.LeanLvRd as RdM
open import OCF.Lean.NegLeanLvEmb using (kTop3; miss-top; E1)
open import OCF.Lean.NegLeanLvBlind using (sim2)
open import OCF.Lean.NegLeanLvPre using (Sg)
```

## §1 读回的输出只含像里的种类

```agda
module _ {S : KS} (P : K S → Set) where
  AllK : HB S → Set
  AllK hz = ⊤
  AllK (hs h) = AllK h
  AllK (hl f) = ∀ n → AllK (f n)
  AllK (hΩ κ g) = P κ × (∀ c → AllK (g c))

  allK-has : ∀ {κ h} → AllK h → HasK κ h → P κ
  allK-has a hhere = proj₁ a
  allK-has a (hinS q) = allK-has a q
  allK-has a (hinL n q) = allK-has (a n) q
  allK-has a (hinΩ c q) = allK-has (proj₂ a c) q

module _ {S′ S : KS} (Em : Emb S′ S) (P : K S → Set) (pj : ∀ κ → P (j Em κ)) where
  all-nbJ : ∀ b (s : HB S′ → HB S → HB S) → AllK P b → (∀ y h → AllK P h → AllK P (s y h)) → ∀ y → AllK P (nbJ Em b s y)
  all-nbJ b s ab as hz = ab
  all-nbJ b s ab as (hs y) = as y _ (all-nbJ b s ab as y)
  all-nbJ b s ab as (hl f) = λ n → all-nbJ b s ab as (f n)
  all-nbJ b s ab as (hΩ κ h) = pj κ , (λ e → all-nbJ b s ab as (h (cv Em e)))

module Img (T : KS) where
  open Tree T
  open RdM T

  MP : ∀ {X} (P : K X → Set) {x} → Emb (Lv (ls x)) X ⊎ ⊤ → Set
  MP P (inj₁ Ep) = ∀ κ → P (j Ep κ)
  MP P (inj₂ _) = ⊤

  readS-P  : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) (P : K X → Set) → (∀ κ → P (j Em κ)) →
             ∀ {W} (lW : LgW L₀ W) b (d : D a W) → AllK P b → AllK P (readS σ Em lW b d)
  readSp-P : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) (P : K X → Set) → (∀ κ → P (j Em κ)) →
             ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D a W) → AllK P b → ∀ n → AllK P (readSp σ Em lW b d n)
  rdN-P    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) → AllK P b → AllK P (rdN σ₀ E₀ lW b r₀ u)
  rdP-P    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {a x} (σ : Sim T a x) (Em : Emb (Lv x) X) → (∀ κ → P (j Em κ)) → (m : Emb (Lv (ls x)) X ⊎ ⊤) → MP P m →
             ∀ {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) (Q : k ⊲[ W ] a) → AllK P b → AllK P (rdP σ₀ E₀ σ Em m lW b r₀ u Q)
  slf-P    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) (P : K X → Set) → (∀ κ → P (j E₀ κ)) →
             ∀ {a x} (σ : Sim T a x) (m : Emb (Lv (ls x)) X ⊎ ⊤) → MP P m →
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

  rdN-P (ss σ₁) Em P pj lW b (ss Q) u ab =
    rdP-P (ss σ₁) Em P pj σ₁ (Em ∘E stepE) (λ κ → pj (inj₁ κ)) (inj₁ Em) pj lW b (ss Q) u Q ab
  rdN-P (sl σf) Em P pj lW b (sl n Q) u ab =
    rdP-P (sl σf) Em P pj (σf n) (Em ∘E supE n) (λ κ → pj (n , κ)) (inj₂ tt) tt lW b (sl n Q) u Q ab
  rdN-P (sΩ cv′ σg) Em P pj lW b (sL {c = e} bd Q) u ab =
    rdP-P (sΩ cv′ σg) Em P pj (σg e) (Em ∘E supE (inj₂ (cv′ e))) (λ κ → pj (inj₂ (cv′ e) , κ)) (inj₂ tt) tt lW b (sL bd Q) u Q ab

  rdP-P σ₀ E₀ P p₀ σ Em pj m pm lW b r₀ u hself ab = slf-P σ₀ E₀ P p₀ σ m pm lW b r₀ u ab
  rdP-P σ₀ E₀ P p₀ (ss σ₁) Em pj m pm lW b r₀ u (hsuc Q) ab =
    rdP-P σ₀ E₀ P p₀ σ₁ (Em ∘E stepE) (λ κ → pj (inj₁ κ)) (inj₁ Em) pj lW b r₀ u Q ab
  rdP-P σ₀ E₀ P p₀ (sl σf) Em pj m pm lW b r₀ u (hlim n Q) ab =
    rdP-P σ₀ E₀ P p₀ (σf n) (Em ∘E supE n) (λ κ → pj (n , κ)) (inj₂ tt) tt lW b r₀ u Q ab
  rdP-P σ₀ E₀ P p₀ (sΩ cv′ σg) Em pj m pm lW b r₀ u (hLim {c = e} bd Q) ab =
    rdP-P σ₀ E₀ P p₀ (σg e) (Em ∘E supE (inj₂ (cv′ e))) (λ κ → pj (inj₂ (cv′ e) , κ)) (inj₂ tt) tt lW b r₀ u Q ab

  slf-P σ₀ E₀ P p₀ σ (inj₁ Ep) pm lW b r₀ u ab =
    pm (inj₂ tt) ,
    (λ e → all-nbJ (Ep ∘E stepE) P (λ κ → pm (inj₁ κ)) b _ ab
             (λ y h ah → readS-P σ₀ E₀ P p₀ lW h (u ≤rf lW (inS r₀ (wrS σ y))) ah) (cv Ep e))
  slf-P σ₀ E₀ P p₀ σ (inj₂ _) pm lW b r₀ u ab = readS-P σ₀ E₀ P p₀ lW b (u ≤rf lW (inS r₀ n0)) ab

  -- 像: Σ κ′, j Em κ′ ≡ κ
  InImg : ∀ {S′ S : KS} → Emb S′ S → K S → Set
  InImg {S′} Em κ = Σ (K S′) (λ κ′ → j Em κ′ ≡ κ)

  img-readS : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) {W} (lW : LgW L₀ W) b (d : D a W) →
    AllK (InImg Em) b → AllK (InImg Em) (readS σ Em lW b d)
  img-readS σ Em lW b d = readS-P σ Em (InImg Em) (λ κ → κ , refl) lW b d
```

## §2 头 3 读不出 `kTop3`

```agda
  no-top3 : ∀ {a} (σ : Sim T a (st 2)) {W} (lW : LgW L₀ W) b (d : D a W) →
    AllK (InImg E1) b → ¬ HasK kTop3 (readS σ E1 lW b d)
  no-top3 σ lW b d ab h with allK-has (InImg E1) (img-readS σ E1 lW b d ab) h
  ... | κ , e = miss-top κ e

  -- 前提实例: 起点 0
  no-top3-hz : ∀ {a} (σ : Sim T a (st 2)) {W} (lW : LgW L₀ W) (d : D a W) → ¬ HasK kTop3 (readS σ E1 lW hz d)
  no-top3-hz σ lW d = no-top3 σ lW hz d tt
```

## §3 停在 $\Omega$-极限的一支本身: 读成输入 $0$ 的分支

对一切 $T$, 一切 $\Omega$-头的同形 `sΩ cv′ σg` (头 2 的 `sim2` 是一例): 过一支 $h\,c$ 本身的结点读成分支在输入 $0$ 处的读回.

```agda
  rdΩ-top-lossy : ∀ {κ h k g} (cv′ : E L₀ κ → HB (Lv k)) (σg : ∀ e → Sim T (h e) (g (cv′ e)))
    {X} (Em : Emb (Lv (lΩ k g)) X) {W} (lW : LgW L₀ W) b {c} (bd : Bd L₀ κ c W)
    (u : Br {hΩ κ h} {W} {h c} (sL {κ = κ} {g = h} {c = c} bd hself)) →
    rdN (sΩ cv′ σg) Em lW b (sL {κ = κ} {g = h} {c = c} bd hself) u
      ≡ readS (sΩ cv′ σg) Em lW b (u ≤rf lW (inS (sL {κ = κ} {g = h} {c = c} bd hself) n0))
  rdΩ-top-lossy cv′ σg Em lW b bd u = refl
```

## §4 结论 (按档)

- **[定理, 对一切 $T$]** **`readS-P`**, **`img-readS`**: 沿同形, 经嵌入 `Em` 的读回只产出 `j Em` 的像里的种类的 $\Omega$-结点. **`no-top3`**, `no-top3-hz`: 经 `emb2 1` 的读回不产出 `kTop3` (坐标为 `HB (Lv (st 2))` 的种类).
- **[定理, `refl`]** **`rdΩ-top-lossy`**: $S_1$ 的一支本身处的结点读成输入 $0$ 的分支; 对照 `NegLeanLvPre.succK-co` (那里有忠实的种类).
- **[判断]** (i) 头 $n\ge3$ 的界只按 `Lv (st 2)` 的拷贝里的种类增长 (`no-top3` 是 $n=3$; 一般 $n$ 要把 `miss-top` 推到 `emb2 m`, 未做). (ii) `rdΩ-top-lossy` 落在 `Ωd (Sg 1)` 的主结点上; 改读成 `succK c` 的 $\Omega$-结点是否合法 (分支对 $c$ 单调) 未查.
