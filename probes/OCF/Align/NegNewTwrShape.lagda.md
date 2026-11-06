# 新塔, 否定一路 (三): 塔的形状, 盲区, 最终层里的种类

> 不含记号. 入口 [NegNewTwr](NegNewTwr.lagda.md). 对着接口 [NewTwrIf](NewTwrIf.lagda.md) ("接口定稿 2026-11-05 17:39 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 塔的形状照接口文件 "塔的形状" 一段逐字写成定义 (`Sh`, 与构造一路 `NewTwrK.Twr` 同形; 两者逐站相等见 [NegNewTwrBridge](NegNewTwrBridge.lagda.md)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 1. **接口是盲的 (定理, 反模型).** 常数下降 `rdC` (每站取 $0$) 与 `b₀ = 1` 组成的 `NewTw` 里, 每站层号都是 $1$ (`constB`), 层号对角每项都是起点 (`constΛ`), **每站下降的值域都定义相等于 `Ht`** (`codC`) 且有左逆 (`retC`). 所以接口文件头 "[定理, 构造文件] 每站的下降值域…都不是 `Ht` 的收缩" 与 [判断] "值域随站变大" 都**不是接口的后果**, 要靠具体的下降. 第 0 站更直接: 只要 `b₀ = 1`, 不论下降是什么, 第 0 站的值域就是 `Ht` (`stage0-Ht`). 构造一路取 `b₀ = 2` (`NewTwrK.N₀`), 避开了这一条; 本条只否定把它当接口的性质. 最终坍缩同样: 任何保合法的 `HB (step T) → Ht` 接上旧的 `T⁺` 都是 `CollK` (`viaHt`), 所以 "最终坍缩不落回 `Ht`" 也不是接口的律.
> 2. **接口装得下不求值的旧塔 (定理).** 下降取 "级顶后加 1" (`rdT s b = hs (top b)`, 不求值) 时, 新塔的层号与层号对角逐站等于 [KcFoldTower](KcFoldTower.lagda.md) 的截断塔 `KU` 的 (`rdT-B`, `rdT-Bᴧ`). 所以 "新塔" 的形状不区分有没有求值; "读回进了闭项" 只能是对具体下降的定理.
> 3. **最终层里的种类 (定理, 对一切 `NewTw`).** 最终坍缩的层 $1\boxplus\mathrm{up}\,\Lambda_B$ 里的每个 $\Omega$-结点的种类都是 `inj₁ (0 , _)` (起点的) 或 `inj₁ (s+1 , (inj₂ c , _))` (读回分量的) (`final-kinds`): **没有 `step KΛc` 的新种类** (坐标 `HB KΛc` 的那一个), 也没有嵌入拷贝 `inj₁ (s+1 , (inj₁ tt , _))`. 起点无 $\Omega$-结点时 (构造一路的 `b₀ = 2`), 在现有实例 `GΛ` 下**每一个**结点都有损 (`final-lossy`). 对照 GenFold 的折叠 (`GenFoldRun` 文件头的表, 只读观察): 新种类的结点才走第 0, 1 层的回灌 (`κc₁`), 旧种类在第 0 层只有 A-回灌或有损 (`RKa` 的有损一支是 "当前世界的分支, 重复 $\omega$ 次"). 所以最终坍缩里**没有一个结点被回灌** (判断, 依据这条定理与 `GenFoldRun` 的定义; 没有值的定理).
> 4. **读回不是对角的字面第一位置 (定理).** 第 0 站的下降含 $\Omega$-结点时, 对一切 $j\ge2$, 纯于第 $j$ 站且含 $\Omega$-结点的高度 (例如第 $j-1$ 站的增量 `ιΛ j (inc (j-1))`) 不是层号对角 $\Lambda_B$ 的字面第一位置 (`tw-not-below`, 由 [NegNewTwrCum](NegNewTwrCum.lagda.md)). 前提可满足 (`nfT`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwrShape where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺)
open import OCF.Align.LvKtIf using (Kc; KΛc; FN; emb; injL; ιΛ)
open import OCF.Align.GenFoldIf using (fbA)
open import OCF.Align.GenFoldInst using (liftS)
open import OCF.Align.KcFoldTop using (top; Lg-top)
open import OCF.Align.KcFoldTower using (module KU)
open import OCF.Align.NegLvKtTrap using (OmFree; module Trap; module TΛ)
open import OCF.Align.NegNewTwrCum using (module CumTrap)
open import OCF.Align.NegNewTwrFeed using (genΛ; genΛ⁺)
open import OCF.Align.NewTwrIf
```

## §1 塔的形状 (照接口文件)

```agda
module CΛ = CumTrap Kc

module Sh (N : NewTw) where
  B  : ∀ s → HB (Kc s)
  lB : ∀ s → LgB (B s)
  B zero = b₀ N
  B (suc s) = emb (B s) ⊞ injL (B s) (proj₁ (rd N s (B s) (lB s)))
  lB zero = lb₀ N
  lB (suc s) = Lg-⊞ (emb (B s)) (injL (B s) (proj₁ (rd N s (B s) (lB s))))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₁ tt) (B s) (lB s))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (proj₂ (rd N s (B s) (lB s))))

  r : ∀ s → HB (Lev (B s))
  r s = proj₁ (rd N s (B s) (lB s))

  inc : ∀ s → HB (Kc (suc s))
  inc s = injL (B s) (r s)

  δ : ℕ → HB KΛc
  δ s = ιΛ (suc s) (inc s)

  open CΛ.Diag (ιΛ 0 (b₀ N)) δ public using (cum)

  -- 层号对角 (部分和) 与最终层
  Bᴧ : ℕ → HB KΛc
  Bᴧ = cum

  ΛB : HB KΛc
  ΛB = hl Bᴧ

  Lf : HB (step KΛc)
  Lf = hs hz ⊞ up ΛB

  TN : A
  TN = col (cl N) (up ΛB) (Lg-up ΛB lΛB)
    where
    lBᴧ : ∀ s → LgB (Bᴧ s)
    lBᴧ zero = Lg-ι {ℕ} {Kc} 0 (b₀ N) (lb₀ N)
    lBᴧ (suc s) = Lg-⊞ (Bᴧ s) (δ s) (lBᴧ s)
                       (Lg-ι {ℕ} {Kc} (suc s) (inc s) (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (proj₂ (rd N s (B s) (lB s)))))
    lΛB : LgB ΛB
    lΛB = (λ n → ⊞-fst (Bᴧ n) (δ n)) , lBᴧ
```

## §2 盲: 常数下降

```agda
rdC : RdTower
rdC s b lb = hz , tt

clC : CollK KΛc
clC = record { col = λ _ _ → azero ; lgCol = λ _ _ → tt }

NC : NewTw
NC = record { rd = rdC ; b₀ = hs hz ; lb₀ = tt ; cl = clC }

module SC = Sh NC

constB : ∀ s → SC.B s ≡ hs hz
constB zero = refl
constB (suc s) = cong emb (constB s)

constΛ : ∀ s → SC.Bᴧ s ≡ ιΛ 0 (hs hz)
constΛ zero = refl
constΛ (suc s) = constΛ s

-- 每站下降的值域就是 Ht
codC : ∀ s → HB (Lev (SC.B s)) ≡ Ht
codC s = cong (λ b → HB (Lev b)) (constB s)

subst-ss : ∀ {X Y : Set} (e : X ≡ Y) (y : X) → subst (λ Z → Z) (sym e) (subst (λ Z → Z) e y) ≡ y
subst-ss refl y = refl

retC : ∀ s → Σ (HB (Lev (SC.B s)) → Ht) (λ d → Σ (Ht → HB (Lev (SC.B s))) (λ r → ∀ x → r (d x) ≡ x))
retC s = subst (λ Z → Z) (codC s) , subst (λ Z → Z) (sym (codC s)) , subst-ss (codC s)

TC : SC.TN ≡ azero
TC = refl

-- 最终坍缩可以经 Ht: 任何保合法的 d : HB (step T) → Ht 接上 Ht 上的坍缩 T⁺ 都是 CollK
viaHt : ∀ {T : KS} (d : HB (step T) → Ht) → (∀ h → LgB h → LgB (d h)) → CollK T
viaHt d ld = record { col = λ h lh → T⁺ (d h) (ld h lh) ; lgCol = λ h lh → Lg-T⁺ (d h) (ld h lh) }

viaHt-factor : ∀ {T : KS} (d : HB (step T) → Ht) (ld : ∀ h → LgB h → LgB (d h)) h (lh : LgB h) →
  col (viaHt d ld) h lh ≡ T⁺ (d h) (ld h lh)
viaHt-factor d ld h lh = refl

-- 第 0 站: 起点是 1 时, 不论下降, 值域就是 Ht
stage0-Ht : ∀ (N : NewTw) → b₀ N ≡ hs hz → HB (Lev (Sh.B N 0)) ≡ Ht
stage0-Ht N e = cong (λ b → HB (Lev b)) e
```

## §3 盲: 不求值的旧塔

```agda
rdT : RdTower
rdT s b lb = hs (top b) , Lg-top b

NT : NewTw
NT = record { rd = rdT ; b₀ = hs hz ; lb₀ = tt ; cl = clC }

module ST = Sh NT

rdT-B : ∀ s → ST.B s ≡ KU.B s
rdT-B zero = refl
rdT-B (suc s) = cong (λ b → emb b ⊞ injL b (hs (top b))) (rdT-B s)

rdT-Bᴧ : ∀ s → ST.Bᴧ s ≡ KU.Bᴧ s
rdT-Bᴧ zero = refl
rdT-Bᴧ (suc s) = trans (cong (λ y → y ⊞ ST.δ s) (rdT-Bᴧ s))
                       (cong (λ b → KU.Bᴧ s ⊞ ιΛ (suc s) (injL b (hs (top b)))) (rdT-B s))
```

## §4 最终层里的种类

`AllK P x`: $x$ 的每个 $\Omega$-结点的种类满足 $P$.

```agda
AllK : ∀ {S : KS} → (K S → Set) → HB S → Set
AllK P hz = ⊤
AllK P (hs x) = AllK P x
AllK P (hl f) = ∀ n → AllK P (f n)
AllK P (hΩ κ g) = P κ × (∀ c → AllK P (g c))

all⊞ : ∀ {S : KS} {P : K S → Set} (a b : HB S) → AllK P a → AllK P b → AllK P (a ⊞ b)
all⊞ a hz ha hb = ha
all⊞ a (hs b) ha hb = all⊞ a b ha hb
all⊞ a (hl f) ha hb = λ n → all⊞ a (f n) ha (hb n)
all⊞ a (hΩ κ g) ha (p , hb) = p , (λ c → all⊞ a (g c) ha (hb c))

allι : ∀ {I : Set} {F : I → KS} (i : I) {Q : K (F i) → Set} {P : K (sup I F) → Set} →
  (∀ κ → Q κ → P (i , κ)) → ∀ (x : HB (F i)) → AllK Q x → AllK P (ι {I} {F} i x)
allι i h hz q = tt
allι i h (hs x) q = allι i h x q
allι i h (hl f) q = λ n → allι i h (f n) (q n)
allι i h (hΩ κ g) (p , q) = h κ p , (λ c → allι i h (g c) (q c))

allUp : ∀ {S : KS} {P : K (step S) → Set} → ∀ (x : HB S) → AllK (λ κ → P (inj₁ κ)) x → AllK P (up x)
allUp hz q = tt
allUp (hs x) q = allUp x q
allUp (hl f) q = λ n → allUp (f n) (q n)
allUp (hΩ κ g) (p , q) = p , (λ c → allUp (g c) (q c))

allT : ∀ {S : KS} (x : HB S) → AllK (λ _ → ⊤) x
allT hz = tt
allT (hs x) = allT x
allT (hl f) = λ n → allT (f n)
allT (hΩ κ g) = tt , (λ c → allT (g c))

allMap : ∀ {S : KS} {P Q : K S → Set} → (∀ κ → P κ → Q κ) → ∀ (x : HB S) → AllK P x → AllK Q x
allMap h hz q = tt
allMap h (hs x) q = allMap h x q
allMap h (hl f) q = λ n → allMap h (f n) (q n)
allMap h (hΩ κ g) (p , q) = h κ p , (λ c → allMap h (g c) (q c))

allFree : ∀ {S : KS} {P : K S → Set} (x : HB S) → OmFree x → AllK P x
allFree hz h = tt
allFree (hs x) h = allFree x h
allFree (hl f) h = λ n → allFree (f n) (h n)
allFree (hΩ κ g) ()

-- 起点的种类, 或读回分量的种类
OKΛ : K KΛc → Set
OKΛ (zero , _) = ⊤
OKΛ (suc s , (inj₁ _ , _)) = ⊥
OKΛ (suc s , (inj₂ _ , _)) = ⊤

OK⁺ : K (step KΛc) → Set
OK⁺ (inj₁ κ) = OKΛ κ
OK⁺ (inj₂ _) = ⊥

-- 读回分量的种类: 有损
Lossy : K KΛc → Set
Lossy κ = fbA genΛ κ ≡ inj₂ tt

module Fin (N : NewTw) where
  open Sh N

  incOK : ∀ s → AllK OKΛ (δ s)
  incOK s = allι {ℕ} {Kc} (suc s) (λ κ p → p) (inc s)
              (allι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) {Q = λ _ → ⊤} (λ κ _ → tt) (r s) (allT (r s)))

  cumOK : ∀ n → AllK OKΛ (Bᴧ n)
  cumOK zero = allι {ℕ} {Kc} 0 (λ κ _ → tt) (b₀ N) (allT (b₀ N))
  cumOK (suc n) = all⊞ (Bᴧ n) (δ n) (cumOK n) (incOK n)

  final-kinds : AllK OK⁺ Lf
  final-kinds = all⊞ (hs hz) (up ΛB) tt (allUp {S = KΛc} {P = OK⁺} ΛB cumOK)

  -- 起点无 Ω-结点: 对角的每个结点都有损
  incL : ∀ s → AllK Lossy (δ s)
  incL s = allι {ℕ} {Kc} (suc s) (λ κ p → p) (inc s)
             (allι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) {Q = λ _ → ⊤} (λ κ _ → refl) (r s) (allT (r s)))

  cumL : OmFree (b₀ N) → ∀ n → AllK Lossy (Bᴧ n)
  cumL fr zero = allι {ℕ} {Kc} 0 {Q = λ _ → ⊥} (λ κ ()) (b₀ N) (allFree (b₀ N) fr)
  cumL fr (suc n) = all⊞ (Bᴧ n) (δ n) (cumL fr n) (incL n)

  final-lossy : OmFree (b₀ N) → AllK (λ κ → Lossy κ) ΛB
  final-lossy fr = cumL fr

  final-lossy⁺ : OmFree (b₀ N) → AllK (λ κ → fbA genΛ⁺ κ ≡ inj₂ tt) Lf
  final-lossy⁺ fr = all⊞ (hs hz) (up ΛB) tt (allUp {S = KΛc} {P = λ κ → fbA genΛ⁺ κ ≡ inj₂ tt} ΛB
    (allMap {S = KΛc} {P = Lossy} (λ κ e → cong (liftS {T = KΛc} {κ = κ}) e) ΛB (cumL fr)))
```

## §5 读回不是对角的字面第一位置

```agda
module NB (N : NewTw) where
  open Sh N

  pδ : ∀ n → TΛ.Pure (suc n) (δ n)
  pδ n = TΛ.pure-ι (suc n) (inc n)

  nfδ : ¬ OmFree (r 0) → ¬ OmFree (δ 0)
  nfδ nf h = nf (Trap.free-ι (⊤ ⊎ HB S₀) (FN S₀) (r 0) (TΛ.free-ι (inc 0) h))

  tw-not-below : ¬ OmFree (r 0) → ∀ (w : Wd KΛc) j → 1 < j → ∀ {x} →
    x ⊲[ w ] ΛB → TΛ.Pure j x → ¬ OmFree x → ⊥
  tw-not-below nf w j q = CΛ.Diag.Bad.not-below (ιΛ 0 (b₀ N)) δ w (TΛ.pure-ι 0 (b₀ N)) pδ j 0 q (nfδ nf)

  -- 特例: 第 s+1 站的增量 (含 Ω-结点时) 不是对角的第一位置
  inc-not-below : ¬ OmFree (r 0) → ∀ (w : Wd KΛc) s → ¬ OmFree (δ (suc s)) → ¬ (δ (suc s) ⊲[ w ] ΛB)
  inc-not-below nf w s nfs p = tw-not-below nf w (suc (suc s)) (s≤s (s≤s z≤n)) p (pδ (suc s)) nfs
```

**前提可满足.** 不求值的旧塔 `NT` 里每站的下降都含 $\Omega$-结点 (`nfT`).

```agda
nfT : ∀ s → ¬ OmFree (ST.r s)
nfT zero ()
nfT (suc s) ()

nfδT : ∀ s → ¬ OmFree (ST.δ s)
nfδT s h = nfT s (Trap.free-ι (⊤ ⊎ HB (Kc s)) (FN (Kc s)) (ST.r s) (TΛ.free-ι (ST.inc s) h))

incT-not-below : ∀ (w : Wd KΛc) s → ¬ (ST.δ (suc s) ⊲[ w ] ST.ΛB)
incT-not-below w s = NB.inc-not-below NT (nfT 0) w s (nfδT (suc s))
```

## §6 结论 (按档)

- **[定理, 反模型]** **`viaHt`**, `viaHt-factor`: 经 `Ht` 再用旧的坍缩 `T⁺` 的映射也是 `CollK` (接口的 "最终坍缩不落回 `Ht`" 不是律, 是构造的选择). `constB`, `constΛ`, **`codC`**, **`retC`**, `TC`: 常数下降的 `NewTw` 里每站值域就是 `Ht` (有左逆), 层号与对角不长. **`stage0-Ht`**: `b₀ = 1` 时第 0 站值域是 `Ht`, 对一切下降.
- **[定理]** **`rdT-B`**, **`rdT-Bᴧ`**: 不求值的下降给出截断塔 `KU` 的层号与对角.
- **[定理]** **`final-kinds`** (一切 `NewTw`): 最终层没有 `step KΛc` 的新种类, 没有嵌入拷贝的种类. **`final-lossy`**, `final-lossy⁺` (起点无 $\Omega$-结点): 在现有实例 `genΛ`/`genΛ⁺` 下最终层的每个结点有损.
- **[定理, 否定]** **`tw-not-below`**, `inc-not-below` (第 0 站下降含 $\Omega$-结点); 实例 `incT-not-below`, 前提 `nfT`.
- **[判断]** 由 `final-kinds`, `final-lossy` 与 `GenFoldRun` 的定义 (`RKc (inj₁ κ)` 在第 0 层走 `RKa (fbA G κ)`, 有损一支 `ω⋅ (… (u q₀ lW) …)`; 第 $\ge1$ 层保留; 新种类的回灌行 `κc₁` 只对 `nc (inj₂ tt)`): 最终坍缩里没有结点被回灌. 读法: 对角的 $\Omega$-结构只在当前世界 (基世界, 顶坐标 $0$, 构造一路 `NewTwrK.base-bot`) 的分支上被读到. 没有 `ord` 的比较.
