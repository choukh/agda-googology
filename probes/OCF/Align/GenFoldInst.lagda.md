# 对一般种类结构的折叠 (四): 每种类结构的实例 (对构造子递归)

> 不含记号. 入口 [GenFold](GenFold.lagda.md), 接口 [GenFoldIf](GenFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 接口 §3, §6, §7 的三个记录 (`GenK`, `LgDn`, `FbLg`) 对种类结构的三个构造 (`S₀`, `step`, `sup`) 各一行, 再对层号 (`Lev x`, 对 $x$ 结构递归) 与站 (`Kc s`, 对 $s$ 递归) 组装. 与 `NegKcFoldDec` 的 `topLev`, `topKc` 同一个模式.
>
> **A-回灌 `fbA` 在哪里有.** `S₀` 的唯一种类有 (界就是 `A`, 升界就是换掉). `step` 的旧种类沿用, 新种类没有 (坐标是 `HB`, 不是 `A`). **并 `sup I F` 的分量 $i$ 的种类要升界, 就要把世界 (逐分量的族) 在 $i$ 处换掉, 其余分量不动: 这要对下标判定 "是不是 $i$".** 下标是 `ℕ` (`Lev (hl f)`) 或 `⊤ ⊎ _` 的左分量 (`Kc (s+1)` 的旧站分量) 时, 判定是对构造子的匹配, 有; 下标是坐标 (`Lev (hΩ κ g)` 的 `E κ`, `Kc (s+1)` 的读回分量 `inj₂ c`, `c : HB (Kc s)`) 时没有, 这些种类给 `inj₂ tt` (有损). 这是本路的第一个障碍 (`GenFold` 入口), 本文件只写能写的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; lg⊲)
open import Relation.Nullary using (¬_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (FN; nxt; Kc; KΛc)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (topStepG)
```

## §1 底

```agda
fbS₀ : FBA S₀ tt
fbS₀ = record { tpA = λ w → w ; rsA = λ w v → v ; rs≤ = λ p → p ; rsLg = λ lw lv → lv ; tp-rs = C.self }

genS₀ : GenK S₀
genS₀ = record
  { tpK = record { top = λ _ w → w ; topBd = λ _ w → C.self }
  ; w₀ = azero ; lw₀ = tt ; aK = tt ; frE = λ e → e ; frE-lg = λ l → l
  ; frE-mono = λ lw e e′ p → p ; fbA = λ _ → inj₁ fbS₀ }

ldS₀ : LgDn S₀
ldS₀ = record { lgDn = λ p l → lg⊲ p l }

flS₀ : FbLg genS₀
flS₀ tt lw = lw
```

## §2 一步

```agda
module _ {T : KS} where
  liftFB : ∀ {κ} → FBA T κ → FBA (step T) (inj₁ κ)
  liftFB F = record
    { tpA = λ w → tpA F (proj₁ w)
    ; rsA = λ w v → rsA F (proj₁ w) v , proj₂ w
    ; rs≤ = λ p → rs≤ F p , hself
    ; rsLg = λ lw lv → rsLg F (proj₁ lw) lv , proj₂ lw
    ; tp-rs = tp-rs F }

  liftS : ∀ {κ} → FBA T κ ⊎ ⊤ → FBA (step T) (inj₁ κ) ⊎ ⊤
  liftS (inj₁ F) = inj₁ (liftFB F)
  liftS (inj₂ _) = inj₂ tt

  genStep : GenK T → GenK (step T)
  genStep G = record
    { tpK = topStepG (tpK G) ; w₀ = w₀ G , hz ; lw₀ = lw₀ G , tt ; aK = inj₁ (aK G)
    ; frE = frE G ; frE-lg = frE-lg G
    ; frE-mono = λ lw e e′ p → frE-mono G (proj₁ lw) e e′ p
    ; fbA = fb }
    where
    fb : (κ : K (step T)) → FBA (step T) κ ⊎ ⊤
    fb (inj₁ κ) = liftS (fbA G κ)
    fb (inj₂ _) = inj₂ tt

  ldStep : LgDn T → LgDn (step T)
  ldStep Ld = record { lgDn = λ p l → lgDn Ld (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l) }

  flLift : ∀ {κ} (s : FBA T κ ⊎ ⊤) → FbLgAt {T} {κ} s → FbLgAt {step T} {inj₁ κ} (liftS s)
  flLift (inj₁ F) tl lw = tl (proj₁ lw)
  flLift (inj₂ _) _ = tt

  flStep : (G : GenK T) → FbLg G → FbLg (genStep G)
  flStep G fl (inj₁ κ) = flLift (fbA G κ) (fl κ)
  flStep G fl (inj₂ _) = tt
```

## §3 并: 顶坐标与向下封闭对一切下标; A-回灌只在能判定下标处

```agda
module _ (I : Set) (F : I → KS) where
  topSupG : ((i : I) → TopG (F i)) → TopG (sup I F)
  topSupG tp = record
    { top = λ κ w → top (tp (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
    ; topBd = λ κ w → topBd (tp (proj₁ κ)) (proj₂ κ) (w (proj₁ κ)) }

  ldSup : ((i : I) → LgDn (F i)) → LgDn (sup I F)
  ldSup Ld = record { lgDn = λ p l i → lgDn (Ld i) (p i) (l i) }

  -- 下标不能判定: 一切种类有损
  genSupNo : (i₀ : I) → ((i : I) → GenK (F i)) → GenK (sup I F)
  genSupNo i₀ G = record
    { tpK = topSupG (λ i → tpK (G i)) ; w₀ = λ i → w₀ (G i) ; lw₀ = λ i → lw₀ (G i)
    ; aK = i₀ , aK (G i₀) ; frE = frE (G i₀) ; frE-lg = frE-lg (G i₀)
    ; frE-mono = λ lw e e′ p → frE-mono (G i₀) (lw i₀) e e′ p
    ; fbA = λ _ → inj₂ tt }

  flSupNo : (i₀ : I) (G : (i : I) → GenK (F i)) → FbLg (genSupNo i₀ G)
  flSupNo i₀ G κ = tt
```

**下标是 `ℕ`: 在 $n$ 处换掉** (对 $n$ 与 $m$ 的构造子同时递归, 定义相等的换法).

```agda
upd : ∀ {P : ℕ → Set} → ((m : ℕ) → P m) → (n : ℕ) → P n → (m : ℕ) → P m
upd w zero x zero = x
upd w zero x (suc m) = w (suc m)
upd w (suc n) x zero = w zero
upd {P} w (suc n) x (suc m) = upd {λ k → P (suc k)} (λ k → w (suc k)) n x m

upd-R : ∀ {P : ℕ → Set} (R : ∀ m → P m → P m → Set) (w : (m : ℕ) → P m) n (x : P n) →
        (∀ m → R m (w m) (w m)) → R n (w n) x → ∀ m → R m (w m) (upd {P} w n x m)
upd-R R w zero x rf r zero = r
upd-R R w zero x rf r (suc m) = rf (suc m)
upd-R R w (suc n) x rf r zero = rf zero
upd-R {P} R w (suc n) x rf r (suc m) = upd-R {λ k → P (suc k)} (λ k → R (suc k)) (λ k → w (suc k)) n x (λ k → rf (suc k)) r m

upd-Q : ∀ {P : ℕ → Set} (Q : ∀ m → P m → Set) (w : (m : ℕ) → P m) n (x : P n) →
        (∀ m → Q m (w m)) → Q n x → ∀ m → Q m (upd {P} w n x m)
upd-Q Q w zero x qw qx zero = qx
upd-Q Q w zero x qw qx (suc m) = qw (suc m)
upd-Q Q w (suc n) x qw qx zero = qw zero
upd-Q {P} Q w (suc n) x qw qx (suc m) = upd-Q {λ k → P (suc k)} (λ k → Q (suc k)) (λ k → w (suc k)) n x (λ k → qw (suc k)) qx m

upd-at : ∀ {P : ℕ → Set} (w : (m : ℕ) → P m) n (x : P n) (C : P n → Set) → C x → C (upd {P} w n x n)
upd-at w zero x C c = c
upd-at {P} w (suc n) x C c = upd-at {λ k → P (suc k)} (λ k → w (suc k)) n x C c

module _ (F : ℕ → KS) where
  liftℕ : ∀ n {κ} → FBA (F n) κ → FBA (sup ℕ F) (n , κ)
  liftℕ n {κ} Fb = record
    { tpA = λ w → tpA Fb (w n)
    ; rsA = λ w v → upd {λ m → Wd (F m)} w n (rsA Fb (w n) v)
    ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (F m)} (λ m → _≤w_ (F m)) w n (rsA Fb (w n) v) (λ m → ≤w-rf (F m)) (rs≤ Fb p)
    ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (F m)} (λ m → LgW (F m)) w n (rsA Fb (w n) v) lw (rsLg Fb (lw n) lv)
    ; tp-rs = λ {w} {v} → upd-at {λ m → Wd (F m)} w n (rsA Fb (w n) v) (λ u → v ⊲ tpA Fb u) (tp-rs Fb) }

  liftSℕ : ∀ n {κ} → FBA (F n) κ ⊎ ⊤ → FBA (sup ℕ F) (n , κ) ⊎ ⊤
  liftSℕ n (inj₁ Fb) = inj₁ (liftℕ n Fb)
  liftSℕ n (inj₂ _) = inj₂ tt

  genSupℕ : ((n : ℕ) → GenK (F n)) → GenK (sup ℕ F)
  genSupℕ G = record
    { tpK = topSupG ℕ F (λ i → tpK (G i)) ; w₀ = λ i → w₀ (G i) ; lw₀ = λ i → lw₀ (G i)
    ; aK = 0 , aK (G 0) ; frE = frE (G 0) ; frE-lg = frE-lg (G 0)
    ; frE-mono = λ lw e e′ p → frE-mono (G 0) (lw 0) e e′ p
    ; fbA = λ κ → liftSℕ (proj₁ κ) (fbA (G (proj₁ κ)) (proj₂ κ)) }

  flLiftℕ : ∀ n {κ} (s : FBA (F n) κ ⊎ ⊤) → FbLgAt {F n} {κ} s → FbLgAt {sup ℕ F} {n , κ} (liftSℕ n s)
  flLiftℕ n (inj₁ Fb) tl lw = tl (lw n)
  flLiftℕ n (inj₂ _) _ = tt

  flSupℕ : (G : (n : ℕ) → GenK (F n)) → ((n : ℕ) → FbLg (G n)) → FbLg (genSupℕ G)
  flSupℕ G fl κ = flLiftℕ (proj₁ κ) (fbA (G (proj₁ κ)) (proj₂ κ)) (fl (proj₁ κ) (proj₂ κ))
```

## §4 层号: 对高度结构递归

```agda
genLev : ∀ {S} (x : HB S) → GenK (Lev x)
genLev hz = genS₀
genLev (hs x) = genStep (genLev x)
genLev (hl f) = genSupℕ (λ n → Lev (f n)) (λ n → genLev (f n))
genLev {S} (hΩ κ g) = genSupNo (E S κ) (λ c → Lev (g c)) (bot S κ) (λ c → genLev (g c))

ldLev : ∀ {S} (x : HB S) → LgDn (Lev x)
ldLev hz = ldS₀
ldLev (hs x) = ldStep (ldLev x)
ldLev (hl f) = ldSup ℕ (λ n → Lev (f n)) (λ n → ldLev (f n))
ldLev {S} (hΩ κ g) = ldSup (E S κ) (λ c → Lev (g c)) (λ c → ldLev (g c))

flLev : ∀ {S} (x : HB S) → FbLg (genLev x)
flLev hz = flS₀
flLev (hs x) = flStep (genLev x) (flLev x)
flLev (hl f) = flSupℕ (λ n → Lev (f n)) (λ n → genLev (f n)) (λ n → flLev (f n))
flLev {S} (hΩ κ g) = flSupNo (E S κ) (λ c → Lev (g c)) (bot S κ) (λ c → genLev (g c))
```

## §5 站: 旧站的分量能判定 (左分量), 读回分量不能

```agda
module _ {B : Set} {P : ⊤ ⊎ B → Set} where
  updL : ((j : ⊤ ⊎ B) → P j) → P (inj₁ tt) → (j : ⊤ ⊎ B) → P j
  updL w x (inj₁ tt) = x
  updL w x (inj₂ c) = w (inj₂ c)

module _ {Q : KS} where
  private
    N = nxt Q

  liftL : ∀ {κ} → FBA Q κ → FBA N (inj₁ tt , κ)
  liftL {κ} Fb = record
    { tpA = λ w → tpA Fb (w (inj₁ tt))
    ; rsA = λ w v → updL {P = λ j → Wd (FN Q j)} w (rsA Fb (w (inj₁ tt)) v)
    ; rs≤ = λ p → λ { (inj₁ tt) → rs≤ Fb p ; (inj₂ c) → ≤w-rf (Lev c) }
    ; rsLg = λ lw lv → λ { (inj₁ tt) → rsLg Fb (lw (inj₁ tt)) lv ; (inj₂ c) → lw (inj₂ c) }
    ; tp-rs = tp-rs Fb }

  liftSL : ∀ {κ} → FBA Q κ ⊎ ⊤ → FBA N (inj₁ tt , κ) ⊎ ⊤
  liftSL (inj₁ Fb) = inj₁ (liftL Fb)
  liftSL (inj₂ _) = inj₂ tt

  genFN : GenK Q → (i : ⊤ ⊎ HB Q) → GenK (FN Q i)
  genFN G (inj₁ _) = G
  genFN G (inj₂ c) = genLev c

  ldFN : LgDn Q → (i : ⊤ ⊎ HB Q) → LgDn (FN Q i)
  ldFN Ld (inj₁ _) = Ld
  ldFN Ld (inj₂ c) = ldLev c

  genNxt : GenK Q → GenK N
  genNxt G = record
    { tpK = topSupG (⊤ ⊎ HB Q) (FN Q) (λ i → tpK (genFN G i))
    ; w₀ = λ i → w₀ (genFN G i) ; lw₀ = λ i → lw₀ (genFN G i)
    ; aK = inj₁ tt , aK G ; frE = frE G ; frE-lg = frE-lg G
    ; frE-mono = λ lw e e′ p → frE-mono G (lw (inj₁ tt)) e e′ p
    ; fbA = fb }
    where
    fb : (κ : K N) → FBA N κ ⊎ ⊤
    fb (inj₁ tt , κ) = liftSL (fbA G κ)
    fb (inj₂ c , κ) = inj₂ tt

  ldNxt : LgDn Q → LgDn N
  ldNxt Ld = ldSup (⊤ ⊎ HB Q) (FN Q) (ldFN Ld)

  flLiftL : ∀ {κ} (s : FBA Q κ ⊎ ⊤) → FbLgAt {Q} {κ} s → FbLgAt {N} {inj₁ tt , κ} (liftSL s)
  flLiftL (inj₁ Fb) tl lw = tl (lw (inj₁ tt))
  flLiftL (inj₂ _) _ = tt

  flNxt : (G : GenK Q) → FbLg G → FbLg (genNxt G)
  flNxt G fl (inj₁ tt , κ) = flLiftL (fbA G κ) (fl κ)
  flNxt G fl (inj₂ c , κ) = tt

genKc : ∀ s → GenK (Kc s)
genKc zero = genS₀
genKc (suc s) = genNxt (genKc s)

ldKc : ∀ s → LgDn (Kc s)
ldKc zero = ldS₀
ldKc (suc s) = ldNxt (ldKc s)

flKc : ∀ s → FbLg (genKc s)
flKc zero = flS₀
flKc (suc s) = flNxt (genKc s) (flKc s)
```

## §6 A-回灌绑到种类上 (接口 §8)

```agda
bdS₀ : FbBd genS₀
bdS₀ tt = record { toE = λ v → v ; tp-bd = C.self ; rs-bd = C.self }

module _ {T : KS} where
  bdLift : ∀ {κ} (s : FBA T κ ⊎ ⊤) → FbBdAt {T} {κ} s → FbBdAt {step T} {inj₁ κ} (liftS s)
  bdLift (inj₁ F) B = record { toE = toE B ; tp-bd = tp-bd B ; rs-bd = rs-bd B }
  bdLift (inj₂ _) _ = tt

  bdStep : (G : GenK T) → FbBd G → FbBd (genStep G)
  bdStep G B (inj₁ κ) = bdLift (fbA G κ) (B κ)
  bdStep G B (inj₂ _) = tt

module _ (I : Set) (F : I → KS) where
  bdSupNo : (i₀ : I) (G : (i : I) → GenK (F i)) → FbBd (genSupNo I F i₀ G)
  bdSupNo i₀ G κ = tt

module _ (F : ℕ → KS) where
  bdLiftℕ : ∀ n {κ} (s : FBA (F n) κ ⊎ ⊤) → FbBdAt {F n} {κ} s → FbBdAt {sup ℕ F} {n , κ} (liftSℕ F n s)
  bdLiftℕ n {κ} (inj₁ Fb) B = record
    { toE = toE B
    ; tp-bd = tp-bd B
    ; rs-bd = λ {w} {v} → upd-at {λ m → Wd (F m)} w n (rsA Fb (w n) v) (λ u → Bd (F n) κ (toE B v) u) (rs-bd B) }
  bdLiftℕ n (inj₂ _) _ = tt

  bdSupℕ : (G : (n : ℕ) → GenK (F n)) → ((n : ℕ) → FbBd (G n)) → FbBd (genSupℕ F G)
  bdSupℕ G B κ = bdLiftℕ (proj₁ κ) (fbA (G (proj₁ κ)) (proj₂ κ)) (B (proj₁ κ) (proj₂ κ))

bdLev : ∀ {S} (x : HB S) → FbBd (genLev x)
bdLev hz = bdS₀
bdLev (hs x) = bdStep (genLev x) (bdLev x)
bdLev (hl f) = bdSupℕ (λ n → Lev (f n)) (λ n → genLev (f n)) (λ n → bdLev (f n))
bdLev {S} (hΩ κ g) = bdSupNo (E S κ) (λ c → Lev (g c)) (bot S κ) (λ c → genLev (g c))

module _ {Q : KS} where
  bdLiftL : ∀ {κ} (s : FBA Q κ ⊎ ⊤) → FbBdAt {Q} {κ} s → FbBdAt {nxt Q} {inj₁ tt , κ} (liftSL s)
  bdLiftL (inj₁ Fb) B = record { toE = toE B ; tp-bd = tp-bd B ; rs-bd = rs-bd B }
  bdLiftL (inj₂ _) _ = tt

  bdNxt : (G : GenK Q) → FbBd G → FbBd (genNxt G)
  bdNxt G B (inj₁ tt , κ) = bdLiftL (fbA G κ) (B κ)
  bdNxt G B (inj₂ c , κ) = tt

bdKc : ∀ s → FbBd (genKc s)
bdKc zero = bdS₀
bdKc (suc s) = bdNxt (genKc s) (bdKc s)
```

**换种类不成立 (对照否定一路的 `fba-swap`).** 第 1 站 `Kc 1` 里, 旧站的种类 `(inj₁ tt , tt)` 的 A-回灌搬到读回分量的底种类 `(inj₂ 1 , inj₁ tt)` 上, `rs-bd` 不成立: 升界只改 `inj₁ tt` 分量, 读回分量的界仍是基世界 ($0$), 而 $1$ 不在 $0$ 之下.

```agda
no-swap₁ : ¬ (∀ {w v} → Bd (Kc 1) (inj₂ (hs hz) , inj₁ tt) v (rsA (liftL {S₀} fbS₀) w v))
no-swap₁ h with h {w₀ (genKc 1)} {asuc azero}
... | ()
```
