# 层号换类型 (一): 换类型的塔, 两站, 对一切站, 对角, 闭项

> 不含记号. 入口 [LvKt](LvKt.lagda.md), 接口 [LvKtIf](LvKtIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 本篇的塔以模块参数 (每站一个 `FoldAtK` 与 "取哪一部分回灌" 的 `φ`) 为前提; 无条件的实例在 [LvKtInst](LvKtInst.lagda.md).
>
> - **§1 嵌入的律 (定理).** `emb`, `injL`, `ιΛ` 是并的分量注入, 保第一位置 (同一分量的世界里), 保合法 (`ι-⊲`, `Lg-ι` 的实例). 不判定任何东西.
> - **§2 两站 (s = 0, 1).** `Two`: 第 0 站层号 $B_0$ 在 `HB S₀`; 在顶码上折叠得读回 $r_0$ (第 $B_0$ 级的高度) 与输出 $H_0$; 第 1 站层号 $B_1=\mathrm{emb}\,B_0\boxplus\mathrm{injL}\,B_0\,(\varphi\,r_0)$ 在 `HB (Kc 1)`; 再折叠得 $r_1$, $H_1$; $B_2$ 在 `HB (Kc 2)`. 合法由形状给出.
> - **§3 对一切站 (`Tower`).** 同一个递归对站号 $s$: 层号 `B s : HB (Kc s)`, 合法 `lB`, 覆盖 `cB`, 读回 `rts s : HB (Lev (B s))`, 输出 `Hs s : Ht` 同时递归; `B (s+1) = emb (B s) ⊞ inc s`, `inc s = injL (B s) (φ s (B s) (rts s))`. 新站的层号就是上一站读回所在的类型注入的结果 (第 $s$ 站的回灌输出成为第 $s+1$ 站层号所在类型 `HB (Kc (s+1))` 里的高度).
> - **§4 对角.** 层号在 `KΛc = sup ℕ Kc` 里另写一列 `Bᴧ` (同样的增量 `inc s`, 经 `ιΛ (s+1)` 进极限, 累加), `ΛB = hl Bᴧ` 合法. 输出的对角 `Λ∞ = hl cum` (各站 `Hs` 累加, 同 `LvTopTower`), 闭项 `TΛ∞ = T⁺ Λ∞ _`. 极限站 `Lim`: 在 `ΛB` 的顶码上再折叠一次 (`KΛc` 上的一个 `FoldAtK`), `TΛ∞ω = T⁺ (Λ∞ ⊞ Hω) _`.
> - **§5 条件版** `FullK FA FL b₀`: 前提 `FA : FoldTower` (每站一切码上的折叠), `FL : FoldLimK`, 回灌整个读回 (`φ = id`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
```

## §1 嵌入的律

```agda
module _ {K : KS} where
  emb-⊲ : ∀ {x y} {w : Wd (nxt K)} → x ⊲[ w (inj₁ tt) ] y → emb x ⊲[ w ] emb y
  emb-⊲ = ι-⊲ {⊤ ⊎ HB K} {FN K}

  Lg-emb : ∀ x → LgB x → LgB (emb {K} x)
  Lg-emb = Lg-ι {⊤ ⊎ HB K} {FN K} (inj₁ tt)

  injL-⊲ : ∀ c {x y} {w : Wd (nxt K)} → x ⊲[ w (inj₂ c) ] y → injL c x ⊲[ w ] injL c y
  injL-⊲ c = ι-⊲ {⊤ ⊎ HB K} {FN K}

  Lg-injL : ∀ c x → LgB x → LgB (injL {K} c x)
  Lg-injL c = Lg-ι {⊤ ⊎ HB K} {FN K} (inj₂ c)

Lg-ιΛ : ∀ s x → LgB x → LgB (ιΛ s x)
Lg-ιΛ s = Lg-ι {ℕ} {Kc} s

-- 全 0 的世界
w₀K : ∀ {K} (ck : CdK K) {a b} → WbK ck a b
w₀K ck k = hz

lw₀K : ∀ {K} (ck : CdK K) {a b} → LgWbK ck (w₀K ck {a} {b})
lw₀K ck k = tt

-- 在基世界里, 界 b 的顶码上折叠 (外层世界显式给出)
module _ {K : KS} (ck : CdK K) {Cov : HB K → Set} (F : FoldAtK K ck Cov) where
  rtTop : ∀ b → LgB b → Cov b → HB (Lev b)
  rtTop b lb cv = FoldAtK.rt F {a = w0 ck} {b = b} (lw0 ck) lb (Codes.top ck {a = w0 ck} b) cv (w₀K ck) (lw₀K ck)

  lrtTop : ∀ b (lb : LgB b) (cv : Cov b) → LgB (rtTop b lb cv)
  lrtTop b lb cv = FoldAtK.lrt F {a = w0 ck} {b = b} (lw0 ck) lb (Codes.top ck {a = w0 ck} b) cv (w₀K ck) (lw₀K ck)

  HTop : ∀ b → LgB b → Cov b → Ht
  HTop b lb cv = FoldAtK.H F {a = w0 ck} {b = b} (lw0 ck) lb (Codes.top ck {a = w0 ck} b) cv (w₀K ck) (lw₀K ck)

  lgHTop : ∀ b (lb : LgB b) (cv : Cov b) → LgB (HTop b lb cv)
  lgHTop b lb cv = FoldAtK.lgH F {a = w0 ck} {b = b} (lw0 ck) lb (Codes.top ck {a = w0 ck} b) cv (w₀K ck) (lw₀K ck)
```

## §2 两站

```agda
module Two (C0 : HB (Kc 0) → Set) (F0 : FoldAtK (Kc 0) (ckc 0) C0)
           (C1 : HB (Kc 1) → Set) (F1 : FoldAtK (Kc 1) (ckc 1) C1)
           (b₀ : HB S₀) (lb₀ : LgB b₀) (cv0 : C0 b₀)
           (cv1 : ∀ r → C1 (emb b₀ ⊞ injL b₀ r)) where
  -- 第 0 站: 层号在 HB S₀
  r0 : HB (Lev b₀)
  r0 = rtTop (ckc 0) F0 b₀ lb₀ cv0

  lr0 : LgB r0
  lr0 = lrtTop (ckc 0) F0 b₀ lb₀ cv0

  H0 : Ht
  H0 = HTop (ckc 0) F0 b₀ lb₀ cv0

  -- 第 1 站: 层号在 HB (Kc 1); 第 0 站的读回原样注入
  B1 : HB (Kc 1)
  B1 = emb b₀ ⊞ injL b₀ r0

  lB1 : LgB B1
  lB1 = Lg-⊞ (emb b₀) (injL b₀ r0) (Lg-emb b₀ lb₀) (Lg-injL b₀ r0 lr0)

  B1-fst : ∀ {w} → emb b₀ ⊲[ w ] B1
  B1-fst = ⊞-fst (emb b₀) (injL b₀ r0)

  r1 : HB (Lev B1)
  r1 = rtTop (ckc 1) F1 B1 lB1 (cv1 r0)

  lr1 : LgB r1
  lr1 = lrtTop (ckc 1) F1 B1 lB1 (cv1 r0)

  H1 : Ht
  H1 = HTop (ckc 1) F1 B1 lB1 (cv1 r0)

  -- 第 2 站的层号: 在 HB (Kc 2)
  B2 : HB (Kc 2)
  B2 = emb B1 ⊞ injL B1 r1

  lB2 : LgB B2
  lB2 = Lg-⊞ (emb B1) (injL B1 r1) (Lg-emb B1 lB1) (Lg-injL B1 r1 lr1)
```

## §3 对一切站

```agda
module Tower (Cov : ∀ s → HB (Kc s) → Set) (F : ∀ s → FoldAtK (Kc s) (ckc s) (Cov s))
             (φ : ∀ s (b : HB (Kc s)) → HB (Lev b) → HB (Lev b))
             (lφ : ∀ s b x → LgB x → LgB (φ s b x))
             (b₀ : HB S₀) (lb₀ : LgB b₀) (cov0 : Cov 0 b₀)
             (covS : ∀ s b x → Cov s b → Cov (suc s) (emb b ⊞ injL b (φ s b x))) where

  B    : ∀ s → HB (Kc s)
  lB   : ∀ s → LgB (B s)
  cB   : ∀ s → Cov s (B s)
  rts  : ∀ s → HB (Lev (B s))
  lrts : ∀ s → LgB (rts s)
  B zero = b₀
  B (suc s) = emb (B s) ⊞ injL (B s) (φ s (B s) (rts s))
  lB zero = lb₀
  lB (suc s) = Lg-⊞ (emb (B s)) (injL (B s) (φ s (B s) (rts s)))
                    (Lg-emb (B s) (lB s)) (Lg-injL (B s) _ (lφ s (B s) (rts s) (lrts s)))
  cB zero = cov0
  cB (suc s) = covS s (B s) (rts s) (cB s)
  rts s = rtTop (ckc s) (F s) (B s) (lB s) (cB s)
  lrts s = lrtTop (ckc s) (F s) (B s) (lB s) (cB s)

  Hs : ℕ → Ht
  Hs s = HTop (ckc s) (F s) (B s) (lB s) (cB s)

  lHs : ∀ s → LgB (Hs s)
  lHs s = lgHTop (ckc s) (F s) (B s) (lB s) (cB s)

  -- 增量: 第 s 站的回灌, 已在第 s+1 站层号的类型里
  inc : ∀ s → HB (Kc (suc s))
  inc s = injL (B s) (φ s (B s) (rts s))

  linc : ∀ s → LgB (inc s)
  linc s = Lg-injL (B s) _ (lφ s (B s) (rts s) (lrts s))

  B-suc : ∀ s → B (suc s) ≡ emb (B s) ⊞ inc s
  B-suc s = refl

  -- 旧站的层号搬进新站后是新层号的第一位置 (一切世界)
  B-fst : ∀ s {w} → emb (B s) ⊲[ w ] B (suc s)
  B-fst s = ⊞-fst (emb (B s)) (inc s)
```

## §4 对角与闭项

```agda
  -- 层号的对角: 同样的增量在 KΛc 里累加
  Bᴧ : ℕ → HB KΛc
  Bᴧ zero = ιΛ 0 b₀
  Bᴧ (suc s) = Bᴧ s ⊞ ιΛ (suc s) (inc s)

  lBᴧ : ∀ s → LgB (Bᴧ s)
  lBᴧ zero = Lg-ιΛ 0 b₀ lb₀
  lBᴧ (suc s) = Lg-⊞ (Bᴧ s) (ιΛ (suc s) (inc s)) (lBᴧ s) (Lg-ιΛ (suc s) (inc s) (linc s))

  ΛB : HB KΛc
  ΛB = hl Bᴧ

  lΛB : LgB ΛB
  lΛB = (λ n → ⊞-fst (Bᴧ n) (ιΛ (suc n) (inc n))) , lBᴧ

  -- 输出的对角
  cum : ℕ → Ht
  cum zero = Hs zero
  cum (suc k) = cum k ⊞ Hs (suc k)

  lcum : ∀ k → LgB (cum k)
  lcum zero = lHs zero
  lcum (suc k) = Lg-⊞ (cum k) (Hs (suc k)) (lcum k) (lHs (suc k))

  Λ∞ : Ht
  Λ∞ = hl cum

  lΛ∞ : LgB Λ∞
  lΛ∞ = (λ k → ⊞-fst (cum k) (Hs (suc k))) , lcum

  TΛ∞ : A
  TΛ∞ = T⁺ Λ∞ lΛ∞

  Lg-TΛ∞ : Lg TΛ∞
  Lg-TΛ∞ = Lg-T⁺ Λ∞ lΛ∞

  fghΛ∞ : ℕ → ℕ
  fghΛ∞ = FLv.FGH (ord TΛ∞)

  -- 极限站: 在层号对角 ΛB 的顶码上再折叠一次
  module Lim (CovL : HB KΛc → Set) (FL : FoldAtK KΛc ckΛ CovL) (covL : CovL ΛB) where
    rtω : HB (Lev ΛB)
    rtω = rtTop ckΛ FL ΛB lΛB covL

    Hω : Ht
    Hω = HTop ckΛ FL ΛB lΛB covL

    lHω : LgB Hω
    lHω = lgHTop ckΛ FL ΛB lΛB covL

    Λ∞ω : Ht
    Λ∞ω = Λ∞ ⊞ Hω

    lΛ∞ω : LgB Λ∞ω
    lΛ∞ω = Lg-⊞ Λ∞ Hω lΛ∞ lHω

    TΛ∞ω : A
    TΛ∞ω = T⁺ Λ∞ω lΛ∞ω

    Lg-TΛ∞ω : Lg TΛ∞ω
    Lg-TΛ∞ω = Lg-T⁺ Λ∞ω lΛ∞ω

    fghΛ∞ω : ℕ → ℕ
    fghΛ∞ω = FLv.FGH (ord TΛ∞ω)
```

## §5 条件版: 每站一切码上的折叠

回灌整个读回 (`φ = id`), 覆盖都是 `⊤`.

```agda
module FullK (FA : FoldTower) (FL : FoldLimK) (b₀ : HB S₀) (lb₀ : LgB b₀) where
  open Tower (λ _ _ → ⊤) FA (λ _ _ x → x) (λ _ _ _ l → l) b₀ lb₀ tt (λ _ _ _ _ → tt) public
  open Lim (λ _ → ⊤) FL tt public
  -- 闭项 (条件): TΛ∞, TΛ∞ω; 证书 Lg-TΛ∞, Lg-TΛ∞ω; FGH fghΛ∞, fghΛ∞ω
```
