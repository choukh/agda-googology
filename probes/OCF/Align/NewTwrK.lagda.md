# 新塔 (四): 塔, 层号对角, 无条件闭项, 形状定理, 类型事实

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md), 接口 [NewTwrIf](NewTwrIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 `Twr N`: 对一切 `N : NewTw` 一条.** $B_0=b_0$, $B_{s+1}=\mathrm{emb}\,B_s\boxplus\mathrm{injL}\,B_s\,(\mathrm{rd}\,s\,B_s)$ (下降的值原样进下一站层号所在的类型), 层号对角 `Bᴧ` 在 `KΛc` 里取部分和, `ΛB = hl Bᴧ`, 最终坍缩 `cl` 作用在 `up ΛB : HB (step KΛc)` 上. 合法由形状给出 (`Lg-⊞`, `⊞-fst`, `Lg-ι`, `Lg-up`). **这个模块里没有 `Ht`.**
> - **§2 无条件闭项** `TN = Twr.TN N₀`, `N₀ = (rdN, 2, collΛ)`: 下降是 [NewTwrEv](NewTwrEv.lagda.md) 的求值 (值域 `HB (Lev B_s)`), 最终坍缩是 [NewTwrColl](NewTwrColl.lagda.md) 的 `collΛ` (GenFold 的一般折叠在 `step KΛc` 上). 证书 `Lg-TN`, FGH `fghN`.
> - **§3 形状定理 (对一切 $s$, `refl`).** 每站层号的头是后继 (`B-suc`), 所以第 $s+1$ 站的下降就是第 $X_s$ 级之上的求值 (`rd-suc`); 求值的输出原样进了下一站层号与层号对角 (`Bᴧ-suc`), 对角原样进了闭项的层 (`TN-def`); 每站下降的头是新种类的 $\Omega$-结点 (`rd-head`), 所以每站都不是 $2$ (`rd-not-two`: 排除 `NegDnFoldBlind.dnC`, `NegGenFoldBlind.dnGenC` 那种每站输出 $2$ 的下降). 只说形状, 不说大小 (手册 §3.3).
> - **§4 类型事实 (定理).** 第 $s+1$ 站的值域是 `HB (step (Lev X_s))` (`cod-suc`), 第 $s+2$ 站有坐标类型为 `HB (Lev X_s)` 的种类 (`coord-new`); 每站值域与最终层的类型都不是 `Ht` 的收缩 (`cod-no-ret`, `fin-no-ret`, 由 `NegDnFoldRet.no-faithful`).
> - **§5 第一个障碍的编译陈述.** 最终坍缩里, 层号对角里来自读回分量的种类没有回灌 (`lossy-rd`), 它们在基世界里的顶坐标是 $0$ (`base-bot`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrK where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc; FN; nxt; emb; injL; ιΛ)
open import OCF.Align.GenFoldIf using (GenK; fbA; tpK; top; w₀)
open import OCF.Align.NewTwrIf
open import OCF.Align.NewTwrEv
open import OCF.Align.NewTwrColl using (collΛ; GΛ)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.NegDnFoldRet using (HasHt; no-faithful; Tw; t2; ts; tw⊞; twι; hasTw)
```

## §1 一切 `NewTw` 的塔

```agda
ordN : A → FLv.Ordᶜ FLv.zero
ordN azero = FLv.zero
ordN (asuc a) = FLv.suc (ordN a)
ordN (alim f) = FLv.lim (λ n → ordN (f n))

module Twr (N : NewTw) where
  B  : ∀ s → HB (Kc s)
  lB : ∀ s → LgB (B s)
  B zero = b₀ N
  B (suc s) = emb (B s) ⊞ injL (B s) (proj₁ (rd N s (B s) (lB s)))
  lB zero = lb₀ N
  lB (suc s) = Lg-⊞ (emb (B s)) (injL (B s) (proj₁ (rd N s (B s) (lB s))))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₁ tt) (B s) (lB s))
                    (Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (proj₂ (rd N s (B s) (lB s))))

  -- 增量: 第 s 站的下降, 已在第 s+1 站层号的类型里
  inc : ∀ s → HB (Kc (suc s))
  inc s = injL (B s) (proj₁ (rd N s (B s) (lB s)))

  linc : ∀ s → LgB (inc s)
  linc s = Lg-ι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₂ (B s)) _ (proj₂ (rd N s (B s) (lB s)))

  B-fst : ∀ s {w} → emb (B s) ⊲[ w ] B (suc s)
  B-fst s = ⊞-fst (emb (B s)) (inc s)

  -- 层号对角: 同样的增量在 KΛc 里取部分和
  Bᴧ : ℕ → HB KΛc
  Bᴧ zero = ιΛ 0 (b₀ N)
  Bᴧ (suc s) = Bᴧ s ⊞ ιΛ (suc s) (inc s)

  lBᴧ : ∀ s → LgB (Bᴧ s)
  lBᴧ zero = Lg-ι {ℕ} {Kc} 0 (b₀ N) (lb₀ N)
  lBᴧ (suc s) = Lg-⊞ (Bᴧ s) (ιΛ (suc s) (inc s)) (lBᴧ s) (Lg-ι {ℕ} {Kc} (suc s) (inc s) (linc s))

  ΛB : HB KΛc
  ΛB = hl Bᴧ

  lΛB : LgB ΛB
  lΛB = (λ n → ⊞-fst (Bᴧ n) (ιΛ (suc n) (inc n))) , lBᴧ

  -- 最终坍缩的层: 对角之上一步的类型
  Lf : HB (step KΛc)
  Lf = up ΛB

  lLf : LgB Lf
  lLf = Lg-up ΛB lΛB

  TN : A
  TN = col (cl N) Lf lLf

  Lg-TN : Lg TN
  Lg-TN = lgCol (cl N) Lf lLf

  fghN : ℕ → ℕ
  fghN = FLv.FGH (ordN TN)

  -- 每站的部分和是最终层的第一位置 (输入一侧)
  stage-in : ∀ s {w} → up (Bᴧ s) ⊲[ w ] Lf
  stage-in s = up-⊲ (hlim s hself)
```

## §2 无条件闭项

```agda
N₀ : NewTw
N₀ = record { rd = rdN ; b₀ = two ; lb₀ = tt ; cl = collΛ }

module NT = Twr N₀

TN : A
TN = NT.TN

Lg-TN : Lg TN
Lg-TN = NT.Lg-TN

fghN : ℕ → ℕ
fghN = NT.fghN
```

## §3 形状定理

```agda
-- 第 s 站之后的层号 (去掉头上的后继)
X : ∀ s → HB (Kc (suc s))
X s = emb (NT.B s) ⊞ injL (NT.B s) (ρ′ (NT.B s))

B-zero : NT.B 0 ≡ two
B-zero = refl

B-suc : ∀ s → NT.B (suc s) ≡ hs (X s)
B-suc s = refl

-- 第 0 站的下降: 第 1 级之上的求值
rd-zero : proj₁ (rdN 0 (NT.B 0) (NT.lB 0)) ≡ hs (evN {S₀} (hs hz))
rd-zero = refl

-- 第 s+1 站的下降: 第 X s 级之上的求值, 值在 HB (step (Lev (X s)))
rd-suc : ∀ s → proj₁ (rdN (suc s) (NT.B (suc s)) (NT.lB (suc s))) ≡ hs (evN (X s))
rd-suc s = refl

-- 求值的输出原样进了下一站的层号
B-suc-ev : ∀ s → NT.B (suc (suc s)) ≡ hs (emb (NT.B (suc s)) ⊞ injL (NT.B (suc s)) (evN (X s)))
B-suc-ev s = refl

-- 原样进了层号对角
Bᴧ-suc : ∀ s → NT.Bᴧ (suc (suc s)) ≡ NT.Bᴧ (suc s) ⊞ ιΛ (suc (suc s)) (injL (NT.B (suc s)) (hs (evN (X s))))
Bᴧ-suc s = refl

-- 对角原样进了闭项的层
TN-def : TN ≡ col collΛ (up (hl NT.Bᴧ)) NT.lLf
TN-def = refl

-- 每站下降的头: 后继之下是新种类的 Ω-结点
rd-head0 : Σ (HB (Lev {S₀} (hs hz)) → HB (step (Lev {S₀} (hs hz))))
             (λ g → proj₁ (rdN 0 (NT.B 0) (NT.lB 0)) ≡ hs (hΩ (inj₂ tt) g))
rd-head0 = _ , refl

rd-head : ∀ s → Σ (HB (Lev (X s)) → HB (step (Lev (X s))))
                  (λ g → proj₁ (rdN (suc s) (NT.B (suc s)) (NT.lB (suc s))) ≡ hs (hΩ (inj₂ tt) g))
rd-head s = _ , refl

-- 每站都不是 2
rd-not-two : ∀ s → ¬ (proj₁ (rdN s (NT.B s) (NT.lB s)) ≡ two)
rd-not-two zero ()
rd-not-two (suc s) ()
```

## §4 类型事实

第 $s+1$ 站的下降值域是第 $X_s$ 级之上一级的高度; 第 $s+2$ 站的种类结构里有坐标类型为 `HB (Lev X_s)` 的种类 (就是第 $s+1$ 站下降值所在的级). 类型依赖于上一站算出的值 ($X_s$ 含第 $s$ 站的求值).

```agda
cod-suc : ∀ s → Lev (NT.B (suc s)) ≡ step (Lev (X s))
cod-suc s = refl

coord-new : ∀ s → E (Kc (suc (suc s))) (inj₂ (NT.B (suc s)) , inj₂ tt) ≡ HB (Lev (X s))
coord-new s = refl
```

**不是 `Ht` 的收缩.** 起点取 $2$, 每站层号沿 `emb` 与 `⊞` 留着字面的 $2$ (`twB`, 同 `NegDnFoldRet.TwB.twB`), 所以每站的级 `Lev B_s` 都有坐标类型为 `Ht` 的种类; 由 `NegDnFoldRet.no-faithful`, 每站下降的值域到 `Ht` 的任何映射都没有左逆 (`cod-no-ret`, 对一切 $s$). 最终层的类型 `HB (step KΛc)` 同样 (`fin-no-ret`). 这两条说值域与最终层 "不落回 `Ht`" 是类型事实, 不是值的界.

```agda
twB : ∀ s → Tw (NT.B s)
twB zero = t2
twB (suc s) = ts (tw⊞ (twι {⊤ ⊎ HB (Kc s)} {FN (Kc s)} (inj₁ tt) (twB s)) (injL (NT.B s) (ρ′ (NT.B s))))

cod-no-ret : ∀ s (d : HB (Lev (NT.B s)) → Ht) (r : Ht → HB (Lev (NT.B s))) → ¬ (∀ x → r (d x) ≡ x)
cod-no-ret s = no-faithful (hasTw (twB s))

hasΛ : HasHt (step KΛc)
hasΛ = inj₁ (1 , (inj₂ (two {S₀}) , inj₂ tt)) , refl

fin-no-ret : ∀ (d : HB (step KΛc) → Ht) (r : Ht → HB (step KΛc)) → ¬ (∀ x → r (d x) ≡ x)
fin-no-ret = no-faithful hasΛ
```

## §5 第一个障碍的编译陈述

最终坍缩 `collΛ` 用 GenFold 的实例 `GΛ = genSupℕ Kc genKc`: 第 $s+1$ 站读回分量 `inj₂ c` 里的一切种类没有 A-回灌 (`lossy-rd`, 对一切 $s$, $c$, $\kappa$; 来自 `GenFoldInst.genNxt` 的有损一支: 下标 $c$ 是高度, 不能判定). 层号对角的 $\Omega$-结点正是这些种类 (`rd-head` 的头经 `injL` 变成种类 `(inj₂ B_s , inj₂ tt)`). 在基世界里它们的顶坐标是 $0$ (`base-bot`).

```agda
lossy-rd : ∀ s (c : HB (Kc s)) (κ : K (Lev c)) → fbA GΛ (suc s , (inj₂ c , κ)) ≡ inj₂ tt
lossy-rd s c κ = refl

base-bot : ∀ s → top (tpK GΛ) (suc (suc s) , (inj₂ (NT.B (suc s)) , inj₂ tt)) (w₀ GΛ) ≡ hz
base-bot s = refl
```
