# 按级回灌, 否定一路 (六): "一起升" 满足不了 `KLv` 的两条升界律

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 对着接口 [KindLvIf](KindLvIf.lagda.md) ("接口定稿 2026-11-05 18:33", 变更记录: 无) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> `KLv` 的升界是 `rs` 加两条律: `rs-top` (升后 $\kappa$ 的顶**恰好**是 $v$, 无前提) 与 `rs≤` (前提 "旧顶是 $v$ 的第一位置" 下, 世界变大). [NegKindLvUpd](NegKindLvUpd.lagda.md) 说在以高度为下标的并里不能 "升一份留别份"; 接口也不要 "留". 剩下的办法是 "一起升": 对每一份拷贝用同一个算子 $R$ 改界. 本篇: **在 `K₁` 的读回分量的底拷贝 `κ₁ f` 上, 对任何 $R : A\to A\to A$, "一起升" `upAllR R` 不能同时满足 `rs-top` 与 `rs≤`** (`no-upAllR`, `no-klv-upAllR`). 原因: `rs-top` 对一切旧界 $a$ 逼出 $R\,a\,v\equiv v$; `rs≤` 又要别的拷贝的旧界 $a'$ (前提只管 $\kappa$ 自己的旧界) 是 $R\,a'\,v=v$ 的第一位置, 取 $a'=2$, $v=1$ 即矛盾. 这与 `RaiseC` 一路的 `no-fba-upAll` (`FBA.tp-rs` 无条件) 同型, 这里落在 `KLv` 上.
>
> **两半各自可满足**: $R\,a\,v=v$ (每份拷贝置成 $v$) 满足 `rs-top` (`half-top`); $R\,a\,v=a$ (不动) 满足 `rs≤` (`half-≤`).
>
> **只否定什么.** 只否定: `rs` 是 "每个读回分量的每份底拷贝用同一个 $R$" (`upAllR`) 的形状, 且同时满足 `rs-top`, `rs≤`. **不否定**: 只升 κ 自己所在分量 (要判定下标, 撞 `NegKindLvUpd`/`NegGenFoldUpd` 的 "留" 那一半只在要求 "留" 时; 只升不留而精确置顶, 未否定); 按拷贝不同的 $R$ (例如依赖分量的构造子); 可判定下标上的 `rs` (构造一路在 ℕ 分量与 `step` 的第二分量上写的); 有损 (`inj₂ tt`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvRaise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.GenFoldIf using (K₁; TopG; top; tpK)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NegGenFoldUpd using (jx; κ₁)
open import OCF.Align.KindLvIf using (KLv; rs; rs-top; rs≤)
```

## §1 "一起升": 每份底拷贝用同一个 $R$

```agda
-- 第 c 级的世界里, 每份底拷贝 (S₀ 的 A-界) 换成 φ (旧界)
rBR : ∀ {S : KS} (c : HB S) → (A → A) → Wd (Lev c) → Wd (Lev c)
rBR hz φ w = φ w
rBR (hs c) φ (w , β) = rBR c φ w , β
rBR (hl f) φ w = λ n → rBR (f n) φ (w n)
rBR (hΩ κ g) φ w = λ e → rBR (g e) φ (w e)

upAllR : (A → A → A) → Wd K₁ → A → Wd K₁
upAllR R w v (inj₁ tt) = w (inj₁ tt)
upAllR R w v (inj₂ c) = rBR c (λ a → R a v) (w (inj₂ c))

tp₁ : TopG K₁
tp₁ = tpK (genKc 1)

-- κ₁ f 的顶就是分量 jx f 的第 0 个子分量
top-κ₁ : ∀ f w → top tp₁ (κ₁ f) w ≡ w (inj₂ (jx f)) 0
top-κ₁ f w = refl
```

## §2 两条律不能同时成立

```agda
two one : A
two = asuc (asuc azero)
one = asuc azero

-- 每份底拷贝的界都是 a
wA : A → Wd K₁
wA a (inj₁ tt) = azero
wA a (inj₂ c) = rBR c (λ _ → a) (dWLev c)

-- 分量 hz (一份底拷贝) 的界是 2, 其余读回分量的底拷贝的界是 0
w′ : Wd K₁
w′ (inj₁ tt) = azero
w′ (inj₂ hz) = two
w′ (inj₂ (hs c)) = dWLev (hs c)
w′ (inj₂ (hl g)) = dWLev (hl g)
w′ (inj₂ (hΩ κ g)) = dWLev (hΩ κ g)

no21 : ¬ (two ⊲ one)
no21 (C.suc ())

no-upAllR : ∀ (R : A → A → A) (f : ℕ → H₀) →
  (∀ w v → top tp₁ (κ₁ f) (upAllR R w v) ≡ v) →
  (∀ {w v} → Pr K₁ (κ₁ f) w (top tp₁ (κ₁ f) w) v → _≤w_ K₁ w (upAllR R w v)) → ⊥
no-upAllR R f rt r≤ = no21 (subst (two ⊲_) (rt (wA two) one) (r≤ {w′} {one} (C.suc C.self) (inj₂ hz)))

no-klv-upAllR : ∀ (R : A → A → A) (f : ℕ → H₀) {Λ} (L : KLv K₁ tp₁ Λ (κ₁ f)) → (∀ w v → rs L w v ≡ upAllR R w v) → ⊥
no-klv-upAllR R f L eq = no-upAllR R f
  (λ w v → subst (λ u → top tp₁ (κ₁ f) u ≡ v) (eq w v) (rs-top L))
  (λ {w} {v} p → subst (λ u → _≤w_ K₁ w u) (eq w v) (rs≤ L p))
```

## §3 两半各自可满足

```agda
half-top : ∀ f w v → top tp₁ (κ₁ f) (upAllR (λ a v → v) w v) ≡ v
half-top f w v = refl

refl-rBR : ∀ {S : KS} (c : HB S) (w : Wd (Lev c)) → _≤w_ (Lev c) w (rBR c (λ a → a) w)
refl-rBR hz w = C.self
refl-rBR (hs c) (w , β) = refl-rBR c w , hself
refl-rBR (hl f) w = λ n → refl-rBR (f n) (w n)
refl-rBR (hΩ κ g) w = λ e → refl-rBR (g e) (w e)

half-≤ : ∀ f {w v} → Pr K₁ (κ₁ f) w (top tp₁ (κ₁ f) w) v → _≤w_ K₁ w (upAllR (λ a v → a) w v)
half-≤ f p (inj₁ tt) = C.self
half-≤ f {w} p (inj₂ c) = refl-rBR c (w (inj₂ c))
```

## §4 结论 (按档)

- **[定理, 否定]** **`no-upAllR`**, **`no-klv-upAllR`**: 对任何 $R$, `K₁` 的底拷贝 `κ₁ f` (对一切 $f$, 一切 $\Lambda$) 的 `KLv` 的 `rs` 不能是 "一起升" `upAllR R`.
- **[定理, 前提实例]** `half-top` ($R\,a\,v=v$ 满足 `rs-top`), `half-≤` ($R\,a\,v=a$ 满足 `rs≤`), `top-κ₁`.
- **[判断]** 合读 [NegKindLvUpd](NegKindLvUpd.lagda.md): 在以高度为下标的并的分量里, `KLv` 的 `rs` 既不能 "升一份留别份" (那里要 "留", 接口不要, 所以那条不直接打接口), 也不能 "一起升" (本篇, 打接口的 `rs-top` + `rs≤`). 余下的形状 (精确置 κ 自己的分量, 别的分量只增不减, 且增的方式依赖分量) 未否定也未构造; "穷尽" 是判断.
