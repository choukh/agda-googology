# `SL` 上带证据的回灌, 否定一路 (四): 接口 §4 各形状的边界

> 不含记号. 入口 [NegSLFb](NegSLFb.lagda.md). 对着接口 [SLFbIf](SLFbIf.lagda.md) ("接口定稿 2026-11-05 20:06 (首次编译通过)", 变更记录: 无) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP 作公设 (条件实例里 UIP 由 Hedberg 从前提 `DecLH` 推出), 不用函数外延; `FEΩ` 只在 `…→WLPO` 里作前提.
>
> 接口 §4 的四个形状 (`RsSL`, `RsSLᴾ`, `RsSL⊵`, `RsEv`) 都**不含** "别的分量不动" 一类的律. 本篇说清: 一旦加上这类律 (裸下标), 每个形状都撞墙; 不加时, 形状本身在本篇里**既没有构造也没有否定** (除 `lz` 与条件实例).
>
> - **加 "留" ⇒ 分离子** (对 $s$ 的头是 `lΩ`): `rsK+keep-sep` (`RsSL` 的分量, 或任一 `RsK`), `rsUp+keep-sep` (`RsSL⊵` 的分量), `rsEv+keep-sep` (`RsEv tpL w* Λ` 在第 $n+2$ 站, 站带字面公共上界证据 `stage-fst`; 证据只在目标下标上, 不在 "留" 比较的另一个下标上).
> - **`RsSLᴾ` + 同界证据 + "别的分量原样" ⇒ $\bot$**, 对一切 $s$ (`rsSLᴾ+keep-⊥`, 即 `NegSLFbSh.no-inv-keep`).
> - **前提可满足 (条件实例).** 在层号可判定的前提 `DecLH` 下, `RsSL tpL` 与 "留" 同时成立 (`decLH→RsSL`, `decLH→keep`). `DecLH` 经典地成立 (判断), 在 Agda 里证不出 (判断). 无条件的实例: `lz` 处 (`NegSLFbBlind.rkLz`, 它也满足 "留", `rkLz-keep`).
>
> **只否定什么.** 只否定 "§4 的形状 + 对裸下标的 '留'". **不否定** `RsSL`, `RsSLᴾ`, `RsSL⊵`, `RsEv` 本身: 它们只要求在一个下标处精确置 (或抬高) 而别处只增; 这要对一切层号 $k'$ 写出 $k'$ 处的新世界, 在 $k'\equiv s$ 时含 $v$ (插入). 本篇没有插入的构造, 也没有它推出分离子的定理 (判断: 插入单独不含可读出判定的信息, §4).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFbBd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top)
open import OCF.Align.LFReTy
open import OCF.Align.LFReTower using (tw; Λ)
open import OCF.Align.FabLFReGen using (stage-fst)
open import OCF.Align.RsOwnIf using (RsK; rs; rs≤; rsLg; rs-top; RsInv; module PW)
open import OCF.Align.SLFbIf
open import OCF.Align.NegSLFbSep using (wb; SepAt; PtUpdVP; updVP-sep; v→1; stage-sep; stage-lΩ; FEΩ; sep→WLPO)
open import OCF.Align.ColimWNeg using (WLPO)
open import OCF.Align.NegSLFbSh using (ShL; no-inv-keep; KeepC; shL-wb)
open import OCF.Align.NegSLFbBlind using (tpL; rkLz; rsLz)

open PW LH FL using (Keep)
```

## §1 "留" 的写法; 由 `RsK` 或 `RsUp` 加 "留" 得点更新

`Keep` 是 `RsOwnIf.PW.Keep` (下标不同的分量原样, 前提 `¬ (i ≡ i₀)` 是裸下标的不等). `KeepU` 是它对 `RsUp` 的同形.

```agda
rsK→pt : ∀ s (R : RsK SL tpL (νL s)) → Keep tpL s (inj₂ tt) R → PtUpdVP s (λ _ → ⊤)
rsK→pt s R kp = record
  { updV = λ w _ v → rs R w v
  ; raiseV = λ w _ v → subst (λ b → b ⊲[ proj₁ (rs R w v s) ] proj₂ (rs R w v s)) (rs-top R) hself
  ; keepV = λ w _ v k ne {c} b → subst (λ y → c ⊲[ proj₁ y ] proj₂ y) (Keep.keep kp w v k ne) b }

KeepU : ∀ s → RsUp SL tpL (νL s) → Set
KeepU s R = ∀ w v k → ¬ (k ≡ s) → rsu R w v k ≡ w k

rsUp→pt : ∀ s (R : RsUp SL tpL (νL s)) → KeepU s R → PtUpdVP s (λ _ → ⊤)
rsUp→pt s R kp = record
  { updV = λ w _ v → rsu R w v
  ; raiseV = λ w _ v → rs⊵ R
  ; keepV = λ w _ v k ne {c} b → subst (λ y → c ⊲[ proj₁ y ] proj₂ y) (kp w v k ne) b }
```

## §2 边界定理

```agda
-- RsSL 的一个分量 (或任一 RsK) + 留 ⇒ 分离子
rsK+keep-sep : ∀ k g (R : RsK SL tpL (νL (lΩ k g))) → Keep tpL (lΩ k g) (inj₂ tt) R → SepAt k g
rsK+keep-sep k g R kp = updVP-sep k g tt (rsK→pt (lΩ k g) R kp)

rsSL+keep-sep : ∀ (R : RsSL tpL) k g → Keep tpL (lΩ k g) (inj₂ tt) (R (lΩ k g)) → SepAt k g
rsSL+keep-sep R k g kp = rsK+keep-sep k g (R (lΩ k g)) kp

-- 一起抬高 + 留 ⇒ 分离子
rsUp+keep-sep : ∀ k g (R : RsUp SL tpL (νL (lΩ k g))) → KeepU (lΩ k g) R → SepAt k g
rsUp+keep-sep k g R kp = updVP-sep k g tt (rsUp→pt (lΩ k g) R kp)

-- 带字面公共上界证据的下标: 第 n+2 站带证据, 但 "留" 比较的是裸下标
rsEv+keep-sep : ∀ (w* : Wd SL) (E : RsEv tpL w* Λ) n →
  Keep tpL (ofHB (tw (suc (suc n)))) (inj₂ tt) (E (tw (suc (suc n))) (stage-fst (suc (suc n)))) →
  SepAt lz (proj₁ (stage-lΩ n))
rsEv+keep-sep w* E n kp = stage-sep n tt (v→1 (rsK→pt _ (E (tw (suc (suc n))) (stage-fst (suc (suc n)))) kp))

rsEv+keep→WLPO : FEΩ → ∀ (w* : Wd SL) (E : RsEv tpL w* Λ) n →
  Keep tpL (ofHB (tw (suc (suc n)))) (inj₂ tt) (E (tw (suc (suc n))) (stage-fst (suc (suc n)))) → WLPO
rsEv+keep→WLPO fe w* E n kp = sep→WLPO fe lz (proj₁ (stage-lΩ n)) (rsEv+keep-sep w* E n kp)

-- 带同界证据 + 别的分量原样 ⇒ ⊥ (对一切 s)
rsSLᴾ+keep-⊥ : ∀ {P : Wd SL → Set} → (∀ {w} → P w → ShL w) → ∀ {w₁} → P w₁ →
  (R : RsSLᴾ P tpL) → ∀ s → KeepC (R s) → ⊥
rsSLᴾ+keep-⊥ sh p₁ R s kp = no-inv-keep s sh p₁ (R s) kp

-- 前提 P 的实例: ShL 本身, 含基世界
shL-inst : ShL wb
shL-inst = shL-wb
```

## §3 前提可满足: `lz` 无条件, 一切层号在 `DecLH` 下

```agda
rkLz-keep : Keep tpL lz (inj₂ tt) rkLz
rkLz-keep = record { keep = kp }
  where
  kp : ∀ w v i → ¬ (i ≡ lz) → rsLz w v i ≡ w i
  kp w v lz ne = ⊥-elim (ne refl)
  kp w v (ls x) ne = refl
  kp w v (ll f) ne = refl
  kp w v (lΩ k g) ne = refl

DecLH : Set
DecLH = (x y : LH) → Dec (x ≡ y)

module WithDec (dec : DecLH) where
  open Decidable⇒UIP dec using (≡-irrelevant)

  ins : (k k′ : LH) → Dec (k′ ≡ k) → Wd (FL k′) → HB (Lv k) → Wd (FL k′)
  ins k k′ (yes refl) wk v = proj₁ wk , v
  ins k k′ (no _) wk v = wk

  rsD : (k : LH) → Wd SL → HB (Lv k) → Wd SL
  rsD k w v k′ = ins k k′ (dec k′ k) (w k′) v

  ins-at : ∀ k (d : Dec (k ≡ k)) wk v → proj₂ (ins k k d wk v) ≡ v
  ins-at k (yes e) wk v = subst (λ e′ → proj₂ (ins k k (yes e′) wk v) ≡ v) (≡-irrelevant refl e) refl
  ins-at k (no ne) wk v = ⊥-elim (ne refl)

  ins-≤ : ∀ (w : Wd SL) k k′ (d : Dec (k′ ≡ k)) v → proj₂ (w k) ⊲[ proj₁ (w k) ] v →
    _≤w_ (FL k′) (w k′) (ins k k′ d (w k′) v)
  ins-≤ w k .k (yes refl) v pre = ≤w-rf (Lv k) , pre
  ins-≤ w k k′ (no _) v pre = ≤w-rf (FL k′)

  ins-lg : ∀ (w : Wd SL) k k′ (d : Dec (k′ ≡ k)) v → LgW SL w → LgB v → LgW (FL k′) (ins k k′ d (w k′) v)
  ins-lg w k .k (yes refl) v lw lv = proj₁ (lw k) , lv
  ins-lg w k k′ (no _) v lw lv = lw k′

  ins-keep : ∀ (w : Wd SL) k k′ (d : Dec (k′ ≡ k)) v → ¬ (k′ ≡ k) → ins k k′ d (w k′) v ≡ w k′
  ins-keep w k .k (yes refl) v ne = ⊥-elim (ne refl)
  ins-keep w k k′ (no _) v ne = refl

  decLH→RsSL : RsSL tpL
  decLH→RsSL k = record
    { rs = rsD k
    ; rs≤ = λ {w} {v} pre k′ → ins-≤ w k k′ (dec k′ k) v pre
    ; rsLg = λ {w} {v} lw lv k′ → ins-lg w k k′ (dec k′ k) v lw lv
    ; rs-top = λ {w} {v} → ins-at k (dec k k) (w k) v }

  decLH→keep : ∀ s → Keep tpL s (inj₂ tt) (decLH→RsSL s)
  decLH→keep s = record { keep = λ w v k′ ne → ins-keep w s k′ (dec k′ s) v ne }

-- 精确升界给出一起抬高 (rs⊵ 是 rs-top 的运输)
rsK→rsUp : ∀ k → RsK SL tpL (νL k) → RsUp SL tpL (νL k)
rsK→rsUp k R = record
  { rsu = rs R ; rsu≤ = rs≤ R ; rsuLg = rsLg R
  ; rs⊵ = λ {w} {v} → subst (λ b → b ⊲[ proj₁ (rs R w v k) ] proj₂ (rs R w v k)) (rs-top R) hself }

decLH→RsSL⊵ : DecLH → RsSL⊵ tpL
decLH→RsSL⊵ dec k = rsK→rsUp k (WithDec.decLH→RsSL dec k)

-- 检查: 条件实例与边界定理相容 (DecLH 本身就给分离子)
decLH→sep : DecLH → ∀ k g → SepAt k g
decLH→sep dec k g = rsSL+keep-sep (WithDec.decLH→RsSL dec) k g (WithDec.decLH→keep dec (lΩ k g))
```

## §4 结论 (按档)

- **[定理, 否定]** **`rsK+keep-sep`**, **`rsSL+keep-sep`**, **`rsUp+keep-sep`**, **`rsEv+keep-sep`** (对 $s$ 的头是 `lΩ` 或第 $n+2$ 站: 形状 + 裸下标的 "留" ⇒ 分离子); **`rsSLᴾ+keep-⊥`** (同界证据 + 别的分量原样 ⇒ $\bot$, 对一切 $s$). **[条件 `FEΩ`]** `rsEv+keep→WLPO`.
- **[定理]** `rsK→pt`, `rsUp→pt` (形状 + 留 ⇒ `PtUpdVP`); `shL-inst`.
- **[定理, 前提实例]** `rkLz`, **`rkLz-keep`** (`lz` 处 `RsK` 与 "留" 同时成立, 无条件); **[条件 `DecLH`]** **`decLH→RsSL`**, **`decLH→keep`**, `decLH→sep` (一切层号上 `RsSL` 与 "留" 同时成立; UIP 由 Hedberg 从 `DecLH` 得出, 不是公设). `rsK→rsUp` (精确升界给出一起抬高), **[条件 `DecLH`]** `decLH→RsSL⊵`.
- **[判断]** `DecLH` 经典地成立, 在 Agda 里证不出. 不带 "留" 时, §4 的形状要对一切层号 $k'$ 写出新世界并在 $k'\equiv s$ 处含 $v$ ("插入"); 插入在含函数的 $s$ 上没有写出, 也没有否定 (未走通). 一条候选是逐结构的搬运 `HB (Lv s) → HB (Lv k′)`, 在 $k'\equiv s$ 时恒等要函数外延 (见 `NegSLFbSh` §5 末).
