# 新塔, 否定一路 (二): 最终坍缩的种类结构 `step KΛc` 上的回灌

> 不含记号. 入口 [NegNewTwr](NegNewTwr.lagda.md). 对着接口 [NewTwrIf](NewTwrIf.lagda.md) ("接口定稿 2026-11-05 17:39 (首次编译通过)", 变更记录: 无) 写, 导入它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在条件定理 `updΛ⁺→WLPO` 里作前提.
>
> 接口 §2 的 `CollGenTy` 说: 最终坍缩是 GenFold 的一般折叠在 `step T` 上 (取 `T = KΛc`), 要 `GenK KΛc`, `LgDn KΛc`, `FbLg`. 接口文件头: 回灌 "只在可判定下标上点更新 (`GenFoldInst.upd`, `updL`), 其余有损", "本接口不含 '升一份留别份'". 嫌疑 (i) 问的就是这一处. 本篇:
>
> 1. **`updΛ-sep`, `updΛ⁺-sep` (定理, 否定).** 在 `KΛc` 与最终层所在的 `step KΛc` 上, 对一切世界一致地 "升第 1 站读回分量 `jx f` 里的底拷贝, 留 `jx f′` 里的底拷贝" 推出分离子 (`FE₀` 下 WLPO). 这是 `NegGenFoldUpd.upd₁-sep` 经 ℕ-分量 (可判定) 与 `step` 的旧种类搬上来. 两半各自可满足 (`halfΛR`, `halfΛK`, `halfΛ⁺R`, `halfΛ⁺K`). 所以接口不含 "升一份留别份" 是**被逼的**, 不是省略: 最终坍缩里读回分量的种类要么有损, 要么 "一起升".
> 2. **`lossyΛ⁺` (定理, `refl`).** 现有的 `GenK` 实例 (`GenFoldInst.genKc` 经 `genSupℕ`, 再 `genStep`, 记 `genΛ⁺`) 在 `step KΛc` 的一切读回分量种类 `inj₁ (s+1 , (inj₂ c , κ))` 上给 `inj₂ tt` (有损). 与 [NegNewTwrShape](NegNewTwrShape.lagda.md) 的 `final-kinds` 合起来: 最终层里的 $\Omega$-结点全落在有损的种类上 (`final-lossy`).
> 3. **`fbBd-any` (定理, 盲).** GenFold 接口 §8 的 `FbBd` (为回应 `NegGenFold.fba-swap` 而加的 "回灌绑到种类上") 对**一切** `GenK` 成立: `toE` 取底坐标 `bot`, 两条律都是 `botBd`. 所以 §8 不能区分 "升了 κ 自己的界" 与 "升了别的分量" (`NegGenFoldBlind.genK₁` 也满足它, `fbBd₁`). 本接口的 `CollGenTy` 连 `FbBd` 都不要.
> 4. **`hasΛ⁺` (定理, 对照).** 接口说 "最终层的类型不是 `Ht` 的收缩": 对的. `step KΛc` 有坐标类型定义相等于 `Ht` 的种类, 由 `NegDnFoldRet.no-faithful` 得 `HB (step KΛc) → Ht` 无左逆 (`no-ret-final`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwrFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀; Ht)
open import OCF.Align.LvKtCode using (w0)
open import OCF.Align.LvKtIf using (Kc; KΛc; ckc)
open import OCF.Align.GenFoldIf using (K₁; GenK; FBA; FBABd; FbBd; FbBdAt; fbA; FbLg; LgDn)
open import OCF.Align.GenFoldInst using (genKc; genSupℕ; genStep; ldKc; ldSup; ldStep; flKc; flSupℕ; flStep)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.NegGenFoldUpd using (jx; κ₁; PtUpdB₁; Sep; updB₁-sep; sep→WLPO; upAll₁)
open import OCF.Align.NegGenFoldBlind using (genK₁)
open import OCF.Align.NegDnFoldRet using (HasHt; no-faithful)
open import OCF.Align.NewTwrIf using (CollGenTy)
```

## §1 `KΛc` 与 `step KΛc` 上的点更新

`κΛ f`: 第 1 站读回分量 `inj₂ (jx f)` 里第 0 个子分量的底种类 (坐标 `A`), 作为 `KΛc` 的种类. 证明只在一个世界 `ext₁ w` 上用到点更新, 别的站取基世界; 第 1 站的分量就是 `K₁` 的世界 (ℕ-下标可判定, 按模式写).

```agda
κΛ : (ℕ → H₀) → K KΛc
κΛ f = 1 , κ₁ f

record PtUpdBΛ : Set where
  field
    updB   : Wd KΛc → (ℕ → H₀) → A → Wd KΛc
    raiseB : ∀ w f x {c} → c ⊲ x → Bd KΛc (κΛ f) c (updB w f x)
    keepB  : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd KΛc (κΛ f′) c (updB w f x) → Bd KΛc (κΛ f′) c w

ext₁ : Wd K₁ → Wd KΛc
ext₁ w zero = w0 (ckc 0)
ext₁ w (suc zero) = w
ext₁ w (suc (suc s)) = w0 (ckc (suc (suc s)))

toB₁ : PtUpdBΛ → PtUpdB₁
toB₁ P = record
  { updB = λ w f x → updB (ext₁ w) f x 1
  ; raiseB = λ w f x p → raiseB (ext₁ w) f x p
  ; keepB = λ w f x f′ ne b → keepB (ext₁ w) f x f′ ne b }
  where open PtUpdBΛ P

updΛ-sep : PtUpdBΛ → Sep
updΛ-sep P = updB₁-sep (toB₁ P)

-- 最终层所在的种类结构: step KΛc 的旧种类就是 KΛc 的种类
record PtUpdBΛ⁺ : Set where
  field
    updB   : Wd (step KΛc) → (ℕ → H₀) → A → Wd (step KΛc)
    raiseB : ∀ w f x {c} → c ⊲ x → Bd (step KΛc) (inj₁ (κΛ f)) c (updB w f x)
    keepB  : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} →
             Bd (step KΛc) (inj₁ (κΛ f′)) c (updB w f x) → Bd (step KΛc) (inj₁ (κΛ f′)) c w

toBΛ : PtUpdBΛ⁺ → PtUpdBΛ
toBΛ P = record
  { updB = λ w f x → proj₁ (updB (w , hz) f x)
  ; raiseB = λ w f x p → raiseB (w , hz) f x p
  ; keepB = λ w f x f′ ne b → keepB (w , hz) f x f′ ne b }
  where open PtUpdBΛ⁺ P

updΛ⁺-sep : PtUpdBΛ⁺ → Sep
updΛ⁺-sep P = updΛ-sep (toBΛ P)

updΛ⁺→WLPO : FE₀ → PtUpdBΛ⁺ → WLPO
updΛ⁺→WLPO fe P = sep→WLPO fe (updΛ⁺-sep P)
```

**两半各自可满足.** 只升: 第 1 站的分量用 `NegGenFoldUpd.upAll₁` (每份底拷贝一起升), 别的站不动. 只留: 世界不动.

```agda
upΛ : Wd KΛc → (ℕ → H₀) → A → Wd KΛc
upΛ w f x zero = w zero
upΛ w f x (suc zero) = upAll₁ (w 1) f x
upΛ w f x (suc (suc s)) = w (suc (suc s))

halfΛR : ∀ w f x {c} → c ⊲ x → Bd KΛc (κΛ f) c (upΛ w f x)
halfΛR w f x p = p

stayΛ : Wd KΛc → (ℕ → H₀) → A → Wd KΛc
stayΛ w f x = w

halfΛK : ∀ w f (x : A) f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd KΛc (κΛ f′) c (stayΛ w f x) → Bd KΛc (κΛ f′) c w
halfΛK w f x f′ ne b = b

halfΛ⁺R : ∀ (w : Wd (step KΛc)) f x {c} → c ⊲ x → Bd (step KΛc) (inj₁ (κΛ f)) c (upΛ (proj₁ w) f x , proj₂ w)
halfΛ⁺R w f x p = p

halfΛ⁺K : ∀ (w : Wd (step KΛc)) f (x : A) f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} →
  Bd (step KΛc) (inj₁ (κΛ f′)) c (stayΛ (proj₁ w) f x , proj₂ w) → Bd (step KΛc) (inj₁ (κΛ f′)) c w
halfΛ⁺K w f x f′ ne b = b
```

## §2 现有实例在读回分量上有损

```agda
genΛ : GenK KΛc
genΛ = genSupℕ Kc genKc

genΛ⁺ : GenK (step KΛc)
genΛ⁺ = genStep genΛ

ldΛ⁺ : LgDn (step KΛc)
ldΛ⁺ = ldStep (ldSup ℕ Kc ldKc)

flΛ⁺ : FbLg genΛ⁺
flΛ⁺ = flStep genΛ (flSupℕ Kc genKc flKc)

-- KΛc 的一切读回分量种类: 有损
lossyΛ : ∀ s (c : HB (Kc s)) (κ : K (Lev c)) → fbA genΛ (suc s , (inj₂ c , κ)) ≡ inj₂ tt
lossyΛ s c κ = refl

-- 作为 step KΛc 的旧种类: 有损
lossyΛ⁺ : ∀ s (c : HB (Kc s)) (κ : K (Lev c)) → fbA genΛ⁺ (inj₁ (suc s , (inj₂ c , κ))) ≡ inj₂ tt
lossyΛ⁺ s c κ = refl

-- step KΛc 的新种类: 也不给 A-回灌 (它的回灌是第 0, 1 层的新种类行, GenFoldRun 的 κc₁)
newΛ⁺ : fbA genΛ⁺ (inj₂ tt) ≡ inj₂ tt
newΛ⁺ = refl
```

## §3 GenFold 接口 §8 是盲的

```agda
bdAt : ∀ {T : KS} {κ : K T} (s : FBA T κ ⊎ ⊤) → FbBdAt {T} {κ} s
bdAt {T} {κ} (inj₁ F) = record { toE = λ _ → bot T κ ; tp-bd = botBd T κ _ ; rs-bd = botBd T κ _ }
bdAt (inj₂ _) = tt

fbBd-any : ∀ {T : KS} (G : GenK T) → FbBd G
fbBd-any G κ = bdAt (fbA G κ)

-- NegGenFoldBlind.genK₁ (每个种类的 "回灌" 都只升旧站分量 inj₁ tt) 也满足 §8
fbBd₁ : FbBd genK₁
fbBd₁ = fbBd-any genK₁
```

## §4 对照: 最终层的类型确实不是 `Ht` 的收缩

```agda
two : HB S₀
two = hs (hs hz)

hasΛ⁺ : HasHt (step KΛc)
hasΛ⁺ = inj₁ (1 , (inj₂ two , inj₂ tt)) , refl

no-ret-final : ∀ (d : HB (step KΛc) → Ht) (r : Ht → HB (step KΛc)) → ¬ (∀ x → r (d x) ≡ x)
no-ret-final = no-faithful hasΛ⁺
```

## §5 结论 (按档)

- **[定理, 否定]** **`updΛ-sep`** (`KΛc`), **`updΛ⁺-sep`** (`step KΛc`): 点更新 (升 `κΛ f`, 留 `κΛ f′`) ⇒ 分离子. **[条件 `FE₀`]** `updΛ⁺→WLPO`. **[定理, 前提实例]** `halfΛR`, `halfΛK`, `halfΛ⁺R`, `halfΛ⁺K` (两半各自可满足); 分离子经典地成立 (判断).
- **[定理, `refl`]** `lossyΛ`, `lossyΛ⁺`, `newΛ⁺`: 现有实例 `genΛ⁺` 在一切读回分量种类上有损, 新种类也不给 A-回灌. `genΛ⁺`, `ldΛ⁺`, `flΛ⁺` 是 `CollGenTy` 的前提的实例 (所以 `CollGenTy` 用于 `KΛc` 不空).
- **[定理, 盲]** **`fbBd-any`**: GenFold 接口 §8 的 `FbBd` 对一切 `GenK` 成立; `fbBd₁`.
- **[定理, 对照]** `hasΛ⁺`, `no-ret-final`: 接口关于最终层类型的说法成立.
- **只否定什么.** 只否定 `step KΛc` (与 `KΛc`) 的世界上对一切世界一致的 "升一份底拷贝, 留另一份" (两份在第 1 站的两个以高度为下标的读回分量里). **不否定**: 接口的任何记录 (接口本来就不含这条律); 有损回灌; "一起升" (`upΛ`, 判断: 它把别的分量的底拷贝也升了, `NegGenFoldUpd.upAll₁-moves`, 合法性要另证); 可判定下标上的点更新 (`GenFoldInst.upd`, `updL`).
