# `Lev` 取并的否定: 入口

> 不含记号. 对着接口 [ColimWIf](ColimWIf.lagda.md) ("接口定稿 2026-11-05 10:46", 变更记录: 无) 写; 本篇导入它, 不另造接口. 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2, §2.4, §3.1. 草稿 [ColimWNegDraft](ColimWNegDraft.lagda.md) 是定稿前对 "沿塔的映射取余极限" 写的一般形, 与接口的差别见那里. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延 `FE₀`, `FE₁` 只作前提, 用到它的结论标 "条件".
>
> **判决: 部分.** 认同本身 (`Glob`) 不推出禁忌; 墙落在更新上, 而且**可入版的律也挡不住**, 因为世界 `GW S = A × Π_{y : HB S} HB (Lev y)` 是裸层号上的函数.
>
> 1. **`RaiseA` (可入版更新) 推出分离子, 有外延时推出 WLPO.** `SepA.raiseA-sep` (无条件): 若对一族合法的外层世界 `wα α` 都有 `RaiseA x₀ (wα α)`, 则对每个 $lpha$: 要么 `up (yα α) ≢ up ω₀`, 要么 $lpha$ 恒假. `raiseA→WLPO` (条件: `FE₀`): WLPO. 原因: 律只对可入层号陈述, 但 `raiseA` 的值是对**一切**层号的函数; 在 $y_0$ 处必须变 (`atA`), 在可入且 $
eq y_0$ 处必须不变 (`offA`), 于是值本身就把 $y_0$ 与可入层号分开了. 测试层号 `up ω₀` 是否可入, 取决于 $lpha$ (`adm₁`: 某处为真时可入), 所以这个分离子对不带证据的输入起作用. 这正是诊断 §3.1 第 1 条 "世界 = 裸下标上的积" 换了一个位置重新出现: `AdmWIf` 的世界以 (坐标, 证据) 为下标, 这里的 `GW` 以裸层号为下标.
> 2. **判定证书只到有限层号.** `up ω₀` 在 $x_0$ 之下可入 (`adm-ω`, 合法世界 `wω`). `decAtω→WLPO` (条件: `FE₀`): `DecAt (up ω₀)` 推出 WLPO; `raiseGω→WLPO` (条件: `FE₀`): 只在这一个层号上的 `RaiseG (up ω₀)` 也推出 WLPO. 无条件的部分是 `decAtω-sep`, `SepG.raiseGω-sep`. 有限层号上证书是构造 (`decAt-fin`, `decAt→raiseG`).
> 3. **`RaiseG` 对一切层号**: 层号相等的弱判定 (`raiseG→wdec`, 对一切 `S`). 这是 `CohWUpd.upd→wdec` 在接口记录上的重证; 接口自己已写明.
> 4. **可满足与反模型.** 由可入层号上的证书造 `RaiseA` (`decAdm→raiseA`, 对一切 `S`, $x$, $w$; 五条律都是定理). 外层界是有限高度时可入层号都是有限的, `RaiseA x₀ (a, finH k)` 是构造 (`raiseA-fin`), 且可入集非空 (`adm-fin-ex`). 所以 `RaiseA` 这个类型不是空的, 墙在 "对一族外层世界一致地造" 上.
> 5. **认同不要判定, 也不撞 `no-retract`, Ω-极限处不比较分支 (判断, 不是否定).** `Glob` 每条只含一个种类; `restr` 在 Ω-极限处逐坐标取, 不比较坐标; `LevC x` 的种类就是 `Lev x` 的, 不新增种类, `no-retract` 照旧成立 (构造一路的 `ColimWKS.no-retractC`, 我只读了它的陈述, 没有复核). 诊断的嫌疑 (i), (iii), (iv) 在这个接口上我找不到要否定的律. (i) 的一般形 (若认同改成 "沿塔的映射", 律写在裸下标的第一位置关系上) 在草稿里是**无条件**的 WLPO (`ColimWNegDraft.wdec⊲→WLPO`, `wdecH→WLPO`), 但接口没有这样的律.
> 6. **字面认同到外延为止** (§6, 条件: `FE₁`): `up ω₀` 与 `hl finH` 字面不同而逐点相等; 有外延时相等 (`up-ω`), 没有外延时 `GW` 在两处各有一个分量. 不是否定.
>
> **律为什么是构造一路需要的.** `RaiseA` 是接口 §4 自己写下的可入版回灌; 折叠在节点 $x$ 处把当前世界里某个可入层号的界接长, 当前的外层世界随折叠变化, 所以一致的构造给出对一切合法外层世界的 `RaiseA x w`, 特别地对 `wα` 这一族 (每个都合法, `Lg-wα`). 证明只用 `raiseA`, `atA`, `offA` 三个字段, 世界 `W₀` 合法 (`lgW₀`), 增量 $1$ 合法. `DecAt` 是接口给 `RaiseG` 的证书; `up ω₀` 是 $x_0$ 下坐标 `hs ω₀` 处新种类的层号, 折叠到这个种类时要升它的界 (判断: 折叠对它遇到的每个种类回灌).
>
> **前提实例.** `wα α` 合法 (`Lg-wα`), $y_0 =$ `up (yα α)` 可入 (`p₀α`), `up ω₀` 在 $lpha$ 某处为真时可入 (`adm₁`), 在 `wω` 里可入 (`adm-ω`). `RaiseA` 的实例: `raiseA-fin`; 经典地 (高度相等可判定, 由 Hedberg 对角给 `refl`) 有一切 `DecAt`, 再由 `decAdm→raiseA` 得到一切 `RaiseA x w`, 所以前提族经典地可满足. `FE₀`, `FE₁` 在 Agda 里证不出也否证不了; 有外延而 WLPO 不成立的构造性模型 (实现性) 里, 条件定理说那一族 `RaiseA` 不存在 (纸面, 元定理, 不是编译的), 与 `CohW2Need.raise-Lc→WLPO` 同档.
>
> **只否定什么.** 只否定: 在 `GW` 上, 对 $x_0$ 与 `wα` 这一族合法外层世界一致地满足 `raiseA`/`atA`/`offA` (条件: `FE₀`; 无条件的是分离子); `DecAt (up ω₀)` 与 `RaiseG (up ω₀)` (条件: `FE₀`). **不否定**: `LevC`, `Glob`, `GlobPr`, `cmpK`, `botBd` (认同本身); 单个外层世界上或可入层号都有证书时的 `RaiseA` (`raiseA-fin` 是构造); 世界只对可入层号给分量 (例如 $\Sigma_y$ `AdmL x w y` $	o$ `HB (Lev y)`, 判断: 那时输入带证据, `bdec` 给出分离, 本文的论证不适用; 没有试); 不带 `offA` 的更新 (例如对 $y_0$ 之上的一切层号一起接长); 取并这个方向本身.
>
> **定理表.** §3 `SepA.raiseA-sep` [定理], `raiseA→WLPO` [定理, 条件 FE₀]; §4 `raiseG→wdec` [定理], `SepG.raiseGω-sep`, `decAtω-sep` [定理], `raiseGω→WLPO`, `decAtω→WLPO` [定理, 条件 FE₀], `adm-ω`, `Lg-wω` [定理]; §5 `decAt-fin`, `decAt→raiseG`, `decAdm→raiseA`, `raiseA-fin`, `adm-fin`, `adm-fin-ex` [定理, 构造]; §6 `up-ω` [定理, 条件 FE₁].

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.ColimWIf
open RaiseG
open RaiseA
```

## §1 禁忌与外延

```agda
WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

-- 函数外延, 只对 ℕ → HB S₀, 只作前提
FE₀ : Set
FE₀ = ∀ (f g : ℕ → HB S₀) → (∀ n → f n ≡ g n) → f ≡ g

t≢f : true ≡ false → ⊥
t≢f ()

hs≢hz : ∀ {T : KS} {t : HB T} → hs t ≡ hz → ⊥
hs≢hz ()

isz : ∀ {T : KS} → HB T → Bool
isz hz = true
isz (hs _) = false
isz (hl _) = false
isz (hΩ _ _) = false

isz-true : ∀ {T : KS} (t : HB T) → isz t ≡ true → t ≡ hz
isz-true hz e = refl
isz-true (hs _) ()
isz-true (hl _) ()
isz-true (hΩ _ _) ()

unhs : ∀ {T : KS} → HB T → HB T
unhs (hs t) = t
unhs t = t

-- 层号函数在相等的两个层号上取相等的值 (沿 J; 两端都是变元)
tr-at : ∀ {S : KS} (F : (y : HB S) → HB (Lev y)) {y₀ y : HB S} → y₀ ≡ y → F y₀ ≡ hs hz → F y ≡ hz → ⊥
tr-at F refl e e′ = hs≢hz (trans (sym e) e′)
```

## §2 一族层号: 恒假时是 $\omega$, 某处为真时字面不同

`or α n` 是 $\alpha$ 前 $n+1$ 项的析取. `hα α n`: 尚未见到真时是 $n$, 见到之后是 $\omega + (n+1)$. `yα α = lim hα`. 恒假时 (有外延) `yα α` 就是 `ω₀ = lim finH`; 某处为真时 `up (yα α)` 与 `up ω₀` 字面不同 (无外延).

```agda
or : (ℕ → Bool) → ℕ → Bool
or α zero = α zero
or α (suc n) = or α n ∨ α (suc n)

or-in : ∀ α k → α k ≡ true → or α k ≡ true
or-in α zero e = e
or-in α (suc k) e with or α k
... | true = refl
... | false = e

or-false : ∀ α → (∀ n → α n ≡ false) → ∀ n → or α n ≡ false
or-false α h zero = h zero
or-false α h (suc n) rewrite or-false α h n = h (suc n)

hpick : Bool → ℕ → HB S₀
hpick false n = finH n
hpick true n = ω₀ ⊞ finH (suc n)

hα : (ℕ → Bool) → ℕ → HB S₀
hα α n = hpick (or α n) n

yα : (ℕ → Bool) → HB S₀
yα α = hl (hα α)

lg-fin : ∀ {S : KS} n → LgB {S} (finH n)
lg-fin zero = tt
lg-fin (suc n) = lg-fin n

Lg-ω₀ : LgB ω₀
Lg-ω₀ = (λ n → hsuc hself) , lg-fin

stepP : ∀ {w} b c k → hpick b k ⊲[ w ] hpick (b ∨ c) (suc k)
stepP true c k = hsuc hself
stepP false false k = hsuc hself
stepP false true k = ⊲ᴮ-tr (hlim k hself) (⊞-fst ω₀ (finH (suc (suc k))))

lgP : ∀ b k → LgB (hpick b k)
lgP false k = lg-fin k
lgP true k = Lg-⊞ ω₀ (finH (suc k)) Lg-ω₀ (lg-fin (suc k))

Lg-yα : ∀ α → LgB (yα α)
Lg-yα α = (λ n → stepP (or α n) (α (suc n)) n) , (λ n → lgP (or α n) n)
```

外层世界 `wα α = (0, yα α + 2)`. 合法.

```agda
bα : (ℕ → Bool) → HB S₀
bα α = hs (hs (yα α))

wα : (ℕ → Bool) → Wd S₁
wα α = azero , bα α

Lg-wα : ∀ α → LgW S₁ (wα α)
Lg-wα α = tt , Lg-yα α
```

**可入.** 层号 `up (yα α)` 在 $x_0$ 之下对一切 $\alpha$ 可入 (经坐标 `hs (yα α)`); 层号 `up ω₀` 在 $\alpha$ 某处为真时可入 (经坐标 `hs ω₀`, 它字面地在 `yα α` 的某一项之下).

```agda
p₀α : ∀ α → AdmL x₀ (wα α) (up (yα α))
p₀α α = hLim {c = hs (yα α)} (hsuc hself) hself

one⊲ : ∀ k → _⊲[_]_ {S₀} (finH 1) azero (finH (suc k))
one⊲ zero = hself
one⊲ (suc k) = hsuc (one⊲ k)

hit⊲ : ∀ α k → α k ≡ true → _⊲[_]_ {S₀} (hs ω₀) azero (yα α)
hit⊲ α k e = hlim k (subst (λ b → hs ω₀ ⊲[ azero ] hpick b k) (sym (or-in α k e)) (⊞-⊲ ω₀ (one⊲ k)))

adm₁ : ∀ α k → α k ≡ true → AdmL x₀ (wα α) (up ω₀)
adm₁ α k e = hLim {c = hs ω₀} (hsuc (hsuc (hit⊲ α k e))) hself
```

**某处为真时字面不同** (无外延): 看极限的第 $k$ 项剥去前导后继之后的头.

```agda
comp : ∀ {T : KS} → HB T → ℕ → HB T
comp (hl f) n = f n
comp _ n = hz

tip : ∀ {T : KS} → HB T → Bool
tip hz = true
tip (hs t) = tip t
tip (hl _) = false
tip (hΩ _ _) = false

tip-fin : ∀ k → tip (up {S₀} (finH k)) ≡ true
tip-fin zero = refl
tip-fin (suc k) = tip-fin k

tip-ω : ∀ k → tip (up (ω₀ ⊞ finH k)) ≡ false
tip-ω zero = refl
tip-ω (suc k) = tip-ω k

tipP : ∀ b k → b ≡ true → tip (up (hpick b k)) ≡ false
tipP true k refl = tip-ω (suc k)

ne₁ : ∀ α k → α k ≡ true → ¬ (up (yα α) ≡ up ω₀)
ne₁ α k e eq = t≢f (trans (sym (tip-fin k)) (trans (sym (cong (λ t → tip (comp t k)) eq)) (tipP (or α k) k (or-in α k e))))

-- 恒假时 (有外延) 相等
yα≡ : FE₀ → ∀ α → (∀ n → α n ≡ false) → yα α ≡ ω₀
yα≡ fe α h = cong hl (fe (hα α) finH (λ n → cong (λ b → hpick b n) (or-false α h n)))
```

## §3 可入版更新 `RaiseA`: 世界是裸层号上的函数, 仍要分出 $y_0$

全 0 的世界 `W₀`, 增量 $1$.

```agda
W₀ : ∀ {S : KS} → GW S
W₀ = azero , (λ y → hz)

lgW₀ : ∀ {S : KS} → LgG {S} W₀
lgW₀ = tt , (λ y → tt)

module SepA (R : ∀ α → RaiseA x₀ (wα α)) where
  Fα : (ℕ → Bool) → GW S₁
  Fα α = raiseA (R α) W₀ (up (yα α)) (p₀α α) (hs hz)

  vα : (ℕ → Bool) → HB (Lev (up ω₀))
  vα α = proj₂ (Fα α) (up ω₀)

  look : ∀ α (b : Bool) → isz (vα α) ≡ b → ¬ (up (yα α) ≡ up ω₀) ⊎ (∀ n → α n ≡ false)
  look α true e = inj₁ (λ eq → tr-at (proj₂ (Fα α)) eq (atA (R α) W₀ (up (yα α)) (p₀α α) (hs hz)) (isz-true (vα α) e))
  look α false e = inj₂ (λ n → helper n (α n) refl)
    where
    helper : ∀ n b → α n ≡ b → α n ≡ false
    helper n false h = h
    helper n true h = ⊥-elim (t≢f (trans (sym (cong isz (offA (R α) W₀ (up (yα α)) (p₀α α) (hs hz) (up ω₀) (adm₁ α n h) (ne₁ α n h)))) e))

  raiseA-sep : ∀ α → ¬ (up (yα α) ≡ up ω₀) ⊎ (∀ n → α n ≡ false)
  raiseA-sep α = look α (isz (vα α)) refl

raiseA→WLPO : FE₀ → (∀ α → RaiseA x₀ (wα α)) → WLPO
raiseA→WLPO fe R α with SepA.raiseA-sep R α
... | inj₁ ne = inj₂ (λ h → ne (cong up (yα≡ fe α h)))
... | inj₂ h = inj₁ h
```

## §4 裸层号版 `RaiseG` 与判定证书 `DecAt`, 在单个无穷层号 `up ω₀` 上

```agda
-- RaiseG 在一切层号上: 层号相等的弱判定 (对一切 S)
module _ {S : KS} (R : ∀ (y₀ : HB S) → RaiseG y₀) where
  lookG : ∀ y₀ y (b : Bool) → isz (proj₂ (raise (R y₀) W₀ (hs hz)) y) ≡ b → ¬ (y₀ ≡ y) ⊎ ¬ ¬ (y₀ ≡ y)
  lookG y₀ y true e = inj₁ (λ eq → tr-at (proj₂ (raise (R y₀) W₀ (hs hz))) eq (at (R y₀) W₀ (hs hz)) (isz-true _ e))
  lookG y₀ y false e = inj₂ (λ ne → t≢f (trans (sym (cong isz (off (R y₀) W₀ (hs hz) y ne))) e))

  raiseG→wdec : ∀ y₀ y → ¬ (y₀ ≡ y) ⊎ ¬ ¬ (y₀ ≡ y)
  raiseG→wdec y₀ y = lookG y₀ y _ refl

-- RaiseG 只在一个层号 up ω₀ 上
module SepG (R : RaiseG (up ω₀)) where
  FG : GW S₁
  FG = raise R W₀ (hs hz)

  lookω : ∀ α (b : Bool) → isz (proj₂ FG (up (yα α))) ≡ b → ¬ (up ω₀ ≡ up (yα α)) ⊎ (∀ n → α n ≡ false)
  lookω α true e = inj₁ (λ eq → tr-at (proj₂ FG) eq (at R W₀ (hs hz)) (isz-true _ e))
  lookω α false e = inj₂ (λ n → helper n (α n) refl)
    where
    helper : ∀ n b → α n ≡ b → α n ≡ false
    helper n false h = h
    helper n true h = ⊥-elim (t≢f (trans (sym (cong isz (off R W₀ (hs hz) (up (yα α)) (λ eq → ne₁ α n h (sym eq))))) e))

  raiseGω-sep : ∀ α → ¬ (up ω₀ ≡ up (yα α)) ⊎ (∀ n → α n ≡ false)
  raiseGω-sep α = lookω α _ refl

raiseGω→WLPO : FE₀ → RaiseG (up ω₀) → WLPO
raiseGω→WLPO fe R α with SepG.raiseGω-sep R α
... | inj₁ ne = inj₂ (λ h → ne (cong up (sym (yα≡ fe α h))))
... | inj₂ h = inj₁ h

-- 判定证书 DecAt 在 up ω₀ 上
decAtω-sep : DecAt (up ω₀) → ∀ α → (∀ n → α n ≡ false) ⊎ ¬ (up ω₀ ≡ up (yα α))
decAtω-sep (d , _) α with d (up (yα α))
... | inj₂ ne = inj₂ ne
... | inj₁ eq = inj₁ (λ n → helper n (α n) refl)
  where
  helper : ∀ n b → α n ≡ b → α n ≡ false
  helper n false h = h
  helper n true h = ⊥-elim (ne₁ α n h (sym eq))

decAtω→WLPO : FE₀ → DecAt (up ω₀) → WLPO
decAtω→WLPO fe D α with decAtω-sep D α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (cong up (sym (yα≡ fe α h))))

-- up ω₀ 确实是 x₀ 之下的可入层号 (在一个合法世界里)
wω : Wd S₁
wω = azero , hs (hs ω₀)

Lg-wω : LgW S₁ wω
Lg-wω = tt , Lg-ω₀

adm-ω : AdmL x₀ wω (up ω₀)
adm-ω = hLim {c = hs ω₀} (hsuc hself) hself
```

## §5 前提可满足: 有限层号上的判定证书, 与由证书造出的 `RaiseA`

```agda
mapS : ∀ {S : KS} {a b : HB S} → (a ≡ b) ⊎ ¬ (a ≡ b) → (hs a ≡ hs b) ⊎ ¬ (hs a ≡ hs b)
mapS (inj₁ e) = inj₁ (cong hs e)
mapS (inj₂ ne) = inj₂ (λ e → ne (cong unhs e))

dfin : ∀ {S : KS} n (y : HB S) → (finH n ≡ y) ⊎ ¬ (finH n ≡ y)
dfin zero hz = inj₁ refl
dfin zero (hs y) = inj₂ (λ ())
dfin zero (hl f) = inj₂ (λ ())
dfin zero (hΩ κ g) = inj₂ (λ ())
dfin (suc n) hz = inj₂ (λ ())
dfin (suc n) (hs y) = mapS (dfin n y)
dfin (suc n) (hl f) = inj₂ (λ ())
dfin (suc n) (hΩ κ g) = inj₂ (λ ())

dfin-diag : ∀ {S : KS} n → dfin {S} n (finH n) ≡ inj₁ refl
dfin-diag zero = refl
dfin-diag (suc n) = cong mapS (dfin-diag n)

decAt-fin : ∀ {S : KS} n → DecAt {S} (finH n)
decAt-fin n = dfin n , dfin-diag n

-- 沿判定证书的增量: 判为相等时搬过去, 否则 0
module _ {S : KS} where
  inc : ∀ {y₀ y : HB S} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → HB (Lev y₀) → HB (Lev y)
  inc (inj₁ e) δ = subst (λ z → HB (Lev z)) e δ
  inc (inj₂ _) δ = hz

  Lg-inc : ∀ {y₀ y : HB S} (t : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ → LgB δ → LgB (inc t δ)
  Lg-inc (inj₁ refl) δ l = l
  Lg-inc (inj₂ _) δ l = tt

  inc-off : ∀ {y₀ y : HB S} (t : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ → ¬ (y₀ ≡ y) → inc t δ ≡ hz
  inc-off (inj₁ e) δ ne = ⊥-elim (ne e)
  inc-off (inj₂ _) δ ne = refl

-- 有证书就有 RaiseG (裸层号的 off 由证书给出)
decAt→raiseG : ∀ {S : KS} {y₀ : HB S} → DecAt y₀ → RaiseG y₀
decAt→raiseG {y₀ = y₀} (d , dd) = record
  { raise = λ W δ → proj₁ W , (λ y → proj₂ W y ⊞ inc (d y) δ)
  ; base = λ W δ → refl
  ; at = λ W δ → cong (λ t → proj₂ W y₀ ⊞ inc t δ) dd
  ; off = λ W δ y ne → cong (λ t → proj₂ W y ⊞ t) (inc-off (d y) δ ne)
  ; mono = λ W δ → C.self , (λ y → ⊞-fst (proj₂ W y) (inc (d y) δ))
  ; legal = λ W δ l lW → proj₁ lW , (λ y → Lg-⊞ (proj₂ W y) (inc (d y) δ) (proj₂ lW y) (Lg-inc (d y) δ l)) }

-- 由可入层号上的判定证书造 RaiseA (对一切 S, x, w)
module _ {S : KS} {x : HB S} {w : Wd S} (D : ∀ y₀ → AdmL x w y₀ → DecAt y₀) where
  rA : GW S → (y₀ : HB S) → AdmL x w y₀ → HB (Lev y₀) → GW S
  rA W y₀ p₀ δ = proj₁ W , (λ y → proj₂ W y ⊞ inc (proj₁ (D y₀ p₀) y) δ)

  decAdm→raiseA : RaiseA x w
  decAdm→raiseA = record
    { raiseA = rA
    ; atA = λ W y₀ p₀ δ → cong (λ t → proj₂ W y₀ ⊞ inc t δ) (proj₂ (D y₀ p₀))
    ; offA = λ W y₀ p₀ δ y _ ne → cong (λ t → proj₂ W y ⊞ t) (inc-off (proj₁ (D y₀ p₀) y) δ ne)
    ; monoA = λ W y₀ p₀ δ → C.self , (λ y → ⊞-fst (proj₂ W y) (inc (proj₁ (D y₀ p₀) y) δ))
    ; legalA = λ W y₀ p₀ δ l lW → proj₁ lW , (λ y → Lg-⊞ (proj₂ W y) (inc (proj₁ (D y₀ p₀) y) δ) (proj₂ lW y) (Lg-inc (proj₁ (D y₀ p₀) y) δ l)) }
```

外层界是有限高度 `finH k` 时, $x_0$ 之下的可入层号都是有限的, 所以有证书, `RaiseA` 是构造.

```agda
up-fin : ∀ {S : KS} n → up {S} (finH n) ≡ finH n
up-fin zero = refl
up-fin (suc n) = cong hs (up-fin n)

fin⊲ : ∀ {T : KS} {c : HB T} {w} k → c ⊲[ w ] finH k → Σ ℕ (λ j → c ≡ finH j)
fin⊲ zero hself = zero , refl
fin⊲ (suc k) hself = suc k , refl
fin⊲ (suc k) (hsuc p) = fin⊲ k p

adm-fin′ : ∀ {w : Wd S₁} {y₀ : HB S₁} {c : HB S₀} → Σ ℕ (λ j → c ≡ finH j) → hs y₀ ⊲[ w ] up c → Σ ℕ (λ n → y₀ ≡ finH n)
adm-fin′ {w} {y₀} (j , refl) q with fin⊲ j (subst (λ t → hs y₀ ⊲[ w ] t) (up-fin j) q)
... | zero , ()
... | suc m , e = m , cong unhs e

adm-fin : ∀ {a k y₀} → AdmL x₀ (a , finH k) y₀ → Σ ℕ (λ n → y₀ ≡ finH n)
adm-fin {k = k} (hLim e q) = adm-fin′ (fin⊲ k e) q

raiseA-fin : ∀ a k → RaiseA x₀ (a , finH k)
raiseA-fin a k = decAdm→raiseA (λ y₀ p₀ → subst DecAt (sym (proj₂ (adm-fin p₀))) (decAt-fin (proj₁ (adm-fin p₀))))

-- 非空: 外层界 2 之下, 层号 0 可入
adm-fin-ex : AdmL x₀ (azero , finH 2) hz
adm-fin-ex = hLim {c = finH 1} (hsuc hself) hself
```

## §6 字面层号的认同到外延为止 (条件)

`up ω₀` 与 `hl finH` (都在 `HB S₁` 里) 字面不同, 逐点相等 (`up-fin`). 有 `ℕ → HB S₁` 的外延时它们相等, 所以 `GW` 在两处的分量是同一个; 没有外延时, `GW` 是内涵层号上的函数, 两个分量各读各的. 这一条不是否定, 只说接口的认同 "按字面层号" 精确到哪里.

```agda
FE₁ : Set
FE₁ = ∀ (f g : ℕ → HB S₁) → (∀ n → f n ≡ g n) → f ≡ g

up-ω : FE₁ → up ω₀ ≡ hl finH
up-ω fe = cong hl (fe (λ n → up (finH n)) finH up-fin)
```
