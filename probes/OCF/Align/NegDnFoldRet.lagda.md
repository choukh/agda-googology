# 有内容的下降, 否定一路 (一): 可取回的下降不存在 (`no-retract`), 它比接口的忠实强

> 不含记号. 入口 [NegDnFold](NegDnFold.lagda.md). 对着接口 [DnFoldIf](DnFoldIf.lagda.md) ("接口定稿 2026-11-05 16:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 嫌疑 (iv): "下降忠实" 与 `HtTowerNeg.no-retract` 的关系. 接口的忠实 `FaithRd T d` 只要求下降**区分两个读回** (`rdTop T` 与截断 `rdCut T`). 更强的读法是**可取回**: 有 $r : \mathrm{Ht}\to$ `HB S` 使 $r\circ d=\mathrm{id}$ (从下降后的 `Ht` 取回读回). 本篇:
>
> 1. **可取回的下降不存在, 只要级里有一个坐标是 `Ht` 的种类 (定理, `no-faithful`).** 种类 $\kappa$ 的坐标类型 `E S κ ≡ Ht` 时, 任何 $d$ 都没有左逆: 否则 $d$ (经等式搬运) 与 $r$ 给出种类 $\kappa$ 的坐标装下全部高度的收缩, 撞 `no-retract`. 与下降怎么写 (D1 求值, D2 有损, 别的) 无关.
> 2. **塔上每一站 $s\ge1$ 的级都有这样的种类 (定理, `twB`, `no-faithfulB`).** 对**一切** `DnTower`, `DnLim`, 一切 $s$: `Lev (B (s+1))` 有坐标是 `Ht` 的种类 (第 1 站是坐标 $y=1$ 那一支的 `Lev 2` 的新种类, 以后沿 `emb` 与 `⊞` 传下去). 所以第 $s+1$ 站的下降 (接口 `FaithTower` 说的那一个) 一律不可取回.
> 3. **可取回推出接口的忠实 (定理, `ret→faith`), 反过来不成立 (见 [NegDnFoldBlind](NegDnFoldBlind.lagda.md)).** `rdTop T ≢ rdCut T` (`top≢cut`). 所以 `FaithRd` 是严格更弱的读法 (第 2 篇给出满足 `FaithRd` 而输出只有有限高度的下降, 定理).
> 4. **对照: 第 0 站可取回 (定理, `ret0`).** `Lev (hs hz) = S₁`, 恒等就是可取回的下降. 所以 `no-faithful` 的前提不是空的条件, 墙从第 1 站开始.
>
> **只否定什么.** 只否定 "下降有左逆" (读回可以从下降后的 `Ht` 原样取回), 在一切含坐标为 `Ht` 的种类的级上, 特别是塔上一切 $s\ge1$ 的第 $s+1$ 站. **不否定** 接口的任何记录, 不否定 `FaithRd`/`FaithTower` (有实例, 第 2 篇), 不否定有损的或经求值的下降本身.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegDnFoldRet where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; Ht)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.LvKtIf
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTop using (top)
open import OCF.Align.KcFoldTower using (module KD)
open import OCF.Align.DnFoldIf
```

## §1 坐标是 `Ht` 的种类挡住左逆

```agda
HasHt : KS → Set₁
HasHt S = Σ (K S) (λ κ → E S κ ≡ Ht)

subst-ss : ∀ {X Y : Set} (e : X ≡ Y) (y : Y) → subst (λ Z → Z) e (subst (λ Z → Z) (sym e) y) ≡ y
subst-ss refl y = refl

no-faithful : ∀ {S : KS} → HasHt S → (d : HB S → Ht) (r : Ht → HB S) → ¬ (∀ x → r (d x) ≡ x)
no-faithful {S} (κ , eq) d r rd =
  no-retract {S = S} κ (λ x → subst (λ Z → Z) (sym eq) (d x)) (λ c → r (subst (λ Z → Z) eq c))
    (λ x → trans (cong r (subst-ss eq (d x))) (rd x))
```

## §2 塔上每一站 $s\ge1$ 的级里都有这样的种类

`Tw c`: 沿构造子的一条路走到字面的 `hs (hs hz)` (第 2 级, 它的新种类坐标是 `HB S₁ = Ht`). `Tw` 经 `step`, `sup` 传给 `Lev`, 经 `⊞` 的左边, `ι` 保持.

```agda
hasStep : ∀ {S} → HasHt S → HasHt (step S)
hasStep (κ , eq) = inj₁ κ , eq

hasSup : ∀ {I : Set} {F : I → KS} (i : I) → HasHt (F i) → HasHt (sup I F)
hasSup i (κ , eq) = (i , κ) , eq

data Tw {𝕂 : KS} : HB 𝕂 → Set where
  t2 : Tw (hs (hs hz))
  ts : ∀ {c} → Tw c → Tw (hs c)
  tl : ∀ {f} n → Tw (f n) → Tw (hl f)
  tΩ : ∀ {κ g} x → Tw (g x) → Tw (hΩ κ g)

hasTw : ∀ {𝕂 : KS} {c : HB 𝕂} → Tw c → HasHt (Lev c)
hasTw t2 = inj₂ tt , refl
hasTw (ts t) = hasStep (hasTw t)
hasTw (tl {f} n t) = hasSup {ℕ} {λ m → Lev (f m)} n (hasTw t)
hasTw {𝕂} (tΩ {κ} {g} x t) = hasSup {E 𝕂 κ} {λ c → Lev (g c)} x (hasTw t)

tw⊞ : ∀ {𝕂 : KS} {a : HB 𝕂} → Tw a → ∀ b → Tw (a ⊞ b)
tw⊞ t hz = t
tw⊞ t (hs b) = ts (tw⊞ t b)
tw⊞ t (hl f) = tl 0 (tw⊞ t (f 0))
tw⊞ {𝕂} t (hΩ κ g) = tΩ (bot 𝕂 κ) (tw⊞ t (g (bot 𝕂 κ)))

twι : ∀ {I : Set} {F : I → KS} (i : I) {x : HB (F i)} → Tw x → Tw (ι {I} {F} i x)
twι i t2 = t2
twι i (ts t) = ts (twι i t)
twι i (tl n t) = tl n (twι i t)
twι i (tΩ x t) = tΩ x (twι i t)

module TwB (dn : DnTower) (dnL : DnLim) where
  open KD dn dnL

  -- 第 1 站: 层号头的 Ω-结点在坐标 y = 1 处的那一支是字面的 2
  twB : ∀ s → Tw (B (suc s))
  twB zero = ts (tΩ (hs hz) t2)
  twB (suc s) = ts (tw⊞ (twι {⊤ ⊎ HB (Kc (suc s))} {FN (Kc (suc s))} (inj₁ tt) (twB s)) (injL (B (suc s)) (top (B (suc s)))))

  hasB : ∀ s → HasHt (Lev (B (suc s)))
  hasB s = hasTw (twB s)

  -- FaithTower 说的那一个下降: 一律不可取回
  no-faithfulB : ∀ s (r : Ht → HB (Lev (B (suc s)))) →
    ¬ (∀ x → r (proj₁ (dn (suc s) (B (suc s)) (lB (suc s))) x) ≡ x)
  no-faithfulB s r = no-faithful (hasB s) _ r
```

## §3 可取回推出接口的忠实

```agda
br : ∀ {T : KS} → HB (step T) → HB T → HB (step T)
br (hs (hΩ (inj₂ tt) g)) y = g y
br _ y = hz

top≢cut : ∀ (T : KS) → ¬ (rdTop T ≡ rdCut T)
top≢cut T eq with cong (λ t → br t (hs hz)) eq
... | ()

ret→faith : ∀ (T : KS) (d : HB (step T) → Ht) (r : Ht → HB (step T)) → (∀ x → r (d x) ≡ x) → FaithRd T d
ret→faith T d r rd e = top≢cut T (trans (sym (rd (rdTop T))) (trans (cong r e) (rd (rdCut T))))
```

## §4 对照: 第 0 站可取回

第 0 站层号 `hs hz`, 级 `Lev (hs hz) = step S₀ = S₁`, 高度类型就是 `Ht`.

```agda
ret0 : Σ (HB (Lev {S₀} (hs hz)) → Ht) (λ d → Σ (Ht → HB (Lev {S₀} (hs hz))) (λ r → ∀ x → r (d x) ≡ x))
ret0 = (λ x → x) , (λ x → x) , (λ x → refl)
```

## §5 结论 (按档)

- **[定理]** `no-faithful`: 级 `S` 有坐标类型为 `Ht` 的种类时, 任何 `HB S → Ht` 都没有左逆.
- **[定理]** `TwB.twB`, `TwB.hasB`, **`TwB.no-faithfulB`**: 对一切 `DnTower`, `DnLim`, 一切 $s$, 第 $s+1$ 站在层号 `B (s+1)` 上的下降没有左逆.
- **[定理]** `top≢cut`, `ret→faith`: 可取回推出 `FaithRd`. 反方向的否定见 `NegDnFoldBlind.cheapFaith` (满足 `FaithRd` 的下降, 输出只有 $0,1,2,\dots$ 形的有限高度; 有限高度没有左逆的余地).
- **[定理]** `ret0`: 第 0 站可取回 (前提的对照).
- 为什么构造一路需要: 接口文件头 "忠实: 下降区分读回 `rdTop T` 与截断 `rdCut T`", 嫌疑 (iv) 问它与 `no-retract` 的关系. 若把 "让读回进入闭项" 读成 "闭项里能取回读回", 就是这里的左逆; 本篇说它在第 1 站起不可能, 接口选的较弱读法 (只区分两个读回) 不撞 `no-retract`.
