# NegRaise (四): 一般下标 $c_0$ 上的 `FBA SA (c₀ , tt)` (读第 $c_0$ 个分量)

> 不含记号. 入口 [NegRaise](NegRaise.lagda.md). 对象是构造一路的积世界 `RaiseCFba.SA` (世界 `A → A`, 种类 $(c_0,\mathrm{tt})$ 的界是第 $c_0$ 个分量), 导入它与 `GenFoldIf.FBA`, 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 主审转告的问题: 不限 `upAll` 形状, 一般 $c_0$ 上的 `FBA SA (c₀ , tt)` (`tpA` 读第 $c_0$ 个分量) 能不能否定. 本篇的结果:
>
> 1. **`fbaDec` (构造, 无条件).** 若 "下标等于 $c_0$" 可判定 (`DecAt c₀`), 就有 `tpA` 读第 $c_0$ 个分量的 `FBA SA (c₀ , tt)`: 点更新. 有限数 $c_0$ (`fbaFin k`) 是实例; 它推广了构造一路的 `fba₀` ($c_0=0$).
> 2. **`fba-up`, `Fsuc`, `fba-suc` (盲).** 读第 $c_0$ 个分量的 `FBA` 对 `rsA` 的输出向上封闭: 每个分量再包一层合法的东西 (例如后继) 仍是这样的 `FBA`. 与 `RaiseA` 一样, `FBA` 的律都是下界 (`rs≤` 的结论, `tp-rs`), 不含 "留" 那样的上界.
> 3. **判断 (未编译): 一般 $c_0$ 上的否定未走通.** `NegGenFoldUpd.upd₁-sep` 用的可判定观察来自 "留" (新世界里的界蕴含旧世界里的界, 上界); `FBA` 没有这条律. 在 $c_0=\omega$ 处, 点更新的做法要 `DecAt ω`, 而 `NegRaiseFin.deqω→WLPO` (条件 `FEA`) 说那是 WLPO; 这只否定 "用判定相等做点更新" 这一种做法, 不否定 `FBA SA (ω , tt)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaiseFba where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (FBA; tpA; rsA; rs≤; rsLg; tp-rs)
open import OCF.Align.RaiseCFba using (SA)
open import OCF.Align.NegRaiseFin using (DecAt; nat; nat-deq)
```

## §1 可判定的下标上点更新

```agda
module PtDec (c₀ : A) (deq : DecAt c₀) where
  upd : (A → A) → A → (c : A) → Dec (c ≡ c₀) → A
  upd w v c (yes _) = v
  upd w v c (no _) = w c

  rsP : (A → A) → A → (A → A)
  rsP w v c = upd w v c (deq c)

  rsP≤ : ∀ {w v} → w c₀ ⊲ v → ∀ c → w c ⊲ rsP w v c
  rsP≤ {w} {v} p c with deq c
  ... | yes e = subst (λ x → w x ⊲ v) (sym e) p
  ... | no _ = C.self

  rsPLg : ∀ {w v} → (∀ c → Lg (w c)) → Lg v → ∀ c → Lg (rsP w v c)
  rsPLg lw lv c with deq c
  ... | yes _ = lv
  ... | no _ = lw c

  rsP-at : ∀ {w v} → v ⊲ rsP w v c₀
  rsP-at with deq c₀
  ... | yes _ = C.self
  ... | no ne = ⊥-elim (ne refl)

fbaDec : ∀ c₀ → DecAt c₀ → FBA SA (c₀ , tt)
fbaDec c₀ deq = record
  { tpA = λ w → w c₀
  ; rsA = rsP
  ; rs≤ = rsP≤
  ; rsLg = rsPLg
  ; tp-rs = rsP-at }
  where open PtDec c₀ deq

fbaDec-tp : ∀ c₀ deq (w : A → A) → tpA (fbaDec c₀ deq) w ≡ w c₀
fbaDec-tp c₀ deq w = refl

fbaFin : ∀ k → FBA SA (nat k , tt)
fbaFin k = fbaDec (nat k) (nat-deq k)
```

## §2 盲: 读第 $c_0$ 个分量的 `FBA` 对输出向上封闭

```agda
module Up (c₀ : A) (F : FBA SA (c₀ , tt)) (tpEq : ∀ w → tpA F w ≡ w c₀) where
  fba-up : (rs′ : (A → A) → A → (A → A)) →
    (∀ {w v} c → rsA F w v c ⊲ rs′ w v c) →
    (∀ {w v} → (∀ c → Lg (w c)) → Lg v → ∀ c → Lg (rs′ w v c)) →
    Σ (FBA SA (c₀ , tt)) (λ F′ → ∀ w → tpA F′ w ≡ w c₀)
  fba-up rs′ up lg = record
    { tpA = λ w → w c₀
    ; rsA = rs′
    ; rs≤ = λ {w} {v} p c → ⊲-tr (rs≤ F (subst (_⊲ v) (sym (tpEq w)) p) c) (up c)
    ; rsLg = lg
    ; tp-rs = λ {w} {v} → ⊲-tr (subst (v ⊲_) (tpEq (rsA F w v)) (tp-rs F)) (up c₀) } , λ w → refl

  -- 每个分量外包后继
  Fsuc : Σ (FBA SA (c₀ , tt)) (λ F′ → ∀ w → tpA F′ w ≡ w c₀)
  Fsuc = fba-up (λ w v c → asuc (rsA F w v c)) (λ c → C.suc C.self) (λ lw lv c → rsLg F lw lv c)

  fba-suc : ∀ w v c → rsA (proj₁ Fsuc) w v c ≡ asuc (rsA F w v c)
  fba-suc w v c = refl
```

## §3 结论 (按档)

- **[定理, 构造]** `fbaDec` (前提 `DecAt c₀`), `fbaFin` (有限数下标, 无条件), `fbaDec-tp` (`refl`: `tpA` 读第 $c_0$ 个分量).
- **[定理, 盲]** `Up.fba-up`, `Up.Fsuc`, `Up.fba-suc`.
- **[判断]** 一般 $c_0$ (例如 $\omega$) 上读第 $c_0$ 个分量的 `FBA SA (c₀ , tt)`: 未构造, 未否定. 与 `RaiseA` 同一个缺口: 律只给下界, 我没有找到能泄露 "$c\equiv c_0$" 的可判定观察.
