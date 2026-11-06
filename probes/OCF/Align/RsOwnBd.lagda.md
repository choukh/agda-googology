# 积世界上的升界 (四): 带字面公共上界的升界, 对一切底拷贝

> 不含记号. 入口 [RsOwn](RsOwn.lagda.md), 接口 [RsOwnIf](RsOwnIf.lagda.md) §3 (`RsBd`), 工具 [RsOwnSh](RsOwnSh.lagda.md) (`rM`), 取大算子 [RaiseCBd](RaiseCBd.lagda.md) (`Rᵇ`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 世界的上界数据 `Up w`: 一个合法的 $\Lambda$, 每份底拷贝的界都 $\lhd\Lambda$. 回灌值的证据 `U b w u v`: $v$ (读成 `A`) $\lhd \Lambda$. 升界: **每份**底拷贝的界 $a$ 换成 `Rᵇ` $(a, v)$ (在公共上界 $\Lambda$ 之下取大). 这是 `RaiseCFba.upAllᵇ` (在 `SA` 上) 推广到一切带 `ShB` 的种类结构 (`Lev c`, `Kc s`, `KΛc`), 并接上 `RsBd` 的律:
>
> - `rsᵇ≤`: 无前提世界变大 (`Rᵇ-lo`); `rsᵇLg`; `rsᵇ-up`: 升后仍在 $\Lambda$ 之下 (`Rᵇ-Λ`).
> - `rsᵇ-top`: 旧顶 $\lhd v$ 时, 自己的顶恰为 $v$ (`Rᵇ-cases` 加反对称 `⊲-antisym`). 无前提时**不**成立 (那就是 `NegKindLvRaise.no-upAllR` 的 `rs-top`).
> - 值: 升后每份底拷贝 $\unrhd v$ 且 $\lhd \Lambda$ (`rsᵇ-hi`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwnBd where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; tpK)
open import OCF.Align.RaiseCBase using (⊲-antisym)
open import OCF.Align.RaiseCBd using (Rᵇ; Rᵇ-cases; Rᵇ-lo; Rᵇ-hi; Rᵇ-Λ; Rᵇ-lg)
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.NewTwrColl using (GΛ)
open import OCF.Align.RsOwnIf
open import OCF.Align.RsOwnSh
```

```agda
module BD {T : KS} {tp : TopG T} {w0 : Wd T} (Sh : ShB T tp w0) where
  Up : Wd T → Set
  Up w = Σ A (λ Λ → Lg Λ × Al Sh (λ x → x ⊲ Λ) w)

  U : ∀ {κ} → Bot Sh κ → (w : Wd T) → Up w → E T κ → Set
  U b w u v = toA Sh b v ⊲ proj₁ u

  module _ (κ : K T) (b : Bot Sh κ) where
    P : A → A → Set
    P Λ x = x ⊲ Λ

    φ : ∀ {Λ v} → v ⊲ Λ → Lg Λ → ∀ a → P Λ a → A
    φ q l a p = Rᵇ p q l

    upᵇ : (w : Wd T) (u : Up w) (v : E T κ) → U b w u v → Wd T
    upᵇ w (Λ , l , al) v q = rM Sh (φ q l) w al

    upᵇ≤ : ∀ {w u v} (q : U b w u v) → _≤w_ T w (upᵇ w u v q)
    upᵇ≤ {w} {Λ , l , al} q = rM-≤ Sh {P Λ} {φ q l} (λ a p → Rᵇ-lo p q l) al

    upLg : ∀ {w u v} (q : U b w u v) → LgW T w → LgE T κ v → LgW T (upᵇ w u v q)
    upLg {w} {Λ , l , al} q lw lv = rM-lg Sh {P Λ} {φ q l} (λ a p → Rᵇ-lg p q l) al lw

    upUp : ∀ {w u v} (q : U b w u v) → Up (upᵇ w u v q)
    upUp {w} {Λ , l , al} q = Λ , l , rM-al Sh {P Λ} {φ q l} {P Λ} (λ a p → Rᵇ-Λ p q l) al

    up-hi : ∀ {w u v} (q : U b w u v) → Al Sh (λ x → toA Sh b v ⊲ x) (upᵇ w u v q)
    up-hi {w} {Λ , l , al} {v} q = rM-al Sh {P Λ} {φ q l} {λ x → toA Sh b v ⊲ x} (λ a p → Rᵇ-hi p q l) al

    -- 取大在旧顶 ⊲ v 时就是 v
    pick-v : ∀ {a v Λ} (p : a ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) → a ⊲ v → Rᵇ p q l ≡ v
    pick-v p q l av with Rᵇ-cases p q l
    ... | inj₁ (e , va) = trans e (⊲-antisym av va)
    ... | inj₂ (e , _) = e

    upTop : ∀ {w u v} (q : U b w u v) → Pr T κ w (top tp κ w) v → top tp κ (upᵇ w u v q) ≡ v
    upTop {w} {Λ , l , al} {v} q pr =
      trans (sym (fr-to Sh b _))
        (trans (cong (frA Sh b) (trans (rM-tp Sh b {P Λ} {φ q l} al) (pick-v (tp-al Sh b al) q l (prA Sh b pr))))
               (fr-to Sh b v))

    rsBd : RsBd T tp κ Up (U b)
    rsBd = record { rsᵇ = upᵇ ; rsᵇ≤ = upᵇ≤ ; rsᵇLg = upLg ; rsᵇ-top = upTop ; rsᵇ-up = upUp }
```

在极限站 `KΛc` 上 (含一切站的读回分量里含函数下标的底拷贝):

```agda
rsBdΛ : ∀ κ (b : Bot shΛ κ) → RsBd KΛc (tpK GΛ) κ (BD.Up shΛ) (BD.U shΛ b)
rsBdΛ κ b = BD.rsBd shΛ κ b
```

## 结论 (按档)

- **[构造]** `BD.rsBd`: 对任一带 `ShB` 的种类结构的每个底拷贝, `RsBd` 的五条律成立; `rsBdΛ` 是 `KΛc` 的实例. 不判定下标.
- **[定理]** `up-hi` (升后每份底拷贝含 $v$), `upUp` (仍在 $\Lambda$ 之下), `pick-v`.
- **[判断]** 与 `RaiseC.no-bounded-raise` 的关系: 那里否定的是 "$v$ 不在世界的公共上界之下" 时保上界; 这里 $v\lhd\Lambda$ 是前提 (`U`). 所以 `RsBd` 要折叠在回灌时给出 $v\lhd\Lambda$ 的证据; `KindLvRun` 的回灌值 $v=\mathrm{sum}(\mathrm{top},\Delta)$ 没有这样的上界 (判断, 未检查到有), 本路的闭项 (`RsOwnTm`) 不用 `RsBd`, 用的是 `RsInv` (`RsOwnSW`).
