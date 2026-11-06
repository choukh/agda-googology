# 站以 ℕ 为下标, 层由 `LH` 一次封闭: 每站头种类精确回灌的闭项

> 不含记号. Fable 5.1, 2026-11-05 (第二轮自选). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数. 不改任何已有文件; 配对否定在 [Fab2SLsNeg](Fab2SLsNeg.lagda.md).
>
> **这一篇做什么.** 上一轮 [FabLFReGen](FabLFReGen.lagda.md) 把 ψ₀Λ 候选闭项放在一次封闭的 `SL = sup LH FL` 上, 剩下 C6: `SL` 的世界以层号 `LH` 为下标, 第 $n\ge2$ 站的层号含函数分支, "恰好升这一站" 要对含函数的层号判等 (分离子). 同一天 [StratTw](StratTw.lagda.md) 用分层塔 (普通 ℕ 递归, 带拷贝、嵌入、同形证据) 让每站头种类都按级回灌 (`all-heads`), 墙移到每站级里的深种类 (`deep-lossy`, `updD-sep`). 本篇指出: **把 "站" 与 "层" 分开, 两件事各取现成的解.** 站以 ℕ 为下标 (`SLs = sup ℕ (FL ∘ st)`, `st n` 是 `SL` 里第 $n$ 站的层号 `ofHB (tw n)`), 所以每站头种类 `νS n` 的界用 ℕ 上的点更新精确升高 (`setH`: 升这一份 `setH-top`, 留别份 `setH-keep`, 都是定理, 对**一切** $n$, 不带证据, 不分层, 不判定层号); 层仍由 `LH` 的一次封闭给出 (`Lv (st n)`), 所以每站头种类的坐标类型字面就是该站的层的值 (`coord-stage`, `refl`), 不要拷贝与同形证据. 折叠取 [KindLvRun](KindLvRun.lagda.md) (按级回灌的一般折叠, 只查 `LvFb`), 坍缩取 [KindLvTw](KindLvTw.lagda.md) 的 `ColL`, 得无条件闭项 `TΛs` (§5), 其中**每一站**的头种类都走级回灌 (`all-heads`, `refl`), 深种类有损 (`deep-lossy`, `refl`). `all-heads` 说的是表 `lvS`; 折叠在第 0 层目标下遇到种类 `inj₁ (νS n)` 的闭包结点时调用 `KH n` 是 `KindLvRun.RKv` 的定义, 这些结点来自每一站的头 (`tws (suc n)` 字面是 `hΩ (νS n) …`); "读回进了闭项" 的形状定理 (同 StratTw 的 `head-fed` 那一档) 本篇没有写.
>
> **行数 (切片, 近似).** 脚本 `Survey/scripts/fab2/locslice_fab2.py`, 口径同 `strattw/locslice_strattw.py`: 层 1 487 / 层 2 1309 / 层 3 **1346** / 层 4 1366, 记号 0; 前 3 层闭包无 `GenFoldRun` 块. 其中 `KindLvRd` 93, `KindLvEmb` 45, `LvKtIf` 10, `NewTwrColl` 2 是切片器的假象 (`ColL` 所在文件 `KindLvTw` 的模块级导入被整体算进根), 闭项不用它们; 去掉后约 1196 (判断). 对照: `TS` 1453, `TK` 1479, `TΛ` 1042, `TN` 1268.
>
> **读回是可数的 (如实).** 级回灌要一个读回 `rd : DK ℓ W → E κ → E κ` (级层数据读进坐标). [KindLvRd](KindLvRd.lagda.md) 的 `readL` 读进 `HB (Lev c)` (`HtTowerTy.Lev`), 而这里的坐标是 `HB (Lv (st n))` (`LFReTy.Lv`), 两者在底 (`S₀` 对 `S⊥`) 与 $\Omega$-极限处 (`Lev` 的 `sup (E κ)` 对 `Lv` 的 `sup (⊤ ⊎ HB (Lv k))`) 不同, `readL` 用不上. 本篇的读回 `rdC` 把级层数据压成第 0 层数据 (`flat`: `ni`, `nc` 结点各记 $1$), `sum` 成 `A`, 嵌入成高度接在旧界后面: $\mathrm{rd}(b, x) = b \boxplus \mathrm{emb}(\mathrm{sum}\,0\,(\mathrm{flat}\,x))$. 它不是常数 (`rdC-one`: 数据 `n1` 读成 `hs b`), 但增量没有 $\Omega$-结点 (`rdC-form`, `refl`): 头种类的界只按可数的量升高. 要让界带 $\Omega$-结点升高, 要对 `Lv` 写级读回 (接手清单第 1 条); 本篇的类型事实与升界定理与读回无关.
>
> **值 (判断).** 没有 `ord` 定理. 读法: 每站头种类的界沿可数增量攀升, 深种类有损, 与 `TS` (StratTw), `TK`, `TN`, `TΛ` 同在 ψ₀(Ω_2) 与 ψ₀(Ω_Ω) 之间 (判断, 同 ValTK 的口径); 本篇不提高强度. 它做的是把 C6 的两半分开: **站的那一半是下标类型的事, 下标换成 ℕ 就没有 (定理 `setH-top`, `setH-keep`); 层的那一半 (每站级里以坐标为下标的深种类) 仍在**, 否定一路把它在 `Lv (st 2)` 上写成分离子定理 (`Fab2SLsNeg.updD₂-sep`).
>
> **翻译账.** 没有新结点, 没有新接口, 没有新字段. 用到的都是树侧已有的定义: `LH`/`Lv` (`LFReTy`), `tw` (`LFReTower`), `sup`/`step`/`up`/`ι`/`⊞` (`HtTowerTy`), `upd` (`GenFoldInst`), `KLv`/`LvFb` (`KindLvIf`), `ColL` (`KindLvTw`). 摆脱侧: 与 StratTw 比, 去掉分层 (`solFin`/`strat`)、拷贝、嵌入、同形证据; 与 FabLFReGen 比, 去掉以 `LH` 为下标的世界. `Lv` 的形状记为记号引导 (`LFReTy` 自述); 塔 `tws` 的形状 ($t_{n+1}=\sup_{c<\Omega_{t_n+1}}(t_n\boxplus c)$, 即 $\Omega_{t_n+1}$) 由种类 `νS n` 的坐标类型逼出, 与 `LFReTower.Ω̂` 的连续版 ($\Omega_{t_n}$) 不同, 上确界相同 (判断, 纸面序数算术).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab2SLs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree; topStepG)
open import OCF.Align.GenFoldInst using (ldStep; topSupG; ldSup; upd; upd-R; upd-Q; upd-at)
open import OCF.Align.LFReTy using (LH; Lv; FL; S⊥; ofHB)
open import OCF.Align.LFReTower using (tw)
open import OCF.Align.FabLFReGen using (topLv; ldLv; w₀Lv; lw₀Lv; frE⊥; frE⊥-⊲; frE⊥-lg)
open import OCF.Align.KindLvIf using (KLv; LvFb)
open import OCF.Align.KindLvTw using (module ColL)
```

## §1 站与层: `SLs`, 塔, 对角

`st n` 是 `SL` 里第 $n$ 站的层号 (`ofHB (tw n)`: `lz`, `ls lz`, `lΩ lz …`, …); `FS n = step (Lv (st n))` 是第 $n$ 站的种类结构, 新种类 `νS n` 的坐标是第 `st n` 层的值 `HB (Lv (st n))`. `SLs` 把各站并起来, 下标是 ℕ.

```agda
st : ℕ → LH
st n = ofHB (tw n)

FS : ℕ → KS
FS n = FL (st n)

SLs : KS
SLs = sup ℕ FS

ιS : ∀ n → HB (FS n) → HB SLs
ιS n = ι {ℕ} {FS} n

νS : ℕ → K SLs
νS n = n , inj₂ tt
```

塔: $t_0=0$, $t_{n+1}=\sup_c(t_n\boxplus c)$, $c$ 过第 $n$ 站的层的值 (坐标经 `up` 放进第 $n$ 站, 再经 `ιS n` 进 `SLs`). 相邻项是第一位置 (坐标取 `bot`, 对一切世界), 合法是一步定理 (与 `LFReTower.Lg-Ω̂` 的后继行同一个证明).

```agda
tws : ℕ → HB SLs
tws zero = hz
tws (suc n) = hΩ (νS n) (λ c → tws n ⊞ ιS n (up c))

tws-st : ∀ {W} n → tws n ⊲[ W ] tws (suc n)
tws-st {W} n = hLim (botBd SLs (νS n) W) (⊞-fst (tws n) hz)

Lg-tws : ∀ n → LgB (tws n)
Lg-tws zero = tt
Lg-tws (suc n) =
  (λ {W} lw e e′ p → ⊞-⊲ (tws n) (ι-⊲ {ℕ} {FS} {n} {w = W} (up-⊲ p))) ,
  (λ c lc → Lg-⊞ (tws n) (ιS n (up c)) (Lg-tws n) (Lg-ι n (up c) (Lg-up c lc)))
```

对角前接 $1$ (坍缩要 $1$ 是最终层的字面第一位置, 对一切世界; `tws 1` 的 $1$ 那一支要世界的界, 所以不用它), 最终层 `ΛS = up Λs`.

```agda
Λs : HB SLs
Λs = hl (λ n → hs hz ⊞ tws n)

Lg-Λs : LgB Λs
Lg-Λs = (λ n → ⊞-⊲ (hs hz) (tws-st n)) , (λ n → Lg-⊞ (hs hz) (tws n) tt (Lg-tws n))

ΛS : HB (step SLs)
ΛS = up Λs

lΛS : LgB ΛS
lΛS = Lg-up Λs Lg-Λs

oneS : ∀ {w} → hs hz ⊲[ w ] ΛS
oneS = hlim 0 hself
```

**类型事实 (定理).** 第 $n$ 站的级层 `up (1 ⊞ tws n)` 是最终层的字面第一位置, 对一切世界; 第 $n$ 站头种类的坐标类型字面就是第 `st n` 层的值. 这两条是 `KindLvTw` 文件头说要互递归才能同时满足的, 这里与 `FabLFReGen.stage-fst`/`coord-stage` 一样是一行; 而且 (与那里不同) 这一站的界可以精确升高 (§3).

```agda
stage-fst : ∀ n {w : Wd (step SLs)} → up (hs hz ⊞ tws n) ⊲[ w ] ΛS
stage-fst n = hlim n hself

coord-stage : ∀ n → E SLs (νS n) ≡ HB (Lv (st n))
coord-stage n = refl
```

## §2 `GenK SLs`: 顶坐标, 基世界, 底种类, 向下封闭

每站用 [FabLFReGen](FabLFReGen.lagda.md) 对 `Lv k` 写好的 `topLv`, `ldLv`, `w₀Lv`, `lw₀Lv`. 底种类是第 0 站的新种类 (坐标 `HB S⊥`, 读成 `A` 是 `frE⊥`). A-回灌一律 `inj₂ tt`: 头种类走 §4 的级回灌, 不走 A-回灌.

```agda
GS : GenK SLs
GS = record
  { tpK = topSupG ℕ FS (λ n → topStepG (topLv (st n)))
  ; w₀ = λ n → w₀Lv (st n) , hz
  ; lw₀ = λ n → lw₀Lv (st n) , tt
  ; aK = νS 0
  ; frE = frE⊥
  ; frE-lg = λ {e} le → frE⊥-lg e le
  ; frE-mono = λ lw e e′ p → frE⊥-⊲ p
  ; fbA = λ _ → inj₂ tt }

LdS : LgDn SLs
LdS = ldSup ℕ FS (λ n → ldStep (ldLv (st n)))

flS : FbLg GS
flS κ = tt

tpS : TopG SLs
tpS = tpK GS

-- 头种类的顶坐标就是该站世界的第二分量
top-head : ∀ n (w : Wd SLs) → top tpS (νS n) w ≡ proj₂ (w n)
top-head n w = refl
```

## §3 每站头种类的精确升界: ℕ 上的点更新

`setH n w v`: 把第 $n$ 站世界的第二分量换成 $v$, 别的站不动. 三条律 (`KindLvIf.KLv` 的 `rs≤`, `rsLg`, `rs-top`) 对一切 $n$; 加上 "留别份" (`setH-keep`): 这正是 [NegGenFoldUpd](NegGenFoldUpd.lagda.md) 的 `PtUpd` (升 + 留), 在 ℕ 下标上两半同时成立 (那里的 `upd∘`), 在坐标下标上推出分离子 (那里的 `upd₁-sep`, 这里的 `Fab2SLsNeg.updD₂-sep`).

```agda
WS : Set
WS = Wd SLs

setH : ∀ n → WS → HB (Lv (st n)) → WS
setH n w v = upd {λ m → Wd (FS m)} w n (proj₁ (w n) , v)

setH≤ : ∀ n (w : WS) v → proj₂ (w n) ⊲[ proj₁ (w n) ] v → _≤w_ SLs w (setH n w v)
setH≤ n w v p =
  upd-R {λ m → Wd (FS m)} (λ m → _≤w_ (FS m)) w n (proj₁ (w n) , v) (λ m → ≤w-rf (FS m)) (≤w-rf (Lv (st n)) , p)

setHLg : ∀ n (w : WS) v → LgW SLs w → LgB v → LgW SLs (setH n w v)
setHLg n w v lw lv =
  upd-Q {λ m → Wd (FS m)} (λ m → LgW (FS m)) w n (proj₁ (w n) , v) lw (proj₁ (lw n) , lv)

-- 升这一份: 升后第 n 站头种类的顶坐标恰是 v
setH-top : ∀ n (w : WS) v → top tpS (νS n) (setH n w v) ≡ v
setH-top n w v = upd-at {λ m → Wd (FS m)} w n (proj₁ (w n) , v) (λ y → proj₂ y ≡ v) refl

-- 留别份: 别的站的世界原样
upd-keep : ∀ {P : ℕ → Set} (w : (m : ℕ) → P m) n (x : P n) m → ¬ (n ≡ m) → upd {P} w n x m ≡ w m
upd-keep w zero x zero ne = ⊥-elim (ne refl)
upd-keep w zero x (suc m) ne = refl
upd-keep w (suc n) x zero ne = refl
upd-keep {P} w (suc n) x (suc m) ne =
  upd-keep {λ k → P (suc k)} (λ k → w (suc k)) n x m (λ e → ne (cong suc e))

setH-keep : ∀ n (w : WS) v m → ¬ (n ≡ m) → setH n w v m ≡ w m
setH-keep n w v m ne = upd-keep {λ m → Wd (FS m)} w n (proj₁ (w n) , v) m ne
```

## §4 可数读回与每站的级回灌

```agda
open Tree SLs using (D; D₀; sum; Lg-sum)

-- 级层数据压成第 0 层数据: ni, nc 结点各记 1
flat : ∀ {L W} → D L W → D₀ W
flat n0 = n0
flat n1 = n1
flat (x ⨾ y) = flat x ⨾ flat y
flat (nl d) = nl (λ n → flat (d n))
flat (ni r u) = n1
flat (nc κ z u) = n1
flat (nw p x) = nw p (flat x)

-- A 嵌入任一种类结构的高度 (没有 Ω-结点), 保第一位置与合法
embA : ∀ {S : KS} → A → HB S
embA azero = hz
embA (asuc a) = hs (embA a)
embA (alim f) = hl (λ n → embA (f n))

embA-⊲ : ∀ {S : KS} {w : Wd S} {a b} → a ⊲ b → embA {S} a ⊲[ w ] embA b
embA-⊲ C.self = hself
embA-⊲ (C.suc p) = hsuc (embA-⊲ p)
embA-⊲ (C.lim n p) = hlim n (embA-⊲ p)

Lg-embA : ∀ {S : KS} a → Lg a → LgB (embA {S} a)
Lg-embA azero l = tt
Lg-embA (asuc a) l = Lg-embA a l
Lg-embA (alim f) (st , l) = (λ n → embA-⊲ (st n)) , (λ n → Lg-embA (f n) (l n))

-- 第 n 站的读回: 旧界接上数据的可数读数
rdC : ∀ n {W} → LgW (step SLs) W → HB (Lv (st n)) → D (up (hs hz ⊞ tws n)) W → HB (Lv (st n))
rdC n lW b x = b ⊞ embA (sum azero (flat x))

rdC-lg : ∀ n {W} (lW : LgW (step SLs) W) b x → LgB b → LgB (rdC n lW b x)
rdC-lg n lW b x lb = Lg-⊞ b _ lb (Lg-embA _ (Lg-sum azero (flat x) tt))

KH : ∀ n → KLv SLs tpS ΛS (νS n)
KH n = record
  { ℓ = up (hs hz ⊞ tws n)
  ; ℓ⊲ = λ {w} → stage-fst n {w}
  ; rd = λ {W} lW b x → rdC n lW b x
  ; rd-fst = λ lW b x → ⊞-fst b _
  ; rd-lg = λ lW b x lb → rdC-lg n lW b x lb
  ; rs = λ w v → setH n w v
  ; rs≤ = λ {w} {v} p → setH≤ n w v p
  ; rsLg = λ {w} {v} lw lv → setHLg n w v lw lv
  ; rs-top = λ {w} {v} → setH-top n w v }

lvS : LvFb SLs tpS ΛS
lvS (n , inj₂ _) = inj₁ (KH n)
lvS (n , inj₁ _) = inj₂ tt
```

**读回的形状 (定理).** 不是常数; 增量是 `A` 的嵌入, 没有 $\Omega$-结点.

```agda
rdC-one : ∀ n {W} (lW : LgW (step SLs) W) b → rdC n lW b n1 ≡ hs b
rdC-one n lW b = refl

rdC-form : ∀ n {W} (lW : LgW (step SLs) W) b x → rdC n lW b x ≡ b ⊞ embA (sum azero (flat x))
rdC-form n lW b x = refl
```

## §5 无条件闭项

```agda
module CS = ColL GS LdS flS ΛS lΛS oneS lvS

TΛs : A
TΛs = CS.Tψ

Lg-TΛs : Lg TΛs
Lg-TΛs = CS.Lg-Tψ

ordS : A → FLv.Ordᶜ FLv.zero
ordS azero = FLv.zero
ordS (asuc a) = FLv.suc (ordS a)
ordS (alim f) = FLv.lim (λ n → ordS (f n))

fghΛs : ℕ → ℕ
fghΛs = FLv.FGH (ordS TΛs)
```

**每站头种类都走级回灌; 深种类有损 (定理, `refl`).** 与 `StratTw.all-heads` 同一陈述, 这里不分层.

```agda
all-heads : ∀ n → lvS (νS n) ≡ inj₁ (KH n)
all-heads n = refl

deep-lossy : ∀ n (κ : K (Lv (st n))) → lvS (n , inj₁ κ) ≡ inj₂ tt
deep-lossy n κ = refl
```

## 结论 (按档)

- **[定理]** `SLs`, `tws`, `tws-st`, `Lg-tws`, `Λs`, `Lg-Λs`, `ΛS`, `lΛS`, `oneS`; `stage-fst`, `coord-stage`; `GS`, `LdS`, `flS`, `top-head`; 对一切 $n$ 的精确升界 `setH` 与 `setH≤`, `setHLg`, `setH-top` (升这一份), `setH-keep` (留别份); `flat`, `embA`, `embA-⊲`, `Lg-embA`, `rdC`, `rdC-lg`, `rdC-one`, `rdC-form`; 每站的级回灌 `KH n`, `lvS`; 闭项 `TΛs`, 证书 `Lg-TΛs`, FGH `fghΛs`; `all-heads`, `deep-lossy`.
- **[判断]** 读法在 ψ₀(Ω_2) 与 ψ₀(Ω_Ω) 之间, 与 `TS`, `TK`, `TN`, `TΛ` 同档; 没有 `ord` 定理. $\sup_n t_n$ 与 `LFReTower.Λ` 的值相同是纸面序数算术.
- **翻译账.** 无新结点, 无新接口, 无新字段; 摆脱侧去掉分层、拷贝、嵌入、同形证据 (对 StratTw) 与以 `LH` 为下标的世界 (对 FabLFReGen). `Lv` 的形状记为记号引导.
