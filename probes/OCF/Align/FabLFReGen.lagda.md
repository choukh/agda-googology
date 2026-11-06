# 一次封闭的层号上的一般折叠: 不造塔的 ψ₀Λ 候选闭项

> 不含记号. Fable 5.1, 2026-11-05. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数. 不改任何已有文件.
>
> **这一篇做什么.** 今天的主线 (LvKt → KcFold → DnFold → GenFold → NewTwr → KindLv) 把层号塔逐站造出来, 最后卡在两件事: "塔的类型" (每站的级要既是对角的字面第一位置, 又读进 `HB (Lev X_s)`, 于是种类结构族与级要互递归, `KindLvTw` 的草稿停机检查失败) 与 "升界形状" (C6). 本篇指出: **第一件在仓库里已经有现成的解, 只是没有和一般折叠接上.** [LFReTy](LFReTy.lagda.md) 把层号 `LH` 与以层号为下标的种类结构 `Lv : LH → KS` 写成一个归纳-递归块, 一切层的种类都在同一个种类结构 `SL = sup LH (step ∘ Lv)` 里, 塔 `tw n = Ω̂ⁿ 0`, 对角 `Λ = hl tw`, 以及 Λ 之上的不动点 `Λn` 都是 `HB SL` 的合法高度 ([LFReTower](LFReTower.lagda.md)); 那一路停在 "卡在接受第 1 层以上种类的折叠". 而 [GenFoldRun](GenFoldRun.lagda.md) 的折叠对**一切**种类结构 `T` 一条定义, 只要一个 `GenK T`. 把两者接上: 给 `SL` 一个 `GenK` (§1, §2), 最终坍缩取 [NewTwrColl](NewTwrColl.lagda.md) 的 `collG` (与骨架总审 `SkelDxGen.Gen0.ev₀` 同一个式子), 就得到层为 `up Λ`, `up Λ₂`, `up (Λn n)` 的无条件闭项 `TΛ`, `TΛ₂`, `TΛn` (§3): 合法由形状给出 (`Lg-sum` 一次调用), 布劳威尔树值, 有 FGH.
>
> **这些闭项的类型事实 (定理).** 在 `SL` 里, 第 n 站的层号 `tw n` 是对角 `Λ` 的字面第一位置 (`stage-fst`, 对一切世界), 第 n 站的新种类 `νL (ofHB (tw n))` 的坐标类型字面就是第 `ofHB (tw n)` 层的值 `HB (Lv (ofHB (tw n)))` (`coord-stage`, `refl`). 这两条正是 [KindLvTw](KindLvTw.lagda.md) 文件头说 "要互递归" 才能同时满足的两件事; 这里由 `LH` 的一次封闭直接给出, 没有停机问题, 没有分层, 没有逐站的 `emb`/`injL`/部分和. 骨架总审 §2 的类型条件 C1–C5, C7–C9 对本闭项也都满足 (最终坍缩在 `step SL` 上, 不经 `Ht`; 对角 `Λ` 在 `HB SL` 里取, 不在 `Ht` 里; 层号的类型是 `LH`, 不固定在 `HB S₀`).
>
> **值 (如实; 判断).** 本篇给 `SL` 的 `GenK` 把**一切**种类的 A-回灌都写成 "有损" (`fb-lossy`, `refl`), 基世界里每个种类的顶坐标都是底 (`top-base`, 定理); 折叠里唯一有回灌的是 `step SL` 的新种类 (坐标 `HB SL`, `GenFoldRun.κc₁`), 它的读回 `rd₁` 只含底种类的结点 (`NewTwrObs.onlyA-rd₁`). 所以 C6 在这里一样没有解决, 读法 (判断) 与 `TN`, `TK`, `TXΛ` 同一机制, 远低于 ψ₀Λ, 没有 `ord` 的定理. 本篇**不**提高强度; 它把 "塔的类型" 这一障碍从 ψ₀Λ 候选闭项的账上划掉, 让剩下的只有 C6 一件, 并且把 C6 在这个形状下的字面陈述写清楚 (§4): `SL` 的世界是以层号 `LH` 为下标的积, 第 n 站 (n ≥ 2) 的层号 `ofHB (tw n)` 含函数分支 (`lΩ`), 所以 "恰好升这一站的分量" 要对含函数的层号判等, 落在 `upd₁-sep`, `updHΛ-sep`, `raiseA-sep` 一族的定义域里; 这不是新墙, 是同一堵墙在更干净的类型上的陈述.
>
> **翻译账.** 本篇没有新结点, 没有新接口, 没有新字段; 用到的都是树侧已有的定义 (`LH`/`Lv`/`SL` 来自 `LFRe`, `GenK`/`collG` 来自 `GenFold`/`NewTwr`). 摆脱侧: 去掉了逐站造塔的全部脚手架 (`Kc`, `nxt`, `emb`, `injL`, `ιΛ`, `Bᴧ`, 下降, `Sk`/`Cvt`), 闭项只经一个封闭类型与一个一般折叠. `Lv` 的形状受下标塔的直觉启发 (`LFReTy` 自述), 如实记为 "记号引导的形状", 不算树自足.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FabLFReGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.GenFoldInst using (ldStep; topSupG; ldSup)
open import OCF.Align.LFReTy
open import OCF.Align.LFReTower using (tw; Λ; Lg-Λ; Λ₂; Lg-Λ₂; Λn; Lg-Λn)
open import OCF.Align.NewTwrIf using (CollK; col; lgCol)
open import OCF.Align.NewTwrColl using (collG)
```

## §1 每一层的顶坐标, 基世界, 向下封闭: 对层号 `LH` 递归

`Lv` 的四行分别是 `S⊥`, `step`, `sup ℕ`, `sup (⊤ ⊎ HB (Lv k))`; 顶坐标与向下封闭用 [GenFoldInst](GenFoldInst.lagda.md) 对 `step` 与 `sup` 的组合子, `S⊥` 没有种类, 三件都是空的. 递归经 `lΩ k g` 的分支 `g c`, 检查器接受 (与 `LFReTy.lvl`, `upL` 同形).

```agda
top⊥ : TopG S⊥
top⊥ = record { top = λ () ; topBd = λ () }

ld⊥ : LgDn S⊥
ld⊥ = record { lgDn = λ _ _ → tt }

LvΩ : (k : LH) → (HB (Lv k) → LH) → ⊤ ⊎ HB (Lv k) → KS
LvΩ k g = [ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′

topLv : (k : LH) → TopG (Lv k)
topLv lz = top⊥
topLv (ls x) = topStepG (topLv x)
topLv (ll f) = topSupG ℕ (λ n → Lv (f n)) (λ n → topLv (f n))
topLv (lΩ k g) = topSupG (⊤ ⊎ HB (Lv k)) (LvΩ k g) tp
  where
  tp : (i : ⊤ ⊎ HB (Lv k)) → TopG (LvΩ k g i)
  tp (inj₁ _) = topStepG (topLv k)
  tp (inj₂ c) = topLv (g c)

ldLv : (k : LH) → LgDn (Lv k)
ldLv lz = ld⊥
ldLv (ls x) = ldStep (ldLv x)
ldLv (ll f) = ldSup ℕ (λ n → Lv (f n)) (λ n → ldLv (f n))
ldLv (lΩ k g) = ldSup (⊤ ⊎ HB (Lv k)) (LvΩ k g) ld
  where
  ld : (i : ⊤ ⊎ HB (Lv k)) → LgDn (LvΩ k g i)
  ld (inj₁ _) = ldStep (ldLv k)
  ld (inj₂ c) = ldLv (g c)
```

**基世界**: 每个 `step` 的新界取 $0$, 积的每个分量取下一层的基世界. 合法.

```agda
w₀Lv : (k : LH) → Wd (Lv k)
w₀Lv lz = tt
w₀Lv (ls x) = w₀Lv x , hz
w₀Lv (ll f) n = w₀Lv (f n)
w₀Lv (lΩ k g) (inj₁ _) = w₀Lv k , hz
w₀Lv (lΩ k g) (inj₂ c) = w₀Lv (g c)

lw₀Lv : (k : LH) → LgW (Lv k) (w₀Lv k)
lw₀Lv lz = tt
lw₀Lv (ls x) = lw₀Lv x , tt
lw₀Lv (ll f) n = lw₀Lv (f n)
lw₀Lv (lΩ k g) (inj₁ _) = lw₀Lv k , tt
lw₀Lv (lΩ k g) (inj₂ c) = lw₀Lv (g c)
```

## §2 `SL` 的 `GenK`

底种类取第 0 层的新种类 `νL lz = (lz , inj₂ tt)`: 它的坐标是 `HB S⊥` (只有 $0$, 后继, ℕ-极限的树), 读成 `A` 是逐构造子的翻译 `frE⊥`, 保第一位置与合法. A-回灌一律 "有损" (`inj₂ tt`); 这是本篇如实的选择, 不是定理逼出的 (见 §4).

```agda
frE⊥ : HB S⊥ → A
frE⊥ hz = azero
frE⊥ (hs h) = asuc (frE⊥ h)
frE⊥ (hl f) = alim (λ n → frE⊥ (f n))
frE⊥ (hΩ () _)

frE⊥-⊲ : ∀ {a b} {w : Wd S⊥} → a ⊲[ w ] b → frE⊥ a ⊲ frE⊥ b
frE⊥-⊲ hself = C.self
frE⊥-⊲ (hsuc p) = C.suc (frE⊥-⊲ p)
frE⊥-⊲ (hlim n p) = C.lim n (frE⊥-⊲ p)
frE⊥-⊲ (hLim {κ = ()} _ _)

frE⊥-lg : ∀ a → LgB a → Lg (frE⊥ a)
frE⊥-lg hz l = tt
frE⊥-lg (hs a) l = frE⊥-lg a l
frE⊥-lg (hl f) (st , l) = (λ n → frE⊥-⊲ (st {tt} n)) , (λ n → frE⊥-lg (f n) (l n))
frE⊥-lg (hΩ () _) l

GL : GenK SL
GL = record
  { tpK = topSupG LH FL (λ k → topStepG (topLv k))
  ; w₀ = λ k → w₀Lv k , hz
  ; lw₀ = λ k → lw₀Lv k , tt
  ; aK = νL lz
  ; frE = frE⊥
  ; frE-lg = λ {e} le → frE⊥-lg e le
  ; frE-mono = λ lw e e′ p → frE⊥-⊲ p
  ; fbA = λ _ → inj₂ tt }

LdL : LgDn SL
LdL = ldSup LH FL (λ k → ldStep (ldLv k))

flL : FbLg GL
flL κ = tt
```

## §3 无条件闭项: 层取 `up Λ`, `up Λ₂`, `up (Λn n)`

最终坍缩 `collG GL LdL flL : CollK SL`: 层 `h : HB (step SL)` 前接 $1$, 在基世界 `(w₀ GL , 0)` 里把 $\Omega_{1\boxplus h}$ 的数据折到第 0 层, `sum` 成 `A`. 对角 `Λ : HB SL` 经 `up` 进 `step SL` (旧种类原样), 合法由 `Lg-up` 给出.

```agda
collL : CollK SL
collL = collG GL LdL flL

TΛ : A
TΛ = col collL (up Λ) (Lg-up Λ Lg-Λ)

Lg-TΛ : Lg TΛ
Lg-TΛ = lgCol collL (up Λ) (Lg-up Λ Lg-Λ)

TΛ₂ : A
TΛ₂ = col collL (up Λ₂) (Lg-up Λ₂ Lg-Λ₂)

Lg-TΛ₂ : Lg TΛ₂
Lg-TΛ₂ = lgCol collL (up Λ₂) (Lg-up Λ₂ Lg-Λ₂)

TΛn : ℕ → A
TΛn n = col collL (up (Λn n)) (Lg-up (Λn n) (Lg-Λn n))

Lg-TΛn : ∀ n → Lg (TΛn n)
Lg-TΛn n = lgCol collL (up (Λn n)) (Lg-up (Λn n) (Lg-Λn n))

ordL : A → FLv.Ordᶜ FLv.zero
ordL azero = FLv.zero
ordL (asuc a) = FLv.suc (ordL a)
ordL (alim f) = FLv.lim (λ n → ordL (f n))

fghΛ : ℕ → ℕ
fghΛ = FLv.FGH (ordL TΛ)

fghΛ₂ : ℕ → ℕ
fghΛ₂ = FLv.FGH (ordL TΛ₂)

fghΛn : ℕ → ℕ → ℕ
fghΛn n = FLv.FGH (ordL (TΛn n))
```

## §4 类型事实与如实的盲点

**每站的级是对角的字面第一位置, 且读进自己那一层的值.** 这是 `KindLvTw` 文件头列出的、要 "种类结构族与级互递归" 才能同时满足的两件事; 在 `SL` 里两条都是一行.

```agda
-- 第 n 站的层号 tw n 是对角 Λ 的字面第一位置, 对一切世界
stage-fst : ∀ n {w : Wd SL} → tw n ⊲[ w ] Λ
stage-fst n = hlim n hself

-- 第 n 站的新种类的坐标类型字面就是第 ofHB (tw n) 层的值
coord-stage : ∀ n → E SL (νL (ofHB (tw n))) ≡ HB (Lv (ofHB (tw n)))
coord-stage n = refl

-- 更一般: SL 的每个种类的坐标类型是它读回层的值 (LFReTy.E-rbl 的重述)
coord-rbl : ∀ κ → E SL κ ≡ HB (Lv (rbl κ))
coord-rbl = E-rbl
```

**盲点 (如实, 定理).** 本篇的 `GenK` 对一切种类都 "有损"; 基世界里每个种类的顶坐标都是底. 所以 [GenFoldRun](GenFoldRun.lagda.md) 在 `inj₁ κ` 上第 0 层目标一律走 `RKa (inj₂ _)` (当前世界的分支重复 $\omega$ 次), 新种类之外没有任何种类的界被升高; 这与 `NegNewTwr.final-only-bot`, `fb-new-none` 对 `TN` 说的是同一件事.

```agda
fb-lossy : ∀ κ → fbA GL κ ≡ inj₂ tt
fb-lossy κ = refl

top-base-Lv : ∀ k κ → top (topLv k) κ (w₀Lv k) ≡ bot (Lv k) κ
top-base-Lv lz ()
top-base-Lv (ls x) (inj₁ κ) = top-base-Lv x κ
top-base-Lv (ls x) (inj₂ _) = refl
top-base-Lv (ll f) (n , κ) = top-base-Lv (f n) κ
top-base-Lv (lΩ k g) (inj₁ _ , inj₁ κ) = top-base-Lv k κ
top-base-Lv (lΩ k g) (inj₁ _ , inj₂ _) = refl
top-base-Lv (lΩ k g) (inj₂ c , κ) = top-base-Lv (g c) κ

top-base : ∀ κ → top (tpK GL) κ (w₀ GL) ≡ bot SL κ
top-base (k , inj₁ κ) = top-base-Lv k κ
top-base (k , inj₂ _) = refl
```

**C6 在这个形状下的字面陈述 (判断, 依据已有定理).** `Wd SL = (k : LH) → Wd (FL k)`, 世界以层号为下标. 要让第 n 站的新种类 `νL (ofHB (tw n))` 不有损, 要给它一个 `FBA SL (νL (ofHB (tw n)))`, 它的 `rsA` 要改世界在下标 `ofHB (tw n)` 处的分量. $n = 0, 1$ 时下标是 `lz`, `ls lz`, 不含函数, 按模式判定 (同 `KindLvTw.isTwo`); $n \ge 2$ 时 `ofHB (tw n)` 的头是 `lΩ lz (λ c → …)`, 含函数分支, "恰好改这一处, 别处不动" 要对含函数的层号判等, 这是 `NegGenFoldUpd.upd₁-sep`, `NegKindLvUpd.updHΛ-sep`, `ColimWNeg.raiseA-sep` 一族的定义域 (推出分离子; 加外延得 WLPO). 所以 ψ₀Λ 候选闭项剩下的只有 C6 一件, 而且在 `SL` 上它的形状比塔上更干净: 下标是层号 `LH` 本身, 不是 `Kc s` 里的拷贝. 未否定的出口与此前相同: 带字面公共上界的有界升界 (`RaiseC.Rᵇ`), 或对可入层号 (带 `⊲[ w ] b` 证据) 的更新 (`ColimA`); 两者在 `SL` 上都没有写.

## 结论 (按档)

- **[定理]** `GL : GenK SL`, `LdL`, `flL`; 闭项 `TΛ`, `TΛ₂`, `TΛn n` 与证书 `Lg-TΛ`, `Lg-TΛ₂`, `Lg-TΛn`, FGH `fghΛ`, `fghΛ₂`, `fghΛn`; `stage-fst`, `coord-stage`, `coord-rbl`; `fb-lossy`, `top-base-Lv`, `top-base`.
- **[判断]** 读法: 与 `TN`, `TK`, `TXΛ` 同一机制 (只有 `step SL` 的新种类有回灌, 读回只含底种类结点), 远低于 ψ₀Λ; 没有 `ord` 定理. "塔的类型" 障碍在 `SL` 上不出现, 是类型事实 (`stage-fst`, `coord-stage`); "剩下只有 C6" 是判断.
- **翻译账.** 无新结点, 无新接口, 无新字段; 去掉逐站造塔的脚手架. `Lv` 的形状记为记号引导.
