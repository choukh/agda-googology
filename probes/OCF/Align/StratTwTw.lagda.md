# 分层互递归塔 (二): 前缀与级的 ℕ 递归, 每站头种类按自己的级回灌, 无条件闭项

> 不含记号. 入口 [StratTw](StratTw.lagda.md), 接口 [StratTwIf](StratTwIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 分层.** 记录 `Stg` (前缀结构 `Pf` 与它里面的级 `Xf`), 一步 `nxtS`: 新前缀是 `sup (⊤ ⊎ ⊤)` 的两个分量 [旧前缀, `step (Lev X)`], 新级是 $\mathrm{hs}(\iota_{\mathrm{l}}X)\boxplus\iota_{\mathrm{r}}(\mathrm{ev}\,X)$ (`KindLvEv.evK`, 第 $X$ 级之上一级的求值, 值在 `HB (step (Lev X))`). 按 $s$ 普通 ℕ 递归: `st 0 = (S₀ , 1)`, `st (s+1) = nxtS (st s)`. 这是 KindLv 草稿 `Ys (suc s) = hs (Ys s) ⊞ ι (suc s) (evN (Ys s))` 的分层写法: **第 $s$ 站的级只住在只含分量 $\le s$ 的类型里**, 所以不需要先有整个族.
> - **§2 总结构与总结构里的级.** `C 0 = S₀`, `C (s+1) = step (Lev (X s))`, `U = sup ℕ C` (`C` 只调用已经造好的 `X s`, 不互递归). 总结构里的级 `Y` 另写: `Y 0 = ι 0 1`, `Y (s+1) = hs (Y s) ⊞ ι (s+1) (evK (X s))`; 层号对角 `Bᴧ s = hs (Y s)`, 相邻项 `⊞-fst` (字面). **`Y s` 与 `X s` 同形** (`sim s : Sim (MP s) (Y s) (X s)`), 由三条对构造子的引理归纳给出 (`Sim-⊞`, `Sim-up`, `Sim-new`); 两者不定义相等, 也不需要.
> - **§3 每个种类的级回灌 `lvU`.** 第 0 个分量的底种类: 级层 $0$, 读回 `sum`, 升界是 ℕ 下标 $0$ 的点更新 (`KA`, 同 KindLv 草稿). **第 $s+1$ 个分量的头种类** `(suc s , inj₂ tt)`, 坐标 `HB (Lev (X s))`, 对**一切** $s$ (`KT s`): 级层 `lyL (Y s) = up (Bᴧ s)`, 是 $\Lambda$ 的字面第一位置 (`hlim s hself`, 对一切世界); 读回是沿同形的级读回 `readS (sim s)` ([StratTwRd](StratTwRd.lagda.md)); 升界是对 ℕ 下标 $s+1$ 的点更新, 换掉 `step` 的第二分量 (就是这个种类的界). 下标都可判定, **不用升界算子**, 没有 "升一份留别份" 于含函数的下标. 其余种类 (`Lev (X s)` 里的种类) 退回 `fbA`.
> - **§4 无条件闭项** `TS`, 证书 `Lg-TS`, FGH `fghS`; 坍缩 `ColS` 是 `KindLvTw.ColL` 的逐字拷贝 (按级回灌的折叠 `KindLvRun`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StratTwTw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (GenK; LgDn; FbLg; tpK; w₀; lw₀; module FoldTy; n0; n1; _⨾_)
open import OCF.Align.GenFoldTree using (module Tree; topStepG; accᴸ)
open import OCF.Align.GenFoldInst using (genS₀; ldS₀; flS₀; genStep; ldStep; flStep; genLev; ldLev; flLev;
                                         genSupℕ; ldSup; flSupℕ; upd; upd-R; upd-Q; upd-at)
open import OCF.Align.KindLvEv using (evK; lg-evK)
open import OCF.Align.KindLvIf using (KLv; LvFb; lyL)
import OCF.Align.KindLvRun as KR
open import OCF.Align.StratTwIf using (KMap; Sim; sz; ss; sl; sΩ; StratTw; Bᴧ; ΛS; OwnHd)
import OCF.Align.StratTwRd as SRd
```

## §0 一般坍缩 (`KindLvTw.ColL` 的逐字拷贝)

基世界里把 $\Omega_\Lambda$ 的数据经按级回灌的折叠 `KindLvRun` 折到第 0 层, `sum` 成 `A`. 拷贝而不导入, 是因为 `KindLvTw` 顶层的带参数 `open` (`KRd KΛc LdΛ`) 会被定义级切片算进闭项 (行数口径的脚手架, 不改值). 放在最前, 免得与下面的 `st`, `Y` 撞名.

```agda
module ColS {T : KS} (G : GenK T) (Ld : LgDn T) (fl : FbLg G) (Λ′ : HB (step T)) (lΛ′ : LgB Λ′)
            (o : ∀ {w} → hs hz ⊲[ w ] Λ′) (lv : LvFb T (tpK G) Λ′) where
  open Tree T
  open Om (topStepG (tpK G))
  open KR T G Ld fl Λ′ lΛ′ o lv
  open FoldTy T Λ′ using (Ig; St; st; Df)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y′ = Stp Y′

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  W₁ : Wd L₀
  W₁ = w₀ G , hz

  lW₁ : LgW L₀ W₁
  lW₁ = lw₀ G , tt

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ′ {W₁}) ≤rf lW₁ hself Act n0 Y₀

  ΨΩ : D hz W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ lW₁)

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt
```

## §1 分层: 前缀与前缀里的级

```agda
record Stg : Set₁ where
  constructor stg
  field
    Pf : KS
    Xf : HB Pf
open Stg public

QF : (t : Stg) → ⊤ ⊎ ⊤ → KS
QF t (inj₁ _) = Pf t
QF t (inj₂ _) = step (Lev (Xf t))

nxtS : Stg → Stg
nxtS t = stg (sup (⊤ ⊎ ⊤) (QF t))
             (hs (ι {⊤ ⊎ ⊤} {QF t} (inj₁ tt) (Xf t)) ⊞ ι {⊤ ⊎ ⊤} {QF t} (inj₂ tt) (evK (Xf t)))

st : ℕ → Stg
st zero = stg S₀ (hs hz)
st (suc s) = nxtS (st s)

P : ℕ → KS
P s = Pf (st s)

X : (s : ℕ) → HB (P s)
X s = Xf (st s)
```

## §2 总结构, 总结构里的级, 同形

```agda
C : ℕ → KS
C zero = S₀
C (suc s) = step (Lev (X s))

U : KS
U = sup ℕ C

jP : ∀ s → K (P s) → K U
jP zero κ = 0 , κ
jP (suc s) (inj₁ _ , κ) = jP s κ
jP (suc s) (inj₂ _ , κ) = suc s , κ

cvP : ∀ s (κ : K (P s)) → E U (jP s κ) → E (P s) κ
cvP zero κ e = e
cvP (suc s) (inj₁ _ , κ) e = cvP s κ e
cvP (suc s) (inj₂ _ , κ) e = e

MP : ∀ s → KMap (P s) U
MP s = record { j = jP s ; cv = cvP s }

Y : ℕ → HB U
Y zero = ι {ℕ} {C} 0 (hs hz)
Y (suc s) = hs (Y s) ⊞ ι {ℕ} {C} (suc s) (evK (X s))

lY : ∀ s → LgB (Y s)
lY zero = tt
lY (suc s) = Lg-⊞ (hs (Y s)) (ι {ℕ} {C} (suc s) (evK (X s))) (lY s) (Lg-ι {ℕ} {C} (suc s) (evK (X s)) (lg-evK (X s)))

Yfst : ∀ s {w} → hs (Y s) ⊲[ w ] Y (suc s)
Yfst s = ⊞-fst (hs (Y s)) (ι {ℕ} {C} (suc s) (evK (X s)))
```

同形的三条引理, 都对一个高度的构造子归纳. `Sim-up` 用到 `jP (suc s) (inj₁ _ , κ) = jP s κ` (定义相等), `Sim-new` 用到 `jP (suc s) (inj₂ _ , κ) = (suc s , κ)`.

```agda
Sim-⊞ : ∀ {S′} {M : KMap S′ U} {a x b y} → Sim M a x → Sim M b y → Sim M (a ⊞ b) (x ⊞ y)
Sim-⊞ σa sz = σa
Sim-⊞ σa (ss σ) = ss (Sim-⊞ σa σ)
Sim-⊞ σa (sl σf) = sl (λ n → Sim-⊞ σa (σf n))
Sim-⊞ σa (sΩ σg) = sΩ (λ e → Sim-⊞ σa (σg e))

Sim-up : ∀ s {a x} → Sim (MP s) a x → Sim (MP (suc s)) a (ι {⊤ ⊎ ⊤} {QF (st s)} (inj₁ tt) x)
Sim-up s sz = sz
Sim-up s (ss σ) = ss (Sim-up s σ)
Sim-up s (sl σf) = sl (λ n → Sim-up s (σf n))
Sim-up s (sΩ {κ} σg) = sΩ {κ = inj₁ tt , κ} (λ e → Sim-up s (σg e))

Sim-new : ∀ s (e : HB (C (suc s))) → Sim (MP (suc s)) (ι {ℕ} {C} (suc s) e) (ι {⊤ ⊎ ⊤} {QF (st s)} (inj₂ tt) e)
Sim-new s hz = sz
Sim-new s (hs e) = ss (Sim-new s e)
Sim-new s (hl f) = sl (λ n → Sim-new s (f n))
Sim-new s (hΩ κ g) = sΩ {κ = inj₂ tt , κ} (λ c → Sim-new s (g c))

sim : ∀ s → Sim (MP s) (Y s) (X s)
sim zero = ss sz
sim (suc s) = Sim-⊞ (ss (Sim-up s (sim s))) (Sim-new s (evK (X s)))

hd : ℕ → K U
hd s = suc s , inj₂ tt

StU : StratTw U
StU = record { P = P ; X = X ; M = MP ; Y = Y ; sim = sim ; lY = lY ; Yfst = Yfst ; hd = hd ; hdE = λ s → refl }

-- 最终层 (与接口的 ΛS StU 定义相等; 直接写出, 让闭项的切片不经记录 StU)
Λ : HB (step U)
Λ = up (hl (λ s → hs (Y s)))

lΛ : LgB Λ
lΛ = Lg-up (hl (λ s → hs (Y s))) ((λ n → hsuc (Yfst n)) , lY)

one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ
one⊲ = hlim 0 (hsuc hself)
```

## §3 实例: `GenK U`, `LgDn U`, 每个种类的级回灌

```agda
genC : (n : ℕ) → GenK (C n)
genC zero = genS₀
genC (suc s) = genStep (genLev (X s))

ldC : (n : ℕ) → LgDn (C n)
ldC zero = ldS₀
ldC (suc s) = ldStep (ldLev (X s))

flC : (n : ℕ) → FbLg (genC n)
flC zero = flS₀
flC (suc s) = flStep (genLev (X s)) (flLev (X s))

GU : GenK U
GU = genSupℕ C genC

LdU : LgDn U
LdU = ldSup ℕ C ldC

flU : FbLg GU
flU = flSupℕ C genC flC

open SRd U LdU using (module SR)
open Tree U using (sum; sum-fst; Lg-sum)

-- 第 0 个分量的底种类: 级层 0, 读回 sum
KA : KLv U (tpK GU) Λ (0 , tt)
KA = record
  { ℓ = hz ; ℓ⊲ = λ {w} → z⊲ᴮ Λ
  ; rd = λ lW b x → sum b x ; rd-fst = λ lW b x → sum-fst b x ; rd-lg = λ lW b x lb → Lg-sum b x lb
  ; rs = λ w v → upd {λ m → Wd (C m)} w 0 v
  ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (C m)} (λ m → _≤w_ (C m)) w 0 v (λ m → ≤w-rf (C m)) p
  ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (C m)} (λ m → LgW (C m)) w 0 v lw lv
  ; rs-top = refl }

-- 第 s+1 个分量的头种类: 坐标 HB (Lev (X s)), 级层 lyL (Y s) = up (Bᴧ s), 读回沿同形 sim s
nw⁺ : ∀ s → Wd U → HB (Lev (X s)) → Wd (C (suc s))
nw⁺ s w v = proj₁ (w (suc s)) , v

KT : ∀ s → KLv U (tpK GU) Λ (hd s)
KT s = record
  { ℓ = lyL (Y s) ; ℓ⊲ = λ {w} → hlim s hself
  ; rd = λ lW b x → SR.readS (MP s) (sim s) lW b x
  ; rd-fst = λ lW b x → SR.readS-fst (MP s) (sim s) lW b x
  ; rd-lg = λ lW b x lb → SR.Lg-readS (MP s) (sim s) lW b x lb
  ; rs = λ w v → upd {λ m → Wd (C m)} w (suc s) (nw⁺ s w v)
  ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (C m)} (λ m → _≤w_ (C m)) w (suc s) (nw⁺ s w v) (λ m → ≤w-rf (C m)) (≤w-rf (Lev (X s)) , p)
  ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (C m)} (λ m → LgW (C m)) w (suc s) (nw⁺ s w v) lw (proj₁ (lw (suc s)) , lv)
  ; rs-top = λ {w} {v} → upd-at {λ m → Wd (C m)} w (suc s) (nw⁺ s w v) (λ u → proj₂ u ≡ v) refl }

lvU : LvFb U (tpK GU) Λ
lvU (zero , tt) = inj₁ KA
lvU (suc s , inj₂ tt) = inj₁ (KT s)
lvU (suc s , inj₁ κ) = inj₂ tt

-- 接口 §4: 每站头种类按自己的级回灌
ownU : OwnHd StU (tpK GU) lvU
ownU s = KT s , refl , refl
```

## §4 无条件闭项

坍缩 `ColS` (§0) 用在 $T=U$ 上.

```agda
TS : A
TS = ColS.Tψ GU LdU flU Λ lΛ one⊲ lvU

Lg-TS : Lg TS
Lg-TS = ColS.Lg-Tψ GU LdU flU Λ lΛ one⊲ lvU

ordS : A → FLv.Ordᶜ FLv.zero
ordS azero = FLv.zero
ordS (asuc a) = FLv.suc (ordS a)
ordS (alim f) = FLv.lim (λ n → ordS (f n))

fghS : ℕ → ℕ
fghS = FLv.FGH (ordS TS)
```
