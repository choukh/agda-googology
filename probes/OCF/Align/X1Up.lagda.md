# 在 $X_1$ 上叠层: 越过 ψ₀(Ω_Ω) 的第一步 (入口)

> 不含记号. 构造一路 X1Up (配对否定一路 NegX1Up), 2026-11-05. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 不改任何已有文件.
>
> 文件: 接口 [X1UpIf](X1UpIf.lagda.md) (定稿 23:45, 只增 `PathOutIf`), 上层折叠 [X1UpFold](X1UpFold.lagda.md) (对一切满足接口的 `U`), 本篇 (实例, 闭项, 证书, FGH, 决定正确, 否定一条).
>
> **这一篇做什么.** 作者本轮选定 "C 线继续: X₁ 上叠层", 接 [PathOut](PathOut.lagda.md) 接手清单第 1 条: 在 $X_1$ 上叠可数层号 $m$ (层 $X_1\oplus m$), 写上层折叠, 留下 $X_1$ 的种类, 证上层输出带路径, 再交给 `PathOutFold.Ψ`.
>
> 1. **接口** `X1UpIf`: `PathOutIf` 加世界的序 `_≼_` 与三条律 (`ev↑` 证据随世界变大, `adm↓` 可入随世界变小且进入后的世界有序, `≼-nxt` 进入不缩小世界; 律里成对的两个世界都带字面证据 $W\preceq W'$), 加底层地板 `topX` (合法, 带路径).
> 2. **上层折叠** `X1UpFold.ΦU`: 与 `TySupFold.Φ` 逐子句同式; 决定 `decU`: 底种类一律留 (嵌入 `emb t κ₀`), 新种类的层号 $j$ 与目标 $t$ 用 `cmpB` 比较 (公共上界 $m$). `ΦX`: 折到第 $X_1$ 层, 当前界是地板 `topX` (`topL`). 叠层的种类结构 `LS m` 是 `XS` 上的 `step`/`sup` 塔.
> 3. **路径** `X1UpFold.PSL`, **定理** `PH-ΦU`, `PH-ΦX`: 当前界与输入带路径 ⇒ 输出带路径, 对一切世界, 对一切 `U`. 新种类的可入是 Kripke 式 (有更大世界 $V$, 坐标在 $V$ 里带路径); 朴素写法不满足 `adm↓` (本篇 `naive-anti`, 定理).
> 4. **卡点的处理** (PathOut 接手清单第 1 条: 留下的底种类经嵌入 `emb t κ₀` 到目标层后, 证据要沿嵌入搬运, 对变量层号不是 `refl`): **写了搬运引理**, 但不证世界相等, 只证世界**有序** (`clP`, `upkE`, `upkA`: 输入侧的世界 $\preceq$ $\kappa_0$ 的世界 $\preceq$ 目标侧的世界), 再用 `PH-mono` 搬. 每条引理对层号递归, 每一步类型字面对上, 不用 `subst`. 这条路依赖 PathOut 选的 "证据同向" (`PH-mono` 由它得到).
> 5. **闭项**: `TU m lm` (第 $X_1\oplus m$ 层的地板经 `ΦX` 再经 `Ψ` 折到第 0 层), `TU1 = TU 1`, 对角 `TU2 = hl yU` ($y_{n+1}=y_n\boxplus TU(y_n+1)$). 证书 `LgB-TU`, `LgB-TU2` (标准 `LgB`, 由 `Sh-Ψ` 的形状给出), FGH `fghU1`, `fghU2`. 路径由定理给出, 不是假设.
>
> **读法 (判断, 没有值的定理).** 按 TySup 的约定 (ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加累加): `ΦX (hs hz)` 是链 $d_0=T(\Omega_{\Omega_1})$, $d_{n+1}=d_n\boxplus T(\Omega_{\Omega_1}\boxplus d_n)$ 的极限 ($T$ 是底种类全留时的折叠), 读 $\varepsilon_{\Omega_{\Omega_1}+1}$; 再经 `Ψ` 读 ψ₀(Ω_{Ω_1+1}). `TU m` 读 ψ₀(Ω_{Ω_1+m}); `TU2` 是 $\alpha\mapsto$ ψ₀(Ω_{Ω_1+α}) 的不动点迭代, 读 **ψ₀(Ω_{Ω·2})** (Ω = Ω_1). 与 PathOut 的 `TXL` (读 ψ₀(Ω_Ω)) 比, **越过 ψ₀(Ω_Ω)** (判断). 对角走的是可数层号 (前一个输出当叠层层号), 不是一个 `lΩ` 层号的地板; 后者 (层号 $\Omega_{\Omega_1\cdot 2}$ 作 `lΩ` 结点) 本路没有写.
>
> **代价, 如实.** (1) 累加: `ΦU` 与 `Ψ` 的 ℕ-极限取部分和 (同 TySupFold); 叠层地板 `topU (hl f)` 是部分和 (同 TySupSum). (2) 路径机制的行数大于折叠本身 (见文末行数: `X1UpFold` 里折叠 80 行, 路径独有 216 行). (3) 上层输出只证带路径, 没有 `LgB`: 否定一路报告 (`NegX1UpInst`, 主审复核前不算数) `NotMonoU.ΦU-not-mono` (对一切 `U`) 与 `kept-not-LgB-U` (合法输入折到 $X_1$ 后留下的 $\Omega_1$ 结点不满足 `LgB`); `Ψ` 的输出合法不靠输入合法. (4) 接口没有 "地板的根是结点" 的律 (否定一路 `NegX1UpIf.flatTopOf`: 换成无结点的地板仍是实例, 链会塌); 实例用 `topL`, `nonflat1` (定理) 说链的第 0 项根是 $\Omega_1$ 结点.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.X1Up where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupIf using (Dc; keep; same; above)
open import OCF.Align.TySupC using (Cd; _⊏ᶜ_; _⊑ᶜ_; wfC)
open import OCF.Align.TySup using (ord⊥)
open import OCF.Align.PathOutX1 using (IX₁; XS₁; κΩ; Ev₁; Adm₁; nxt₁)
open import OCF.Align.PathOut using (W₀; lW₀; sh→lgB₁; topL; Lg-topL; PH-topL)
import OCF.Align.PathOutFold as PF
open PF IX₁ using (Ψ; Sh-Ψ)
open import OCF.Align.X1UpIf
import OCF.Align.X1UpFold as UF
import OCF.Free.Level as FLv
```

## §1 实例: $X_1$ 的世界序与三条律

世界是界 $B$ (第 0 层的值), 序是字面第一位置 $B\lhd B'$. 种类 `(inj₂ y , κ)` 的证据 $y+1\lhd B$ 随界变大仍成立; $\Omega_1$ 种类的可入 $B\lhd y$ 随界变小仍成立, 进入后的世界都是 $y+1$; 进入不缩小世界 ($B\lhd y+1$, 或世界不变).

```agda
_≼₁_ : Cd → Cd → Set
B ≼₁ B′ = B ⊲[ tt ] B′

ev↑₁ : ∀ {B B′} → B ≼₁ B′ → ∀ {κ} → Ev₁ B κ → Ev₁ B′ κ
ev↑₁ q {inj₁ _ , inj₁ ()}
ev↑₁ q {inj₁ _ , inj₂ _} ev = tt
ev↑₁ q {inj₂ y , κ} ev = ⊲ᴮ-tr ev q

adm↓₁ : ∀ {B B′} (q : B ≼₁ B′) {κ} (ev : Ev₁ B κ) {e} (a′ : Adm₁ B′ κ e) →
        Σ (Adm₁ B κ e) (λ a → nxt₁ B κ ev e a ≼₁ nxt₁ B′ κ (ev↑₁ q {κ} ev) e a′)
adm↓₁ q {inj₁ _ , inj₁ ()}
adm↓₁ q {inj₁ _ , inj₂ _} ev (By , ly) = (⊲ᴮ-tr q By , ly) , hself
adm↓₁ q {inj₂ y , κ} ev a′ = tt , q

≼-nxt₁ : ∀ {B κ} (ev : Ev₁ B κ) e (a : Adm₁ B κ e) → B ≼₁ nxt₁ B κ ev e a
≼-nxt₁ {κ = inj₁ _ , inj₁ ()}
≼-nxt₁ {κ = inj₁ _ , inj₂ _} ev y (By , ly) = hsuc By
≼-nxt₁ {κ = inj₂ y , κ} ev e a = hself

IU : X1UpIf
IU = record
  { P = IX₁ ; _≼_ = _≼₁_ ; ≼-rf = hself ; ≼-tr = ⊲ᴮ-tr
  ; ev↑ = ev↑₁ ; adm↓ = adm↓₁ ; ≼-nxt = ≼-nxt₁
  ; topX = topL ; Lg-topX = Lg-topL ; PH-topX = PH-topL }

open UF IU
```

## §2 闭项

`TU m lm`: 第 $X_1\oplus m$ 层的地板 `topU m` 经上层折叠 `ΦX` 折到第 $X_1$ 层 (界 `topL`), 再经 `Ψ` 折到第 0 层. 路径由定理 `PH-ΦX` 与 `PH-topU` 给出, 不是假设.

```agda
TU : (m : Cd) → LgB m → HB S⊥
TU m lm = Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz (ΦX m lm (topU m)) (PH-ΦX m lm (topU m) W₀ (PH-topU m W₀))

LgB-TU : ∀ m lm → LgB (TU m lm)
LgB-TU m lm = sh→lgB₁ (TU m lm)
  (Sh-Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz (ΦX m lm (topU m)) (PH-ΦX m lm (topU m) W₀ (PH-topU m W₀)))

-- 一层: X₁ ⊕ 1
TU1 : HB S⊥
TU1 = TU (hs hz) tt

-- 对角: y₀ = 0, y_{n+1} = y_n ⊞ TU (y_n + 1)
yU : ℕ → Cd
lg-yU : ∀ n → LgB (yU n)
yU zero = hz
yU (suc n) = yU n ⊞ TU (hs (yU n)) (lg-yU n)
lg-yU zero = tt
lg-yU (suc n) = Lg-⊞ (yU n) (TU (hs (yU n)) (lg-yU n)) (lg-yU n) (LgB-TU (hs (yU n)) (lg-yU n))

TU2 : HB S⊥
TU2 = hl yU

LgB-TU2 : LgB TU2
LgB-TU2 = (λ n → ⊞-fst (yU n) (TU (hs (yU n)) (lg-yU n))) , lg-yU

fghU1 : ℕ → ℕ
fghU1 = FLv.FGH (ord⊥ TU1)

fghU2 : ℕ → ℕ
fghU2 = FLv.FGH (ord⊥ TU2)
```

## §3 决定正确 (定理)

底种类一律留; 新种类 (第 $j$ 层): 留 ⇒ $j+1\lhd t$; 同层 ⇒ $j=t$; 在上 ⇒ 报的层就是 $j$. 两个下标 ($j$ 与 $t$) 都是 $m$ 的字面第一位置, 公共上界 $m$ 合法.

```agda
OkU : ∀ {m t κ} → UF.ClD IU m κ → Dc LS _⊏ᶜ_ _⊑ᶜ_ m t κ → Set
OkU (bas _ _) (keep _ _) = ⊤
OkU (bas _ _) (same _) = ⊥
OkU (bas _ _) (above _ _ _ _) = ⊥
OkU {t = t} (nw j _ _) (keep _ _) = j ⊏ᶜ t
OkU {t = t} (nw j _ _) (same _) = j ≡ t
OkU (nw j _ _) (above i _ _ _) = i ≡ j

okP : ∀ {m t j} {κ : K (LS m)} (to : HB (LS j) → E (LS m) κ) (pj : j ⊏ᶜ m) r →
      OkU {m} {t} (nw j pj to) (pickU to pj r)
okP to pj (inj₂ q) = q
okP to pj (inj₁ hself) = hself
okP to pj (inj₁ (hsuc hself)) = refl
okP to pj (inj₁ (hsuc (hsuc q))) = refl
okP to pj (inj₁ (hsuc (hlim n q))) = refl
okP to pj (inj₁ (hsuc (hLim {κ = ()} _ _)))

okU : ∀ m t (pt : t ⊑ᶜ m) lm κ (c : UF.ClD IU m κ) → OkU c (decU m t pt lm κ c)
okU m t pt lm κ (bas κ₀ to) = tt
okU m t pt lm κ (nw j pj to) = okP to pj (cmpB pj pt tt lm)
```

## §4 字面事实 (定理, refl)

第 $X_1\oplus 1$ 层的地板是新种类 (第 $0$ 号叠层) 的结点; 对目标 $X_1$ 它是同层, 读回恒等. $X_1$ 层的 $\Omega_1$ 种类在第 $X_1\oplus 1$ 层里是底种类, 对目标 $X_1$ 留下, 种类字面不变.

```agda
private
  root1 : decU (hs hz) hz (z⊲ᴮ (hs hz)) tt (inj₂ tt) (clD (hs hz) (inj₂ tt)) ≡ same (λ c → c)
  root1 = refl

  keepΩ : decU (hs hz) hz (z⊲ᴮ (hs hz)) tt (inj₁ κΩ) (clD (hs hz) (inj₁ κΩ)) ≡ keep κΩ (λ c → c)
  keepΩ = refl
```

**不塌 (定理, 对实例).** 否定一路提醒: "同层" 的链若从 $0$ 起步, 链的每一项都不含 $\Omega$-结点. 这里界是 `topL`: 第 $X_1\oplus 1$ 层的地板折到 $X_1$ 是链的 ℕ-极限, 链的第 0 项的根是 $\Omega_1$ 种类的结点 (由计算, `tt`).

```agda
RootΩ₁ : HB XS₁ → Set
RootΩ₁ (hΩ (inj₁ _ , inj₂ _) _) = ⊤
RootΩ₁ (hΩ (inj₁ _ , inj₁ ()) _)
RootΩ₁ (hΩ (inj₂ _ , _) _) = ⊥
RootΩ₁ hz = ⊥
RootΩ₁ (hs _) = ⊥
RootΩ₁ (hl _) = ⊥

HeadΩ₁ : HB XS₁ → Set
HeadΩ₁ (hl f) = RootΩ₁ (f 0)
HeadΩ₁ hz = ⊥
HeadΩ₁ (hs _) = ⊥
HeadΩ₁ (hΩ _ _) = ⊥

nonflat1 : HeadΩ₁ (ΦX (hs hz) tt (topU (hs hz)))
nonflat1 = tt
```

## §5 为什么新种类的可入是 Kripke 式 (否定, 定理)

`adm↓` 要可入随世界变小. 若新种类的可入写成朴素的 "坐标在 $W$ 里带路径" (进入后世界不变), `adm↓` 就要 "带路径" 对世界**反**单调. 对实例它不成立: 坐标为 $1$ 的第 2 层种类的结点在界 $3$ 里带路径, 在界 $1$ 里不带 (要 $2\lhd 1$). 所以可入改成 "有更大的世界 $V$, 坐标在 $V$ 里带路径", 进入后世界换成 $V$ (`X1UpFold.StepPS`). 前提 $1\lhd 3$ 是 `hsuc (hsuc hself)`.

```agda
-- hs (hs hz) ⊲ hs hz, 即 2 ⊲ 1
no21 : _⊏ᶜ_ (hs hz) (hs hz) → ⊥
no21 (hsuc ())

cy : HB XS₁
cy = hΩ (inj₂ (hs hz) , inj₂ tt) (λ _ → hz)

naive-anti : (∀ {W W′} → W ≼₁ W′ → ∀ c → PHg base W′ c → PHg base W c) → ⊥
naive-anti f = no21 (proj₁ (f {hs hz} {hs (hs (hs hz))} (hsuc (hsuc hself)) cy (hsuc hself , λ _ _ → tt)))
```

## 行数 (定义级切片)

`Survey/scripts/x1up/locslice_x1up.py` (口径同 `pathout/locslice_pathout.py`; `X1UpFold`, `PathOutFold`, `TySupFold` 经模块应用使用, 模块内定义手工列根, 近似). 2026-11-05 跑出 (主闭项 `TU2`, 括号里是 `TU1`):

| 层 | 本路新增 (`X1Up*`) | PathOut 承接 | 树侧全部 (累计) | 记号模块 |
|---|---|---|---|---|
| 1 定义 (接口 `PathOutIf`+`X1UpIf`, 层号 $X_1$ 与叠层 `LS`, 世界与证据, `Lv`, `KS`/`HB`/`step`/`sup`) | 39 | 65 | 501 | 0 |
| 2 + 折叠 (`ΦU`, `decU`, 上层路径 `PSL` 与 `PH-ΦU`, `Ψ`, `dec₁`, `shift₁`, 可数层号的 `Φ`, 实例 `IU`, 闭项, FGH) | 364 (355) | 230 (225) | 1101 (1087) | 0 |
| 3 + 证书 (`Sh-Ψ`, `LgB-TU2`, 地板合法 `Lg-topU`, `Lg-topL`) | 374 (366) | 230 | **1111** (1103) | 0 |
| 4 + 形状 (`okU`, `nonflat1`) | 406 (398) | 230 | 1143 (1135) | 0 |

- **对照 (前 3 层累计, 同口径, 取自各自文件).** PathOut 743 (读 ψ₀(Ω_Ω)), FabLFReGen 1513 (读法是判断). 本路 1111 (读 ψ₀(Ω_{Ω·2}), 判断), 比 PathOut 多 368 行. 跨读法的行数不作比较结论.
- **累加, 如实.** 层 2 里 `X1UpFold` 的折叠本身 (`LS`, `topU`, 两类种类, 嵌入, `decU`, `ΦU`, `ΦX`, 连同闭包) 80 行; **路径独有 216 行** (`PS` 的 `step`/`sup` 搭法, `PSL`, 单调与加法, 地板的路径, 搬运引理 `clP`/`upkE`/`upkA`, `PH-ΦU`). 闭项 `TU` 要路径作 `Ψ` 的参数, 所以路径在定义层就被拉进来 (同 PathOut 的 `PH-topL`). 对角 `yU` 要上一个输出的 `LgB` (`lg-yU`, 经 `LgB-TU`), 所以层 2 已含证书的一部分 (同 `TySupSum.yΣ`).
- 层 1 的 501 比 PathOut 的 334 多, 主要因为接口字段 `PH-topX` 引用 `PathOutFold.PH`, 切片把 `PathOutFold` 的模块头 (`open F R`) 一并算进 (切片的近似).

## 翻译账

- **新结点, 新字段.** 无新结点. 叠层 `LS m` 是 `step`/`sup` 塔 (与 `LFReTy.Lv` 同式). 新字段: 世界的序与三条律 (`X1UpIf`), 地板 `topX`. 新的规则: 底种类一律留, 新种类按层号比较 (与 TySupC 相同的比较, 只加 "底种类" 一类).
- **由树逼出.** (1) 世界的序与 `PH-mono`: 上层折叠把当前界传进留下的 $\Omega_1$ 结点的分支, 分支的世界是 `nxt`, 界的路径要搬过去 (`PH-⊞` 也要它). (2) 新种类的可入是 Kripke 式: 朴素写法要 "带路径" 反单调, 对实例不成立 (`naive-anti`, 定理). (3) 搬运只要序不要相等: 输入侧与目标侧的世界各自沿递归归到底种类的世界, 两边都只差一个 $\preceq$ (`clP`, `upkE`, `upkA`), 由 (1) 搬过去; 这是 PathOut 接手清单第 1 条卡点的处理. (4) 链的起点是地板: 否定一路的提醒 (从 $0$ 起步则 "同层" 的链无结点), `nonflat1` 是对实例的定理.
- **受记号启发, 如实.** 读法 ψ₀(Ω_{Ω_1+m}), ψ₀(Ω_{Ω·2}) 是对照扩展 Buchholz 记号的判断; 对角的不动点迭代形状同 TySup 的 `TΩΩ`.
- **摆脱侧.** 没有读记号的基本列规则; 叠层的折叠就是 `TySupFold.Φ` 对 "带底的可数层号" 的同式推广; 新的东西都是路径的律 (序, 单调, Kripke 可入), 都由树侧的要求说出 (上面 (1)(2)). 但路径机制的行数是折叠本身的 2.7 倍, 这是本路加深的那部分脚手架 (判断: 是 "带证据的决定" 的代价, 不是翻译带来的).
- **攀爬侧.** 读法从 ψ₀(Ω_Ω) 升到 ψ₀(Ω_{Ω·2}) (判断).

## 接手清单

1. **统一两个折叠.** 现在有两段折叠: `PathOutFold.Ψ` (`lΩ` 层号 $X_1$ 折到可数层号, 可数部分用 `TySupIf`) 与 `X1UpFold.ΦU` (底上的可数叠层折到底). 下一站 (层号 $\Omega_{\Omega_1\cdot 2}$ 作 `lΩ` 结点, 即 $X_2=$ `lΩ lz (λ c → ls (ofU c))`) 要一个 `Ψ`, 它的 "在上" 之后用的可数部分是 `ΦU` (带底), 不是 `TySupIf` (`noK` 排除带底的层). 要把 `TySupIf` 推广成 "带底的可数层号" (本篇的 `ΦU` 就是这个推广的一个实例), 再把 `PathOutIf` 的 `R` 换成它; 路径要沿底种类与 `PSL` 一起传. 判断: 这是到 Λ 的反复的一步, 写成一个对层号 `LH` 递归的折叠才不会每站重写.
2. **值的定理.** 没有. `TU1` 与 `PathOut.TXL` 的序数值关系要比较 `Ψ` 在两个字面不同的输入上的输出; `Ψ` 的输出依赖路径证明 (路径不是命题, `NegPathOutPath.paths-not-prop`), 直接的 `≡` 要函数外延与依赖相等, 本路没做.
3. **接口盲区.** "地板的根是结点" 不是律 (`NegX1UpIf.flatTopOf`); 新种类的 Kripke 世界不要求合法 (否定一路的 `cJ` 边界: 只在不合法世界里带路径的值也可入). 两者都不影响实例的闭项 (最终交给 `Ψ` 的是第 $X_1$ 层的 `PH W₀`, 里面没有新种类), 判断.
4. **上层输出的 `LgB`.** 不成立 (否定一路报告, 见代价 (3)); 中间层只有路径与形状. 若下一站的 `Ψ` 要输入合法, 要换不累加或单调的上层折叠.

## 结论 (按档)

- **[定理]** 接口 `X1UpIf` (律带字面世界序证据); 对一切 `U`: 上层折叠 `ΦU`, `ΦX`, 地板合法 `Lg-topU`, 路径结构 `PSL` (每层满足三条律), `PH-mono`, `PH-⊞`, `PH-chain`, `PH-topU`, 搬运引理 `clP`, `upkE`, `upkA`, **`PH-ΦU`**, **`PH-ΦX`**; 实例 `IU` (`ev↑₁`, `adm↓₁`, `≼-nxt₁`); 闭项 `TU`, `TU1`, **`TU2`**, 证书 `LgB-TU`, **`LgB-TU2`**, FGH `fghU1`, `fghU2`; 决定正确 `okU`; `root1`, `keepΩ`, `nonflat1`; 否定 `naive-anti`.
- **[判断]** 读法: `TU1` ψ₀(Ω_{Ω_1+1}), `TU m` ψ₀(Ω_{Ω_1+m}), `TU2` ψ₀(Ω_{Ω·2}), 越过 ψ₀(Ω_Ω); 累加不改读法; 接手清单第 1 条的推广方向.
