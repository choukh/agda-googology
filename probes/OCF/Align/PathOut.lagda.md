# 路径记在折叠输出上: 带类型折叠到 `lΩ` 层号 (入口)

> 不含记号. 构造一路 PathOut (配对否定一路 NegPathOut), 2026-11-05. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 不改任何已有文件.
>
> 文件: 接口 [PathOutIf](PathOutIf.lagda.md) (定稿 23:16), 折叠 [PathOutFold](PathOutFold.lagda.md) (对一切满足接口的 `P`), 实例 [PathOutX1](PathOutX1.lagda.md) (层号 $X_1$), 本篇 (闭项, 证书, FGH).
>
> **这一篇做什么.** 作者本轮选定 "①(b): 路径记在折叠输出上": 层号 `LH`/`Lv` 与种类不动, 只把折叠的输入输出改成 "带路径的高度". 依据 [Fab4LOm](Fab4LOm.lagda.md): 在 `lΩ` 层号上, 裸坐标的精确决定推出分离子 (`exact→Sep`), 带同一界之下的路径时决定可归到子层 (`om-step`). 本路的做法:
>
> 1. **接口** `PathOutIf`: 世界 (界 $B$), 目标证据 `Tg` ($t\lhd B$), 种类证据 `Ev` ($y+1\lhd B$, $y$ 是种类的坐标), 进入分支的坐标可入 `Adm` 与新世界 `nxt`, 带路径的回灌 `shift`, 决定 `dec` (两个下标都带相对同一世界的证据), **决定正确** `correct` (留 ⇒ 层号严格在目标下; 同层 ⇒ 层号就是目标; 在上 ⇒ 报的层就是层号). 回应 `NegTySupC.blind-TC`: 常值决定不满足 `correct`.
> 2. **折叠** `PathOutFold.Ψ`: 输入是高度加路径 `PH W h` (每个结点的种类带 `Ev`, 每个可入的分支在 `nxt` 世界里递归地带路径). 与 `TySupFold.Φ` 逐子句对应, 进分支时坐标先 `shift`, 世界换 `nxt`. "在上" 之后从第 $i$ 层折到目标用可数层号的 `TySupFold.Φ`. 输出由形状合法 (`Sh-Ψ`).
> 3. **实例** `PathOutX1.IX₁`: 层号 $X_1=$ `lΩ lz (λ c → ls (ofC c))` (就是 `Fab4LOm.X₁`). 公共上界是世界的界 $B$; $\Omega_1$ 结点的分支坐标 $c\mapsto B\boxplus\mathrm{leg}\,c$ (回灌不再是恒等), 进入后世界换成 $y+1$. `correct₁` 是定理.
> 4. **闭项** `TXL` (主闭项): $X_1$ 的合法地板 `topL` ($\Omega_1$ 结点, 分支 $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{c+1}$) 折到第 0 层; 输入合法 (`Lg-topL`, 回应否定一路 `NegPathOutInst.¬LgB-topX₁`) 且带路径 (`PH-topL`, 对一切世界); 证书 `LgB-TXL` (标准 `LgB`), FGH `fghXL`. 早先的 `TX₁` (地板 `topX₁` $=\sup_c\Omega_{c+1}$, 带路径但**不合法**) 保留作对照.
>
> **读法 (判断, 没有值的定理).** `TXL` (与 `TX₁`) 读 ψ₀(Ω_{Ω_1}) (按 TySup 的约定 ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加累加): 链 $d_{n+1}=d_n\boxplus\psi_0(\Omega_{1+\mathrm{leg}(b\boxplus d_n)+1})$ 是 $\alpha\mapsto\psi_0(\Omega_\alpha)$ 的不动点迭代. 这与 `TySup.TΩΩ` 的读法 ψ₀(Ω_Ω) **相同** (Ω = Ω_1); 本路**没有越过** ψ₀(Ω_Ω). 新的是: 同一个序数现在由一个 `lΩ` 层号的地板经带类型折叠得到, 留/坍缩的决定对带证据的种类正确 (定理), 而不是由可数层号的对角得到.
>
> **代价, 如实.** (1) **累加两处**: `Ψ` 的 ℕ-极限取部分和 (同 TySupFold); `leg` 把回灌的坐标的 ℕ-极限取部分和 (新增). 后者改变进入的坐标的值 (对相邻项相等的极限给 $x\cdot\omega$), 坐标在 $\Omega_1$ 之下共尾, 读法不变是判断. (2) **坐标接在界后** ($B\boxplus\cdot$): 分支在 $\{B\boxplus c\}$ 上取, 共尾不变是判断. (3) **只到 $X_1$.** 下一步 $X_1\oplus m$ (`ls`/`ll` 叠在 $X_1$ 上, 读 ψ₀(Ω_{Ω_1+m}), 对角读 ψ₀(Ω_{Ω_1·2})) 要一个保留 $X_1$ 种类的上层折叠, 并证明它的输出带路径 (接手清单第 1 条); 本路没有写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.PathOut where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.TySupC using (Cd; LC)
open import OCF.Align.TySupSum using (topΣ; ICdΣ; Lg-topΣ)
open import OCF.Align.TySup using (ord⊥)
import OCF.Align.TySupFold as F
open import OCF.Align.PathOutIf using (DcP; keep; same; above; OkP)
open import OCF.Align.PathOutX1
open import OCF.Align.TySupC using (_⊏ᶜ_)
open import Data.Empty using (⊥)
import OCF.Align.PathOutFold as PF
open PF IX₁ using (PH; Ψ; Sh-Ψ)
import OCF.Free.Level as FLv
```

## §1 $X_1$ 的地板与它的路径

`topX₁` $=\sup_c\Omega_{c+1}$: $\Omega_1$ 种类的结点, 坐标 $c$ 处的分支是第 $c+1$ 层的地板, 经 `ι (inj₂ c)` 放进 `Lv X₁`. 它带路径 (`PH-top`, 对一切世界): $\Omega_1$ 结点的分支在坐标 $y$ 处进入世界 $y+1$, 里面一切种类的坐标都是 $y$, 证据 $y+1\lhd y+1$ 是 `hself`.

```agda
topX₁ : HB XS₁
topX₁ = hΩ κΩ (λ c → ι (inj₂ c) (topΣ (hs c)))

PH-ι : ∀ y (h : HB (LC (hs y))) → PH (hs y) (ι (inj₂ y) h)
PH-ι y hz = tt
PH-ι y (hs h) = PH-ι y h
PH-ι y (hl f) = λ n → PH-ι y (f n)
PH-ι y (hΩ κ g) = hself , (λ e a → PH-ι y (g e))

PH-top : ∀ B → PH B topX₁
PH-top B = tt , (λ y a → PH-ι y (topΣ (hs y)))
```

## §2 闭项, 证书, FGH

`TX₁`: $X_1$ 的地板折到第 0 层, 初始世界 $B=1$, 当前界 $0$. 第 0 层没有种类, `Sh` 就是 `LgB`.

```agda
W₀ : Cd
W₀ = hs hz

lW₀ : LgW₁ W₀
lW₀ = tt , hself

TX₁ : HB S⊥
TX₁ = Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz topX₁ (PH-top W₀)

sh→lgB₁ : ∀ h → F.Sh ICdΣ {S⊥} h → LgB h
sh→lgB₁ hz s = tt
sh→lgB₁ (hs h) s = sh→lgB₁ h s
sh→lgB₁ (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lgB₁ (f n) (s n))
sh→lgB₁ (hΩ () _) s

LgB-TX₁ : LgB TX₁
LgB-TX₁ = sh→lgB₁ TX₁ (Sh-Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz topX₁ (PH-top W₀))

fghX₁ : ℕ → ℕ
fghX₁ = FLv.FGH (ord⊥ TX₁)
```

## §2′ 合法的地板 (θ 形)

否定一路 `NegPathOutInst.¬LgB-topX₁`: `topX₁` 带路径但不合法 (分支 $0$ 与 $1$ 落在 `Lv X₁` 的不同分量, 不是第一位置), 所以 `TX₁` 是 `Ψ` 用在不合法的输入上 (`LgB-TX₁` 来自 `Sh-Ψ`, 不看输入). 同 `TySupSum` 修 `topC`: 把分支写成接起来的形状 $g\,0=0$, $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{c+1}$, $g(\lim f)=\lim(g\circ f)$ (`HtTowerU.θ` 的形状; 否定一路的 `top′` 也是这个). 合法 (`Lg-topL`, 对 $\Omega_1$ 结点的单调由形状给出), 带路径 (`PH-topL`, 对一切世界): 分支 $g\,y$ 里的种类坐标都严格在 $y$ 之下, 进入后世界是 $y+1$.

```agda
gt : HB S⊥ → HB XS₁
gt hz = hz
gt (hs c) = gt c ⊞ ι (inj₂ c) (topΣ (hs c))
gt (hl f) = hl (λ n → gt (f n))
gt (hΩ () _)

topL : HB XS₁
topL = hΩ κΩ gt

gt-⊲ : ∀ {a b} {w : Wd XS₁} → a ⊲[ tt ] b → gt a ⊲[ w ] gt b
gt-⊲ hself = hself
gt-⊲ (hsuc {b = b} p) = ⊲ᴮ-tr (gt-⊲ p) (⊞-fst (gt b) (ι (inj₂ b) (topΣ (hs b))))
gt-⊲ (hlim n p) = hlim n (gt-⊲ p)
gt-⊲ (hLim {κ = ()} _ _)

Lg-gt : ∀ c → LgB c → LgB (gt c)
Lg-gt hz l = tt
Lg-gt (hs c) l = Lg-⊞ (gt c) (ι (inj₂ c) (topΣ (hs c))) (Lg-gt c l) (Lg-ι (inj₂ c) (topΣ (hs c)) (Lg-topΣ (hs c)))
Lg-gt (hl f) (st , l) = (λ n → gt-⊲ (st n)) , (λ n → Lg-gt (f n) (l n))
Lg-gt (hΩ () _) l

Lg-topL : LgB topL
Lg-topL = (λ lw e e′ p → gt-⊲ p) , Lg-gt

PH-⊞ι : ∀ {W} a c (h : HB (LC (hs c))) → PH W a → hs c ⊲[ tt ] W → PH W (a ⊞ ι (inj₂ c) h)
PH-⊞ι a c hz pa q = pa
PH-⊞ι a c (hs h) pa q = PH-⊞ι a c h pa q
PH-⊞ι a c (hl f) pa q = λ n → PH-⊞ι a c (f n) pa q
PH-⊞ι a c (hΩ κ g) pa q = q , (λ e _ → PH-⊞ι a c (g e) pa q)

PH-gt : ∀ y W → y ⊲[ tt ] W → PH W (gt y)
PH-gt hz W q = tt
PH-gt (hs c) W q = PH-⊞ι (gt c) c (topΣ (hs c)) (PH-gt c W (⊲ᴮ-tr (hsuc hself) q)) q
PH-gt (hl f) W q = λ n → PH-gt (f n) W (⊲ᴮ-tr (hlim n hself) q)
PH-gt (hΩ () _) W q

PH-topL : ∀ B → PH B topL
PH-topL B = tt , (λ y a → PH-gt y (hs y) (hsuc hself))

-- 输入合法的闭项
TXL : HB S⊥
TXL = Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz topL (PH-topL W₀)

LgB-TXL : LgB TXL
LgB-TXL = sh→lgB₁ TXL (Sh-Ψ W₀ lW₀ hz (z⊲ᴮ W₀) hz topL (PH-topL W₀))

fghXL : ℕ → ℕ
fghXL = FLv.FGH (ord⊥ TXL)
```

## §3 字面事实 (定理, refl)

**决定.** 根结点 ($\Omega_1$ 种类) 对目标 $0$ 是同层, 读回恒等. 坐标 $y=2$ 的 "第 3 层新种类" (层号 $2$) 在世界 $B=3+1$ 里对目标 $0$ 是在上, 报的层就是 $2$.

```agda
dec-root : dec₁ W₀ hz lW₀ (z⊲ᴮ W₀) κΩ tt ≡ same (λ c → c)
dec-root = refl

private
  two three four : Cd
  two = hs (hs hz)
  three = hs two
  four = hs three

  lW₄ : LgW₁ four
  lW₄ = tt , hsuc (hsuc (hsuc hself))

  IsAbove : ∀ {C L _⊑_ LgC XS Tn t κ} → DcP {C} L _⊑_ LgC XS Tn t κ → Set
  IsAbove (above _ _ _ _ _) = ⊤
  IsAbove (keep _ _) = ⊥
  IsAbove (same _) = ⊥

  lv-two : lvX₁ (inj₂ two , inj₂ tt) ≡ two
  lv-two = refl

  dec-above : IsAbove (dec₁ four hz lW₄ (z⊲ᴮ four) (inj₂ two , inj₂ tt) (hsuc hself))
  dec-above = tt

  ok-above : OkP _⊏ᶜ_ two (dec₁ four hz lW₄ (z⊲ᴮ four) (inj₂ two , inj₂ tt) (hsuc hself))
  ok-above = correct₁ four hz lW₄ (z⊲ᴮ four) (inj₂ two , inj₂ tt) (hsuc hself)
```

## 行数 (定义级切片)

`Survey/scripts/pathout/locslice_pathout.py` (口径同 `tysup/locslice_tysup.py`; `PathOutFold` 与 `TySupFold` 经模块应用使用, 模块内定义手工列根, 近似). 2026-11-05 跑出:

| 层 | 本路新增 | 树侧全部 (累计) | 记号模块 |
|---|---|---|---|
| 1 定义 (接口, 层号 $X_1$, 世界与证据, `Lv`, `KS`/`HB`/`step`/`sup`) | 57 | 334 | 0 |
| 2 + 折叠 (`Ψ`, `dec₁` 含 `cmpB`, `shift₁`/`leg`, 可数层号的 `Φ`, 地板 `topL`, 闭项 `TXL`, FGH) | 217 | 696 | 0 |
| 3 + 证书 (`Sh-Ψ`, `Lg-topL`, `PH-topL`, `LgB-TXL`) | 236 | 743 | 0 |
| 4 + 形状 (`dec-root`) | 238 | 745 | 0 |

闭项与对照闭项 `TX₁` 不在切片的根里. 层 2 已含 `PathOutX1` 的全部 103 行: 实例记录 `IX₁` 的字段包括律 (`lg-nxt₁`, `tg-nxt₁`, `adm-shift₁`, `correct₁`), 闭项经 `IX₁` 用到折叠, 所以这些律在定义层就被拉进来. 本路的 `correct` 是接口字段, 定义 `TX₁` 要它; 这是 "决定正确进接口" 的行数代价 (`correct₁` 与 `okΩ`, `okI` 约 20 行).

对照 (前 3 层, 同口径, 各自的切片; 对照的数取自各自文件): TySup 504 (读法 ψ₀(Ω_Ω), 可数层号的对角), 1295, FabLFReGen 1513 (读法与 ψ₀Λ 候选的读法都是判断). 本路 743 的读法 ψ₀(Ω_{Ω_1}) (判断), 与 TySup 的读法相同; 多出的 239 行买的是 "经 `lΩ` 层号, 决定带证据且正确". 跨读法的行数不作比较结论.

## 翻译账

- **新结点, 新字段.** 无新结点, 层号与种类不动. 接口字段: 世界的界 (Fab3Typed 的世界, TySup 的当前界), 两种证据 ($t\lhd B$, $y+1\lhd B$; `om-step` 与 `cmpB` 要的字面公共上界), `shift` ($B\boxplus$, `⊞-fst` 给路径; Fab4LOm §5 的出口), `correct` (`NegTySupIf.Ok`). 都是树侧的东西; 没有读记号的基本列规则.
- **由树逼出.** (1) 证据要相对同一世界: `exact→Sep`. (2) 留下的 $\Omega_1$ 结点在输出里对一切坐标有分支, 输入的分支要在带路径的坐标处取: 这就是 `shift`; 没有它, 那里的种类坐标与目标无公共上界 (NegPathOut 的提醒). (3) 证据的方向: 先试 "种类坐标在界之上" ($B\lhd y$), 公共上界只能是 $y+1$, 而 $y+1\lhd B+1$ 不是字面路径 (编译报错 `y != hs y`); 改成两边都在界之下 ($t\lhd B$, $y+1\lhd B$), 公共上界就是 $B$. (4) `leg`: 进入的坐标要合法 (`cmpB` 要 `LgB` 的界), 输入的坐标是任意树, 部分和给出形状合法.
- **受记号启发, 如实.** 读法 ψ₀(Ω_{Ω_1}) 是对照 Buchholz 式记号的判断. `Lv` 的形状 LFReTy 已自述为记号引导.
- **摆脱侧.** 相对 FabLFReGen/GenFold: 没有数据树, 状态, 读回, 升界; 相对 TySup: 同一个折叠骨架推到 `lΩ` 层号, 新增的只是证据与 `shift`. 本路没有读记号.
- **攀爬侧.** 读法不升 (ψ₀(Ω_{Ω_1}), 与 TySup 相同).

## 接手清单

1. **$X_1\oplus m$ (越过 ψ₀(Ω_Ω) 的第一步).** 层号 `ofU x` ($X_1$ 上叠可数层号 $x$), 种类结构 `Lv (ofU x)` = $X_1$ 的种类 (底) 加新种类. 要: (a) 上层折叠 (同 `TySupFold.Φ`, 底种类一律留, 新种类按可数层号比较; `TySupIf` 不能直接实例化, 因为 `noK`: 第 0 号层号有底种类); (b) 上层输出带路径 `PHU`, 再交给 `Ψ`. 卡点 (判断, 未编译): 留下的底种类在目标层里的种类 `embB t κ₀` 与输入的种类经不同的递归到达同一个 `Ev₁`, 证据要沿嵌入搬运 (`ev-emb`, `adm-back`, `nxt-emb`), 对变量层号不是 refl. `PH` 对世界的单调 (证据同向, 见 `PathOutX1` 文首) 是 `⊞` 保路径要的; 本路选同向证据正是为了它.
2. **一般的 `lΩ k g`** (到 Λ): 实例的 $\Omega_{k+1}$ 坐标是 `HB (Lv k)` (含 $\Omega$-结点), `leg` 只在第 0 层由形状给合法; 高层要 `Sh` 与 `LgB` 的差 (`NegTySupC.kept-not-LgB-ICd`).
3. **值的定理.** 没有. 先试 `TX₁` 与 `TySupSum.TΩΩΣ` 的序数值关系.
4. **`correct` 的盲区.** `correct` 不管回灌 (`same` 的 `to` 可以是常值而 `correct` 仍成立); 可请否定一路对它写盲定理.

## 结论 (按档)

- **[定理]** 接口 `PathOutIf` (律带相对同一世界的证据, 含 `correct`); 折叠 `PathOutFold.Ψ`, `PH`, `Sh-Ψ` (对一切 `P`); 实例 `IX₁` 与 `correct₁` (决定正确), `Lg-leg`; 合法地板 `topL`, `Lg-topL`, `PH-topL`; 主闭项 `TXL`, 证书 `LgB-TXL`, FGH `fghXL`; 对照闭项 `TX₁` (输入不合法, 否定一路 `¬LgB-topX₁`), `LgB-TX₁`, `PH-top`; `dec-root`, `dec-above`, `ok-above`.
- **[判断]** 读法 ψ₀(Ω_{Ω_1}) (与 TySup.TΩΩ 相同, 未越过 ψ₀(Ω_Ω)); `leg` 与 $B\boxplus$ 不改读法; 接手清单第 1 条的卡点.
