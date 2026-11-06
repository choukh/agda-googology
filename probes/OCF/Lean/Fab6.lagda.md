# Fab6: 外部种类 — 跨底的证据变成分支的类型 (入口)

> 不含记号. Fable 第六轮自选, 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 导入闭包只有 stdlib 与 `OCF.Lean.Fab6*`. 不改任何已有文件.
>
> | 文件 | 内容 | 参考 (只作参考, 未拷贝) |
> |---|---|---|
> | [Fab6Base](Fab6Base.lagda.md) | 种类结构 `KS`, **外部种类 `XK`**, 高度 `HB X S` (多一个构造子 `hE`), 第一位置, 合法, `cmpB`, `⊞`, `step`, `sup`, `up`, `ι`, `S⊥`, `X⊥`, `Cd` | `CRwBase` |
> | [Fab6Fold](Fab6Fold.lagda.md) | 塔 `Tw`, 种类分类与嵌入, 决定 `pick`, 地板 `topT`, 可达性, 累加, **同底折叠 `Φ`** (对一切 `X`, `S`), 形状 `Sh-Φ` | `CRwFold` 的同底部分 |
> | 本篇 | 外部种类 `X₁`, 合法化 `leg`, 地板 `topL`, **跨底折叠 `ΦX`**, 闭项 `TX`, `TU`, `TU2`, 证书, FGH (CRw 的 $X_1$ 站, 用来对照与测试) | `CRw` §1, §3; `CRwFold` 的 `cx` 子句 |
> | [Fab6Lay](Fab6Lay.lagda.md) | **层的代数**: 层 = (外部种类, 地板, 这一层自己的折叠) `FL`; 算子 `ext`, `supL`, `diag`; 闭项与证书对一切层一条 (`clL`, `Lg-clL`); 沿 Cd 迭代 `It`, `pow`, `P`, `Pc`; 闭项到 `TΩ^Ω` | 无 (新) |
> | [Fab6Cmp](Fab6Cmp.lagda.md) | 与 CRw 闭项的有限测试; 层的代数的闭项的结点数 (验收文件, 导入 CRw) | — |

## §0 这一步是什么, 为什么

**作者的担心** (原话): "后选树的前 3 层已经非常接近标杆了. 如果后续不大幅压缩, 或者找出树的语言和来自自身的后路指引, 即使闭项写出来, 也没有太大意义." 本轮两路在跑攻击 (ψ₀Λ 候选) 与值 (P2), 我选**压缩与树的语言**这一侧, 对象是 C 线压缩后的 `CRw` (前 3 层 696).

**CRw 里最大的一块脚手架是路径** (239 行, 34%; `CRw` §5): 跨底折叠 ($\Omega_1$ 层折到可数层号) 要把 `XS` 的种类 $(c,\kappa)$ 的层号 $c+1$ 与目标 $t$ 带字面公共上界比较 (壁垒), 公共上界是世界 $B$; 所以每个结点要带证据 $c+1\lhd B$, 进入 $\Omega_1$ 结点在坐标 $e$ 处的分支时世界换成 $e+1$, 这些证据要沿同底折叠搬运 (`PH-ΦX`, 192 行), 叠层新种类的可入要 Kripke 式. 换句话说, CRw 用一个**命题** `PH B h` 说 "树 $h$ 里坐标 $y$ 处的分支只用层号 $\le y$ 的种类".

**本路把这个命题变成类型.** $\Omega_1$ 层的 $\Omega_\Omega$ 结点不再是 "种类结构 `XS` 的一个普通种类", 而是一个**外部种类** (`XK`): 坐标是可数树 $y$, 坐标 $y$ 处的分支的**类型**是 `HB X⊥ (Tw X⊥ S⊥ y)`, 即高度 $y$ 的塔上的树. 分支里的种类是塔里的位置 ($j+1\lhd y$), 比较只用 `cmpB` 以 $y$ 为公共上界, 不需要世界. 于是:

- 跨底折叠 `ΦX` 只处理一种结点 (`hE`), 决定只比较位置 $1$ ($\Omega_1$) 与目标 $t$, 公共上界是输入的界 $B$ ($t\lhd B$, $1\lhd B$); 分支在坐标 $B\boxplus\mathrm{leg}\,c$ 处取, 由**同底折叠**从高度 $B\boxplus\mathrm{leg}\,c$ 折到 $t$ (目标在高度之下: $t\lhd B\lhd B\boxplus\mathrm{leg}\,c$).
- 没有 `PH`, `PS`, `Po`, `pX`, `Nd`, Kripke 式可入, `PH-ΦX`, 地板的路径. 接口 `CRwIf` 的 7 个字段也不需要: 世界的移动只剩一条字面的算式 $B\boxplus\mathrm{leg}\,c$.
- 同底折叠对一切外部种类一份: 外部结点原样留下, 只折前缀 (`Φ` 的 `hE` 子句, 一行).

外部结点带前缀 (`hE x p g` 读 $p+\Omega_x(g)$), 使 `⊞` 与第一位置 `⊞-fst` 对它成立: 位置进前缀, 不进分支.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fab6 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Lean.Fab6Base
open import OCF.Lean.Fab6Fold
```

## §1 外部种类 $X_1$ 与合法化

```agda
X₁ : XK
X₁ = record { KX = ⊤ ; EX = λ _ → Cd ; Br = λ _ y → HB X⊥ (Tw X⊥ S⊥ y) ; LgBr = λ _ y → LgB }
```

`leg` 同 CRw: 可数树的 ℕ-极限换成部分和, 输出合法 (累加, 如实; 用处是让回灌后的高度 $B\boxplus\mathrm{leg}\,c$ 合法, `cmpB` 要合法的界).

```agda
Σ₀ : (ℕ → Cd) → ℕ → Cd
Σ₀ f zero = f 0
Σ₀ f (suc n) = Σ₀ f n ⊞ f (suc n)

leg : Cd → Cd
leg hz = hz
leg (hs x) = hs (leg x)
leg (hl f) = hl (Σ₀ (λ n → leg (f n)))
leg (hΩ () _)
leg (hE () _ _)

Lg-leg : ∀ x → LgB (leg x)
Lg-Σ₀ : ∀ f n → LgB (Σ₀ (λ m → leg (f m)) n)
Lg-leg hz = tt
Lg-leg (hs x) = Lg-leg x
Lg-leg (hl f) = (λ n → ⊞-fst (Σ₀ (λ m → leg (f m)) n) (leg (f (suc n)))) , Lg-Σ₀ f
Lg-leg (hΩ () _)
Lg-leg (hE () _ _)
Lg-Σ₀ f zero = Lg-leg (f 0)
Lg-Σ₀ f (suc n) = Lg-⊞ _ (leg (f (suc n))) (Lg-Σ₀ f n) (Lg-leg (f (suc n)))
```

## §2 地板

$\Omega_\Omega$ 的地板: 外部结点, 前缀 $0$, 坐标 $y$ 处的分支是高度 $y$ 的塔的地板 `topT X⊥ S⊥ hz y` (读 $\Omega_y$). 与 CRw 的 `gt y` ($\sum_{c<y}\iota_c\Omega_{c+1}$) 的差: 这里分支不累加, 因为外部结点的合法 (`LgB (hE …)`) 只要求每个分支在自己的层上合法, 不要求分支对坐标单调 (位置进不了分支, 没有什么要单调).

```agda
topL : HB X₁ S⊥
topL = hE tt hz (topT X⊥ S⊥ hz)
```

## §3 跨底折叠

`brX B lB t pt s g c`: 坐标 $c$ 处的分支, 由同底折叠从高度 $B\boxplus\mathrm{leg}\,c$ 折到 $t$, 种子 $s$. `nodeX`: $\Omega_\Omega$ 结点的决定, 由 `cmpB` 比较位置 $1$ 与 $t$ (公共上界 $B$) 的结果读出: $1\lhd t$ 留成第 $t$ 层塔里位置 $0$ 的新种类 (`along`); $t=1$ 留成 `inj₂ tt`; $t=0$ 同层, 取回灌链. 没有 "在上" ($t\lhd 0$ 不可能, 由 `t ⊲ hs hz` 的两个构造子穷尽). 留下的结点的每个分支加上前缀折出的值 `bp`.

```agda
brX : ∀ B → LgB B → ∀ t → t ⊲ B → HB X⊥ (Tw X⊥ S⊥ t) → ((y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) → Cd → HB X⊥ (Tw X⊥ S⊥ t)
brX B lB t pt s g c =
  Φ (B ⊞ leg c) (wf _) (Lg-⊞ B (leg c) lB (Lg-leg c)) t (⊲ᴮ-tr pt (⊞-fst B (leg c))) s (g (B ⊞ leg c))

nodeX : ∀ B → LgB B → ∀ t → t ⊲ B → (b bp : HB X⊥ (Tw X⊥ S⊥ t)) → ((y : Cd) → HB X⊥ (Tw X⊥ S⊥ y)) →
        (t ⊲ hs hz) ⊎ (hs hz ⊲ t) → HB X⊥ (Tw X⊥ S⊥ t)
nodeX B lB t pt b bp g (inj₂ q) = hΩ (along q) (λ c → bp ⊞ brX B lB t pt b g (frA q c))
nodeX B lB _ pt b bp g (inj₁ hself) = hΩ (inj₂ tt) (λ c → bp ⊞ brX B lB (hs hz) pt b g c)
nodeX B lB _ pt b bp g (inj₁ (hsuc hself)) = hl (chain bp (λ c → brX B lB hz pt c g c))

ΦX : ∀ B → LgB B → hs hz ⊲ B → ∀ t → t ⊲ B → HB X⊥ (Tw X⊥ S⊥ t) → HB X₁ S⊥ → HB X⊥ (Tw X⊥ S⊥ t)
ΦX B lB o t pt b hz = hs hz
ΦX B lB o t pt b (hs h) = hl (mul (ΦX B lB o t pt b h))
ΦX B lB o t pt b (hl f) = hl (Σ⁺ (λ n → ΦX B lB o t pt b (f n)))
ΦX B lB o t pt b (hΩ () _)
ΦX B lB o t pt b (hE _ p g) = nodeX B lB t pt b (ΦX B lB o t pt b p) g (cmpB o pt tt lB)
```

形状给出的合法 (`Sh`), 同 `Sh-Φ`.

```agda
Sh-brX : ∀ B lB t pt s g c → Sh (brX B lB t pt s g c)
Sh-brX B lB t pt s g c = Sh-Φ (B ⊞ leg c) (wf _) (Lg-⊞ B (leg c) lB (Lg-leg c)) t (⊲ᴮ-tr pt (⊞-fst B (leg c))) s (g (B ⊞ leg c))

Sh-nodeX : ∀ B lB t pt b bp g d → Sh bp → Sh (nodeX B lB t pt b bp g d)
Sh-nodeX B lB t pt b bp g (inj₂ q) sp = λ c → Sh-⊞ bp _ sp (Sh-brX B lB t pt b g (frA q c))
Sh-nodeX B lB _ pt b bp g (inj₁ hself) sp = λ c → Sh-⊞ bp _ sp (Sh-brX B lB (hs hz) pt b g c)
Sh-nodeX B lB _ pt b bp g (inj₁ (hsuc hself)) sp = Sh-chain bp _ (λ c → Sh-brX B lB hz pt c g c)

Sh-ΦX : ∀ B lB o t pt b h → Sh (ΦX B lB o t pt b h)
Sh-ΦX B lB o t pt b hz = tt
Sh-ΦX B lB o t pt b (hs h) = Sh-mul _ (Sh-ΦX B lB o t pt b h)
Sh-ΦX B lB o t pt b (hl f) = Sh-Σ _ (λ n → Sh-ΦX B lB o t pt b (f n))
Sh-ΦX B lB o t pt b (hΩ () _)
Sh-ΦX B lB o t pt b (hE _ p g) = Sh-nodeX B lB t pt b _ g (cmpB o pt tt lB) (Sh-ΦX B lB o t pt b p)
```

## §4 闭项, 证书, FGH

初始界 $B=1$. `TX`: $\Omega_\Omega$ 的地板折到第 0 层. `TU m`: 第 $\Omega_\Omega\oplus m$ 层的地板 (塔 `Tw X₁ S⊥ m` 的地板, 底是 `topL`) 先经同底折叠折到 $\Omega_1$ 层 (种子 `topL`), 再经跨底折叠折到第 0 层. `TU2`: 对角 $y_0=0$, $y_{n+1}=y_n\boxplus TU(y_n+1)$ (同 CRw).

```agda
W₀ : Cd
W₀ = hs hz

TX : Cd
TX = ΦX W₀ tt hself hz (z⊲ᴮ W₀) hz topL

inU : (m : Cd) → LgB m → HB X₁ S⊥
inU m lm = Φ m (wf m) lm hz (z⊲ᴮ m) topL (topT X₁ S⊥ topL m)

TU : (m : Cd) → LgB m → Cd
TU m lm = ΦX W₀ tt hself hz (z⊲ᴮ W₀) hz (inU m lm)

LgB-TX : LgB TX
LgB-TX = sh→lg TX (Sh-ΦX W₀ tt hself hz (z⊲ᴮ W₀) hz topL)

LgB-TU : ∀ m lm → LgB (TU m lm)
LgB-TU m lm = sh→lg (TU m lm) (Sh-ΦX W₀ tt hself hz (z⊲ᴮ W₀) hz (inU m lm))

TU1 : Cd
TU1 = TU (hs hz) tt

yU : ℕ → Cd
lg-yU : ∀ n → LgB (yU n)
yU zero = hz
yU (suc n) = yU n ⊞ TU (hs (yU n)) (lg-yU n)
lg-yU zero = tt
lg-yU (suc n) = Lg-⊞ (yU n) (TU (hs (yU n)) (lg-yU n)) (lg-yU n) (LgB-TU (hs (yU n)) (lg-yU n))

TU2 : Cd
TU2 = hl yU

LgB-TU2 : LgB TU2
LgB-TU2 = (λ n → ⊞-fst (yU n) (TU (hs (yU n)) (lg-yU n))) , lg-yU
```

```agda
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero = x
iter f x (suc n) = f (iter f x n)

FGH : Cd → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ () _) n
FGH (hE () _ _) n

fghX fghU1 fghU2 : ℕ → ℕ
fghX = FGH TX
fghU1 = FGH TU1
fghU2 = FGH TU2
```

## §5 读法与测试

**读法 (判断, 没有值的定理).** 约定同 CRw (ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加累加). `TX` 读 ψ₀(Ω_Ω), `TU m` 读 ψ₀(Ω_{Ω+m}), `TU2` 读 ψ₀(Ω_{Ω·2}); 机制与 CRw 相同 (外部结点留成 $\Omega_1$-结点或取回灌链, 分支经同底折叠), 只是证据从命题变成类型. 层的代数 ([Fab6Lay](Fab6Lay.lagda.md)): 若 $L$ 读 $\Omega_\alpha$ 层, `ext L` 读 $\Omega_{\alpha+\Omega}$ (新结点 = $\sup_{y<\Omega_1}$ 高度 $y$ 的塔的地板 = $\sup_y\Omega_{\alpha+y}$), `pow L c` 读 $\Omega_{\alpha+\Omega\cdot c}$, `diag F` 读 $\sup_{c<\Omega_1}$ 各层; 于是 `TΩΩ` ψ₀(Ω_Ω), `TΩΩ₂` ψ₀(Ω_{Ω·2}), `TΩ²` ψ₀(Ω_{Ω²}), `TΩ³` ψ₀(Ω_{Ω³}), `TΩ^ω` ψ₀(Ω_{Ω^ω}), **`TΩ^Ω` ψ₀(Ω_{Ω^Ω})**. 这些都是对照机制的判断, 不是定理; 本路没有值的定理, 也没有与参照树的 `≼`. 按 "中间站给界" 的规则, 写成界: `TΩ^Ω` 的读法在 ψ₀(Ω_{Ω·ω}) (RecB 的 `Tω`, 同是判断) 之上, 判断的依据是 `diag` 对 Cd-族取 $\Omega_1$-共尾的并, 而 RecB 只对 ℕ 取并.

**有限测试** ([Fab6Cmp](Fab6Cmp.lagda.md), 深度 4 的结点数, `refl`): `TX`, `TU1`, `TU2` 与 CRw 的 `TX`, `TU1`, `TU2` **逐项相同** (41, 41, 32). 层的代数的闭项: `T₀` 36, `TΩΩ` 44, `TΩΩ₂` 41, `TΩ²` 45, `TΩ³` 45, `TΩ^ω` 41, `TΩ^Ω` 41 (只记录; 深度 4 的结点数不随强度单调, 不作比较). 测试不是证明.

## §6 行数 (定义级切片)

脚本 `Survey/scripts/fab6/locslice_fab6.py` (口径同 `crw/locslice_crw.py`). 同一台切片机同一轮重算 CRw 得 251 / 692 / 696, 与 CRw 文末一致. 2026-11-06 跑出:

| 层 | Fab6 ($X_1$ 站, 主闭项 `TU2`) | Fab6Lay (层的代数, 主闭项 `TΩ^Ω`) | CRw (`TU2`, 同机) | RecB (`Tω`, 取自文件) |
|---|---|---|---|---|
| 1 定义 | 165 | 184 | 251 | 245 |
| 2 + 折叠, 闭项, FGH | 411 | 408 | 692 | 810 |
| 3 + 证书 | **415** | **462** | **696** | **817** |

- $X_1$ 站: 415 对 696, 少 281 行 (40%), 读法相同 (判断), 有限测试逐项相同. 少的就是路径: CRw 第 3 层里路径专用 239 行, 这里外部种类与跨底折叠合计 36 行 (`XK`, `X₁`, `topL`, `brX`, `nodeX`, `ΦX` 与它们的 `Sh`); 接口 `CRwIf` (10 行) 与实例 `I₁` 也不需要.
- 层的代数: 462 行覆盖 `ext`/`supL`/`diag` 生成的一切层, 闭项与证书对一切层一条 (`clL`, `Lg-clL`); 层的代数本身 83 行. 与 RecB (817, 读 ψ₀(Ω_{Ω·ω})) 比: 少 355 行, 读法更高 (判断). 跨读法的行数不作比较结论, 但同口径的 "一个定义覆盖多少站" 可以比: RecB 覆盖 $\Omega\cdot n+m$, 这里覆盖 Cd 上由 `ext`, `supL`, `diag` 生成的一切层号.
- 两列第 3 层都在标杆 1513 之下; 闭包里 `OCF.Lean.Fab6*` 之外的仓库模块 0, 记号模块 0 (`importclosure.py --only OCF.Lean. OCF.Lean.Fab6Lay` OK).
- 口径差, 如实: (1) 同 CRw, 不证地板合法 (证书由形状给出, 不读输入). (2) 层的代数一列不含入口的 `ΦX` 一路 (`nodeX`, `brX` 等), 那一路只为对照 CRw 的 $X_1$ 站. (3) `Fab6Fold` 的 `Cl`/`cl`/`along`/`pick`/`dcl` 在 Fab6Lay 一列里只经 `Φ` 使用 (同底折叠).

## §7 翻译账

- **新构造子, 新字段.** 树多一个构造子 `hE` (外部种类的结点, 带前缀); 结构多一个记录 `XK` (种类, 坐标, 分支类型, 分支合法). **字段形状不读自记号的基本列规则**: `Br x y` 是 "坐标 $y$ 处分支的类型", 由 "跨底比较要字面公共上界" 逼出 (下一条).
- **由树逼出.** (1) **分支类型随坐标变**: CRw 的路径 `PH B h` 是命题 "坐标 $y$ 处的分支只用层号 $\le y$ 的种类", 它存在的理由是壁垒 (裸坐标上没有精确决定, 跨底比较要证据); 把它写成分支的类型, 分支里的种类就是塔里的位置, 比较用塔的高度作公共上界, 不要世界. (2) **外部结点带前缀**: 没有前缀, `⊞-fst` ($a\lhd a\boxplus b$) 在 $b$ 是外部结点时写不出 (分支是别的层的树, $a$ 加不进去); 部分和的形状证书 (`Sh-Σ`, `Sh-chain`) 要它. (3) **分支不要求对坐标单调**: 第一位置进不了分支 (`hEx` 只进前缀), 所以 `LgB (hE …)` 只要求各分支在自己的层上合法; 这使地板的分支可以直接取各层的地板 (`topT`, `fl`), 不必像 CRw 的 `gt` 那样累加. (4) **$\Omega_1$ 作底种类 (`S₁`), 折叠不坍缩它**: 层的折叠 `Ψ` 只把外部结点改写成 $\Omega_1$-结点; 唯一的坍缩在最后一步. 这是由 "外部结点的共尾度都是 $\Omega_1$" 逼出的: 留下的结点要一个坐标是可数树的种类, 塔的新种类坐标是上一层的树, 不是; 所以底要有 $\Omega_1$.
- **受记号启发, 如实.** 读法是对照 Buchholz 式 $\psi$ 的判断. `ext` 的 "新种类 = $\sup_{y<\Omega_1}$ 高度 $y$ 的塔" 与 $\Omega_{\alpha+\Omega}=\sup_{y<\Omega_1}\Omega_{\alpha+y}$ 同形, 但它的定义不引用记号, 只引用塔 (`Tw`) 与地板 (`topT`); `diag` 同理. 这两个算子是看着 "$\Omega_1$-共尾" 这一树侧事实写的: 一个外部种类就是一个坐标为可数树、分支类型随坐标变的结点.
- **累加, 如实.** 同底折叠 `Φ` 的后继、ℕ-极限、链与 CRw 相同 (部分积, 部分和, 回灌链); `leg`, `ΣT`, `supL` 的地板取部分和. 层的折叠 `Ψ` **不累加** (逐点), 它不需要证书 (证书只看最后一步 `Φ` 的形状). 所以累加比 CRw 少一处 (跨底折叠), 但毛刺 (`NegValCInst.acc-not-mono≤` 那种) 仍在 `Φ` 里, 本路没有碰它.
- **摆脱侧.** (a) 路径脚手架整块去掉 (239 → 36 行). (b) 下一站不再是判断: `ext` 给下一个 $\Omega_1$-共尾的种类, `diag` 给对一族取对角, 闭项与证书对一切层一条 (`clL`, `Lg-clL`, 不按站写). 这是 "闭包定理与阶段无关" 与 "下一步的定义不看记号就能写出" 两条判据第一次在 C 线上同时成立 (判断: 成立的范围是 `ext`/`supL`/`diag` 生成的层, 即坐标都是可数树的层; 坐标是不可数层的树的层 (如 $\Omega_{\Omega_{\Omega+1}}$) 不在这个代数里, 见 §8).
- **攀爬侧.** 读法 (判断) 从 C 线此前的 ψ₀(Ω_{Ω·ω}) (RecB) 到 ψ₀(Ω_{Ω^Ω}); 没有值的定理.

## §8 接手清单

1. **值的定理.** 本路没有. 最近的: 把 `ValC` 的值关系搬到 `HB X S` (多一个构造子 `hE`, 值关系上外部结点按分支逐点比较); `Ψ` 逐点不累加, 可能比 CRw 的跨底折叠更容易证单调 (判断).
2. **不可数坐标.** 层的代数里一切外部种类的坐标都是 `Cd`. 往 $\Omega_{\Omega_{\Omega+1}}$ (坐标是 $\Omega_{\Omega+1}$ 层的树) 走, 外部种类的坐标要换成 `HB X S₁` 一类的树, 分支类型随这样的坐标变, 折叠时 "坐标 $c$ 处的分支折到目标" 要先知道 $c$ 折到哪一层, 即要对坐标折叠; 这正是 LHRec §4 的两难所在, 本路没有碰. 判断: 外部种类的写法把 "分支只用层号 $\le y$ 的种类" 从命题变成类型, 对可数坐标够用; 对不可数坐标, "$\le y$" 本身要比较不可数层的树, 壁垒回来.
3. **有限测试的扩展.** `Fab6Cmp` 只到深度 4; 层的代数的闭项与 RecB 的 `TD`, `Tω` 没有对照 (类型不同, 机制不同: 这里 $\Omega_1$ 只在最后坍缩).
4. **地板合法** 没有证 (同 CRw). 外部结点的 `LgB` 只要求各分支合法, 所以 `Lg-fl` 对层的代数应当是对 `FL` 加一个字段 `Lg-fl` 后逐算子传递 (估计 30 行).
5. **`Ψ` 与 `Φ` 的关系.** 层的折叠 `Ψ` 只折到 `S₁` 上的塔; 本路的闭项只用 $t=0$. 一般 $t$ 的 `Ψ` 在 `ext` 的分支里用了 (`Ψ L t`), 但没有闭项用它; 可以删成只有 $t=0$ (估计少 10 行), 没有删是为了保持 "折到任一层" 的形状.

## §9 结论 (按档)

- **[定理]** `Fab6Base`: 带外部种类的高度树 `HB X S` 及其第一位置、合法、`cmpB`、`⊞`、`step`、`sup` (对一切 `X`, `S`). `Fab6Fold`: 塔与同底折叠 `Φ`, 形状 `Sh-Φ`, `sh→lg` (对一切 `X`, `S`). 本篇: 跨底折叠 `ΦX` (无路径, 无世界, 无接口), 闭项 `TX`, `TU m`, `TU1`, **`TU2`**, 证书 `LgB-TX`, `LgB-TU`, **`LgB-TU2`** (标准 `LgB`), FGH. `Fab6Lay`: 层 `FL`, 算子 `ext`, `supL`, `diag`, `It`, `pow`, `P`, `Pc`; **闭项与证书对一切层一条** (`clL`, `Lg-clL`); 闭项 `T₀` … **`TΩ^Ω`**, 证书 `Lg-TΩ^Ω`, FGH `fghΩ^Ω`.
- **[有限测试]** `Fab6Cmp`: `TX`, `TU1`, `TU2` 与 CRw 逐项相同 (深度 4); 层的代数闭项的结点数.
- **[判断]** 一切读法 (§5); "路径变类型" 这一步对不可数坐标不够 (§8.2); 行数的口径差 (§6).
