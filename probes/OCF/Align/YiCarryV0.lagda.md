# YiCarryV0：全部原分支递归携带起点的探针（不定稿）

**结论：一般层上，有起点当且仅当下界合法；但本版递归 `Carry`
不覆盖规范 `Ω̂ 2`，也不覆盖 `tw 3`。二者的 `Reg` 仍成立。**
原因是原合法坐标可读回下界不合法、守卫域为空的 lc 结点。
因此本篇是带版本号的探针，**不是共用接口，不定稿**；
后续递归域由作者决定。本轮不写 K1′／K2′ 的冻结记录。

本篇只在原块外增加谓词与证明，不改 `Reg`、`Gd`、`Lgl`、`Legal`。
起点证据取下界合法性：一般层也有“可入点存在当且仅当下界合法”。
`Carry` 递归覆盖层号、第一支与全部原守卫分支；不增加严格性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryV0 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase
  using (Below; one; more; e-suc; e-lim; e-first; e-branch)
open import OCF.Align.YiRegBase using (Reg)
import OCF.Align.YiK2Stop as S
import OCF.Align.RR4RegOmega2 as R
import OCF.Align.YiK1 as K
```

## 1. 一般层的起点条件

`Point k c` 是第 k 层下界 c 的一个原守卫坐标。正向只投影守卫，
再用原块 `lgl-cp` 沿第一位置取合法性；反向自取 c，不需要严格后继。
没有假设层号合法、正则或可比较。

```agda
Point : (k : LF) → Raw k → Set
Point k c = Σ (Raw k) (Gd k c)

coordinate→bound-legal : ∀ k c → Point k c → Lgl k c
coordinate→bound-legal k c (η , p , lη) = F.lgl-cp k p lη

bound-legal→coordinate : ∀ k c → Lgl k c → Point k c
bound-legal→coordinate k c lc = c , (inj₁ refl , lc)

start-iff : ∀ k c →
  (Point k c → Lgl k c) × (Lgl k c → Point k c)
start-iff k c = coordinate→bound-legal k c , bound-legal→coordinate k c

cO-start : ∀ k → Point k (V.cO k)
cO-start k = bound-legal→coordinate k (V.cO k) (V.Lgl-cO k)
```

这是一对蕴含，不声称两种证据类型同构或证明无关。规范 `cO k` 的
下界合法性由原 `Lgl-cO` 给出，故所有 k 的起点条件有实例。

## 2. 递归携带证据

lc 保留冻结 Reg 的 bound，把层号、第一支、全部分支的递归 Reg 换成
Carry，最后增加下界合法性。
`Carry` 没有包含 `Legal`，两份证据在下游并列传入。

```agda
Carry : LF → Set
Carry F.zero = ⊤
Carry (F.suc x) = Carry x
Carry (F.lim f) = ∀ n → Carry (f n)
Carry (F.lc k c t g) =
  Below (F.suc k) (F.lc k c t g) ×
  Carry k × Carry t × (∀ η e → Carry (g η e)) × Lgl k c

forget : ∀ {x} → Carry x → Reg x
forget {F.zero} r = tt
forget {F.suc x} r = forget {x} r
forget {F.lim f} r = λ n → forget {f n} (r n)
forget {F.lc k c t g} (bound , rk , rt , rg , lc) =
  bound , forget {k} rk , forget {t} rt ,
  (λ η e → forget {g η e} (rg η e))

lower : ∀ {k c t g} → Carry (F.lc k c t g) → Lgl k c
lower (bound , rk , rt , rg , lc) = lc

start : ∀ {k c t g} → Carry (F.lc k c t g) → Point k c
start {k} {c} r = bound-legal→coordinate k c (lower r)

read0-carry : ∀ (η : Raw F.zero) → Carry (V.up F.zero η)
read0-carry G.zero = tt
read0-carry (G.suc a) = read0-carry a
read0-carry (G.lim f) = λ n → read0-carry (f n)
read0-carry (G.lc () c t g)
read0-carry (G.em () t)
read0-carry G.top = tt

tw0-carry : Carry (V.tw 0)
tw0-carry = tt

tw1-carry : Carry (V.tw 1)
tw1-carry = tt

tw2-carry : Carry (V.tw 2)
tw2-carry = one e-first , tt , tt , (λ η e → read0-carry η) , tt
```

## 3. 规范实例要求中的冲突

原 `Raw 1` 的合法 lc 坐标也不要求自己的下界合法。把 K2 的坏下界
放入这个坐标，第一支与全部分支取 top；它仍过 `Ω̂ 2` 的原守卫。
读回后是下界非法的第 0 层 lc，所以递归的 `Carry` 无法覆盖该分支。

```agda
bad-coordinate : Raw (F.suc F.zero)
bad-coordinate = G.lc (inj₁ tt) S.bad-bound G.top (λ _ _ → G.top)

bad-coordinate-lgl : Lgl (F.suc F.zero) bad-coordinate
bad-coordinate-lgl =
  (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

bad-coordinate-guard : Gd (F.suc F.zero) (V.cO (F.suc F.zero)) bad-coordinate
bad-coordinate-guard = inj₂ (inj₁ refl) , bad-coordinate-lgl

bad-coordinate-read : V.up (F.suc F.zero) bad-coordinate ≡
  F.lc F.zero S.bad-bound (V.Ω̂ (F.suc F.zero))
    (λ _ _ → V.Ω̂ (F.suc F.zero))
bad-coordinate-read = refl

bad-bound-no-start : Point F.zero S.bad-bound → ⊥
bad-bound-no-start p =
  S.no-bound-legal (coordinate→bound-legal F.zero S.bad-bound p)

bad-read-legal : V.Legal (V.up (F.suc F.zero) bad-coordinate)
bad-read-legal =
  V.lgl→Legal (F.suc F.zero) tt bad-coordinate bad-coordinate-lgl

bad-read-bound : Below (F.suc F.zero) (V.up (F.suc F.zero) bad-coordinate)
bad-read-bound = more (one e-first) e-first

bad-read-reg : Reg (V.up (F.suc F.zero) bad-coordinate)
bad-read-reg = R.guarded-reg bad-coordinate bad-coordinate-lgl
  (proj₁ bad-coordinate-guard)

-- 读回结点除根起点之外的 Carry 字段都有闭证据。
bad-read-without-start :
  Below (F.suc F.zero) (V.up (F.suc F.zero) bad-coordinate) ×
  Carry F.zero × Carry (V.Ω̂ (F.suc F.zero)) ×
  (∀ (η : Raw F.zero) (e : Gd F.zero S.bad-bound η) →
    Carry (V.Ω̂ (F.suc F.zero)))
bad-read-without-start =
  bad-read-bound , tt , tw2-carry , (λ _ _ → tw2-carry)

bad-read-no-carry : Carry (V.up (F.suc F.zero) bad-coordinate) → ⊥
bad-read-no-carry r = S.no-bound-legal (lower r)

no-carry-Ω₂ : Carry (V.Ω̂ (F.suc (F.suc F.zero))) → ⊥
no-carry-Ω₂ (bound , rk , rt , rg , lc) =
  bad-read-no-carry (rg bad-coordinate bad-coordinate-guard)

Ω₂-reg : Reg (V.Ω̂ (F.suc (F.suc F.zero)))
Ω₂-reg = R.Ω₂-reg

Ω₂-legal : V.Legal (V.Ω̂ (F.suc (F.suc F.zero)))
Ω₂-legal = V.Legal-Ω₂

no-carry-tw3 : Carry (V.tw 3) → ⊥
no-carry-tw3 (bound , rk , rt , rg , lc) =
  no-carry-Ω₂ (rg R.raw2 R.raw2-guard)

tw3-reg : Reg (V.tw 3)
tw3-reg = K.tw3-reg

tw3-legal : V.Legal (V.tw 3)
tw3-legal = V.Legal-tw 3
```

反例的三个层次须分开：

1. 坐标是 `bad-coordinate : Raw 1`，具体为
   `G.lc (inj₁ tt) bad-bound top (λ _ _ → top)`。
   它自己的第一支、单调性、证据无关性、分支合法性全由自反或 tt 给出；
   原 `Lgl` 不问 `bad-bound` 是否合法。`bad-coordinate-lgl` 和
   `bad-coordinate-guard` 是闭证据，没有假定一个不可能的守卫。
   外层守卫的下界是 `cO 1 = top`，通过坐标自己的第一支 top。
2. 读回结点是 `lc 0 bad-bound Ω₁ (λ _ _ → Ω₁)`，
   其中 `Ω₁ = Ω̂ 1`；等式 `bad-coordinate-read` 由 refl 检查。
   它是 `Ω̂ 2` 在上述合法坐标处的实际原分支，不是域外树。
3. 它的下界 `bad-bound = lim (1, 0, 0, …) : Raw 0` 不合法：
   第一个相邻步会要求 1 是 0 的第一位置，构造子反演否定它
   （`YiK2Stop.no-bound-legal`）。一般层等价性随即给出
   `bad-bound-no-start`：该结点没有任何原守卫坐标。

`bad-read-legal`、`bad-read-reg` 与 `bad-read-without-start` 明确给出
同一结点的合法性、Reg，以及除根起点之外的全部 Carry 字段。
最后一项的分支函数直接用到已获 Carry 的 Ω₁ 的常函数给出。
局部失败准确落在新增的起点字段。
规范 `Ω̂ 2` 的 `Reg` 则仍是 RR4 的无条件编译定理；本篇原样引用。

`tw 3` 的分支在第 0 层坐标 `raw2 = suc (suc zero)` 处字面就是
`Ω̂ 2`；`raw2-guard` 已给该坐标的原守卫。因此本版也编译否定
`Carry (tw 3)`，并列保留 K1 的 `Reg (tw 3)`，不改旧结论。

| 本版实例 | 编译结果 |
|---|---|
| Carry (tw 0)、Carry (tw 1)、Carry (tw 2) | 闭证据 `tw0-carry`、`tw1-carry`、`tw2-carry` |
| Carry (tw 3) | `no-carry-tw3` 否定 |
| Carry (Ω̂ 2) | `no-carry-Ω₂` 否定 |
| 一般 k 的规范 cO k 起点条件 | `cO-start k`，无额外前提 |

这不是全塔 Reg、完整 ψ、EBO 下界或某种值的否定。
没有序数值／FGH 比较，也没有有限测试。

## 4. 第 0 层 ψ 是否会在这里调用 gt（判断）

以下是按现有派发规则作的**判断／纸面分析**，不是编译过的完整 ψ
或实际轨道定理。必须区分“这个结点若成为调用的输入，会走哪行”
和“规范输入的执行是否真的到达这个结点”。

按原模板，目标层为 i 时比较 `suc k` 与 i；lt／eq 保留，gt 折叠。
因此若 `lc 0 bad-bound Ω₁ (const Ω₁)` 成为 **ψ₀ 的输入**，
比较的两项是 1 与 0，应走 gt。这不是一个在 ψ₀ 里可以仅以保留行
经过的 lc：原 LF 的每个 lc 都有后继形状的派发下标，不能小于或等于 0。
该 gt 的原守卫域为空，要求调用它的分支函数前先选起点，就会失败。

但 `bad-coordinate-guard` 只证明它是 Ω̂ 2 的**原合法分支坐标**，
不证明它在折叠实际生成的坐标链中。V0 对全部原 Gd 分支量化，
因此可能要求了实际计算不使用的起点。这一反例没有证明规范
Ω̂ 2 或 tw 3 的 ψ₀ 实际会访问它，也没有证明不会访问。
原 K2 只有第 0 层坐标的局部链，没有 Ω̂ 2 所需的完整高层坐标生产器，
不能拿那份局部实现来声称已检查这条轨道。

另一方面，ψ₀ 的高层辅助调用可能以非零 i 为目标；对同一个 k=0
结点，在 i=1 时是 eq 保留，在更高目标且有相应字面位置证据时
可以是 lt 保留。**判断：递归域应记录目标层与实际调用角色，不能只按
“曾作为某个原分支出现”就要求该处有 gt 起点。** 保留本身不需根起点，
但其后对子分支的调用是否需要，仍须逐调用给证据。

## 5. 待作者选择的递归域（只列选项，不实施）

下列三项都是**判断／接口设想**；本篇没有定义它们的谓词、记录或折叠。
“入口可填”仅指该入口的 Reg 和所需根起点，不代表任意嵌套递归已封闭。
所有选项保留 Reg 对全部原 Gd 分支的要求。

| 选项 | 起点证据的递归域 | 规范实例能否满足（判断，非新编译定理） | 是否改已有定义 |
|---|---|---|---|
| A：目标与实际调用域 | 只有实际发出的 gt 调用要求该根的 Lgl 下界；保留行只带本次所需证据。调用域包含目标层，并由有证据的调用步骤生成，不能先假定完整 ψ 已存在 | tw 0、1、2 可由本篇更强的 V0 证书支持；tw 3、Ω̂ 2 的根起点可填，但完整实际调用证书未证。反例坐标是否入域待证，不能标为全证书可满足 | 不改旧定义；需新调用关系和起点保持定理 |
| B：证据随坐标生成 | 给 Ω̂／cO／up 的实际生产步骤带证书；尤其 up 只接收由有证据的坐标生产器生成的参数。Reg 仍覆盖全部原分支，起点只覆盖生产器实际读回的结点 | tw 0、1、2 可填；tw 3、Ω̂ 2 的入口也可填，完整生成证书未证，需证明高层链点一直属于有证据的坐标域。若允许任意原 Gd 坐标作为 up 的输入且对子树全部递归，则本反例已否定 tw 3 和 Ω̂ 2，不能算修复 | 不改旧定义可做伴随证书；若要直接收窄 Raw／Gd 或改 Ω̂ 的分支域，则需作者拍板，本轮不做 |
| C：每次调用只给根，子调用另交证据 | 入口只保存全 Reg 与当前根的起点（当前根为 lc 且确需 gt 时）；递归器每发出一个子调用，显式交付该子调用的证书，不从父证书投影出“全部分支都有起点” | tw 0、1、2、3 及 Ω̂ 2 的入口均可填：已知 Reg，规范 lc 的根下界均为 cO。此项没有自动递归闭包；子调用交付义务未证，不能由入口可填冒称完整 ψ 可运行 | 不改旧定义；需另写子调用的生产／保持合同 |

A 按消费者的实际需求刻画域；B 按生产者刻画同一需求可能落入的充分域；
C 暂不把子调用合同合成遗传谓词。三者能否最后拼成同一可检查递归器，
本轮没有结论。B 中“由 Ω̂／cO／up 产生”必须有坐标生产证书这个限定：
单列操作名称并不能排除本篇的坏读回。

树侧依据是原 Gd 对每个真正要调用的分支强制要求起点，和保留／折叠
两种调用对根起点的需求不同；不是按记号的基本列挑选可用坐标。
没有从值验收反改任何定义，也不以本探针否定这些尚未实施的域。

## 6. 字面公共上界检查

本篇未新增判定器或比较律；不对两个裸下标调用全局比较。
逐项检查新证明和上一节派发分析如下。

| 出现的一对 | 字面公共上界及证据 | 用法与限制 |
|---|---|---|
| 一般层起点中的 c、η | η；守卫第一字段 Cp k c η，自反 Cp k η η，合法性为守卫第二字段 | lgl-cp 只沿已给路径回传合法性，没有比较两个分支 |
| 由合法下界造起点的 c、c | c；两份 inj₁ refl；前提 Lgl k c | 自取下界，不要求严格性 |
| 外层守卫的 top、bad-coordinate | bad-coordinate；经第一支 top 的 Cp 和自反；bad-coordinate-lgl | 只有已给的原守卫关系 |
| tw 3 所选分支的 raw1、raw2 | raw2；raw2-guard 的第一字段和自反；合法性为 tt | 使用闭守卫，不比较两个任意坐标 |
| Reg／Carry 根路径中的 suc k、lc k c t g | 后者是 Below 路径的字面祖先 | 这是结构路径，允许经过 Ω 支；没有把它当成 CP 上界交给有界比较器，Carry 也不冒称含有 Legal |
| 第 0 层派发分析中的 suc k、0 | suc k；自身的 CP 自反及 0 沿后继到它的 CP；合法性由源 Legal 的 Legal k 字段给出 | 仅为 §4 判断列明合法公共界；没有为裸 k 与任意目标索取全局三歧 |
| bad-bound 第一步的 1、0 | 没有假定共同合法上界或步进证据 | 对声称的 Cp 1 0 作构造子反演，不运行比较器，也不由“没有找到界”推否定 |

Reg 实例引用的 K1／RR4 原证明中的极限比较，均带到同一项
`f (m + n)` 的两条 Cp 及该项 Lgl；本篇没有扩大那些律的定义域。
未来 A／B／C 若引入新的比较，仍须重新逐对提供字面合法公共界，
本表不是对尚未写出的接口的认证。

## 7. 翻译账与交付边界

新增的下界字段由 K2 的无起点反例及本篇一般层等价性逼出；
V0 把它遗传地放到全部原分支，是本轮检验的接口选择，现已在规范
Ω̂ 2 与 tw 3 上被编译否定。Reg 没有失败，不增加严格性。
没有新增来自记号基本列的结点、坐标字段或阶段专属闭包前提。
§4 的 lt／eq／gt 读法仍参考原模板，不能称完整程序已由树侧唯一推出。
第 4 层逼出：无。本轮无折叠、值定理或新强度界；闭包干净只保证无引用。

作者本轮已决定不定稿：本篇只交 V0 正反定理及未实施的域选项，
不建可供下游冻结引用的 YiCarry 接口。待作者选域后另开新篇，
不回改本版探针的定义或结论。

## 8. 冷编与审计清单（2026-11-10）

| 本轮模块 | 自身接口删除后重编 | 堆上限 | 退出码 | 目标 Checking 行 |
|---|---|---|---|---|
| OCF.Align.YiCarryV0 | 是 | 6G | 0 | 有 |

依赖使用缓存，不声称冷编整个闭包；一次只跑一个 Agda。
最初未版本化的试写也通过，按作者后续指令改为本版文件，
仅清理本轮这两个名字的自身接口，没有删除别人的接口。

复现类型检查（从仓库根；库文件含 stdlib 与 cubical 的库路径）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryV0.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiCarryV0 --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```

- `--safe --without-K --lossy-unification`；代码中公设、洞、跳过停机／
  正性检查的指示、信任相等与 Funext 前提均为 0；无本机绝对路径、
  临时日志路径或尾随空白。
- 源码导入闭包本地 22、库叶 19；上述白名单外与禁用表命中均为 0，
  无记号或 C 线模块。成功的 `agda --dependency-graph` 本地集合也是
  22，与源码集合逐一相同。
- 成功生成 HTML 后的定义切片：Carry 24、start-iff 27、forget 27、
  no-carry-Ω₂ 44、no-carry-tw3 49、Ω₂-reg 74 个块；
  各根的记号模块块数与其它模块记号词命中均为 0。
  另以单路 6G 成功生成 `EboLean3Lab` 的 HTML 作正对照，
  ebo-lab″ 为 352／33／36；它不在本探针的导入闭包内。
  切片是语法近似，只认证所述无引用范围。
- 数学结果只有上述编译正反定理；§4、§5 全部是判断与未实施的选择，
  有限测试无。没有折叠、旧定义改动、提交或推送。

README 与 LOG 仅新增本轮记录，保留旧结论。递归域与共用接口均待作者决定。
