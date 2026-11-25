# YiCarryPlus：高层起点的伴随证据增补

本篇只增补冻结的 YiCarry V1，不改原树、守卫、合法性或 Carry。
Carry⁺ 在每个递归访问的 lc 根保存下界的 Nested；配合原 Lgl，
下界自身就是带 LglB 的守卫初项。Reg 仍覆盖全部原守卫分支，
额外递归仍只要求 LglB 坐标，层参数 k 仍不作为折叠源递归。

Source⁺、PsiRows⁺、K2′⁺ 仅将 V1 输入证书换成 Carry⁺。
本篇只定义接口，不证明 K2′⁺，不写折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryPlus where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF; Raw; Lgl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiCarryBounds public using (Nested; LglB)
import OCF.Align.YiCarry as Y
open Y public using (Point; PointB; point; coordinate; guard; bounds; Common; RawStep)
import OCF.Align.YiK2Base as A

Carry⁺ : LF → Set
Carry⁺ F.zero = ⊤
Carry⁺ (F.suc x) = Carry⁺ x
Carry⁺ (F.lim f) = ∀ n → Carry⁺ (f n)
Carry⁺ (F.lc k c t g) =
  Reg (F.lc k c t g) × Lgl k c × Nested k c × Carry⁺ t ×
  (∀ η e → LglB k η → Carry⁺ (g η e))

forget⁺ : ∀ {x} → Carry⁺ x → Y.Carry x
forget⁺ {F.zero} r = tt
forget⁺ {F.suc x} r = forget⁺ {x} r
forget⁺ {F.lim f} r = λ n → forget⁺ {f n} (r n)
forget⁺ {F.lc k c t g} (reg , lc , bc , ct , cg) =
  reg , lc , forget⁺ {t} ct , (λ η e b → forget⁺ {g η e} (cg η e b))

lower⁺ : ∀ {k c t g} → Carry⁺ (F.lc k c t g) → LglB k c
lower⁺ (reg , lc , bc , ct , cg) = lc , bc

-- 重述 V0 的 start-iff；不导入 V0 的失败递归谓词。
start-iff : ∀ k c → (Point k c → Lgl k c) × (Lgl k c → Point k c)
start-iff k c = (λ { (η , p , lη) → F.lgl-cp k p lη }) ,
  (λ lc → c , (inj₁ refl , lc))

seed⁺ : ∀ {k c t g} → Carry⁺ (F.lc k c t g) → PointB k c
seed⁺ {k} {c} r = point (proj₁ p) (proj₂ p) (lower⁺ r)
  where
  p : Point k c
  p = proj₂ (start-iff k c) (proj₁ (lower⁺ r))

first-carry⁺ : ∀ {k c t g} → Carry⁺ (F.lc k c t g) → Carry⁺ t
first-carry⁺ (reg , lc , bc , ct , cg) = ct

branch-carry⁺ : ∀ {k c t g} → Carry⁺ (F.lc k c t g) →
  ∀ η e → LglB k η → Carry⁺ (g η e)
branch-carry⁺ (reg , lc , bc , ct , cg) = cg

cp-carry⁺ : ∀ {a b} → V.CP a b → Carry⁺ b → Carry⁺ a
cp-carry⁺ V.self r = r
cp-carry⁺ (V.suc p) r = cp-carry⁺ p r
cp-carry⁺ (V.lim n p) r = cp-carry⁺ p (r n)
cp-carry⁺ (V.fst p) r = cp-carry⁺ p (first-carry⁺ r)
```

start-iff 的反向自取下界，不运行比较器；seed⁺ 的 bounds 正是
原 Lgl 与新增 Nested。它对所有 k 成立，不把 Raw 0 的空嵌套性
误用到高层。其条件有规范闭实例，见 YiCarryPlusInstances。

## 增补的源与行接口

字段与冻结 V1 逐项对应。GtGenerator⁺ 仍要求 seed、next、grow、
output-step；seed⁺ 只完成第一个字段的生产，不冒称完整生成器。
第 0 层的加法更新、初项等式以及带公共界的位置律原样保留。

```agda
record Source⁺ : Set where
  constructor source⁺
  field
    term : LF
    carried : Carry⁺ term
    lawful : V.Legal term
open Source⁺ public

branch-source⁺ : ∀ {k c t g} (r : Carry⁺ (F.lc k c t g)) →
  V.Legal (F.lc k c t g) → ∀ η e → LglB k η → Source⁺
branch-source⁺ {g = g} r l η e b =
  source⁺ (g η e) (branch-carry⁺ r η e b) (Y.branch-legal l η e)

record GtGenerator⁺ (ψ : Source⁺ → Raw F.zero)
  (k : LF) (c : Raw k) (t : LF)
  (g : (η : Raw k) → F.Gd k c η → LF)
  (r : Carry⁺ (F.lc k c t g)) (l : V.Legal (F.lc k c t g)) : Set where
  field
    seed : PointB k c
    next : PointB k c → PointB k c
    grow : ∀ p → F.Dn k (coordinate p) (coordinate (next p))
    output-step : ∀ p →
      RawStep F.zero
        (ψ (branch-source⁺ r l (coordinate p) (guard p) (bounds p)))
        (ψ (branch-source⁺ r l (coordinate (next p))
          (guard (next p)) (bounds (next p))))

generated⁺ : ∀ {ψ k c t g r l} → GtGenerator⁺ ψ k c t g r l → ℕ → PointB k c
generated⁺ d = Y.iterate (GtGenerator⁺.next d) (GtGenerator⁺.seed d)

generated-out⁺ : ∀ (ψ : Source⁺ → Raw F.zero) k c t g r l →
  GtGenerator⁺ ψ k c t g r l → ℕ → Raw F.zero
generated-out⁺ ψ k c t g r l d n =
  ψ (branch-source⁺ r l (coordinate p) (guard p) (bounds p))
  where
  p : PointB k c
  p = generated⁺ d n

record PsiRows⁺ (ψ : Source⁺ → Raw F.zero) : Set where
  field
    gt-generator : ∀ k c t g r l → GtGenerator⁺ ψ k c t g r l
    zero-row : ∀ r l → ψ (source⁺ F.zero r l) ≡ A.one
    suc-row : ∀ x (r : Carry⁺ x) (l : V.Legal x) →
      ψ (source⁺ (F.suc x) r l) ≡ A.successor (ψ (source⁺ x r l))
    lim-row : ∀ f (r : ∀ n → Carry⁺ (f n))
      (st : ∀ n → V.CP (f n) (f (Data.Nat.Base.suc n)))
      (l : ∀ n → V.Legal (f n)) →
      ψ (source⁺ (F.lim f) r (st , l)) ≡
      G.lim (λ n → ψ (source⁺ (f n) (r n) (l n)))
    gt-row : ∀ k c t g r l →
      ψ (source⁺ (F.lc k c t g) r l) ≡
      G.lim (generated-out⁺ ψ k c t g r l (gt-generator k c t g r l))
    gt-additive0 : ∀ c t g r l (p : PointB F.zero c) →
      coordinate (GtGenerator⁺.next (gt-generator F.zero c t g r l) p) ≡
      A._+ʳ_ (coordinate p)
        (ψ (branch-source⁺ r l (coordinate p) (guard p) (bounds p)))
    gt-seed0 : ∀ c t g r l →
      coordinate (GtGenerator⁺.seed (gt-generator F.zero c t g r l)) ≡ c

OutputB⁺ : (Source⁺ → Raw F.zero) → Set
OutputB⁺ ψ = ∀ s → LglB F.zero (ψ s)

record K2′⁺ : Set where
  field
    ψ : Source⁺ → Raw F.zero
    rows : PsiRows⁺ ψ
    output-B : OutputB⁺ ψ
    output-legal : ∀ s → V.Legal (V.up F.zero (ψ s))
    positive : ∀ s → F.Dn F.zero G.zero (ψ s)
    bounded-position : ∀ a b → Common (term a) (term b) →
      V.CP (term a) (term b) → RawStep F.zero (ψ a) (ψ b)
```

新增的证书不索取比较律。原 Common 显式给字面公共界、双 CP 和
界的 Legal；RawStep 显式给右输出的位置及合法性。
相邻坐标的公共界是 next p 的 coordinate，其合法性包含在 bounds。
没有增加裸下标的判等或全局三歧。

## 定稿、结论与翻译账（2026-11-10）

**YiCarryPlus 定稿，只增不改。** 定义及 K2′⁺ 记录先单独编译通过，
再完成规范实例检验并在 README 标记定稿。此后代码块摘要保持不变，
本节只追加结论与审计；YiCarry 与 YiCarryBounds 未改。

**编译定理。** forget⁺ 将新证书递归投影为原 Carry；seed⁺ 对一切 k
给高层起点。它由 start-iff 的反向自取合法下界，新增 Nested 合成 bounds。
[Instances](YiCarryPlusInstances.lagda.md) 给
`tower-carry⁺ : ∀ n → Carry⁺ (V.tw n)`、
`limit-carry⁺ : Carry⁺ V.Λ`，并交与原 Legal 并列的闭源。
[Neg](YiCarryPlusNeg.lagda.md) 的 no-old-source-carry⁺ 排除
YiCarryNeg.no-K2′ 所用的同一个源，精确失败字段是根下界 Nested。
旧源的原 Carry、Legal 与守卫起点仍有闭证据；旧 V1 的否定不撤回。

**条件编译定理。** [Read](YiCarryPlusRead.lagda.md) 的
guard-read-carry⁺ 显式保留 Reg y、Below y (Ω̂ y)、Carry⁺ (Ω̂ y)、
原 cO 守卫与 LglB。read-carrys⁺ 显式保留较强路径
Below (suc y) (Ω̂ y) 及 0..n+1 次的有限证书包。
Instances 的 carry-stages⁺ 构造各次数环境；后继坐标的 pa、ra
均由真子坐标递归实填。y=0 的 guard-read 环境及非零层 high-seed⁺
的闭应用也在该篇说明或实填。不假定全塔，未用函数外延。

**有限测试。** 无。

**判断与范围。** 增补完成了高层 seed 所缺的证据，并与原规范全塔、
Λ 相容，未触发止损。这不证明 GtGenerator⁺ 的 next／grow／output-step
可实现，也不证明 PsiRows⁺、K2′⁺ 可满足。没有折叠、新序数值界或
FGH 比较，不声称 EBO 下界或树自足已经完成。

翻译账：新增 Nested 来自冻结接口的树侧起点反例，不取自记号规则。
复用 YiK1b 归纳时，多用 Raw lc 的 NestedLow 沿槽位运输根证书，
Ω 后继行用 cO-nested，raw1 根用 tt；没有按塔层添加专属前提。
Reg 的全部原分支独立复用旧定理，没有用 LglB 缩域。
四行目标仍承接 V1 模板，只换输入证书；第 4 层逼出：无。

## 冷编清单与引用审计

| 新模块 | 仅删自身精确接口 | 单路堆上限 | 退出码 | 目标 Checking |
|---|---|---|---|---|
| YiCarryPlus | 是 | 6G | 0 | 有 |
| YiCarryPlusRead | 是 | 6G | 0 | 有 |
| YiCarryPlusInstances | 是 | 6G | 0 | 有 |
| YiCarryPlusNeg | 是 | 6G | 0 | 有 |

四件依次运行，依赖取缓存，不称冷编整个闭包。没有 ignore-interfaces，
只删除本轮四件自己的字面接口，退出码直接读取，不经管道。
每次均带 `+RTS -M6G -RTS`。开发中两个退出 42 分别来自局部 term
与源投影重名、辅助实例误认 tw 3 的根层参数，均已改正；不作为否定。
正式冷编全为 0，没有堆耗尽或超时。

复现从仓库根，库文件含 stdlib 与 cubical 的有效库路径：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryPlus.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryPlusRead.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryPlusInstances.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryPlusNeg.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiCarryPlus OCF.Align.YiCarryPlusRead OCF.Align.YiCarryPlusInstances OCF.Align.YiCarryPlusNeg --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```

- 四件 safe／without-K／lossy-unification；公设、洞、跳过停机／正性
  检查的指示、信任相等及 Funext 均为 0，无绝对路径或尾随空白。
- Source⁺／GtGenerator⁺／PsiRows⁺／K2′⁺ 与 V1 逐字段文本比较，
  除 Carry⁺ 及其相应类型／构造名、限定名、排版外完全相同。
- 主接口／Read／Instances／Neg 的源码本地闭包为 23／25／27／26，
  库叶均 19；上述完整白名单外和记号禁用表均为 0，无记号／C 线。
  成功编译器图总模块数为 168／170／172／171，本地集合逐一等于源码闭包。
- 成功 HTML 切片：Carry⁺ 32、forget⁺ 35、seed⁺ 41、Source⁺ 36、
  PsiRows⁺ 53、K2′⁺ 61、read-carrys⁺ 123、tower-carry⁺ 142、
  limit-source⁺ 154、no-old-source-carry⁺ 57 块，记号块与词命中均为 0。
  EboLean3Lab 的 ebo-lab″ 正对照为 352／33／36；单路 6G 成功生成其
  HTML，未删除其旧接口，也不将它导入本轮模块。切片只是语法近似。
- YiCarry、YiCarryBounds、YiCarryNeg 及 YiK1b 四件的源码摘要与开工时
  相同；README／LOG 只增加本轮状态、翻译账与记录，不改旧结论。
  未改 src／archive，未安装包、提交或推送。
