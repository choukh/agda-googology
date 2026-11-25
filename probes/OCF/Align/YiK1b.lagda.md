# K1′：原块全塔与 Λ 的 Carry

本篇填冻结的 YiCarry.K1′：全部原规范塔项及 Λ 都能带伴随证书。
Reg 仍检查全部原守卫分支，Carry 的额外递归仍只走 LglB；
不改树、Reg、Gd、Lgl、Legal、Carry 或接口，不写折叠。
这解决规范闭项的全塔证书义务，不等于已有 ψ、FGH 或 EBO 值下界。

证明分开两项：Reg 的全原守卫量词见 YiK1bReg；本篇给 Carry 的
额外 LglB 量词。它们都使用对任意树层参数的 YiK1bBase.read-regs／
YiK1bCarry.read-carrys，不按具体塔层增加槽位枚举或专属前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK1b where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below)
import OCF.Align.YiK1 as K
import OCF.Align.YiCarry as Y
open Y using (Carry)
open import OCF.Align.YiK1bBase
import OCF.Align.YiK1bReg as R
open import OCF.Align.YiK1bCarry
import OCF.Align.RR4RegOmega2 as O

CarryStage : ℕ → Set
CarryStage n = Carrys (suc n) F.zero ×
  (∀ η → F.Gd F.zero (V.cO F.zero) η → Carrys n (V.up F.zero η))

carry-stage-step : ∀ n → CarryStage n → CarryStage (suc n)
carry-stage-step n (r , old) = (r , rn) , coordinates
  where
  rn : Carry (pow (suc (suc n)) F.zero)
  rn = pow-node-carry n F.zero O.raw1 (F.suc F.zero)
    (λ η e → V.up F.zero η) (R.pow-zero-reg (suc (suc n))) tt
    (carrys-last (suc n) F.zero r)
    (λ η e b → carrys-last n (V.up F.zero η) (old η e))

  coordinate-reg : ∀ η → F.Gd F.zero (V.cO F.zero) η →
    Reg (pow (suc n) (V.up F.zero η))
  coordinate-reg η e = regs-last (suc n) (V.up F.zero η)
    (proj₂ (R.stages (suc n)) η e)

  under-one : ∀ a → F.Cp F.zero a O.raw1 → Carry (pow (suc n) (V.up F.zero a))
  under-one a (inj₁ refl) = rn
  under-one a (inj₂ (inj₁ refl)) = carrys-last (suc n) F.zero r
  under-one a (inj₂ (inj₂ ()))

  go : ∀ η → F.Lgl F.zero η → F.Cp F.zero O.raw1 η →
    Carry (pow (suc n) (V.up F.zero η))
  go G.zero l (inj₁ ())
  go G.zero l (inj₂ ())
  go (G.suc a) l (inj₁ refl) = rn
  go (G.suc a) l (inj₂ q) =
    pow-node-carry n (V.up F.zero a) (V.cO (V.up F.zero a))
      (V.Ω̂ (V.up F.zero a)) (λ ζ d → V.up (V.up F.zero a) ζ)
      (coordinate-reg (G.suc a) (inj₂ q , l))
      (V.Lgl-cO (V.up F.zero a)) (go a l q)
      (λ ζ d b → carrys-last n (V.up (V.up F.zero a) ζ)
        (read-carrys n (V.up F.zero a) pa ra ζ d b))
    where
    ea : F.Gd F.zero (V.cO F.zero) a
    ea = q , l
    pa : Below (F.suc (V.up F.zero a)) (V.Ω̂ (V.up F.zero a))
    pa = R.coordinate-suc-root a ea
    ra : Carrys (suc n) (V.up F.zero a)
    ra = old a ea , go a l q
  go (G.lim f) (st , lf) (inj₁ ())
  go (G.lim f) (st , lf) (inj₂ (m , q)) =
    pow-lim-carry (suc n) (λ j → V.up F.zero (f j)) term
    where
    term : ∀ j → Carry (pow (suc n) (V.up F.zero (f j)))
    term j with F.cmpC F.zero (f (j + m))
      (subst (λ z → F.Cp F.zero (f j) (f z)) (+-comm m j) (K.up-to F.zero f st m j))
      (F.Cp-tr F.zero q (K.up-to F.zero f st j m)) (lf (j + m))
    ... | inj₁ below-one = under-one (f j) below-one
    ... | inj₂ above-one = go (f j) (lf j) above-one
  go (G.lc () c t g) l q
  go (G.em () a) l q
  go G.top l (inj₁ ())
  go G.top l (inj₂ ())

  coordinates : ∀ η → F.Gd F.zero (V.cO F.zero) η →
    Carrys (suc n) (V.up F.zero η)
  coordinates η e = old η e , go η (proj₂ e) (proj₁ e)

carry-stages : ∀ n → CarryStage n
carry-stages zero = (Y.tw0-carry , Y.tw1-carry) , (λ η e → Y.read0-carry η)
carry-stages (suc n) = carry-stage-step n (carry-stages n)

pow-zero-carry : ∀ n → Carry (pow n F.zero)
pow-zero-carry n = carrys-last n F.zero (proj₁ (proj₁ (carry-stages n)))

tower-carry : ∀ n → Carry (V.tw n)
tower-carry n = subst Carry (pow-tw n) (pow-zero-carry n)

limit-carry : Carry V.Λ
limit-carry = tower-carry

k1′ : Y.K1′
k1′ = record { tower = tower-carry ; limit = limit-carry }

tower-legal : ∀ n → V.Legal (V.tw n)
tower-legal = V.Legal-tw

limit-legal : V.Legal V.Λ
limit-legal = V.Legal-Λ

tower-source : ∀ n → Y.Source
tower-source n = Y.source (V.tw n) (tower-carry n) (tower-legal n)

limit-source : Y.Source
limit-source = Y.source V.Λ limit-carry limit-legal
```

## 一步定理与新增使用的字段

`read-root` 把 `Below (suc y) (Ω̂ y)` 传给每个原守卫读回，
用的是字面的 `suc η` Ω 分支、Ω 对 Below 的保持，以及原 cO 的 CP 路径。
`coordinate-suc-root` 在 Raw 0 的正坐标域直接给这个较强路径；
它不是新 Reg／Carry 字段，也不作为未填的全塔假设。

`read-regs n`／`read-carrys n` 是同一个任意层一步接口：
已给 y 在 0..n+1 次 Ω 下的证据与上述路径，即给每个读回在
0..n 次 Ω 下的证据。n=1 正是 K1 停点缺的“读回再取 Ω”；
前提中下一次 Ω 的证据必须实填，不能称作从单份 Carry 的自动保持。
全塔证明用外层次数归纳与内层 Raw 结构递归生产这些前提：
后继坐标所需的 0..n+1 份证据来自其真子坐标的同一递归，
最小坐标所需的塔证据则来自上一归纳包，不循环使用 k1′。

新用到的原字段逐项为：

- Reg 的根 `Below (suc k) node`：`pow-upN-reg` 在槽位进入 lc.k 时
  把它接到迭代后第一支的路径；其余三个递归字段沿槽位下降。
- Reg 的全部原守卫分支：`read-regs` 的后继行填完整分支 Reg，
  不要求坐标有 LglB。
- Carry 的全 Reg 字段与第一支 Carry：分别供全分支 Reg 与原 CP 运输。
- Carry 的 LglB 分支字段：后继行调用 `read-carrys` 递归，只在该域取证。
- LglB.Nested 的下界 Lgl、第一支及**全部原守卫分支**：
  Raw lc 行把它们送入 `pow-upN-carry`，不从根 Lgl 推断 Nested。

这些条件有实际闭实例：`coordinate-suc-root raw1 (inj₁ refl , tt)`、
`carry-stages n` 及其所有坐标字段是构造出的证据；没有 Funext 或公理。

## 结论档位与翻译账

**编译定理：** k1′、全 n tower-carry 与 limit-carry；Reg 侧全 n
tower-reg／limit-reg；合法闭源 tower-source／limit-source。
闭项仍是原 tw 与 Λ；本轮只证 Carry／Reg 性质，
未给序数值比较，未提高已有 ψ₀(Ω_x) 值前沿。

**有限测试：** 无。**判断：** 本结果完成 K1′ 的规范全塔证书义务，
不据此声称一般 `Reg y, Below y (Ω̂ y), Carry (Ω̂ y)` 已自动给
Carry (Ω̂ (Ω̂ y))，也未否定 ReadOmegaCounterexample 或乙路线。
止损反例未构造；规范全塔正面目标已交，因此不继续搜索或写折叠。

翻译账：没有新树节点、记号规则、基本列标签或按具体层号定制的
前提；有限次 Ω 的归纳包只是原证书的有限合取。较强的路径来自
树自己的坐标与原 Ω 分支，不读记号。仍沿用原 LevelFix Ω 的定义，
不声称其历史设计已摆脱记号启发。第 4 层反逼：无。

所有 cmpC 比较都在原 Raw 类型内，以同一项 f(j+m) 为字面公共界，
两条 Cp 显式给出，Lgl 来自该项。Below 只作结构路径，不送进比较器；
没有裸下标律或全局三歧。

## 冷编清单

四件均已删自己接口单路冷编，退出码均 0，各有目标 Checking 行。
本轮只删除 YiK1b 自己的接口，依赖用缓存，
不声称从头重编整个导入闭包。复现从仓库根，库文件含 stdlib 与 cubical：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK1bBase.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK1bReg.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK1bCarry.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK1b.lagda.md +RTS -M6G -RTS
```

审计结果：

- 四件均 `--safe --without-K --lossy-unification`；公设、洞、跳过停机／
  正性检查的指示、信任相等、Funext 前提均为 0；无绝对路径与尾随空白。
- importclosure 白名单为 `OCF.Align.Yi`、`OCF.Align.RR4RegOmega2`、
  `OCF.Align.RR4CoordRoot`、`OCF.Align.LevelFix`、`OCF.Free.Level`、
  `OCF.BTBO`。Base／Reg／Carry／主篇的本地闭包为 23／24／24／26，
  库叶均 19，禁用表与白名单外均 0；四份成功编译器图的本地集合逐一相同。
- 成功 HTML 的定义切片：k1′ 145、tower-carry 141、limit-source 154、
  tower-reg 106、read-root 42、read-regs 92、read-carrys 120 块；
  各根记号模块块数与记号词命中均 0。单路 6G 成功生成 EboLean3Lab
  的 HTML 作正对照，ebo-lab″ 为 352／33／36；它不在本轮导入闭包。
  切片是语法近似，不代替编译器闭包或序数值验收。
- README 只增补当前状态与翻译账，LOG 追加本轮记录，旧结论保留。
  没有改原定义、写折叠、安装包、提交或推送。
