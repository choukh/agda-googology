# 分层互递归塔 (入口与判决): 每站头种类按自己的级回灌

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 作者本轮选定 "分层互递归塔". 本路 (前缀 `StratTw`) 是 [KindLv](KindLv.lagda.md) 接手清单第 1 条 (互递归的塔) 的**构造**一路; 否定一路前缀 `NegStratTw`, 共用接口 [StratTwIf](StratTwIf.lagda.md) (接口定稿 2026-11-05 19:13, 首次编译通过; 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提, 不用升界算子 (`RaiseIf`/`RaiseC`). 闭项与证书无模块参数. 已有文件一律未改.
>
> **判决: 闭项交了, 值没有定理.**
>
> - **(a) 交了.** 无条件闭项 `StratTwTw.TS : A`, 证书 `Lg-TS`, FGH `fghS`. 塔按 $s$ 普通 ℕ 递归 (前缀 $P_s$ 与前缀里的级 $X_s$), **检查器接受**; 第 $s+1$ 个分量的头种类对**一切** $s$ 按自己的级回灌 (`all-heads`, 定理), 级层是层号对角第 $s$ 项之上 (`KT-diag`), 读回是沿同形的级读回 (`KT-rd`), 升界只在 ℕ 下标上点更新并换 `step` 的第二分量.
> - **(b) 值: 没有定理.** 有形状定理 (下表), 其中两条说出仍有损的地方 (`lossy-inner`, `KT-top-lossy`). 读法 (判断) 见下, 不给数.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` 的元素, FGH 在树上算. 纲领 2: 无公理; 塔是普通 ℕ 递归, 级读回对同形证据结构递归, 折叠同 `KindLvRun`, 检查器接受. 纲领 3: 折叠里唯一的比较是 `cmpB` (公共上界 $\Lambda$); 升界只在可判定下标 (ℕ) 上做点更新; 没有 "升一份留别份" 于含函数下标 (`updHΛ-sep` 那一形状不出现); 接口不要求三歧或判定. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 塔的每一行由类型逼出 (下一站的种类是 `step (Lev X_s)`, 读回沿 `Sim` 的构造子走), 不看记号; 这一站新用到的字段是 **`Sim` 的 $\Omega$-构造子里的坐标转换 `cv`** (总结构的坐标回到前缀的坐标, 唯一一处) 与 **前缀结构的二元并** (`sup (⊤ ⊎ ⊤)`, 让第 $s$ 站的级只住在含分量 $\le s$ 的类型里).
>
> **离 ψ₀Λ 候选闭项还差什么 (判断).** KindLv 卡在 "级与对角的类型对不上" 这一个类型条件; 本路在类型上解开了它 (编译). 剩下的都是内容上的有损行, 已知的有: (1) 第 $s+2$ 站起级 `Y (s+1)` 是 $\Omega$-极限, 头种类读回的顶行读输入 $0$ (`KT-top-lossy`, 定理); (2) `Lev (X s)` 内部的种类退回 `fbA` (`lossy-inner`, 定理); (3) 每站求值 `evK` 在基世界里跑, 取平凡级回灌 (骨架总审 C1; 定义); (4) 级读回在极限级, 闭包结点, 写入经过 $\Omega$-路径时有损 (同 `KindLvRd`, 定义). 没有值定理, 不能说闭项到了哪里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StratTw where

import OCF.Align.StratTwIf
import OCF.Align.StratTwRd
import OCF.Align.StratTwTw
import OCF.Align.StratTwCmp
```

## 接口 (`StratTwIf`, 只有类型)

```text
KMap S′ T : j, cv                            -- 没有律
data Sim M : HB T → HB S′ → Set : sz, ss, sl, sΩ (∀ e → Sim (h e) (g (cv M κ e)) → Sim (hΩ (j M κ) h) (hΩ κ g))
RdSTy T = ∀ M c X → Sim M c X → LgW (step T) W → HB (Lev X) → DK T (lyL c) W → HB (Lev X) ; WrSTy T
record StratTw T : P, X, M, Y, sim, lY, Yfst (hs (Y s) ⊲[ w ] Y (suc s)), hd, hdE (E T (hd s) ≡ HB (Lev (X s)))
Bᴧ St s = hs (Y s) ; ΛS St = up (hl (Bᴧ St))
OwnHd St tp lv = ∀ s → Σ L : KLv T tp (ΛS St) (hd s) , lv (hd s) ≡ inj₁ L × ℓ L ≡ lyL (Y s)
```

律的定义域写在接口文件头: `Yfst` 是一对 $(\mathrm{hs}\,Y_s, Y_{s+1})$, 公共上界 $Y_{s+1}$ 本身; `sim` 是形状证据, 不比较; 两站的前缀级之间没有律.

## 分层 (第 1 条: 挑战 "互递归是真循环, 分层能解开")

KindLv 的草稿 (`Cs (suc s) = step (Lev (Ys s))`, `Ys s : HB (sup ℕ Cs)`) 停机检查失败. 本路:

```text
st 0 = (S₀ , 1) ; st (s+1) = nxtS (st s)                 -- 普通 ℕ 递归
nxtS (P , X) = (sup (⊤ ⊎ ⊤) [P , step (Lev X)] , hs (ι 左 X) ⊞ ι 右 (evK X))
C 0 = S₀ ; C (s+1) = step (Lev (X s)) ; U = sup ℕ C           -- C 只调用已造好的 X s
Y 0 = ι 0 1 ; Y (s+1) = hs (Y s) ⊞ ι (s+1) (evK (X s))       -- 总结构里的级, 另一条 ℕ 递归
sim s : Sim (MP s) (Y s) (X s)                               -- Sim-⊞, Sim-up, Sim-new 归纳
```

- **[编译] 分层能解开.** 上面整个塔与闭项检查器接受, 无停机编译指示.
- **[判断] 互递归那一版是类型层的真循环, 不只是检查器的弱点**: 类型 `HB (sup ℕ Cs)` 的种类 $\Sigma_i K(C_i)$ 含 $K(C_{s+1})$, 而 $C_{s+1}$ 要 $Y_s$ 的值. 没有写成否定定理; 本路也没有试归纳-递归的编码.
- **代价 [定理/定义].** 总结构里的级 $Y_s$ 与前缀里的级 $X_s$ 不是同一个项, 只是同形 (`sim s`); `Lev (Y s)` 与 `Lev (X s)` 一般不定义相等. 所以级读回要改写成沿同形递归 (`StratTwRd`, `KindLvRd` 的逐行对应), 头种类的坐标是 `HB (Lev (X s))` (前缀里的级), 级层是 `lyL (Y s)` (总结构里的级, 对角的字面位置). 两者的连接只在读回的类型里, 不需要搬运函数 (`Cvt`) 或函数外延.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `KMap`, `Sim`, `RdSTy`, `WrSTy`, `StratTw`, `Bᴧ`, `ΛS`, `OwnHd` | If | 接口 | 定义 |
| **`readS`**, `readSp`, `rdSS`, **`wrS`**, `wrKS` | Rd §1 | 沿同形的级读回与写入, 对一切 $T$, 一切同形证据 (对证据的构造子递归) | 定义 (停机由检查器) |
| `readS-fst`, **`Lg-readS`** | Rd §2–3 | 起点是第一位置; 合法由形状给出 (对一切数据) | 定理 |
| `rdST`, `wrST` | Rd §4 | 接口的实例 | 定义 |
| `Stg`, `nxtS`, `st`, `P`, `X`, `C`, `U`, `jP`, `cvP`, `MP`, **`Y`** | Tw §1–2 | 分层塔 | 定义 |
| `Sim-⊞`, `Sim-up`, `Sim-new`, **`sim`** | Tw §2 | 总结构的级与前缀的级同形 | 定理 (归纳) |
| `lY`, `Yfst`, `lΛ`, `one⊲`, **`StU`** | Tw §2 | 合法, 对角相邻项, 接口实例 | 定理 |
| `KA`, **`KT`**, **`lvU`**, **`ownU`** | Tw §3 | 底种类与**每站头种类**的级回灌; `ownU : OwnHd StU (tpK GU) lvU` | 构造; 接口性质 |
| `ColS`, **`TS`**, **`Lg-TS`**, **`fghS`** | Tw §0, §4 | 无条件闭项 | 构造; 无条件 |
| **`all-heads`**, **`head-fed`** | Cmp §1 | `lvU (hd s) ≡ inj₁ (KT s)` 对一切 $s$; 第 $s+2$ 站头种类 (= `head-lossy` 的位置) 有回灌 | 定理 (`refl`) |
| `KT-ℓ`, **`KT-diag`**, `KT-ℓ⊲` | Cmp §2 | 级层 $=$ `lyL (Y s)` $=$ `up (Bᴧ StU s)`; 第一位置证据是 `hlim s hself` | 定理 (`refl`) |
| `KT-E`, **`KT-rd`**, `KT-sees` | Cmp §3 | 坐标类型 $=$ 读回输出类型 `HB (Lev (X s))`; 读回 $=$ `readS (sim s)`; 读回不恒取起点 | 定理 (`refl`) |
| **`lossy-inner`** | Cmp §4 | `lvU κ ≡ inj₂ tt` 推出 $\kappa$ 是某个 `(suc s , inj₁ κ′)` (`Lev (X s)` 内部的种类) | 定理 |
| **`hd-occ`**, `start-hd` | Cmp §5 | `Y (s+1) = hs (Y s) ⊞ hΩ (hd s) g` (头种类在对角里, 前提可满足); 起始世界里界是 $0$ | 定理 (`refl`) |
| **`Y-lim`**, **`KT-top-lossy`** | Cmp §6 | `Y (s+1) = hΩ (hd s) g`; `KT (s+1)` 的读回在顶行读输入为 $0$ 的分支 | 定理 (`refl`); 有损的一行 |
| `idM`, `Sim-rf` | Cmp §7 | 同形对恒等自反 (`KindLvRd` 的情形在 `StratTwRd` 里) | 定理 |

## 与 `only-κ₁`, `head-lossy`, `updHΛ-sep` 的对应陈述

- `NegKindLvInst.only-κ₁`: KindLv 里只有 $\kappa_1$ 有级回灌. 本路: 一切头种类 `hd s` 都有 (`all-heads`); 没有级回灌的种类恰好是 `Lev (X s)` 内部的种类 (`lossy-inner`, 方向反过来的刻画).
- `NegKindLvInst.head-lossy`: 第 $s+2$ 站的头种类 `lvΛ … ≡ inj₂ tt`. 本路同一位置: `head-fed s : lvU (suc (suc s) , inj₂ tt) ≡ inj₁ (KT (suc s))`.
- `NegKindLvInst.updHΛ-sep`: 把 $\kappa_1$ 的升界推广到含函数的下标族推出分离子. 本路的头种类的下标是 `suc s : ℕ` (种类 `(suc s , inj₂ tt)`), 升界是 `upd` 在 ℕ 上的点更新, 不在含函数的下标上判定; 这一形状不出现. 原因 (类型事实): KindLv 的头种类以 `HB (Kc s)` 的高度为下标 (`inj₂ B_s`), 本路的总结构 `U = sup ℕ C` 的分量只以 ℕ 为下标, 前缀的二元并只用于造 $X_s$ 的类型, 不进总结构的世界.
- `NegKindLvLev.lv-not-self`: 种类的级不是自己. 本路头种类 `hd s` 在分量 $s+1$, 坐标是第 $X_s$ 级的高度, $X_s$ 在只含分量 $\le s$ 的前缀里 (类型事实), 与它一致.

## 闭项与 FGH 的类型原文

```text
StratTwTw.TS    : A                 -- ColS.Tψ GU LdU flU Λ lΛ one⊲ lvU, Λ = up (hl (λ s → hs (Y s)))
StratTwTw.Lg-TS : Lg TS
StratTwTw.fghS  : ℕ → ℕ             -- FLv.FGH (ordS TS)
StratTwTw.lvU   : LvFb U (tpK GU) Λ  -- (0,tt) ↦ KA ; (suc s , inj₂ tt) ↦ KT s ; 其余 ↦ inj₂ tt
StratTwTw.KT    : ∀ s → KLv U (tpK GU) Λ (hd s)
StratTwRd.SR.readS : ∀ {c X} → Sim M c X → LgW L₀ W → HB (Lev X) → D (lyL c) W → HB (Lev X)
```

## 前提实例

- `ColS` (`KindLvRun`) 的参数: `GU`, `LdU`, `flU` (由 `GenFoldInst` 对构造子递归的实例组装), `Λ`, `lΛ`, `one⊲`, `lvU` (本路).
- `KLv` 的实例: `KA`, `KT s` (对一切 $s$, 无条件). `OwnHd` 的实例: `ownU`.
- `Sim` 的实例: `sim s` 对一切 $s$; `Sim-rf c` 对一切 $c$.
- 按级回灌那一行在坍缩里非空: `hd-occ` (头种类的 $\Omega$-结点在对角的每一项里).

## 读法 (全部是判断; 只从树形与回灌算, 不用 R2)

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| 塔 | 第 $s+1$ 站的级 $Y_{s+1}$ 在 $Y_s$ 之上接一个以第 $X_s$ 级的高度为坐标的 $\Omega$-结点 (`hd-occ`, `Y-lim`); 塔的形状与 KindLv 草稿相同, 只是分层写出 | 定义; `sim` |
| 头种类的结点在最终坍缩里 | 不再取底支: 坐标沿 $v_{n+1}=\mathrm{readS}(\mathrm{top},\Delta_n)$ 迭代 $\omega$ 次 (同 KindLv 的 $\kappa_1$, 现在每站都有); 但第 $s+2$ 站起级是 $\Omega$-极限, 读回的顶行读输入 $0$, 只有路径进入某个有界坐标的分支的结点被读成新种类的结点 | `all-heads`, `KT-rd`, `KT-top-lossy`; 对折叠全程的不变式没写 |
| `TS` | 与 KindLv 的 `TK` 比: 第 1 站同形 ($Y_0=1$, `KT 0` 与 `K1` 同一种读回), 第 2 站起多了头种类的级回灌, 少了顶行; 两者没有 `ord` 的比较. 不给 ψ₀(Ω_x) 的数: 没有值定理, 上面四类有损行 (判决段) 各自压多少没有测 | 本表前两行; KindLv 的读法表 |

**结论 (判断).** "每站头种类按自己的级回灌" 在类型上写成了, 闭项编译; KindLv 的卡点 (级与对角的类型) 由分层加同形解开, 没有用到函数外延, 搬运函数或升界算子. 卡点移到内容: 级是部分和, 从第 2 站起是 $\Omega$-极限, 极限级没有以本层数据为坐标的种类, 顶行有损 (KindLv 接手清单第 3 条预言的情形, 现在是定理 `KT-top-lossy`).

## 第一个障碍

1. **[定理, 形状] 极限级的顶行有损** (`KT-top-lossy`). `Lev (hΩ κ g) = sup (E κ) (Lev ∘ g)` 没有新种类; 级读回在 $\Omega$-级的顶上只能读输入为 $0$ 的分支. 若要不损, 头种类的级层要是后继 (例如取 `hs (Y s)` 的前驱结构), 或读回要把顶行的数据分到各坐标分支 (要一个坐标, 在世界里有界的证据从哪来). 没有写实验.
2. **[定义] 每站求值在基世界里, 级回灌平凡.** `evK` 是 `KindLvEv` 的 (`λ _ → inj₂ tt`); 把每站求值也换成本路的 `lvU` 型回灌要每站一份 `StratTw` (站内的塔), 没有写.
3. **[判断] 值.** 没有 `ord` 的比较; 下一步最小的值实验是在第 1 站上比较 `TS` 与把 `KT 1` 换成 `inj₂ tt` 的同一折叠.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| 前缀 `Stg`, `nxtS` (二元并), ℕ 递归 | 停机: 第 $s$ 站的级的类型不能含 $C_{s+1}$ | 树逼出 (类型的分层) |
| `KMap`, `Sim`, `Sim-⊞/up/new`, `sim` | 前缀里的级与总结构里的级不定义相等 | 树逼出 (分层的代价); `cv` 在实例里是恒等, 是脚手架 |
| `StratTwRd` (`readS`, `wrS`, ...) | `KindLvRd` 逐行改成对 `Sim` 递归 | 树侧 (拷贝 + 换递归参数); 行数与 `KindLvRd` 同量 (120 对 110) |
| `KT s` (ℕ 点更新 + `step` 第二分量) | KindLv 草稿的 `KT s` | 树侧 |
| `ColS` | `KindLvTw.ColL` 逐字拷贝 | 脚手架 (行数切片: 导入 `KindLvTw` 会把它顶层的 `open KRd KΛc LdΛ` 算进闭项) |
| `ordS` | `KindLvTw.ordK` 逐字拷贝 | 脚手架 (同上) |
| `StU`, `ownU`, `hdE = refl` | 接口实例 | 第 4 层 |

归类 (判断): 提供信息. 新定义没有读自基本列规则的字段; 闭包定理 (`Lg-readS`, `Lg-TS`) 没有为某一站加专属前提; 不用 `Lab`. 信息是: 互递归可以拆成 "前缀 ℕ 递归 + 同形证据", 读回只需把递归参数从级换成同形证据; 第 4 层没有改前 3 层, 已有文件一律未改.

## 审计

- **编译.** 删自己的五个 `.agdai` (`probes/_build/2.8.0.2/agda/OCF/Align/StratTwIf.agdai`, `StratTwRd`, `StratTwTw`, `StratTwCmp`, `StratTw`) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/StratTw.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 5 秒, 峰值常驻约 0.9G. 接口 `StratTwIf` 首次编译 19:13 退出码 0.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0. 闭包里有 `HtTowerFTree` 等 (经 `GenFoldIf`), 同 KindLv; 前 3 层的定义级闭包里没有读进 `Ht` 的块 (行数脚本的检查).
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由 scratch 模块 `STSlice` (导入 `OCF.Align.StratTw`, `OCF.Align.KindLv`, `OCF.Align.Om1HnAccept`) 生成, 6G, 退出码 0, 峰值约 2.1G): `StratTwTw:TS` 355/0/0, `Lg-TS` 357/0/0, `fghS` 373/0/0, `lvU` 327/0/0, `KT` 324/0/0, `sim` 289/0/0, `Y` 281/0/0, `Tψ` 293/0/0, `StratTwRd:readS` 120/0/0, `Lg-readS` 134/0/0, `wrS` 120/0/0, `StratTwCmp:all-heads` 331/0/0, `KT-top-lossy` 328/0/0, `StratTwTw:ownU` 342/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 五个文件的代码块里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提, `REWRITE`; 不用 `RaiseIf`/`RaiseC`.

## 四层行数表

`probes/Survey/scripts/strattw/locslice_strattw.py` (同 `kindlv/locslice_kindlv.py` 口径: 定义级切片, agda 块非空非注释行; 参数化模块的模块内定义手工列为根, 见脚本头).

| 层 | 无条件 `TS`: 本路新增 / 其中 KindLv 文件 / 树侧全部 / 记号 |
|---|---|
| 1 定义 | 9 / 30 / 362 / 0 |
| 2 折叠 (沿同形的级读回, 嵌入, 按级回灌的折叠, 分层塔, 对角, 每站求值, 闭项, FGH) | 250 / 304 / 1449 / 0 |
| 3 证书 | 254 / 304 / **1453** / 0 |
| 4 对照, 形状 | 319 / 304 / 1518 / 0 |

前 3 层树侧 1453, **低于标杆 1513**; KindLv `TK` 1479 (同口径). 前 3 层闭包里没有 `GenFoldRun`, `KindLvRd`, `LvKtIf`, `NewTwrColl` 的块 (本路不用 NewTwr 的塔 `Kc`). 第一版导入 `KindLvTw.collLv`/`ordK`, 切片把 `KindLvTw` 顶层的 `open KRd KΛc LdΛ` 带进来, 前 3 层 1575, 超标; 改为拷贝 `ColS`, `ordS` 后 1453.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `StratTwIf` | 45 / 110 | 接口 |
| `StratTwRd` | 120 / 167 | 沿同形的级读回与写入 |
| `StratTwTw` | 164 / 257 | 坍缩 `ColS`, 分层塔, 同形, 级回灌, 闭项 |
| `StratTwCmp` | 53 / 118 | 形状定理 |
| `StratTw` | 6 / 本文件 | 入口 |
| `probes/Survey/scripts/strattw/locslice_strattw.py` | — | 行数脚本 |

## 接手清单

1. **极限级的顶行** (第一个障碍 1): 写一个小实验, 让头种类的级层落在后继上, 或在顶行用世界里的界把数据分到坐标分支; 交否定一路对准 "极限级读回无损" 的形状.
2. **值**: 第 1 站上 `TS` 与 "`KT 1` 换成有损" 的同一折叠做 `ord` 的比较.
3. **每站求值的回灌**: `evK` 换成带 `lvU` 型级回灌的折叠 (站内要一份分层塔).
4. **`StratTwRd` 与 `KindLvRd` 的等价**: `Sim-rf` 只说类型上包含; 逐结点等价 (`M = idM`, `c = X`) 没写.
