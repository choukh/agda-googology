# RecB: 底对 $n$ 递归, 世界做成塔 (入口)

> 不含记号. 构造一路 RecB (配对否定一路 NegRecB), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 导入闭包只有 stdlib 与 `OCF.Lean.CRw*`, `OCF.Lean.RecB*`. 不改任何已有文件.
>
> **任务** (作者本轮选定, 原话 "CRw 上底做成递归"; 说明 "在 CRw 上让 '底' 对层号 LH 递归, 世界做成塔 (wdep₁ 的提示), 一个定义覆盖 X₂ 及以上各站; 报行数与读法").
>
> | 文件 | 内容 |
> |---|---|
> | [RecBIf](RecBIf.lagda.md) | 接口: 每一层世界的移动 (`CRwIf`) 与初始世界 (定稿 01:48) |
> | [RecBFold](RecBFold.lagda.md) | 底 `Sb n` (对 $n$ 递归), 地板, 同底折叠 `ΦS` (对一切种类结构), 跨底折叠 `ΦX n` (对一切 $n$), 形状 |
> | [RecBPath](RecBPath.lagda.md) | 塔上的路径 `PSL Q`, 上抬 `lift`, 定理 `PH-ΦS` (同底保路径, 一切 `Q`), **`PH-ΦX↓`** (跨底把上抬的路径带下来, 一切 `Q`) |
> | [RecBCmp](RecBCmp.lagda.md) | 与 CRw 闭项的有限测试 (验收文件, 不在闭包里) |
> | 本篇 | 实例 `J₁`, 地板带路径, 世界塔 `QL`, 下降 `desc`, 闭项 `TN`, `TD`, `Tω`, 证书, FGH |
>
> **做到了什么, 没做到什么 (先说).** 底对 $n:\mathbb N$ 递归 (层号 $(n,m)$ 读 $\Omega\cdot n+m$), 一份同底折叠、一份跨底折叠覆盖一切 $(n,m)$; 世界是塔 (每个底一层世界, 都是可数树). **没有**做到 "底对层号 `LH` 递归": 底的下标是 $\mathbb N$, 一切层号在 $\Omega\cdot\omega$ 之下, 没有共尾度 $\Omega_2$ 的层号 (`lΩ k g`, $k\neq$ `lz`), 世界塔的每一层都是可数树 (见 §5 卡点). 离 `tw n` 与 $\Lambda$ 还远.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RecB where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to Amap)
open import Data.List.Relation.Unary.All.Properties using (map⁻)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; FGH)
open import OCF.Lean.RecBIf
```

## §1 实例

每一层世界的移动同 CRw 的 `I₁` (可入 $B\lhd e$, 进入后 $e+1$, 回灌 $B\boxplus\mathrm{leg}\,c$), 初始世界 $1$.

```agda
J₁ : RecBIf
J₁ = record { mv = I₁ ; W₀ = hs hz ; o₀ = hself ; lW₀ = tt }

open import OCF.Lean.CRwFold I₁ using (PS; module PS; PH; ⊏⊑; sh→lg; Sh; topT)
open import OCF.Lean.CRwPath I₁ using (PH-⊞; PH-ι; PH-up)
open import OCF.Lean.RecBFold J₁
open import OCF.Lean.RecBPath J₁
```

## §2 地板带路径

自己的结构: 第 $c$ 个分量里的一切树在 $c+1\lhd W$ 的世界里带路径 (分量里不动世界); 地板的根在 $1\lhd B$ 里有证据, 分支 $y$ 进入世界 $y+1$. 上抬的结构: 指标种类平凡, 分量地板的新种类 Kripke 式可入.

```agda
module _ (n : ℕ) where
  PH-cp : ∀ c W → hs c ⊲ W → ∀ x → PH (PSX n) W (ι {Ix} {FX (Sb n)} (cp c) x)
  PH-cp c W q hz = tt
  PH-cp c W q (hs x) = PH-cp c W q x
  PH-cp c W q (hl f) = λ k → PH-cp c W q (f k)
  PH-cp c W q (hΩ κ g) = q , λ e _ → PH-cp c W q (g e)

  PH-gtX : ∀ y W → y ⊲ W → PH (PSX n) W (gtX n y)
  PH-gtX hz W q = tt
  PH-gtX (hs c) W q = PH-⊞ (PSX n) (gtX n c) (ι {Ix} {FX (Sb n)} (cp c) (topT (Sb n) (fl n) (hs c))) (PH-gtX c W (⊲ᴮ-tr (hsuc hself) q)) (PH-cp c W q (topT (Sb n) (fl n) (hs c)))
  PH-gtX (hl f) W q = λ k → PH-gtX (f k) W (⊲ᴮ-tr (hlim k hself) q)
  PH-gtX (hΩ () _) W q

  PH-fl : ∀ B → hs hz ⊲ B → PH (PSX n) B (fl (suc n))
  PH-fl B o = o , λ y a → PH-gtX y (hs y) (hsuc hself)

  PH-gtL : (Q : PS (Sb n)) → ∀ y W → PH (lift Q) W (gtX n y)
  PH-gtL Q hz W = tt
  PH-gtL Q (hs c) W = PH-⊞ (lift Q) (gtX n c) (ι {Ix} {FX (Sb n)} (cp c) (topT (Sb n) (fl n) (hs c))) (PH-gtL Q c W)
    (PH-ι (FQ Q) (cp c) (topT (Sb n) (fl n) (hs c)) (tt , λ e a → PH-up (PSL Q c) e (proj₂ (proj₂ a))))
  PH-gtL Q (hl f) W = λ k → PH-gtL Q (f k) W
  PH-gtL Q (hΩ () _) W
```

## §3 世界塔与下降

`Ok n Q`: 第 $n+1$ 个底上的结构 `Q` 满足 `PH-ΦX↓` 的两个前提. `QL n`: 第 $n+1$ 个底上的树要带的路径结构的塔, 自己的 `PSX n` 在头, 下层的结构上抬一次接在后面. 一切结构都在同一个初始世界 $W_0=1$ 里出发.

```agda
record Ok (n : ℕ) (Q : PS (Sb (suc n))) : Set where
  field
    evI : ∀ W → hs hz ⊲ W → PS.Ev Q W ιK
    ptl : ∀ B → hs hz ⊲ B → PH Q B (fl (suc n))
open Ok

Qn : ℕ → Set₁
Qn n = Σ (PS (Sb (suc n))) (Ok n)

okOwn : ∀ n → Ok n (PSX n)
okOwn n = record { evI = λ W o → o ; ptl = PH-fl n }

liftE : ∀ {n} → Qn n → Qn (suc n)
liftE {n} q = lift (proj₁ q) , record { evI = λ W o → tt ; ptl = λ B o → tt , λ y _ → PH-gtL (suc n) (proj₁ q) y B }

QL : ∀ n → List (Qn n)
QL zero = (PSX 0 , okOwn 0) ∷ []
QL (suc n) = (PSX (suc n) , okOwn (suc n)) ∷ map liftE (QL n)

Gd : ∀ n → HB (Sb (suc n)) → Set₁
Gd n h = All (λ q → PH (proj₁ q) (hs hz) h) (QL n)
```

**下降.** 第 $n+1$ 个底的树: 用自己的结构作跨底折叠 (目标第 $n$ 个底的第 $0$ 层, 当前界是那一层的地板), 下层的结构由 `PH-ΦX↓` 带下来; 到第 $0$ 个底 (可数树) 为止.

```agda
↓Gd : ∀ n (h : HB (Sb (suc (suc n)))) (p : PH (PSX (suc n)) (hs hz) h) →
      All (λ q → PH (lift (proj₁ q)) (hs hz) h) (QL n) →
      Gd n (ΦX (suc n) hz (hs hz) tt (z⊲ᴮ (hs hz)) (fl (suc n)) h p)
↓Gd n h p = Amap (λ {q} pq →
  Down.PH-ΦX↓ n (proj₁ q) (evI (proj₂ q)) (ptl (proj₂ q)) hz (hs hz) tt (z⊲ᴮ (hs hz)) (fl (suc n)) h p
    (hs hz) hself (ptl (proj₂ q) (hs hz) hself) pq)

desc : ∀ n (h : HB (Sb (suc n))) → Gd n h → Cd
desc zero h (p ∷ []) = ΦX 0 hz (hs hz) tt (z⊲ᴮ (hs hz)) hz h p
desc (suc n) h (p ∷ ps) =
  desc n (ΦX (suc n) hz (hs hz) tt (z⊲ᴮ (hs hz)) (fl (suc n)) h p) (↓Gd n h p (map⁻ ps))

Sh-desc : ∀ n h g → Sh (desc n h g)
Sh-desc zero h (p ∷ []) = Sh-ΦX 0 hz (hs hz) tt (z⊲ᴮ (hs hz)) hz h p
Sh-desc (suc n) h (p ∷ ps) = Sh-desc n _ _
```

## §4 闭项, 证书, FGH

`inp n m`: 第 $(n+1, m)$ 层的地板经同底折叠到 $(n+1, 0)$; 每个结构的路径由 `PH-ΦS` 给出. `TN n m`: 再一路下降到可数树. `TD n`: 对 $m$ 的对角 (同 CRw 的 `TU2`). `Tω`: 对 $n$ 的累加对角.

```agda
inp : ∀ n m → LgB m → HB (Sb (suc n))
inp n m lm = ΦS (Sb (suc n)) (fl (suc n)) m (wfC m) lm hz (z⊲ᴮ m) (fl (suc n)) (top (suc n) m)

every : ∀ {A : Set₁} {P : A → Set} → (∀ x → P x) → ∀ xs → All P xs
every f [] = []
every f (x ∷ xs) = f x ∷ every f xs

gd-inp : ∀ n m lm → Gd n (inp n m lm)
gd-inp n m lm = every (λ q →
  let open G (proj₁ q) ; open Top (fl (suc n)) (ptl (proj₂ q)) in
  PH-ΦS m (wfC m) lm hz (z⊲ᴮ m) (fl (suc n)) (top (suc n) m) (hs hz) hself
    (ptl (proj₂ q) (hs hz) hself) (PH-top m (hs hz) hself)) (QL n)

TN : ℕ → (m : Cd) → LgB m → Cd
TN n m lm = desc n (inp n m lm) (gd-inp n m lm)

LgB-TN : ∀ n m lm → LgB (TN n m lm)
LgB-TN n m lm = sh→lg _ (Sh-desc n (inp n m lm) (gd-inp n m lm))

-- 对 m 的对角: y₀ = 0, y_{k+1} = y_k ⊞ TN n (y_k + 1)
yN : ℕ → ℕ → Cd
lg-yN : ∀ n k → LgB (yN n k)
yN n zero = hz
yN n (suc k) = yN n k ⊞ TN n (hs (yN n k)) (lg-yN n k)
lg-yN n zero = tt
lg-yN n (suc k) = Lg-⊞ (yN n k) (TN n (hs (yN n k)) (lg-yN n k)) (lg-yN n k) (LgB-TN n (hs (yN n k)) (lg-yN n k))

TD : ℕ → Cd
TD n = hl (yN n)

LgB-TD : ∀ n → LgB (TD n)
LgB-TD n = (λ k → ⊞-fst (yN n k) (TN n (hs (yN n k)) (lg-yN n k))) , lg-yN n

-- 对 n 的累加对角
zω : ℕ → Cd
zω zero = TD 0
zω (suc k) = zω k ⊞ TD (suc k)

lg-zω : ∀ k → LgB (zω k)
lg-zω zero = LgB-TD 0
lg-zω (suc k) = Lg-⊞ (zω k) (TD (suc k)) (lg-zω k) (LgB-TD (suc k))

Tω : Cd
Tω = hl zω

LgB-Tω : LgB Tω
LgB-Tω = (λ k → ⊞-fst (zω k) (TD (suc k))) , lg-zω

fghω : ℕ → ℕ
fghω = FGH Tω
```

## §5 读法与卡点

**读法 (判断, 没有值的定理).** 同 CRw 的约定 (ψ(a+1)=ψ(a)·ω, ψ(0)=1, 外加累加). 第 $n+1$ 个底是层号 $\Omega\cdot(n+1)$, 它的地板 `fl (suc n)` 读 $\Omega_{\Omega\cdot(n+1)}$ (指标种类 $\Omega_1$ 的分支 $y\mapsto\sum_{c<y}\Omega_{\Omega\cdot n+c+1}$). `TN n m` 读 ψ₀(Ω_{Ω·(n+1)+m}); `TD n` 读 ψ₀(Ω_{Ω·(n+2)}); **`Tω` 读 ψ₀(Ω_{Ω·ω})**. 与 CRw 对照: `TD 0` 与 CRw 的 `TU2` 同读 ψ₀(Ω_{Ω·2}); `TD 1` 读 ψ₀(Ω_{Ω·3}), 是高于 ψ₀(Ω_{Ω·2}) 的第一个闭项. 这些读法都没有定理支撑.

**卡点: 到 `LH` 递归还差什么 (判断, 未编译).**

1. **底的下标.** 本路的底对 $n:\mathbb N$ 递归, 下一个底是 "第 $n$ 个底上一切可数塔的并, 加一个 $\Omega_1$ 指标分量". 对 `LH` 递归时, 层号 `lΩ k g` 的底要是 $\sup_{c\,:\,\texttt{HB (Lv k)}}$ `Lv (g c)` 再加 `step (Lv k)` 分量 (本路的指标分量是 $k=$ `lz` 的情形). 那时分量的下标 $c$ 是第 $k$ 层的值, 不是可数树.
2. **世界塔的一层要换成第 $k$ 层的值.** 跨底比较的公共上界是世界的界; 下标是第 $k$ 层的值时, 界也是第 $k$ 层的值, 而第 $k\ge1$ 层的第一位置依赖世界 (`NegCRwWorld.wdep₁`), 所以世界的一层要再带一个第 $k$ 层的世界: 世界塔要按坐标分支, 不是本路这样每层一棵可数树.
3. **回灌.** 本路的回灌 $B\boxplus\mathrm{leg}\,c$ 是可数树上的. 第 $k$ 层的值上要一个把输出坐标抬到界之上的合法操作 (`⊞` 对一切种类结构有, `leg` 只对可数树写了); 以及与之配套的可入律.
4. **冻结的范围.** 本路的上抬只在上层的指标种类上平凡; 上层的指标分量换成 `step (Lv k)` 后, 那个分量里的种类有自己的坐标层, 上抬时它们是否仍可平凡, 未验证.

## §6 行数 (定义级切片)

脚本 `Survey/scripts/recb/locslice_recb.py` (口径同 `crw/locslice_crw.py`: 定义级切片, 计 agda 块里非空非注释行; 参数化模块经模块应用使用, 用到的模块内定义手工列为根). **脚本的一处改动, 如实:** CRw 的根 `open` 了 `Thm PH-topL using (PH-ΦX)` 与 `Top PH-topL using (PH-top)`, 切片从任一 CRw 块经根会把 CRw 的折叠 `Φ` 与 CRwPath 全部拖进来 (不改时层 3 是 1050); RecB 只用 CRw 的 `I₁`, `leg`, `FGH`, 它们不依赖这些 `open`, 脚本对 `OCF.Lean.CRw` 不跟随根的 `open`. 2026-11-06 跑出 (主闭项 `Tω`):

| 层 | RecB (`Tω`) | 对照 (取自各文件) |
|---|---|---|
| 1 定义 | 245 | CRw 251 |
| 2 + 折叠, 实例, 闭项, FGH | 810 | CRw 692 |
| 3 + 证书 | **817** | CRw **696** (ψ₀(Ω_{Ω·2})), X1Up 1111 (ψ₀(Ω_{Ω·2})), FabLFReGen 1513 |

第 3 层逐模块: `RecBPath` 208, `CRwBase` 149, `CRwFold` 148, `RecBFold` 113, `RecB` 86, `CRwPath` 64, `CRw` 33, `CRwIf` 10, `RecBIf` 6. 闭包里 `OCF.Lean.CRw*`, `RecB*` 之外的仓库模块: 0. 记号模块: 0. 层 2 含 `RecBFold` 根上 `open` 的 `Sh` 一组 (约 30 行, 本该在层 3), 层 3 总数不受影响.

**逐件增量** (第 3 层; RecB 新写 413 行, 沿用 CRw 的块 404 行; CRw 的 696 里 RecB 不用的块 292 行: CRw 的 `Φ`, `PSX`, `PSL`, 搬运与 `PH-ΦX`, `topL` 的路径等).

| 件 | 行 | 说明 |
|---|---|---|
| 底的递归 (`Ix`, `FX`, `XSof`, `Sb`, `ιK`, `fl`, `gtX`, `top`) | 23 | 新 |
| 世界的策略 (`pX`, `PSX`) | 15 | CRw 的 `pX`, `PSX` 对一切 $n$ |
| 决定 (`dcx`, `dcI`) | 7 | CRw 的 `dcx` 加底种类一行; 指标种类一份 |
| 折叠 (`ΦS`, `ΦX`, `AccC`, `wfC`, `gC`) | 45 | CRw 的 `Φ` (两种目标) 拆成两个对一切底的折叠 |
| 形状 (`Sh-ΦS`, `Sh-ΦX`) | 21 | |
| 搬运与塔的路径 (`PSL`, `triv`, `FQ`, `lift`, `ClP`…`upkA`, `PH-top`) | 67 | CRwPath §1, §3, §4 对一切 `Q` 重写; `triv`, `FQ`, `lift` 新 |
| 同底保路径 `PH-ΦS` 及辅助 | 67 | CRwPath §5 对一切 `Q`, 一切底 |
| 跨底带路径 `PH-ΦX↓` 及辅助 (`Down`, `Cp`) | 70 | 新 |
| 实例, 地板路径 (`J₁`, `PH-cp`, `PH-gtX`, `PH-fl`, `PH-gtL`) | 21 | |
| 世界塔与下降 (`Ok`, `Qn`, `okOwn`, `liftE`, `QL`, `Gd`, `↓Gd`, `desc`, `every`, `gd-inp`) | 33 | 新 |
| 闭项, FGH (`inp`, `TN`, `yN`, `lg-yN`, `TD`, `zω`, `Tω`, `fghω`) | 19 | |
| 证书 (`Sh-desc`, `LgB-TN`, `LgB-TD`, `lg-zω`, `LgB-Tω`) | 12 | |

路径与世界塔专用的块合计 322 行 (第 3 层的 39%), 折叠本身 (`ΦS`, `ΦX`, 决定, 累加) 77 行. 若 CRw 的路径定理当初就对一切 `Q` 写, RecB 的 134 行 (搬运 + `PH-ΦS`) 可直接沿用 (估计). 读法从 ψ₀(Ω_{Ω·2}) 到 ψ₀(Ω_{Ω·ω}) (判断) 多 121 行; 跨读法的行数不作结论.

**累加, 如实.** 同 CRw: 两个折叠的后继与 ℕ-极限子句取部分积、部分和, 坍缩取回灌链; 地板的 `gtX` 取部分和; 对 $n$ 的对角 `zω` 取部分和 (否则相邻项不是第一位置, 对角不合法; 否定一路 `NegRecBPre.sup-diag-illegal` 报告了同一件事, 主审复核前不算数).

## §7 有限测试 ([RecBCmp](RecBCmp.lagda.md))

有界展开 (深度 4, 每个 ℕ-极限展开前 4 项) 的结点数: `TN 0 1` 与 CRw 的 `TU1` 相同, `TD 0` 与 CRw 的 `TU2` 相同 (`refl`). `TD 1` 在深度 4 是 32, 深度 5 与 `TD 0` 相同: 这个测试分不开 `TD 0` 与 `TD 1`, 不说明任何读法. 路径指纹 (沿第 2 项走 30 步) 在 6G 内 10 分钟未完成, 已停. 测试不是证明.

## §8 翻译账

- **新结点, 新字段.** 无新结点. 新组织: 底是 $\mathbb N$ 上的递归 `XSof`; 每个底多一个**指标分量** `step S⊥` (这一层自己的 $\Omega_1$).
- **由树逼出.** (1) **指标分量** (判断, 没有编译的否定): 跨底折叠在移动世界的种类上回灌 ($Boxplus\mathrm{leg}\,c$); 若那个种类同时是下层的 $\Omega_1$ (CRw 的写法: $\Omega_1$ 是分量 $0$ 的新种类), 输出的分支要在下层世界 $c+1$ 里带路径, 输入的分支只在 $(Boxplus\mathrm{leg}\,c)+1$ 里带, 方向反了, `PH-ΦX↓` 证不出. 让每个底有自己的 $\Omega_1$ 指标种类, 回灌只发生在它上面, 而它在下层结构里平凡 (`lift` 的 `triv`), `PH-ΦX↓` 就成立. 形状与 `LFReTy.Lv (lΩ k g)` 的 `step (Lv k)` 分量相同 ($k$ = 第 $0$ 层); 那里已自述为记号引导, 本路是从路径的搬运逼出, 两者一致是事实, 不是推论. (2) 跨底时底种类一律留 (它们的层号在目标之下). (3) 世界塔: 下层的结构在上层上抬 (`lift`), 第 $c$ 个分量的新种类 Kripke 式可入 (同 CRw, X1Up `naive-anti`).
- **受记号启发, 如实.** 读法是对照扩展 Buchholz 记号的判断; $\Omega\cdot n+m$ 的层号形状.
- **摆脱侧.** 两个折叠对一切底一份, 两条路径定理对一切结构 `Q` 一份, 下降对一切 $n$ 一份: 下一站 ($\Omega\cdot(n+1)$) 不需要新写定义. 这一步**没有**让树说出 "对 `LH` 递归" 怎么写 (§5 卡点).
- **攀爬侧.** 读法 ψ₀(Ω_{Ω·2}) → ψ₀(Ω_{Ω·ω}) (判断).

## §9 接手清单

1. **底对 `LH` 递归** (§5 卡点 1–4). 第一步: 把分量的下标从 `Cd` 换成第 $k$ 层的值 `HB (Lv k)` (层号 `lΩ k g`), 世界的一层换成 (第 $k$ 层的界, 第 $k$ 层的世界); 回灌要第 $k$ 层上的 `leg` 类操作. `PH-ΦX↓` 对一切 `Q` 的形状可以沿用 (判断).
2. **指标分量的否定** (交否定一路): 写成定理 "若移动世界的种类在下层结构里不平凡, 则 `PH-ΦX↓` 的结论对某个实例不成立".
3. **路径脚手架** 322 行 (39%) 仍是最大的一块.
4. **值的定理**: 没有. `TD 0` 与 CRw `TU2` 只有有限测试.
5. **地板合法** 没有证 (同 CRw 清单 3).

## §10 结论 (按档)

- **[定理]** 接口 `RecBIf` (定稿 01:48); 对一切 `J`: 底 `Sb n`, 同底折叠 `ΦS` (一切种类结构), 跨底折叠 `ΦX n` (一切 $n$), 形状 `Sh-ΦS`, `Sh-ΦX`; 对一切路径结构 `Q`: `PH-ΦS` (同底保路径), `PH-ΦX↓` (跨底把上抬的路径带下来); 实例 `J₁`; 地板带路径 `PH-fl`, `PH-gtL`; 世界塔 `QL`, 下降 `desc`; 闭项 `TN n m`, `TD n`, **`Tω`** (`Cd`), 证书 `LgB-TN`, `LgB-TD`, **`LgB-Tω`** (标准 `LgB`), FGH `fghω`.
- **[有限测试]** `RecBCmp`: `TN 0 1`, `TD 0` 与 CRw 的 `TU1`, `TU2` 有界展开结点数相同; 分不开 `TD 0` 与 `TD 1`.
- **[判断]** 读法 (`Tω` ψ₀(Ω_{Ω·ω})); §5 卡点; 指标分量由路径搬运逼出.
