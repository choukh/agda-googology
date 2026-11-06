# 结构关系, 第六轮: 两棵不同的第 1 层树, 分支随位置变, 含嵌套 `nκ`: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件.
>
> 1. **(HOLDS, 限定构造子) 对结构推导归纳的语义.** 关系 $\sqsubseteq^{\mathsf S}$ (第 1 层树之间) 有七个构造子: `n0ˢ`, `n1ˢ`, `⨾ˢ`, `nlˢ` (逐项), `nwʳˢ` (右边 `nw`), `prˢ` (部分和), **`κˢ`** (两边分支**随位置变**, 只要求在 $c\le c'$ 的位置对上分支相关). **定理 `snd`**: $x\sqsubseteq^{\mathsf S}x'$ ⇒ `Sem x x′`, 与 `StrRel5Nest.Sem` 同一个语义 (运行世界 $W\le W'$, 路径 $q\sim q'$ 对齐, 状态 `R∀`, 结论对一切读数路径对 $\sqsubseteq^{\mathsf P}$). 两棵树可以不同, 嵌套 `nκ` 在内, 对一切深度一个证明, 无参数. `StrRel5Nest.sem` 是推论 (`nest-rel`, `sem′`).
> 2. **没有收的构造子: `ni`, 传递, 左边 `nw`.** 未做, 不是否定. 判断 (理由在 §2): 传递与 `ni` 都要 "左边自比", 在 "一切读数路径" 的语义下就是**单个状态的结构自洽** (同一状态在两条读数路径上的读数相关), 要先证一条结构版 `coh₁` (对一切树, 含 `ni` 的 `Chn` 与 `nκ` 的格); 左边 `nw` 让左边第 0 格多出前端位置, 对齐 (`Al`) 不收.
> 3. **`HtCrossInst.MonoStep` 一类比较: 本轮的定理不直接适用.** `MonoStep` 陈述在高度折叠 `HtFeedFold` 上 (`Q.ΔΩ`, 输入世界 0→1, 底 1→1+ω), 本轮的 `snd` 在 `SumOneFold` (第 1 层树, 动作 `Step`) 上. 要用, 须把 `StrRel5Walk`/`StrRel5All`/本文移植到 `HtFeedFold` 的 `Walk` 与 `κc`. 判断: 两个折叠的 `nκ` 一句同形, 移植是机械的, 但未做; 也没有检查 `MonoStep` 涉及的树是否落在本文的七个构造子里 (它多一段上下文与状态, 要左边自比时就需要 §2 的自洽).

## 1 关系与定理

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel6 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nκ; nw; cnt; sum; sum-fst)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁; toV0)
open import OCF.Align.KNestSound using (nest; adv-sum)
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.StrRel4Gen using (Al-map)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; pr; vsᴾ; alSuccᴾ; alZeroᴾ)
open import OCF.Align.StrRel5Walk using (Env; Rn)
open import OCF.Align.StrRel5Suf using (rfx)
open import OCF.Align.StrRel5All using (module GoA)
open import OCF.Align.StrRel5Nest using (stepA; E; OA; R∀; advA; cvR; stepR; drpR; Sem)

infix 4 _⊑ˢ_
data _⊑ˢ_ : ∀ {V V′} → D one V → D one V′ → Set where
  n0ˢ  : ∀ {V V′} {x : D one V′} → n0 {W = V} ⊑ˢ x
  n1ˢ  : ∀ {V V′} → n1 {W = V} ⊑ˢ n1 {W = V′}
  ⨾ˢ   : ∀ {V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑ˢ x′ → y ⊑ˢ y′ → (x ⨾ y) ⊑ˢ (x′ ⨾ y′)
  nlˢ  : ∀ {V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑ˢ d′ n) → nl d ⊑ˢ nl d′
  nwʳˢ : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑ˢ x′ → x ⊑ˢ nw p x′
  prˢ  : ∀ {V V′} {x : D one V} {x′ y′ : D one V′} → x ⊑ˢ x′ → x ⊑ˢ (x′ ⨾ y′)
  κˢ   : ∀ {V V′ zz zz′} {u : ∀ {c} → V ⊲ c → Lg c → D one c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D one c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → u p lc ⊑ˢ u′ p′ lc′) →
         nκ zz u ⊑ˢ nκ zz′ u′

-- Sem x x′ 是 StrRel5Nest.Sem 的一般形: 两边是任意的树
SemT : ∀ {V V′} → D one V → D one V′ → Set
SemT {V} {V′} x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ →
  ∀ (q : V ⊲ W) (q′ : V′ ⊲ W′) → Al W W′ q lW q′ lW′ → ∀ w w′ (Y : F.St W) (Y′ : F.St W′) → R∀ Y Y′ →
  OA (Rn (E W lW l₁) x q w Y) (Rn (E W′ lW′ l₁′) x′ q′ w′ Y′)

snd : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ˢ x′ → SemT x x′
snd n0ˢ lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ = z0
snd n1ˢ lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r = stepR {Y = Y} {Y′ = Y′} r
snd (⨾ˢ {x = x} {x′ = x′} hx hy) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ =
  sq (Ox τ τ′) (snd hy lW lW′ l₁ l₁′ le q q′ hq (w ⨾ nw q x) (w′ ⨾ nw q′ x′) _ _ (advA {Y = Y} {Y′ = Y′} (Rn (E W lW l₁) x q w Y) (Rn (E W′ lW′ l₁′) x′ q′ w′ Y′) r Ox) τ τ′)
  where Ox = snd hx lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r
snd (nlˢ {d = d} {d′} hd) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ = lm (λ n → proj₁ (go n) τ τ′)
  where
  P = λ n → F.Rpt ac₁ d q lW l₁ stepA w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ lW′ l₁′ stepA w′ Y′ n
  st : ∀ n → R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go : ∀ n → OA (Rn (E W lW l₁) (d n) q (proj₁ (P n)) (proj₂ (P n))) (Rn (E W′ lW′ l₁′) (d′ n) q′ (proj₁ (P′ n)) (proj₂ (P′ n))) ×
             R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go n = snd (hd n) lW lW′ l₁ l₁′ le q q′ hq _ _ _ _ (st n) , st n
  st zero = r
  st (suc n) = advA {Y = proj₂ (P n)} {Y′ = proj₂ (P′ n)} (Rn (E W lW l₁) (d n) q (proj₁ (P n)) (proj₂ (P n))) (Rn (E W′ lW′ l₁′) (d′ n) q′ (proj₁ (P′ n)) (proj₂ (P′ n))) (st n) (proj₁ (go n))
snd (nwʳˢ {p = p} h) lW lW′ l₁ l₁′ le q q′ hq = snd h lW lW′ l₁ l₁′ le q (⊲-tr p q′) (rfx p hq)
snd (prˢ h) lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ = pr (snd h lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′)
snd {V} {V′} (κˢ {u = u} {u′} h) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ = lm (λ n → drpR (cell n))
  where
  cL : ℕ → F.Cl W V (cnt one)
  cL = F.κc ac₁ u q lW l₁ stepA w Y
  cR : ℕ → F.Cl W′ V′ (cnt one)
  cR = F.κc ac₁ u′ q′ lW′ l₁′ stepA w′ Y′
  eL : ℕ → Env
  eL n = E (F.v (cL n)) (F.lv (cL n)) (⊲-tr l₁ (F.wv (cL n)))
  eR : ℕ → Env
  eR n = E (F.v (cR n)) (F.lv (cR n)) (⊲-tr l₁′ (F.wv (cR n)))
  ΔL : ∀ n → F.Df (F.v (cL n))
  ΔL n = F.κΔ ac₁ u l₁ stepA (cL n)
  ΔR : ∀ n → F.Df (F.v (cR n))
  ΔR n = F.κΔ ac₁ u′ l₁′ stepA (cR n)

  St : ℕ → Set
  St n = (F.v (cL n) ≤ F.v (cR n)) × Al (F.v (cL n)) (F.v (cR n)) (F.av (cL n)) (F.lv (cL n)) (F.av (cR n)) (F.lv (cR n)) ×
         R∀ (F.Sv (cL n)) (F.Sv (cR n))

  out : ∀ n → St n → OA (ΔL n) (ΔR n)
  out n (vle , H , rs) =
    GoA.cellᴬ (eL n) (eR n) u u′ R∀ (λ {Y₂} {Y₂′} Δ Δ′ → advA {Y = Y₂} {Y′ = Y₂′} Δ Δ′)
      (λ p p′ lc lc′ c≤ ad q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ r₁ →
         snd (h p p′ lc lc′ c≤) (F.lv (cL n)) (F.lv (cR n)) (⊲-tr l₁ (F.wv (cL n))) (⊲-tr l₁′ (F.wv (cR n))) vle q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ r₁)
      H (F.ap (cL n)) (F.ap (cR n)) (F.co (cL n)) (F.co (cR n)) (F.Sv (cL n)) (F.Sv (cR n)) rs

  st0 : St zero
  st0 = vsᴾ (proj₂ r) le ,
        alZeroᴾ lW lW′ (Al-map (λ ad → adv-sum (F.z Y) (F.z Y′) ad (toV0 (F.z Y) (F.z Y′) (vsᴾ (proj₂ r) z≤))) hq) (proj₂ r) le ,
        cvR (sum-fst W (F.z Y)) (F.lv (cL zero)) (sum-fst W′ (F.z Y′)) (F.lv (cR zero)) Y Y′ r

  stS : ∀ n → St n → St (suc n)
  stS n st@(vle , H , rs) =
    vsᴾ dr vle , alSuccᴾ dr (F.lv (cL n)) (F.lv (cR n)) vle ,
    cvR (sum-fst (F.v (cL n)) (F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt)) (F.lv (cL (suc n)))
        (sum-fst (F.v (cR n)) (F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt)) (F.lv (cR (suc n)))
        (F.Sv (cL n) F.⊕ ΔL n) (F.Sv (cR n) F.⊕ ΔR n) (advA {Y = F.Sv (cL n)} {Y′ = F.Sv (cR n)} (ΔL n) (ΔR n) rs O)
    where
    O = out n st
    dr = O (inj₁ (z⊲ (F.v (cL n)))) (inj₁ (z⊲ (F.v (cR n))))

  go : ∀ n → St n
  go zero = st0
  go (suc n) = stS n (go n)

  cell : ∀ n → F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt ⊑ᴾ F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt
  cell n = out n (go n) (inj₁ (z⊲ _)) (inj₁ (z⊲ _))

-- StrRel5 的嵌套族是特例
nest-rel : ∀ k {V V′} → nest k {V} ⊑ˢ nest k {V′}
nest-rel zero = n1ˢ
nest-rel (suc k) = κˢ (λ _ _ _ _ _ → nest-rel k)

sem′ : ∀ k → Sem k
sem′ k lW lW′ l₁ l₁′ le {V} {V′} = snd (nest-rel k {V} {V′}) lW lW′ l₁ l₁′ le

-- 两棵不同的树, 分支随位置变: 左边每格的分支是 1, 右边是 1 接上任意 (随位置变的) 一棵
diff : ∀ {V V′} (g : ∀ {c} → V′ ⊲ c → Lg c → D one c) → nκ {W = V} tt (λ {c} _ _ → n1 {W = c}) ⊑ˢ nκ {W = V′} tt (λ p l → n1 ⨾ g p l)
diff g = κˢ (λ _ _ _ _ _ → prˢ n1ˢ)
```

## 2 没有收的三个构造子 (判断)

- **传递.** `StrRel3Lo.sndˡ` 的传递一句在左边自比 (状态 $(Y,Y)$, 读数在固定的 `κ₀`, 所以 `reflᴼ` 给出状态自比). 这里状态关系 `R∀` 对**一切**读数路径对, $(Y,Y)$ 一对就是 "同一状态在任意两条读数路径上的读数结构相关", 是结构版的路径一致 (自洽). 要先证: 自洽的状态跑一切树, 输出自洽 (结构版 `KValSem.coh₁`, 含 `ni` 的 `Chn` 与 `nκ` 的格; 对齐 $q\sim q$ 要一条 `Al` 的自反律, 由 `KNestAdm.split` 给领先量). 判断: 没有否定的迹象, 约 200 到 300 行.
- **`ni`.** 层 0 的链 `Chn` 跑坐标树, 坐标由上一项输出给出, 输出可以含传递与部分和, 所以要 `StrRel3Zero.snd0` 的 "一切读数路径" 版对 $\sqsubseteq^{\mathsf P}$ 全部构造子成立, 其传递一句同样要上面的自洽.
- **左边 `nw`.** `Run (nw p x) q = Run x (⊲-tr p q)`: 左边从更低的树世界出发, 第 0 格多出前端位置 $[V_0,V)$. `Al` 只收右边前端多出 (`rfx`); 左边多出要有右边的位置对上. 判断: 对含 `nκ` 的 $x$, $\mathrm{nw}\,p\,x\sqsubseteq x$ 一般不成立 (左边的格更长). 没有编译反例.

## 3 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `κˢ` 只要 $c\le c'$ 处分支相关, 不带下标 | `walkᴬ` 的分支前提给的正是 $c\le c'$ 与对齐; 语义不读领先量 | **树逼的** |
| 不收左边 `nw` | 左边第 0 格多出前端位置, `Al` 不收 | **树逼的** (判断) |
| `prˢ`, `nwʳˢ` | `Run` 的展开, `rfx` | **树逼的** |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠, 没有 `Lab`, 没有记号. `snd` 对一切推导一个证明, 不按深度加前提. `KNest2Sound` 的下标 ($\alpha,\alpha'$, `Adm`) 在结构语义里**不需要**: 对齐数据 `Al` 取代了它.

## 4 审计与账

- 编译: 删掉 `StrRel6.agdai` 后从头编译, 退出码 0. 无禁用构造, 不出现 `Funext`.
- 导入闭包 (`--only` 同 [StrRel5](StrRel5.lagda.md) 的扩展表): 闭包 55 个模块 (本地 45, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `StrRel6:snd` 212 块, `diff` 19; 记号模块块数 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58.
- 代码行 (代码块内非空): 106.
