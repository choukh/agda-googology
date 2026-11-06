# 结构关系, 第十二轮: 对一切层的可靠性 `sem`: 入口

> **判决: PARTIAL (第 1, 2 项 HOLDS; 第 3, 4 项未做, 第一个障碍见 §3).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树, 折叠与合法性.
>
> 1. **(定理) `sem`: 对一切层 $L$, 结构关系蕴含两世界语义.** `sem : ∀ L → AccY L → Rel L lV lV′ x x′ → SemW L lV lV′ x x′`, 推论 `sem∀` (良基证明取 `accL L`). 一个证明对一切层 (含极限层 `hl` 与 $\Omega$-极限层 `hΩ`), 对 (良基证明, 推导) 字典序归纳, 无模块参数, 停机由结构检查给出. 八条规则都覆盖: 与层无关的六条 (`StrRel12Sem`), 同层节点 `niᴸ` (`StrRel12Ni.sem-ni`, 交接单第 1 项), `nκ` 的 `κᴸ` (`StrRel12Kp.sem-κ`, 交接单第 2 项).
> 2. **相对 `StrRel11Le` 改了两处 (都在第 4 层的关系与语义里, 不碰树与折叠), 理由由折叠的字面逼出, 是判断, 没有写成 "旧版不可靠" 的否定定理:**
>    - 语义的运行路径对与目标对从 `APair` 加强为 **`CP`** = `APair` + 顶端世界可比 $W\le W'$ + 两个顶端 `Lg` **自洽** (`StrRel12Al.Coh`: 极限的 `lg⊲ (st n) (wl (suc n)) ≡ wl n`, 遗传). 可比: 第 0 层目标上 `nκ` 的格世界是 $\Sigma_W z$, 格路径的对齐 (`Al`) 的 `aP` 要位置的值可比, 起点要 $W\le W'$; `StrRel11Le.SemL` 没有这一条, 两边都在 `self` 上时它的前提对 $W=5, W'=3$ 也成立. 自洽: `Walk`/`Cut`/`IW` 在极限的尾段上用 `wl (suc (m+n))` 推下来的 `Lg` 调用分支, 而 `κᴸ`/`niᴸ` 的前提要分支前段的 `Lg` 等式, 这两者只在自洽时一致.
>    - 相应地, 关系 (`StrRel12Rel.Rel`) 的 `niᴸ`, `κᴸ` 只在 `CP` 分支对上比 (`StrRel11Le` 在一切 `APair` 分支对上比). 前提变少, 关系变宽 (判断).
>    - **前提可满足** (`inst`): 对一切不含 $\Omega$-极限的 $\Lambda$ (`NoΩ`), 闭项 `ΔΩ` 的顶层调用满足 `sem∀` 的全部前提 (`cpOne`, `haAct`, `ΩR`), 结论是 `OAc tt tt ΔΩ ΔΩ`. 合法的 `Lg` 由 `Lg-sum` 产生时自洽 (`StrRel12Rel.cohSum`), 闭项从 `tt` 起.
> 3. **(未做) 跨坐标层的节点规则, $\Omega^{\mathsf H}$ 处的 `MonoStep`.** `haAct` 只对不含 $\Omega$-极限的 $\Lambda$ 证: 外层动作 `Act` 在一切目标层 $t\lhd\Lambda$ 上输出 $\Omega_t\cdot\omega$, 要 `Rel t (Ωd t) (Ωd t)` 在两个世界之间成立, 而 $t$ 是 $\Omega$-极限时这正是 `StrRel11Om.¬rel-Ω` 的形状 (本文的关系同样只有同层节点规则; 编译形式 `StrRel12Om.¬ΩR`). 见 §3.

## 0 模块

| 文件 | 内容 | 档 |
|---|---|---|
| [StrRel12Al](StrRel12Al.lagda.md) | `Coh`, `AP`, `CP`, `al-adm`, `Al-top`, `preAP`, `extB`, `extR`, `sfxS`, `posCP`, `LimT`, `LimW` | 定义, 定理 (不提折叠) |
| [StrRel12Rel](StrRel12Rel.lagda.md) | `LeF`/`Rel`/`Below`, `belowOut`, `belowIn`, `out-inS`, `vsum`, `drpR`, `lgsf`, `cohSum`, `sumA`, `genAl` | 定义, 定理 (不提折叠) |
| [StrRel12Int](StrRel12Int.lagda.md) | `CutR.cutR`, `UH`, `uh↾`, `IWm.iwR`, **`IntM`** | 定理 (不提折叠) |
| [StrRel12Sem](StrRel12Sem.lagda.md) | `OAc`, `R∀c`, `cvRc`, `advRc`, `HAW`, `haw↾`, `SemW`, 六条规则, **`WalkR.walkR`** | 定义, 定理 |
| [StrRel12Ni](StrRel12Ni.lagda.md) | `NiS.Go.haAi`, `NiS.Go.Ch`, `NiS.Go.goRk`, **`NiS.sem-ni`** | 定理 (以分支与坐标层的语义为模块参数, `sem` 填上) |
| [StrRel12Kp](StrRel12Kp.lagda.md) | `CS`, `KpS.Go.K.kb`, `KpS.Go.cs`, **`KpS.sem-κ`** | 定理 (以分支的语义为模块参数, `sem` 填上) |
| [StrRel12Om](StrRel12Om.lagda.md) | `cp12`, **`¬ΩR`**: 本族里 `Ωd Ωᴴ` 在世界 0 与 1 之间不相关 | 定理 (否定, 只否定本族的这一相关) |
| 本文 | **`sem`**, **`sem∀`**, `NoΩ`, `ΩR`, `haAct`, `cpOne`, `inst` | 定理 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel12 (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ss; sl; D; n0; Ωd; AccY; acc; accL; accᴸ)
open import OCF.Align.HtFeedClosed using (module At; one)
open import OCF.Align.StrRel4Walk using (aS; aP)
open import OCF.Align.StrRel12Al using (CP; stepA)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; n1ᴸ; ⨾ᴸ; nlᴸ; prᴸ; nwAᴸ; niᴸ; κᴸ)
open import OCF.Align.StrRel12Sem Λ lΛ using (OAc; HAW; SemW; sem-n0; sem-n1; sem-⨾; sem-nl; sem-nw; sem-pr)
open import OCF.Align.StrRel12Ni Λ lΛ using (module NiS)
open import OCF.Align.StrRel12Kp Λ lΛ using (module KpS)
open import OCF.Align.StrRel12Om using (¬ΩR)

module P = At Λ lΛ
open P using (Act; Y₀; ΔΩ; Tg; tm; d; z)
```

## 1 对一切层

```agda
sem : ∀ L → AccY L → ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L V′} → Rel L lV lV′ x x′ → SemW L lV lV′ x x′
sem L ac n0ᴸ = sem-n0 L
sem L ac n1ᴸ = sem-n1 L
sem L ac (⨾ᴸ hx hy) = sem-⨾ L hx (sem L ac hx) (sem L ac hy)
sem L ac (nlᴸ hd) = sem-nl L hd (λ n → sem L ac (hd n))
sem L ac (prᴸ hx) = sem-pr L (sem L ac hx)
sem L ac (nwAᴸ hp hx) = sem-nw L hp (sem L ac hx)
sem L (acc g) (niᴸ {r = r} {r′ = r′} h) =
  NiS.sem-ni r r′ h (λ p p′ lc lc′ cp y y′ b → sem L (acc g) (h p p′ lc lc′ cp y y′ b)) (λ hk → sem _ (g r) hk)
sem L ac (κᴸ h) = KpS.sem-κ h (λ p p′ lc lc′ cp → sem L ac (h p p′ lc lc′ cp))

sem∀ : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ : D L V′} → Rel L lV lV′ x x′ → SemW L lV lV′ x x′
sem∀ L = sem L (accL L)
```

## 2 前提可满足: 不含 $\Omega$-极限的 $\Lambda$, 闭项的顶层调用

```agda
NoΩ : H → Set
NoΩ hz = ⊤
NoΩ (hs b) = NoΩ b
NoΩ (hl f) = ∀ n → NoΩ (f n)
NoΩ (hΩ g) = ⊥

noΩ⊲ : ∀ {t L W} → t ⊲[ W ] L → NoΩ L → NoΩ t
noΩ⊲ hself o = o
noΩ⊲ (hsuc P) o = noΩ⊲ P o
noΩ⊲ (hlim n P) o = noΩ⊲ P (o n)
noΩ⊲ (hLim e P) ()

-- Ω_t 在两个世界之间自相关 (t 不含 Ω-极限)
ΩR : ∀ t → NoΩ t → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → Rel t lW lW′ (Ωd t {W}) (Ωd t {W′})
ΩR hz o = n1ᴸ
ΩR (hs b) o = ⨾ᴸ n1ᴸ (niᴸ {r = ss hself} {r′ = ss hself} (λ p p′ lc lc′ cp y y′ hb → n1ᴸ))
ΩR (hl f) o = ⨾ᴸ n1ᴸ (nlᴸ (λ n → niᴸ {r = sl n hself} {r′ = sl n hself} (λ p p′ lc lc′ cp y y′ hb → n1ᴸ)))
ΩR (hΩ g) ()

haAct : NoΩ Λ → ∀ L {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW L lW lW′ Act Act
haAct o L p p′ l l′ cp w w′ hw Y Y′ hY T T′ tc = nlᴸ (λ _ → ⨾ᴸ (ΩR _ (noΩ⊲ (tm T) o)) (proj₁ hY T T′ tc))

cpOne : CP {V = azero} {V′ = azero} tt tt (z⊲ one) tt (z⊲ one) tt
cpOne = (aP (aS C.self tt) z≤ (stepA azero azero) , stepA azero azero , refl , refl) , ≤-refl one , tt , tt

inst : NoΩ Λ → OAc tt tt ΔΩ ΔΩ
inst o = sem∀ Λ (ΩR Λ o) tt tt accᴸ accᴸ hself hself (z⊲ one) (z⊲ one) cpOne Act Act (haAct o Λ) n0 n0 n0ᴸ Y₀ Y₀
           ((λ T T′ tc → n0ᴸ) , n0ᴸ)
```

## 3 第一个障碍 (未做的第 3, 4 项)

**(判断, 依据 `haAct` 的证明与 `StrRel11Om.¬rel-Ω`)** `sem∀` 的顶层前提里只有一条依赖 $\Lambda$ 的形状: 外层动作 `Act` 的 `HAW`. `Act` 在每个目标层 $t\lhd\Lambda$ 上输出 `ω⋅ (Ωd t ⨾ …)`, 所以 `HAW … Act Act` 要 `Rel t (Ωd t {m}) (Ωd t {m′})` 对一切 `CP` 目标对成立. $t$ 是 $\Omega$-极限 `hΩ g` 时, `Ωd t` 的 `nκ` 在分支世界 $c$ 上是坐标层 `g c` 的节点; `CP` 分支对允许 $c\ne c'$, 两个节点坐标层不同, 本族只有同层的 `niᴸ`, 于是不相关 (本族里的编译形式: `StrRel12Om.¬ΩR`; 从它到 "`HAW … Act Act` 不成立" 这一步是判断). 所以:

- `MonoStep` 在 $\Omega^{\mathsf H}$ 处 (两边高度不同, 动作是 `A²`/`Act`) 要的不只是 `sem∀`, 还要一条**跨坐标层**的节点规则: 坐标层 $k\le k'$ (由对齐的分支世界对 $c\le c'$ 给出 `g c`, `g c′`) 的两个节点相关. 它的可靠性在 `rkT` 上不再由 `rk-agree` 保证同种 (坐标层不同, 目标层可以夹在中间: 一边 `rise` 一边 `keep`), 在 `rise/rise` 上是 "坐标层 $k$ 的链 vs 坐标层 $k'$ 的链".
- MonoPort7 的 `grow≪`/`Lim.monoL` 给的是**值**的单调 ($T$ 沿 $\ll$ 严格增长), 不是本族的结构关系 `Rel`. 本族的语义结论是 `Rel t` (结构的), 要把 "层 $k$ 的链 ≤ 层 $k'$ 的链" 写进 `OAc` 的结论, 得先有一条结构的跨层规则 (例如在 `Rel hz` 上加 "值可比" 的读数关系作为语义的结论层), 再把 `grow≪` 接到第 0 层读数上. 这一步本轮没有做, 没有否定定理.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `CP` 的顶端可比 $W\le W'$ | `κc` 的格世界 `sum W (z Y)`; `Al.aP` 的 `c ≤ c′`; `genAl` 的 `n1ᴸ` 一句 | **树逼的** |
| `Coh` (`Lg` 自洽) | `Walk`/`Cut`/`IW` 的极限尾段用 `wl (suc (m+n))` 往下推, `κᴸ` 的前段要 `Lg` 等式 | **树逼的** (`Lg` 的数据形状) |
| `niᴸ`, `κᴸ` 只取 `CP` 分支对 | 同上: 分支在走法里被调用的位置只给出 `CP` | **树逼的** |
| `Al-top`, `al-adm`, `LimW` | 前段要对齐在自己的顶端 (`AP` 的定义), 走法对 `Al` 自顶向下递归 | **树逼的** (对齐的代数) |
| `IntM` 不要两边同一个 `mk` | `niᴸ` 允许两边 `StH` 不同; 坐标关系经 `belowOut` 取 | **树逼的** |
| `CS` (格的不变量) | `κc` 的 `Cl` 字段逐个对应 | **树逼的** |
| `haAct` 只对 `NoΩ` | `Step` 的字面 `Ωd t`; `¬rel-Ω` | **树逼的** (界定范围) |

**归类: 提供信息.** 没有新构造子或节点字段 (关系的构造子不是树的), 没有改树与折叠, 没有 `Lab`, 没有记号. `sem` 一个证明对一切层, 不按站加前提; 新增的前提 (`CP` 的两项) 是语义的, 对一切规则一样. 这一站新用到的字段: `Lg (alim f)` 的步进路径与各项 `Lg` 之间的关系 (`Coh`), `Al` 的 `aP` 的值字段 (`c ≤ c′`, 交给分支的前段), `Cl` 的全部字段, `κc` 的格路径 `sum-fst`.
