# 局部 UIP 与 "只升 $c_0$": 否定一路的入口

> 不含记号. 作者原话 "两条小引理先判定"; 本路是**否定**一路, 与构造一路 `LocUip*` 配对 (手册 §5.2). 对着接口 [LocUipIf](LocUipIf.lagda.md) ("接口定稿 2026-11-05 10:45 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [LocUipNegLoop](LocUipNegLoop.lagda.md) (第一条引理), [LocUipNegFeed](LocUipNegFeed.lagda.md) (第二条引理), [LocUipNegSec](LocUipNegSec.lagda.md) (截面的值作增量: 对构造一路第一个障碍的改写). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延只在 `LocUipNegLoop` §3 作前提 (条件), 不进任何构造.
>
> **判决.**
>
> 1. **第一条引理 (局部 UIP, 使 `raise₀ᴮ` 无条件保 `Coh≡`): 未证出, 也没有编译的否定; 它不是禁忌.** 编译的是它的确切强度:
>    - `loc⇔funΩ`: 对一切合法世界的 `LocUIP` $\iff$ `UIPᴸ` $\iff$ `FunΩ` (合法极限点的分支函数 $f:\mathbb N\to H$, $g:A\to H$ 上的环都是 `refl`). 局部 UIP 就是函数类型上相等证明的平凡性.
>    - `irr⇔fix`: 卡住的那一步 `IncIrr` $\iff$ `LoopFix` (合法高度上的环沿 `HB ∘ G₀` 搬运是恒等). `chain`: `LoopFix → Fix⊞ → Lemma1 → LoopFix₀`. **第一条引理的目标 `Lemma1` 本身推出环的搬运平凡** (`lemma1→fix₀`), 所以换一条不经 `LocUIP` 的充分条件也躲不开外延性内容.
>    - `¬uipᴸ→¬fe`, `¬irr→¬fe`, `¬lemma1→¬fe`, `¬funΩ→¬fe`: 反驳其中任何一条就反驳函数外延. 所以 `--without-K` 下**造不出** "同一界之下两个不相等的相等证明" (函数外延在立方模型中成立, 标准事实).
>    - [判断] `FunΩ` 在 `--safe --without-K` 无函数外延时证不出; 我没有反模型. [判断] 它不推出全知原理 (它被函数外延推出, 函数外延与 $\neg$LPO 相容), 所以不是壁垒定理意义上的禁忌, 是外延性原理.
> 2. **第二条引理 (回灌是否只升 $c_0$ 本身): 否. 回灌必须升 $c_0$ 之上的分量 (定理).**
>    - `¬feedKeep`: 保 `CopyCoh` 的回灌一步 (接口 `Feed` 的形状) 必须改 `hs c₀` 的分量的旧种类部分 (那里装着 $c_0$ 的槽的拷贝). `slotOnly→¬raiseCopy`: 只改槽的更新 (接口已有的 `raiseᴮ`, `raise₀ᴮ` 都是) 不保 `CopyCoh`. `offF→¬raiseCopyF`: 证据无关写法里满足 `OffF` 的更新也不保.
>    - 被否定的律可满足: `raiseF⁺` (升 $c_0$ 之上的拷贝, 族增量) 无条件保 `Coh≡` 与 `CopyCoh`, 给出接口的 `Feedᶠ (Coh≡ ∧ CopyCoh)` (`feedF⁺`). 单个增量的 `raise⁺ᴮ` 四条律无条件, 保 `CopyCoh` 要 `IncIrr` (`irr→raiseCopy⁺`), 即回到第一条引理.
>
> **两条引理的关系.** 单个增量 $\delta : $ `HB (G₀ c₀)` 要沿判定给的相等证明搬运 (`incD`), 于是 `Coh≡` 与 `CopyCoh` 都卡在 `IncIrr` (= `LoopFix`) 上; 族增量 $\delta : $ `Inc` 只用判定的是/否, 两种相干都无条件 (`raiseFᵒ` 的 `cohF`, `raiseF⁺` 的 `copyF⁺`). 所以在接口给的两种写法里, 第一条引理的困难只属于单个增量的写法 [定理: `raiseFᵒ`, `raiseF⁺`, `irr⇔fix`]; 族增量能否由回灌实际产出是构造一路的第一个障碍; [LocUipNegSec](LocUipNegSec.lagda.md) 把它说准 [定理]: 若读回值是某个 $F:$ `Inc` 在 $c_0$ 的值, 单个增量的 `raise₀ᴮ` 就无条件保 `Coh≡` (`sec→coh`), 且与族增量的 `raiseFᵒ` 逐分量相等 (`sec-agree`); 所以要的是 "回灌对坐标一致", 不是 UIP. 回灌能否这样写, 本路不判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipNeg where

open import OCF.Align.LocUipNegLoop public
open import OCF.Align.LocUipNegFeed public
open import OCF.Align.LocUipNegSec public
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `uipᴸ→funΩ`, `funΩ→uipᴸ`, `loc⇔funΩ` | Loop §1 | 合法世界上的局部 UIP $\iff$ `UIPᴸ` $\iff$ 合法极限点分支函数上的环平凡 | 定理 |
| `uipᴸ→Ωfin` | Loop §1 | 推论: $\omega$ 的分支 `fin` 上的环平凡 | 定理 |
| `irr→fix`, `fix→irr`, `irr⇔fix` | Loop §2 | `IncIrr` $\iff$ `LoopFix` | 定理 |
| `fix→fix⊞`, `fix⊞→lemma1`, `lemma1→fix₀`, `chain` | Loop §2 | `LoopFix → Fix⊞ → Lemma1 → LoopFix₀` | 定理 |
| `Loop.d₀`, `Loop.d₁` | Loop §2 | 合法世界里同一坐标两个证据的判定给 `inj₁ refl` 与 `inj₁ ℓ` | 定理 |
| `uipᴸ→fix` | Loop §2 | `UIPᴸ → LoopFix` | 定理 |
| `¬uipᴸ→¬fe`, `¬irr→¬fe`, `¬lemma1→¬fe`, `¬funΩ→¬fe` | Loop §3 | 反驳它们就反驳函数外延 | 条件定理 (Funext 作前提) |
| `¬feedKeep`, `¬feedKeep-copy`, `¬feedKeep-both` | Feed §2 | 保 `CopyCoh` 而不动 `hs c₀` 旧种类部分的回灌不存在 | 定理 (否定) |
| `slotOnly→¬raiseCopy`, `¬raiseCopy-raise₀`, `¬raiseCopy-raiseᴮ` | Feed §2 | 只改槽的更新不保 `CopyCoh` | 定理 (否定) |
| `raiseFᵒ`, `offFᵒ` | Feed §3 | 满足 `OffF` 的 `RaiseF` (前提实例) | 定理 |
| `offF→¬raiseCopyF`, `¬raiseCopyF-ᵒ` | Feed §3 | 只升 $c_0$ 的族增量更新不保 `CopyCoh` | 定理 (否定) |
| `raiseF⁺`, `copyF⁺`, `feedF⁺`, `up-moves` | Feed §4 | 升拷贝的族增量更新: 无条件保两种相干, 给出 `Feedᶠ (Coh≡ ∧ CopyCoh)` | 定理 |
| `raise⁺ᴮ` | Feed §5 | 升拷贝的单个增量更新, 四条律 | 定理 |
| `irr→raiseCopy⁺` | Feed §5 | `IncIrr` 之下 `raise⁺ᴮ` 保 `CopyCoh` | 条件定理 (IncIrr) |
| `sec-subst`, `sec→irr`, `sec→coh`, `sec-agree` | Sec | 截面的值作增量: `IncIrr` 与 `Lemma1` 的结论无条件成立, 且与族增量一致 | 定理 |
| `feed⁺-inst` | Feed §5 | 见证世界上 `raise⁺ᴮ` 把拷贝升到读回值 | 定理 (`refl`) |

## 律为什么是构造一路需要的

- `Lemma1`, `IncIrr`, `LocUIP`, `UIPᴸ`: 接口 §1 原文; `Lemma1` 是作者的目标 ("`raise₀ᴮ` 无条件保 `Coh≡`"), `IncIrr` 是 `AdmWCoh.incD-irr` 卡住的那一步. `LoopFix`, `Fix⊞`, `LoopFix₀`, `FunΩ` 是本路为了量出强度引入的, 只由接口的名字与 `HtTowerTy` 组成.
- `Feed`, `Feedᶠ`, `CopyCoh`, `SlotOnly`, `RaiseCopy`, `OffF`, `RaiseF`: 接口 §2, §3 原文. `FeedKeep` = `Feed` + "`hs c₀` 的分量的旧种类部分不动", 是 `SlotOnly` 与 `OffF` 在 `hs c₀` 处的共同推论; `RaiseCopyF` = `RaiseCopy` 的 `RaiseF` 版本. `CopyCoh` 之所以是回灌要的相干: 接口文字引 `HtTowerNStage.no-wmatch` [定理] (逐分量独立的界给不出对角的并要的世界对应); 槽种类与它在 `hs c₀` 里的拷贝坐标类型定义相同, 在对角的并里是同一个种类 [判断].

## 前提实例

- `Loop` (Loop §2): 任一合法高度 $x$ 与环 $\ell$; 对 $\ell = $ `refl` 一切合法 $x$ 都是实例 (如 `Lg-ω`). 世界 `wL` 合法 (`loL`), 相干 (`cohL`).
- `¬feedKeep`: `Coh (w₂ , v₂)` 由 `copy₂`, `coh₂` 满足; "Coh 推出 CopyCoh" 对两个实例是投影.
- `slotOnly→¬raiseCopy`: `SlotOnly` 由 `raise₀ᴮ`, `raiseᴮ` 满足 (`refl`). `offF→¬raiseCopyF`: `OffF` 由 `raiseFᵒ` 满足 (`offFᵒ`).
- 见证世界 `w₂ = (0, 1)`, `v₂` 全 $0$: 合法 (`lgW₂`), `CopyCoh` 与 `Coh≡` 都是 `refl`.
- `irr→raiseCopy⁺` 的 `IncIrr`: 由函数外延推出 (`¬irr→¬fe` 的证明里的 `fix→irr (uipᴸ→fix (fe→uipᴸ′ fe))`), 条件.

## 只否定什么, 不否定什么

- **第一条引理.** 没有否定. 定理说的是强度: 局部 UIP 等价于 `FunΩ`; `Lemma1` 推出 `LoopFix₀`. 不否定 `Lemma1` (它在函数外延下成立); 不否定族增量的写法 (那里同一目标无条件成立, `raiseFᵒ.cohF`).
- **第二条引理.** 只否定 "保 `CopyCoh` 的回灌不动 `hs c₀` 的旧种类部分" (`¬feedKeep`), 以及推出它的 `SlotOnly`, `OffF` 加 `RaiseCopy`/`RaiseCopyF`. 不否定接口的 `Feed`/`Feedᶠ` (后者由 `feedF⁺` 无条件成立); 不否定方向 A; 不否定不要求 `CopyCoh` 的回灌. `CopyCoh` 只写了 `hs` 一步, 极限分量里的拷贝未处理.

## 审计

见 [LocUipNegLoop](LocUipNegLoop.lagda.md), [LocUipNegFeed](LocUipNegFeed.lagda.md) 文件头的选项. 导入闭包与定义级切片的数字在本路交回的报告里 (不改 README/LOG).
