# 可入下标比较式更新的否定: 入口

> 不含记号. 对着接口 [AdmWIf](AdmWIf.lagda.md) ("接口定稿 2026-11-05 10:05", 变更记录: 无) 写; 本篇导入它, 不另造接口. 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.4, §3.3 义务 1 与 2, §5.1 第二条引理. 分篇: [AdmWNegCopy](AdmWNegCopy.lagda.md) (对一切种类结构的拷贝引理与独立性模型), [AdmWNegLaws](AdmWNegLaws.lagda.md) (更新律的反模型), [AdmWNegDraft](AdmWNegDraft.lagda.md) (定稿前对诊断原文的草稿, 含 `no-botBd`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **判决: 部分.**
>
> 1. **拷贝墙是定理.** `¬CmpK-Inst : ¬ Inst.CmpK`, `¬CmpK-Slot : ¬ Slot.CmpK`: 接口的第二条引理 (不带相干前提的坐标比较) 在最小实例上**不成立**, 结论是 $\bot$, 不是禁忌. 见证: 界 $b_0=\lim_n 0$ (ℕ-极限重复项) 之下坐标 $0$ 有两个证据 `hlim 0 hself`, `hlim 1 hself`; 世界 `WI` 的这两个分量分别取 $2$ 与 $\lim_n 1$, 外层与每个分量都合法 (`lgWI`); 两个坐标各在自己的分量里有界, 但它们在 `A` 里不可比, 而 `Prᴮ` 要它们在**某个**分量里可比. 一般形 `copy-gen` 对一切 `SupB S κ F`.
> 2. **墙恰好是相干.** 对**一切** `SupB S κ F`, 带相干前提的比较是定理: `cmpKᶜ≤ : CmpKᶜ Coh≤`, `cmpKᶜ≡ : CmpKᶜ Coh≡` (把一边的界沿 `Coh≤` 搬到另一个证据的分量里, 用分量的 `cmpK`). 见证世界不相干 (`WI-incoh`). 所以诊断问的 "`cmpK` 要不要 $p\equiv p'$" 的准确答案是: 不带相干就没有 (`¬CmpK-Inst`); 带 `Coh≤` (比 "分量不依赖证据" `Coh≡` 弱) 就有; 不需要判定证据相等.
> 3. **四条更新律本身不推出禁忌: 有反模型, 在接口的最小实例上.** `raiseM : RaiseIf.RaiseB` (槽族 `Slot`, 下标 `HB S₀`, 分量以 (坐标, 证据) 为下标, 逐分量独立): `at` 对一切证据, `below`, `mono`, `legal` 都是定理; 选择用 `AdmWNegLaws.cmpB₀` (在 $\Omega$-节点处 `cmpF` 返回字面 `self` 时不调用合法性证据里的 `mo`), 所以 `at` 不需要 K (诊断 §3.3 义务 2 在这里由定义的写法绕开). 同一个比较也给出 `openA : Open-buildᴬ` (`UniTr` 的可入版). 推论: 拷贝墙不在更新律里, 在 `cmpK` 里.
> 4. **未定: `RaiseCoh`.** 剩下的问题是更新保相干 (`RaiseCoh Coh≤ R` 或 `RaiseCoh Coh≡ R`). 本篇既没有证出 `raiseM` 保相干, 也没有否定. 判断: 对 `raiseM`, 同一坐标的两个拷贝拿到的嵌入路径来自 `cmpB₀ q p₀`; 在我手算与编译的闭项例子里两个拷贝的路径字面相同 (`AdmWNegLaws.CopyTest.same-path`, 有限测试); 一般情形要说 "合法性证据在环 $t\lhd t$ 上给 `hself`", 我没有在 `--without-K` 下证出来, 也没有反例. 这是构造一路下一步要回答的, 不是本篇的否定.
>
> **律为什么是构造一路需要的.** `CmpK` 是接口自己写下的第二条引理 (`HB (SupB …)` 上的 `cmpB` 要它); `Bdᴮ`, `Prᴮ`, `LgWᴮ` 都取接口的定义, 本篇不选. 一般形 `copy-gen` 的前提只是 "同一坐标有两个证据, 两个分量各有一个合法世界, 其中的两个坐标在一切世界里不可比", 在最小实例上由 `WI` 满足.
>
> **前提可满足.** `lgWI`, `lgWS` (见证世界合法, 逐分量); `WI` 的两个界是构造 (`bI₀`, `bI₁`). `cmpKᶜ≤` 的相干前提可满足: 任何不依赖证据的分量函数都 `Coh≡` (`const-coh`). `raiseM`, `openA` 是构造.
>
> **草稿与定稿接口的差别.** [AdmWNegDraft](AdmWNegDraft.lagda.md) 在定稿前对诊断 §3.3 原文写成. 它的 `SupB` 的种类, 坐标, 世界, 界, 合法与 `AdmWIf.SupB` 的 `Kᴮ`, `Eᴮ`, `Wᴮ`, `Bdᴮ`, `LgWᴮ` 逐字同形 (只是名字不同); 草稿没有固定第一位置, 而以 `AsSupB` (任一含这一形状、`ι` 保合法的种类结构) 陈述 `supB→⊥`, 比本篇对接口 `Prᴮ` 的 `¬CmpK-Inst` 更一般, 也多一个前提 (`lgι`). 接口自己注明 `SupB` 不是 `KS` (缺 `cmpK` 与 `botBd`); 草稿的 `no-botBd` 是后一半的定理形式, 本篇的 `¬CmpK-Inst` 是前一半在不带相干时的否定. 我没有读构造一路的其他 `AdmW*` 文件.
>
> **只否定什么.** 只否定接口的 `CmpK` (以及任何对逐分量合法的一切世界陈述的坐标比较). **不否定**: `CmpKᶜ` (反而是定理); 规范证据 (ℕ-极限取最小 $n$); 路径作种类; `RaiseCoh`; 方向 A 本身. 也不否定 [AdmWNegDraft](AdmWNegDraft.lagda.md) 的 `no-botBd` 之外的 `KS` 改法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_) renaming (wf to wfᴮ; irr to irrᴮ; toLt to toLtᴮ)
open import OCF.Align.UniTrBase using (module W′)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWNegCopy using (X₂; X′; lgX₂; lgX′)
open import OCF.Align.AdmWNegDraft using (b₀; lgb₀; ev₀; ev₁; wK; lgwK)
open import OCF.Align.AdmWNegLaws using (cmpB₀; cmpB₀-diag; <ᴮ-tr; updᴮ; embᴮ; Lg-embᴮ; raise-≤ᴮ; raise-lgᴮ; atᴮ)
  renaming (raiseB to raiseL)
```

## §1 一般形: 两个证据, 两个不相干的分量

对任意 `SupB S κ F`: 外层合法世界 $w$, 坐标 $c$ 的两个证据 $p_0,p_1$, 分量函数 $v$ (逐分量合法), 种类 $k$ 的两个坐标 $x_0, x_1$ 分别在 $(c,p_0)$, $(c,p_1)$ 的分量里有界, 而且在 $F\,c$ 的**一切**世界里互不为第一位置. 则没有 `CmpK`.

```agda
module Gen (S : KS) (κ : K S) (F : E S κ → KS) where
  open SupB S κ F

  copy-gen : ∀ {w} (v : Cmp w) → LgWᴮ (w , v) → ∀ {c} (p₀ p₁ : Bd S κ c w) {k} {x₀ x₁ : E (F c) k} →
    Bd (F c) k x₀ (v c p₀) → Bd (F c) k x₁ (v c p₁) →
    (∀ u → ¬ Pr (F c) k u x₁ x₀) → (∀ u → ¬ Pr (F c) k u x₀ x₁) → ¬ CmpK
  copy-gen {w} v lw {c} p₀ p₁ {k} e₀ e₁ n₁₀ n₀₁ cK with cK {k = (c , k)} {W = (w , v)} (p₀ , e₀) (p₁ , e₁) lw
  ... | inj₁ (p , r) = n₁₀ _ r
  ... | inj₂ (p , r) = n₀₁ _ r
```

## §2 最小实例: `Inst` 与 `Slot` 都没有 `CmpK`

$2$ 与 $\lim_n 1$ 在 `A` 里不可比. `S₀` 的第一位置不看世界, 所以 "一切世界里不可比" 就是这两条.

```agda
incA₁ : ¬ (X₂ ⊲ X′)
incA₁ (C.lim n (C.suc ()))

incA₂ : ¬ (X′ ⊲ X₂)
incA₂ (C.suc (C.suc ()))
```

**`Inst`** (分量 `G₀ c = Lev (up c)`; 坐标 $0$ 的分量是 `S₀`, 世界是 `A`).

```agda
vI : A → A → Inst.Cmp (azero , b₀)
vI a₀ a₁ c hself = wK a₀ (up c)
vI a₀ a₁ c (hlim zero p) = wK a₀ (up c)
vI a₀ a₁ c (hlim (suc n) p) = wK a₁ (up c)

lgvI : ∀ {a₀ a₁} → Lg a₀ → Lg a₁ → ∀ c p → LgW (G₀ c) (vI a₀ a₁ c p)
lgvI l₀ l₁ c hself = lgwK l₀ (up c)
lgvI l₀ l₁ c (hlim zero p) = lgwK l₀ (up c)
lgvI l₀ l₁ c (hlim (suc n) p) = lgwK l₁ (up c)

WI : Inst.Wᴮ
WI = (azero , b₀) , vI X₂ X′

lgWI : Inst.LgWᴮ WI
lgWI = (tt , lgb₀) , lgvI lgX₂ lgX′

bI₀ : Inst.Bdᴮ (hz , tt) X₂ WI
bI₀ = ev₀ , C.self

bI₁ : Inst.Bdᴮ (hz , tt) X′ WI
bI₁ = ev₁ , C.self

¬CmpK-Inst : ¬ Inst.CmpK
¬CmpK-Inst = Gen.copy-gen (step S₀) (inj₂ tt) G₀ (vI X₂ X′) lgWI ev₀ ev₁ {k = tt} {x₀ = X₂} {x₁ = X′}
               C.self C.self (λ u → incA₂) (λ u → incA₁)
```

**`Slot`** (分量 `step (G₀ c)`; 坐标 $0$ 的分量是 `step S₀`, 用旧种类 `inj₁ tt`, 它的界在世界的第一个分量).

```agda
vS : A → A → Slot.Cmp (azero , b₀)
vS a₀ a₁ c p = vI a₀ a₁ c p , hz

WS : Slot.Wᴮ
WS = (azero , b₀) , vS X₂ X′

lgWS : Slot.LgWᴮ WS
lgWS = (tt , lgb₀) , (λ c p → lgvI lgX₂ lgX′ c p , tt)

¬CmpK-Slot : ¬ Slot.CmpK
¬CmpK-Slot = Gen.copy-gen (step S₀) (inj₂ tt) (λ c → step (G₀ c)) (vS X₂ X′) lgWS ev₀ ev₁ {k = inj₁ tt} {x₀ = X₂} {x₁ = X′}
               C.self C.self (λ u → incA₂) (λ u → incA₁)
```

## §3 墙恰好是相干

对一切 `SupB S κ F`, 带 `Coh≤` 的比较是定理: 第一个坐标的界沿 `Coh≤` 搬进第二个证据的分量, 在那里用分量的 `cmpK`.

```agda
module Delim (S : KS) (κ : K S) (F : E S κ → KS) where
  open SupB S κ F

  cmpKᶜ≤ : CmpKᶜ Coh≤
  cmpKᶜ≤ {k} (p , e) (p′ , e′) lw coh
    with cmpK (F (proj₁ k)) (Bd↑ (F (proj₁ k)) (coh (proj₁ k) p p′) e) e′ (proj₂ lw (proj₁ k) p′)
  ... | inj₁ r = inj₁ (p′ , r)
  ... | inj₂ r = inj₂ (p′ , r)

  coh≡→≤ : ∀ W → Coh≡ W → Coh≤ W
  coh≡→≤ W h c p p′ = subst (λ u → _≤w_ (F c) (proj₂ W c p) u) (h c p p′) (≤w-rf (F c))

  cmpKᶜ≡ : CmpKᶜ Coh≡
  cmpKᶜ≡ {W = W} e e′ lw coh = cmpKᶜ≤ e e′ lw (coh≡→≤ W coh)

  -- 前提可满足: 不依赖证据的分量函数相干
  const-coh : ∀ w (u : (c : E S κ) → Wd (F c)) → Coh≡ (w , (λ c _ → u c))
  const-coh w u c p p′ = refl
```

见证世界不相干 (与 `cmpKᶜ≤` 一致).

```agda
WI-incoh : ¬ Inst.Coh≤ WI
WI-incoh h = incA₁ (h hz ev₀ ev₁)
```

## §4 更新律的反模型 (接口的最小实例)

`raiseM`: 对每个分量 $(c,q)$ 看 `cmpB₀ q p₀`: $c_0\lhd c$ 则沿路径嵌入 $\delta$ 接长, 否则不动. 函数体在 [AdmWNegLaws](AdmWNegLaws.lagda.md) §6.

```agda
open RaiseIf

below-go : ∀ {c₀ c b : HB S₀} {a} (δ : HB (G₀ c₀)) (u : Wd (step (G₀ c))) → c <ᴮ c₀ →
           (s : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) → updᴮ {c₀} {b} {a} δ c u s ≡ u
below-go δ u lt (inj₂ _) = refl
below-go {c₀} {c} δ u lt (inj₁ r) with toLtᴮ r
... | inj₁ e = ⊥-elim (irrᴮ (wfᴮ c) (subst (λ z → c <ᴮ z) e lt))
... | inj₂ s = ⊥-elim (irrᴮ (wfᴮ c) (<ᴮ-tr lt s))

raiseM : RaiseB
raiseM = record
  { raiseB = λ w lo v c₀ p₀ δ → raiseL p₀ δ (proj₁ lo) (proj₂ lo) v
  ; at = λ w lo v c₀ p₀ δ → atᴮ p₀ δ (proj₁ lo) (proj₂ lo) v
  ; below = λ w lo v c₀ p₀ δ c p lt → below-go {c₀} {c} {proj₂ w} {proj₁ w} δ (v c p) lt (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo))
  ; mono = λ w lo v c₀ p₀ δ lδ → ≤w-rf (step S₀) , (λ c p → p , raise-≤ᴮ p₀ δ (proj₁ lo) (proj₂ lo) v c p)
  ; legal = λ w lo v c₀ p₀ δ lδ lw → proj₁ lw ,
      proj₂ (proj₂ (raise-lgᴮ p₀ δ (proj₁ lo) (proj₂ lo) v lδ (proj₁ lo , proj₂ lo , proj₂ lw))) }
```

**`UniTr` 的可入版.** 同一个比较作选择子: 见证 $c_0\lhd c$ 时沿路径嵌入, 否则取 $0$. 对角上 `cmpB₀-diag` 给 `hself`, 所以忠实是 `refl`.

```agda
goA : ∀ {c₀ c : HB S₀} {a} → (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀) → HB (G₀ c₀) → HB (G₀ c)
goA (inj₁ r) δ = embᴮ r δ
goA (inj₂ _) δ = hz

Lg-goA : ∀ {c₀ c : HB S₀} {a} (s : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) δ → LgB δ → LgB (goA {c₀} {c} {a} s δ)
Lg-goA (inj₁ r) δ l = Lg-embᴮ r δ l
Lg-goA (inj₂ _) δ l = tt

openA : Open-buildᴬ
openA w lo = record
  { tr = λ i₀ i δ → goA {proj₁ i₀} {proj₁ i} {proj₁ w} (cmpB₀ (proj₂ i) (proj₂ i₀) (proj₁ lo) (proj₂ lo)) δ
  ; faith = λ i₀ δ l → fa (proj₂ i₀) δ
  ; legal = λ i₀ i δ l → Lg-goA {proj₁ i₀} {proj₁ i} {proj₁ w} (cmpB₀ (proj₂ i) (proj₂ i₀) (proj₁ lo) (proj₂ lo)) δ l }
  where
  fa : ∀ {c₀} (p₀ : AdmE w c₀) δ → goA {c₀} {c₀} {proj₁ w} (cmpB₀ p₀ p₀ (proj₁ lo) (proj₂ lo)) δ ≡ δ
  fa p₀ δ rewrite cmpB₀-diag p₀ (proj₁ lo) (proj₂ lo) = refl
```

## §5 结论 (按档)

- **[定理]** `¬CmpK-Inst`, `¬CmpK-Slot`, `copy-gen`: 接口的 `CmpK` 在最小实例上为假 (拷贝墙). `AdmWNegCopy.copy→⊥`: 对一切种类结构, 只要含 "两个证据、两个独立分量、逐分量合法、`ι` 保合法" 的形状, `cmpK` 就不存在; 四组前提彼此独立 (`M1`, `M2`, `M3`).
- **[定理]** `cmpKᶜ≤`, `cmpKᶜ≡`: 加上跨证据的相干, 比较对一切 `SupB` 成立; `WI-incoh`: 见证世界恰好不相干.
- **[定理]** `raiseM`, `openA`: 四条更新律与 `Open-buildᴬ` 在接口的最小实例上有构造; 它们不推出任何禁忌.
- **[定理]** `AdmWNegDraft.no-botBd`: 接口原文的界之下 `KS.botBd` 不可满足 (接口已注明 `SupB` 不是 `KS`, 本条是它的定理形式).
- **[测试]** `AdmWNegLaws.CopyTest`: 一个闭项例子里两个拷贝在 `raiseM` 下拿到同一条路径.
- **[判断]** `RaiseCoh` 未定, 是方向 A 剩下的唯一一处; 我判断难点在 "合法性证据在环上给 `hself`" 能否在 `--without-K` 下绕开 (`cmpB₀` 绕开了 `at` 里的同一处, 但相干要比较**两个不同证据**的路径).
