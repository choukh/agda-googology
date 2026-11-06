# 可入下标上的比较式更新 (二): `raiseB` 与四条律

> 不含记号. 入口 [AdmW](AdmW.lagda.md), 接口 [AdmWIf](AdmWIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 最小实例 `Slot` (外层 `step S₀`, 坐标 `HB S₀`, 分量 `step (G₀ c)`, `G₀ c = Lev (up c)`). 更新 `raise w lo v c₀ p₀ δ`: 对每个可入分量 $(c,p)$, 用 `cmpB₀ p p₀` ([AdmWCmp](AdmWCmp.lagda.md)) 比较 $c$ 与 $c_0$ (两者都在同一个界 $b$ 之下), 槽接上增量 `inc`:
>
> - $c_0\lhd c$ (路径 $r$): 沿 $r$ 用 `UniTrNeg.emb⊲` 把 $\delta$ 嵌进 `G₀ c` (底对齐, 坐标类型不变);
> - $c\lhd c_0$ 且路径字面是 `hself` ($c$ 与 $c_0$ 被合一): 原样 $\delta$;
> - $c\lhd c_0$ 且路径不是 `hself` (严格在下): $0$, 槽不动 ($s\boxplus 0 = s$ 是定义).
>
> **定理 (`raiseᴮ : RaiseB`)**: 接口的四条律全部成立.
>
> - `at`: 在 $(c_0,p_0)$ 处恰好接长, **对一切证据 $p_0$**, 命题相等 (由 `cmpB₀-diag`). 不只字面 `hself`.
> - `below`: $c$ 严格是 $c_0$ 的子项 (且 $c$ 带证据) 时分量不动 (定义相等, 经 η).
> - `mono`: 世界只增 (同一证据, 槽是 `⊞-fst`).
> - `legal`: 保合法 (`Lg-⊞`, `Lg-emb⊲`).
>
> **定理 (`adm-build : Open-buildᴬ`)**: `UniTrBase.W′.UniTr` 的可入版: 下标是可入坐标 $(c, p)$, 增量族 `HB (G₀ c)`, 忠实取 `_≡_`. 这就是 `UniTrNeg.Open.Open-build` 把下标限制到可入坐标之后的陈述; 证明不用判定裸下标的相等, 也不用 `UniTrNeg.dec→sel` 的 Hedberg (`bdec` 给出的相等要沿 `subst` 搬, 对角上的 `subst` 要 UIP, 见 [AdmWCoh](AdmWCoh.lagda.md) §4), 而用 `cmpB₀-diag` 直接作 `Selector.diag` 的角色. 积世界版 `Open-build` (裸下标) 仍未证也未否.
>
> **它说明什么.** 诊断 §2.2 的 W⁺ 的构造一半: 限制在带公共上界证据的下标上, 选择性的更新写得出, 律是定理, 不推出任何判定. 它不说明 `SupB` 上有坐标比较 (`CmpK`), 那是 [AdmWCoh](AdmWCoh.lagda.md) 的事.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWRaise where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; wf; irr; toLt)
open import OCF.Align.UniTrNeg using (emb⊲; Lg-emb⊲)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCmp
open Slot
open RaiseIf
```

## §1 增量

```agda
inc : ∀ {a : A} {c₀ c : HB S₀} → (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀) → HB (G₀ c₀) → HB (G₀ c)
inc (inj₁ r) δ = emb⊲ (up-⊲ {β = hz} r) δ
inc (inj₂ hself) δ = δ
inc (inj₂ (hsuc _)) δ = hz
inc (inj₂ (hlim _ _)) δ = hz
inc (inj₂ (hLim _ _)) δ = hz

Lg-inc : ∀ {a : A} {c₀ c : HB S₀} (x : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) δ → LgB δ → LgB (inc x δ)
Lg-inc (inj₁ r) δ l = Lg-emb⊲ (up-⊲ {β = hz} r) δ l
Lg-inc (inj₂ hself) δ l = l
Lg-inc (inj₂ (hsuc _)) δ l = tt
Lg-inc (inj₂ (hlim _ _)) δ l = tt
Lg-inc (inj₂ (hLim _ _)) δ l = tt

-- 严格在下: 增量是 0
inc-below : ∀ {a : A} {c₀ c : HB S₀} (x : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) δ → c <ᴮ c₀ → inc x δ ≡ hz
inc-below (inj₁ r) δ lt with toLt r
... | inj₁ refl = ⊥-elim (irr (wf _) lt)
... | inj₂ s = ⊥-elim (irr (wf _) (<ᴮ-tr lt s))
inc-below (inj₂ hself) δ lt = ⊥-elim (irr (wf _) lt)
inc-below (inj₂ (hsuc _)) δ lt = refl
inc-below (inj₂ (hlim _ _)) δ lt = refl
inc-below (inj₂ (hLim _ _)) δ lt = refl
```

## §2 更新

```agda
raise : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → HB (G₀ c₀) → Cmp w
raise w lo v c₀ p₀ δ c p = proj₁ (v c p) , (proj₂ (v c p) ⊞ inc (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo)) δ)
```

## §3 四条律

```agda
at′ : ∀ w lo v c₀ p₀ δ → raise w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ)
at′ w lo v c₀ p₀ δ =
  cong (λ t → proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ inc t δ)) (cmpB₀-diag p₀ (proj₁ lo) (proj₂ lo))

below′ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → raise w lo v c₀ p₀ δ c p ≡ v c p
below′ w lo v c₀ p₀ δ c p lt =
  cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (inc-below (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo)) δ lt)

mono′ : ∀ w lo v c₀ p₀ δ → LgB δ → (w , v) ≤ᴮ (w , raise w lo v c₀ p₀ δ)
mono′ w lo v c₀ p₀ δ l =
  ≤w-rf (step S₀) ,
  λ c p → p , (≤w-rf (G₀ c) , ⊞-fst (proj₂ (v c p)) (inc (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo)) δ))

legal′ : ∀ w lo v c₀ p₀ δ → LgB δ → LgWᴮ (w , v) → LgWᴮ (w , raise w lo v c₀ p₀ δ)
legal′ w lo v c₀ p₀ δ l lW =
  proj₁ lW ,
  λ c p → proj₁ (proj₂ lW c p) ,
          Lg-⊞ (proj₂ (v c p)) (inc (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo)) δ) (proj₂ (proj₂ lW c p))
               (Lg-inc (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo)) δ l)

raiseᴮ : RaiseB
raiseᴮ = record { raiseB = raise ; at = at′ ; below = below′ ; mono = mono′ ; legal = legal′ }
```

## §4 `Open-build` 的可入版

```agda
adm-build : Open-buildᴬ
adm-build w lo = record
  { tr    = λ i₀ i δ → inc (cmpB₀ (proj₂ i) (proj₂ i₀) (proj₁ lo) (proj₂ lo)) δ
  ; faith = λ i₀ δ l → cong (λ t → inc t δ) (cmpB₀-diag (proj₂ i₀) (proj₁ lo) (proj₂ lo))
  ; legal = λ i₀ i δ l → Lg-inc (cmpB₀ (proj₂ i) (proj₂ i₀) (proj₁ lo) (proj₂ lo)) δ l }
```
