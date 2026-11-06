# 局部 UIP (二): 证据无关的写法, 增量是坐标的族

> 不含记号. 入口 [LocUip](LocUip.lagda.md), 接口 [LocUipIf](LocUipIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [LocUipHed](LocUipHed.lagda.md) 说: `raise₀ᴮ` 保相干要的局部 UIP 等价于合法高度上的 K. 卡点是 `incD (inj₁ e) δ = subst e δ` 用了判定给的**相等证明** $e$, 而两个证据给出两个 $e$. 这里换一种写法: 增量是坐标的族 $\delta : (c : \mathrm{HB}\,S_0) \to \mathrm{HB}(G_0\,c)$, 更新在判定为 "相等" 的分量上接 $\delta\,c$, **只用判定的是/否**. 是/否对证据无关, 因为 "是" 与 "否" 不能同时成立 (`incF-irr`, 四种情形, 两种矛盾, 两种 `refl`).
>
> **定理.**
>
> - `raiseFᴮ : RaiseF`: 接口记录的五条律 (`atF`, `belowF`, `monoF`, `legalF`, `cohF`) 无条件成立; 外加 `offF : OffF raiseFᴮ`. `cohF` 就是 "保 `Coh≡`", 不用 UIP, 不用外延.
> - `dirAᶠ`: 有保相干的族更新, 且相干世界上有坐标比较 (`AdmWCoh.coh≡→cmpK`). 这是 `AdmWCoh.dirA-cond` 去掉 `UIPᴴ` 之后的族版本.
> - **`raise₀ᴮ` 本身对族的值是相干的** (`raise₀≡F`, `fam→coh₀`): 若单个增量是某个族在 $c_0$ 处的值, $\delta = \hat\delta\,c_0$, 则 `raise₀` 与 `raiseF` 逐分量相等 (`subst e (δ̂ c₀) ≡ δ̂ c` 对 $e$ 归纳, 终点自由, 不要 K), 所以 `raise₀ᴮ` 保 `Coh≡`. 卡住的只是**不能写成族的值**的增量.
> - **有限坐标处一切增量都是族的值** (`extF`, `extF-at`): $c_0$ 是有限数 `fin n` 时, 按构造子匹配坐标就能把 $\delta$ 延成族 (不判定任何裸坐标的相等). 推论 `fin-coh₀`: 在 $c_0$ 为有限数的更新上, `raise₀ᴮ` 无条件保 `Coh≡`.
>
> **代价 (判断).** 族的写法要求回灌的增量对一切坐标一致地给出. 增量在 $c_0$ 处算出, 化成族要么沿相等搬运 (回到 UIP), 要么有一个对坐标一致的读法 (`DiagK3Grow.embL` 一类, 只用底种类, 有损); 对含函数分支的 $c_0$ (如 $\omega$), 把一个 `HB (G₀ c₀)` 延成族, 我判断要函数外延 (对角上恒等要分支函数的外延相等). 这是本路的第一个障碍, 见入口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipFam where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; wf; irr)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (incD; dD; raise₀; raise₀ᴮ; coh≡→cmpK; fin)
open import OCF.Align.LocUipIf
open Slot
open RaiseIf
```

## §1 族增量与它的选择

```agda
incF : ∀ {c₀ c : HB S₀} → (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c) → Inc → HB (G₀ c)
incF {c = c} (inj₁ _) δ = δ c
incF (inj₂ _) δ = hz

incF-irr : ∀ {c₀ c : HB S₀} (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → incF d δ ≡ incF d′ δ
incF-irr (inj₁ _) (inj₁ _) δ = refl
incF-irr (inj₁ e) (inj₂ ne) δ = ⊥-elim (ne e)
incF-irr (inj₂ ne) (inj₁ e) δ = ⊥-elim (ne e)
incF-irr (inj₂ _) (inj₂ _) δ = refl

incF-at : ∀ {c₀ : HB S₀} (d : (c₀ ≡ c₀) ⊎ ¬ (c₀ ≡ c₀)) δ → incF d δ ≡ δ c₀
incF-at (inj₁ _) δ = refl
incF-at (inj₂ ne) δ = ⊥-elim (ne refl)

incF-off : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → ¬ (c₀ ≡ c) → incF d δ ≡ hz
incF-off (inj₁ e) δ ne = ⊥-elim (ne e)
incF-off (inj₂ _) δ ne = refl

Lg-incF : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → LgB (δ c₀) → LgB (incF d δ)
Lg-incF (inj₁ e) δ l = subst (λ z → LgB (δ z)) e l
Lg-incF (inj₂ _) δ l = tt
```

## §2 更新与它的律

```agda
rF : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → Inc → Cmp w
rF w lo v c₀ p₀ δ c p = proj₁ (v c p) , (proj₂ (v c p) ⊞ incF (dD w lo p p₀) δ)

atF′ : ∀ w lo v c₀ p₀ δ → rF w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ c₀)
atF′ w lo v c₀ p₀ δ = cong (λ t → proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ t)) (incF-at (dD w lo p₀ p₀) δ)

offF′ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → ¬ (c₀ ≡ c) → rF w lo v c₀ p₀ δ c p ≡ v c p
offF′ w lo v c₀ p₀ δ c p ne = cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (incF-off (dD w lo p p₀) δ ne)

belowF′ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → rF w lo v c₀ p₀ δ c p ≡ v c p
belowF′ w lo v c₀ p₀ δ c p lt = offF′ w lo v c₀ p₀ δ c p (λ { refl → irr (wf _) lt })

monoF′ : ∀ w lo v c₀ p₀ δ → (w , v) ≤ᴮ (w , rF w lo v c₀ p₀ δ)
monoF′ w lo v c₀ p₀ δ =
  ≤w-rf (step S₀) , λ c p → p , (≤w-rf (G₀ c) , ⊞-fst (proj₂ (v c p)) (incF (dD w lo p p₀) δ))

legalF′ : ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → LgWᴮ (w , v) → LgWᴮ (w , rF w lo v c₀ p₀ δ)
legalF′ w lo v c₀ p₀ δ l lW =
  proj₁ lW ,
  λ c p → proj₁ (proj₂ lW c p) ,
          Lg-⊞ (proj₂ (v c p)) (incF (dD w lo p p₀) δ) (proj₂ (proj₂ lW c p)) (Lg-incF (dD w lo p p₀) δ l)

cohF′ : ∀ w lo v c₀ p₀ δ → Coh≡ (w , v) → Coh≡ (w , rF w lo v c₀ p₀ δ)
cohF′ w lo v c₀ p₀ δ coh c p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (incF-irr (dD w lo p p₀) (dD w lo p′ p₀) δ)

raiseFᴮ : RaiseF
raiseFᴮ = record { raiseF = rF ; atF = atF′ ; belowF = belowF′ ; monoF = monoF′ ; legalF = legalF′ ; cohF = cohF′ }

offF : OffF raiseFᴮ
offF = offF′

-- 无条件: 保相干的族更新 + 相干世界上的坐标比较
dirAᶠ : Σ RaiseF (λ R → OffF R) × CmpKᶜ Coh≡
dirAᶠ = (raiseFᴮ , offF) , coh≡→cmpK (step S₀) (inj₂ tt) (λ c → step (G₀ c))
```

## §3 `raise₀ᴮ` 对族的值是相干的

```agda
subst-fam : ∀ {c₀ c : HB S₀} (e : c₀ ≡ c) (δ : Inc) → subst (λ z → HB (G₀ z)) e (δ c₀) ≡ δ c
subst-fam refl δ = refl

incD≡F : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) (δ : Inc) → incD d (δ c₀) ≡ incF d δ
incD≡F (inj₁ e) δ = subst-fam e δ
incD≡F (inj₂ _) δ = refl

raise₀≡F : ∀ w lo v c₀ p₀ (δ : Inc) c p → raise₀ w lo v c₀ p₀ (δ c₀) c p ≡ rF w lo v c₀ p₀ δ c p
raise₀≡F w lo v c₀ p₀ δ c p = cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (incD≡F (dD w lo p p₀) δ)

fam→coh₀ : ∀ w lo v c₀ p₀ (δ : Inc) → Coh≡ (w , v) → Coh≡ (w , raise₀ w lo v c₀ p₀ (δ c₀))
fam→coh₀ w lo v c₀ p₀ δ coh c p p′ =
  trans (raise₀≡F w lo v c₀ p₀ δ c p) (trans (cohF′ w lo v c₀ p₀ δ coh c p p′) (sym (raise₀≡F w lo v c₀ p₀ δ c p′)))
```

**有限坐标.** `fin n` 的增量延成族: 先按构造子匹配坐标与 `fin n` (`mFin`, 匹配成功时给出由 `cong hs` 搭起来的相等, 它只是 $c$ 的函数, 与证据无关), 再沿这个相等搬. 不判定任何裸坐标的相等 (只匹配构造子).

```agda
mFin : ∀ n (c : HB S₀) → (fin n ≡ c) ⊎ ⊤
mFin zero hz = inj₁ refl
mFin zero (hs _) = inj₂ tt
mFin zero (hl _) = inj₂ tt
mFin zero (hΩ _ _) = inj₂ tt
mFin (suc n) hz = inj₂ tt
mFin (suc n) (hs c) with mFin n c
... | inj₁ e = inj₁ (cong hs e)
... | inj₂ t = inj₂ t
mFin (suc n) (hl _) = inj₂ tt
mFin (suc n) (hΩ _ _) = inj₂ tt

mFin-diag : ∀ n → mFin n (fin n) ≡ inj₁ refl
mFin-diag zero = refl
mFin-diag (suc n) rewrite mFin-diag n = refl

hF : ∀ n {c : HB S₀} → (fin n ≡ c) ⊎ ⊤ → HB (G₀ (fin n)) → HB (G₀ c)
hF n (inj₁ e) δ = subst (λ z → HB (G₀ z)) e δ
hF n (inj₂ _) δ = hz

extF : ∀ n → HB (G₀ (fin n)) → Inc
extF n δ c = hF n (mFin n c) δ

extF-at : ∀ n δ → extF n δ (fin n) ≡ δ
extF-at n δ = cong (λ d → hF n d δ) (mFin-diag n)

-- 推论: c₀ 是有限数时, raise₀ᴮ 无条件保 Coh≡
fin-coh₀ : ∀ w lo v n (p₀ : AdmE w (fin n)) δ → Coh≡ (w , v) → Coh≡ (w , raise₀ w lo v (fin n) p₀ δ)
fin-coh₀ w lo v n p₀ δ coh =
  subst (λ t → Coh≡ (w , raise₀ w lo v (fin n) p₀ t)) (extF-at n δ) (fam→coh₀ w lo v (fin n) p₀ (extF n δ) coh)
```

**范围.** `fin-coh₀` 只覆盖 $c_0$ 为有限数的更新. `Lemma1` 要对一切 $c_0$ (含 $\omega$ 这样有函数分支的坐标); 那一般情形等价于 `UIPᴸ` ([LocUipHed](LocUipHed.lagda.md)), 未证.
