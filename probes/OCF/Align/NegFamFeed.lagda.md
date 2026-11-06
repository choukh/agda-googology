# 族增量世界上的真折叠, 否定一路 (二): 只升 $c_1$ 的族更新上, `Feed₁` 的读回恒为零

> 不含记号. 入口 [NegFam](NegFam.lagda.md). 对着接口 [FamFoldIf](FamFoldIf.lagda.md) ("接口定稿 2026-11-05 11:20 (编译通过)", 变更记录: 无) §3 的记录 `Feed₁ R` 写, 导入它, 不另造接口; 本篇另加的定义 (`Keep₂`, `CopyCoh₂`) 只由 `AdmWIf`, `LocUipIf` 的名字组成. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **判决 (本篇).**
>
> 1. **`offF→rd0`, `offF→flat` (定理).** 若族更新 `R` 满足可入下标上的 `OffF` (只升 $c_0$ 本身, 如 `raiseFᴮ`, `raiseFᵒ`), 则对任一 `F : Feed₁ R`, 在任一外层世界里只要 $2$ (`hs c₁`) 可入且起点相干 (`CohC`), 链上**每一格的读回都是 $0$** (`rdO (输出) ≡ hz`), 于是链上 $c_1$ 的槽恒等于起点的槽, κ₂ 节点的每个分支都在**同一个**槽上取 (`offF→flat`). 也就是: `fold-Ω` 的 ℕ-极限的各项只差世界, 不差分支的输入; 回灌不升界. 证明: `ch-coh` 要新世界保 `CopyCoh`, 拷贝在 $2$ 的分量里, `OffF` 不动它, 而槽升了读回; 两者相等就是 "槽 ⊞ 读回 = 槽", 由子项良基得读回为 $0$ (`⊞≡→hz`).
> 2. **前提可满足 (定理).** `triv : Feed₁ raiseFᵒ` (读回取常值 $0$, 链用 `raiseFᵒ`) 是一个实例, `raiseFᵒ` 满足 `OffF` (`LocUipNegFeed.offFᵒ`); 世界 `w₃ = (0, 2)`, 起点 `v₀`, 证据 `p₁₃`, `p₂₃` 都是闭项. 结论在实例上成立且不是空话.
> 3. **下一层拷贝 (定理, 不是对接口的否定).** 接口的 `CopyCoh` 只管 `hs c₀` 这一步. `LocUipNegFeed.raiseF⁺` (升 `hs c₀` 里的拷贝, 无条件保 `CohC`) 不保**两步**的拷贝相干 `CopyCoh₂` (`hs (hs c₀)` 的分量里 $c_0$ 槽的那份拷贝): **`keep₂→¬copy₂`**, 对一切 "不动两步拷贝" 的族更新 (`Keep₂`), 实例 `¬copy₂-raiseF⁺`, 以及构造一路 `FamFoldOne` 实际用的 `LocUipFeed.raiseFCᴮ` (`¬copy₂-raiseFCᴮ`). 对一切级一条的折叠若要 "同一种类一个界" (`HtTowerNStage.no-wmatch` 那一线, 判断) 到一切深度, 就要逐层升一切嵌套的拷贝; 这是 `no-wmatch` 在族增量世界里的对应, 一步一步地回来.
>
> **律为什么是构造一路需要的.** `ch-coh` 与 `CohC` (`Coh≡ × CopyCoh`) 是接口 §3 原文; 接口文字给的理由是 `HtTowerNStage.no-wmatch` (同一种类一个界). `ch-s`, `famO`, `atF` 是接口原文 (读回是折叠自己的输出的读回族在 $c_1$ 的值, 族更新在 $(c_1,p_0)$ 处恰好接它). `OffF` 是 `LocUipIf` 原文的可入下标上的律. 本篇的结论说: 构造一路若用满足 `OffF` 的族更新 (接口文字 "更新只在判定 '是 $c_0$' 的分量上用它" 正是 `raiseFᴮ` 的写法), `Feed₁` 只剩平凡的回灌; 要升界就必须用升拷贝的更新 (`raiseF⁺` 一类, 不满足 `OffF`).
>
> **只否定什么.** 只否定: `OffF R` 与 `Feed₁ R` 同时成立而某一格读回非零 (在 $2$ 可入的相干世界上). **不否定** `Feed₁ R` 对不满足 `OffF` 的 `R` (如 `raiseF⁺`); 不否定 $2$ 不可入的外层世界上的非零读回 (那里 `CopyCoh` 不约束 $c_1$ 的槽, 例如外层界为 $1$); 不否定 `CohC` 以外的相干. 第 3 条只否定 `Keep₂` 的更新保 `CopyCoh₂`; 接口没有要求 `CopyCoh₂`, 所以它不是对接口的否定, 是下一步的障碍.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegFamFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; n0; nl)
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; wf; irr)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (wz; dD; fin)
open import OCF.Align.LocUipIf
open import OCF.Align.LocUipNegFeed using (raiseFᵒ; offFᵒ; bD; raiseF⁺)
open import OCF.Align.LocUipFeed using (raiseFCᴮ)
open import OCF.Align.FamFoldIf
open Slot
open RaiseIf
open Feed₁
```

## §1 槽 ⊞ 读回 = 槽 ⇒ 读回为 $0$

`a` 是 `a ⊞ d` 的子项或等于它 (`le⊞`); $d\ne 0$ 时是严格子项 (`lt⊞`); 子项良基.

```agda
le⊞ : ∀ {S} (a d : HB S) → (a ≡ a ⊞ d) ⊎ (a <ᴮ a ⊞ d)
le⊞ a hz = inj₁ refl
le⊞ a (hs d) with le⊞ a d
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hs (a ⊞ d)) (sym e) <s₀)
... | inj₂ lt = inj₂ (<s lt)
le⊞ a (hl f) with le⊞ a (f 0)
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hl (λ n → a ⊞ f n)) (sym e) (<l₀ 0))
... | inj₂ lt = inj₂ (<l 0 lt)
le⊞ {S} a (hΩ κ g) with le⊞ a (g (bot S κ))
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hΩ κ (λ c → a ⊞ g c)) (sym e) (<Ω₀ (bot S κ)))
... | inj₂ lt = inj₂ (<Ω (bot S κ) lt)

lt⊞ : ∀ {S} (a d : HB S) → (d ≡ hz) ⊎ (a <ᴮ a ⊞ d)
lt⊞ a hz = inj₁ refl
lt⊞ a (hs d) with le⊞ a d
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hs (a ⊞ d)) (sym e) <s₀)
... | inj₂ lt = inj₂ (<s lt)
lt⊞ a (hl f) with le⊞ a (f 0)
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hl (λ n → a ⊞ f n)) (sym e) (<l₀ 0))
... | inj₂ lt = inj₂ (<l 0 lt)
lt⊞ {S} a (hΩ κ g) with le⊞ a (g (bot S κ))
... | inj₁ e = inj₂ (subst (λ z → z <ᴮ hΩ κ (λ c → a ⊞ g c)) (sym e) (<Ω₀ (bot S κ)))
... | inj₂ lt = inj₂ (<Ω (bot S κ) lt)

⊞≡→hz : ∀ {S} (a d : HB S) → a ⊞ d ≡ a → d ≡ hz
⊞≡→hz a d e with lt⊞ a d
... | inj₁ z = z
... | inj₂ lt = ⊥-elim (irr (wf a) (subst (λ z → a <ᴮ z) e lt))
```

## §2 `OffF` 上的 `Feed₁`: 每一格的读回为 $0$, 槽不动

记号: 第 $n$ 格的世界 $v_n$ = `chain F w lo p₀ v g n`, 输出 $o_n$ = `fold F w lo p₀ vₙ (g (slotAt vₙ c₁ p₀))`.

```agda
module _ (R : RaiseF) (of : OffF R) (F : Feed₁ R) where
  private
    vn : ∀ w lo p₀ v g → ℕ → Cmp w
    vn w lo p₀ v g n = chain F w lo p₀ v g n

    on : ∀ w lo p₀ v g → ℕ → Out₂
    on w lo p₀ v g n = fold F w lo p₀ (vn w lo p₀ v g n) (g (slotAt (vn w lo p₀ v g n) c₁ p₀))

    c₁≢2 : ¬ (c₁ ≡ hs c₁)
    c₁≢2 ()

  -- 下一格的槽 = 这一格的槽 ⊞ 读回
  slot-suc : ∀ w lo p₀ v g n →
    slotAt (vn w lo p₀ v g (suc n)) c₁ p₀ ≡ slotAt (vn w lo p₀ v g n) c₁ p₀ ⊞ rdO F (on w lo p₀ v g n)
  slot-suc w lo p₀ v g n =
    trans (cong (λ V → proj₂ (V c₁ p₀)) (ch-s F w lo p₀ v g n))
      (trans (cong proj₂ (atF R w lo (vn w lo p₀ v g n) c₁ p₀ (proj₁ (famO F) (on w lo p₀ v g n))))
             (cong (λ t → slotAt (vn w lo p₀ v g n) c₁ p₀ ⊞ t) (proj₂ (famO F) (on w lo p₀ v g n))))

  -- 下一格在 2 处的拷贝 = 这一格的拷贝 (OffF)
  copy-suc : ∀ w lo p₀ v g n (p₂ : AdmE w (hs c₁)) →
    proj₂ (proj₁ (vn w lo p₀ v g (suc n) (hs c₁) p₂)) ≡ proj₂ (proj₁ (vn w lo p₀ v g n (hs c₁) p₂))
  copy-suc w lo p₀ v g n p₂ =
    trans (cong (λ V → proj₂ (proj₁ (V (hs c₁) p₂))) (ch-s F w lo p₀ v g n))
          (cong (λ X → proj₂ (proj₁ X)) (of w lo (vn w lo p₀ v g n) c₁ p₀ (proj₁ (famO F) (on w lo p₀ v g n)) (hs c₁) p₂ c₁≢2))

  offF→rd0 : ∀ w lo p₀ v g → CohC (w , v) → (p₂ : AdmE w (hs c₁)) → ∀ n → rdO F (on w lo p₀ v g n) ≡ hz
  offF→rd0 w lo p₀ v g coh p₂ n =
    ⊞≡→hz (slotAt (vn w lo p₀ v g n) c₁ p₀) (rdO F (on w lo p₀ v g n))
      (trans (sym (slot-suc w lo p₀ v g n))
        (trans (sym (proj₂ (ch-coh F w lo p₀ v g coh (suc n)) c₁ p₀ p₂))
          (trans (copy-suc w lo p₀ v g n p₂) (proj₂ (ch-coh F w lo p₀ v g coh n) c₁ p₀ p₂))))

  -- 推论: 槽沿链不动, κ₂ 节点的分支都在起点的槽上取
  offF→flat : ∀ w lo p₀ v g → CohC (w , v) → AdmE w (hs c₁) → ∀ n →
    slotAt (vn w lo p₀ v g n) c₁ p₀ ≡ slotAt v c₁ p₀
  offF→flat w lo p₀ v g coh p₂ zero = cong (λ V → proj₂ (V c₁ p₀)) (ch-z F w lo p₀ v g)
  offF→flat w lo p₀ v g coh p₂ (suc n) =
    trans (slot-suc w lo p₀ v g n)
      (trans (cong (λ t → slotAt (vn w lo p₀ v g n) c₁ p₀ ⊞ t) (offF→rd0 w lo p₀ v g coh p₂ n))
             (offF→flat w lo p₀ v g coh p₂ n))

  offF→branch : ∀ w lo p₀ v g → CohC (w , v) → AdmE w (hs c₁) → ∀ n →
    g (slotAt (vn w lo p₀ v g n) c₁ p₀) ≡ g (slotAt v c₁ p₀)
  offF→branch w lo p₀ v g coh p₂ n = cong g (offF→flat w lo p₀ v g coh p₂ n)
```

## §3 前提实例: `Feed₁ raiseFᵒ` 的平凡实例与一个世界

读回取常值 $0$; 链用 `raiseFᵒ` 接零族; 折叠只在 κ₂ 节点处取链上分支的 ℕ-极限, 别处给 `n0`. `fold-Ω`, `ch-z`, `ch-s` 都是 `refl`.

```agda
Z : Inc
Z c = hz

bD-Z : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) → bD d Z ≡ hz
bD-Z (inj₁ _) = refl
bD-Z (inj₂ _) = refl

chT : ∀ w → LgO w → AdmE w c₁ → Cmp w → (Ht → HB S₂) → ℕ → Cmp w
chT w lo p₀ v g zero = v
chT w lo p₀ v g (suc n) = raiseF raiseFᵒ w lo (chT w lo p₀ v g n) c₁ p₀ Z

foldT : FoldW₁
foldT w lo p₀ v (hΩ (inj₂ tt) g) W = nl (λ n → foldT w lo p₀ (chT w lo p₀ v g n) (g (slotAt (chT w lo p₀ v g n) c₁ p₀)) W)
foldT w lo p₀ v _ W = n0

-- 零族的 raiseFᵒ 保拷贝相干
copyZ : ∀ w lo v c₀ p₀ → CopyCoh (w , v) → CopyCoh (w , raiseF raiseFᵒ w lo v c₀ p₀ Z)
copyZ w lo v c₀ p₀ cc c q₀ q₁ =
  trans (cc c q₀ q₁) (sym (cong (λ t → proj₂ (v c q₀) ⊞ t) (bD-Z (dD w lo q₀ p₀))))

lgT : ∀ w lo p₀ v g → LgWᴮ (w , v) → ∀ n → LgWᴮ (w , chT w lo p₀ v g n)
lgT w lo p₀ v g l zero = l
lgT w lo p₀ v g l (suc n) = legalF raiseFᵒ w lo (chT w lo p₀ v g n) c₁ p₀ Z tt (lgT w lo p₀ v g l n)

cohT : ∀ w lo p₀ v g → CohC (w , v) → ∀ n → CohC (w , chT w lo p₀ v g n)
cohT w lo p₀ v g c zero = c
cohT w lo p₀ v g c (suc n) =
  cohF raiseFᵒ w lo (chT w lo p₀ v g n) c₁ p₀ Z (proj₁ (cohT w lo p₀ v g c n)) ,
  copyZ w lo (chT w lo p₀ v g n) c₁ p₀ (proj₂ (cohT w lo p₀ v g c n))

triv : Feed₁ raiseFᵒ
triv = record
  { fold = foldT
  ; rdO = λ o → hz
  ; lg-rdO = λ o → tt
  ; famO = (λ o → Z) , (λ o → refl)
  ; chain = chT
  ; ch-z = λ w lo p₀ v g → refl
  ; ch-s = λ w lo p₀ v g n → refl
  ; fold-Ω = λ w lo p₀ v g W → refl
  ; ch-lg = lgT
  ; ch-coh = cohT
  ; ch-≤ = λ w lo p₀ v g n → monoF raiseFᵒ w lo (chT w lo p₀ v g n) c₁ p₀ Z }

-- 世界: 外层 (0, 2), 1 与 2 都可入, 全 0 的分量, 两种相干都是 refl
w₃ : Out
w₃ = azero , hs (hs hz)

lo₃ : LgO w₃
lo₃ = tt , tt

v₃ : Cmp w₃
v₃ c p = wz (up c) , hz

coh₃ : CohC (w₃ , v₃)
coh₃ = (λ c p p′ → refl) , (λ c₀ p₀ p₁ → refl)

p₁₃ : AdmE w₃ c₁
p₁₃ = hsuc hself

p₂₃ : AdmE w₃ (hs c₁)
p₂₃ = hself

-- 实例上的结论 (对任一分支 g)
inst : ∀ (g : Ht → HB S₂) n → rdO triv (fold triv w₃ lo₃ p₁₃ (chain triv w₃ lo₃ p₁₃ v₃ g n)
                                  (g (slotAt (chain triv w₃ lo₃ p₁₃ v₃ g n) c₁ p₁₃))) ≡ hz
inst g n = offF→rd0 raiseFᵒ offFᵒ triv w₃ lo₃ p₁₃ v₃ g coh₃ p₂₃ n
```

## §4 下一层拷贝: 升一步拷贝的更新不保两步拷贝的相干

`hs (hs c₀)` 的分量的旧种类部分里, 第二层旧种类部分装着 $c_0$ 槽的一份拷贝 (坐标类型都是 `HB (G₀ c₀)`, 定义相等).

```agda
nest₂ : ∀ {w} (v : Cmp w) (c₀ : HB S₀) → AdmE w (hs (hs c₀)) → HB (G₀ c₀)
nest₂ v c₀ p₂ = proj₂ (proj₁ (proj₁ (v (hs (hs c₀)) p₂)))

CopyCoh₂ : Wᴮ → Set
CopyCoh₂ W = ∀ (c₀ : HB S₀) (p₀ : AdmE (proj₁ W) c₀) (p₂ : AdmE (proj₁ W) (hs (hs c₀))) → nest₂ (proj₂ W) c₀ p₂ ≡ proj₂ (proj₂ W c₀ p₀)

-- 不动两步拷贝
Keep₂ : RaiseF → Set
Keep₂ R = ∀ w lo v c₀ p₀ δ (p₂ : AdmE w (hs (hs c₀))) → nest₂ (raiseF R w lo v c₀ p₀ δ) c₀ p₂ ≡ nest₂ v c₀ p₂

RaiseCopy₂ : RaiseF → Set
RaiseCopy₂ R = ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → CopyCoh₂ (w , v) → CopyCoh₂ (w , raiseF R w lo v c₀ p₀ δ)

δ₁ : Inc
δ₁ c = hs hz

q₀ : AdmE w₃ hz
q₀ = hsuc (hsuc hself)

copy₂₃ : CopyCoh₂ (w₃ , v₃)
copy₂₃ c₀ p₀ p₂ = refl

no-hs : ∀ {w} → ¬ (_⊲[_]_ {S₀} (hs hz) w hz)
no-hs ()

keep₂→¬copy₂ : ∀ R → Keep₂ R → ¬ RaiseCopy₂ R
keep₂→¬copy₂ R k rc =
  no-hs (subst (λ t → hs hz ⊲[ proj₁ (raiseF R w₃ lo₃ v₃ hz q₀ δ₁ hz q₀) ] t)
               (trans (sym (rc w₃ lo₃ v₃ hz q₀ δ₁ tt copy₂₃ hz q₀ p₂₃)) (k w₃ lo₃ v₃ hz q₀ δ₁ p₂₃))
               (subst (λ X → hs hz ⊲[ proj₁ X ] proj₂ X) (sym (atF R w₃ lo₃ v₃ hz q₀ δ₁)) hself))

keep₂-raiseF⁺ : Keep₂ raiseF⁺
keep₂-raiseF⁺ w lo v c₀ p₀ δ p₂ = refl

¬copy₂-raiseF⁺ : ¬ RaiseCopy₂ raiseF⁺
¬copy₂-raiseF⁺ = keep₂→¬copy₂ raiseF⁺ keep₂-raiseF⁺

-- 构造一路实际用的 LocUipFeed.raiseFCᴮ 同样
keep₂-raiseFCᴮ : Keep₂ raiseFCᴮ
keep₂-raiseFCᴮ w lo v c₀ p₀ δ p₂ = refl

¬copy₂-raiseFCᴮ : ¬ RaiseCopy₂ raiseFCᴮ
¬copy₂-raiseFCᴮ = keep₂→¬copy₂ raiseFCᴮ keep₂-raiseFCᴮ
```

## §5 结论 (按档)

- **[定理]** `le⊞`, `lt⊞`, `⊞≡→hz`: 槽 ⊞ $d$ = 槽 ⇒ $d = 0$ (子项良基, 无外延).
- **[定理]** `slot-suc`, `copy-suc`, **`offF→rd0`**, **`offF→flat`**, `offF→branch`: `OffF R` 与 `Feed₁ R` 下, $2$ 可入的相干世界上每格读回为 $0$, 槽不动, κ₂ 节点的分支都取同一个输入.
- **[定理]** `triv : Feed₁ raiseFᵒ`, `w₃`, `coh₃`, `p₁₃`, `p₂₃`, `inst`: 前提实例.
- **[定理]** `keep₂→¬copy₂`, `keep₂-raiseF⁺`, **`¬copy₂-raiseF⁺`**, `keep₂-raiseFCᴮ`, **`¬copy₂-raiseFCᴮ`**: 升一步拷贝的更新不保两步拷贝相干 (下一层的障碍, 不是对接口的否定).
- **[判断]** 对一切级的折叠要的相干是一切深度的拷贝 (加上 ℕ-极限分量里每个 $n$ 的拷贝); 依据 `no-wmatch`. 嵌套拷贝的坐标都与 $c_0$ 在同一个界之下 (`hs` 链与 ℕ-极限的分支都是第一位置), 所以逐层判定写得出 (`bdec`); 有没有对一切深度一致的写法, 未写.
