# 局部 UIP 的否定一路 (二): 回灌不能只升 $c_0$ 本身

> 不含记号. 入口 [LocUipNeg](LocUipNeg.lagda.md). 对着接口 [LocUipIf](LocUipIf.lagda.md) ("接口定稿 2026-11-05 10:45", 变更记录: 无) §3 写, 导入它, 不另造接口; 本篇另加的定义 (`FeedKeep`, `RaiseCopyF`) 都由接口的名字组成. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 接口的第二条引理问: 回灌要的更新律是不是只升 $c_0$ 本身. 回灌一步要的东西写在接口的 `Feed Coh` 里: 新世界变大, 合法, 保相干 `Coh`, 读回值 $b\boxplus\delta$ 在 $(c_0,\text{槽})$ 之下有界. $c_0$ 之上的分量 `hs c₀` 的旧种类部分 (分量的第一分量) 装着 $c_0$ 的槽种类的一份拷贝; 接口的 `CopyCoh` 说拷贝的界等于 $c_0$ 的槽.
>
> **判决: 回灌必须升 $c_0$ 之上的分量 (定理).**
>
> 1. **`¬feedKeep`**: 对任一含 `CopyCoh` 的相干 `Coh` (前提: 见证世界满足它), 不存在这样的回灌: 读回值有界, 保 `Coh`, 而 `hs c₀` 的分量的旧种类部分不动. 见证: 外层世界 $(0, 1)$, 坐标 $0$ 与 $1$ 都可入, 分量全 $0$, 增量 $\delta = 1$. 读回值是 $0\boxplus 1 = 1$; 它有界就要槽 $\rhd 1$; `CopyCoh` 要拷贝等于槽; 拷贝不动就还是 $0$; 而 $1\lhd 0$ 不成立. 证明不用 "变大" 与 "合法" 两个合取项, 所以这一条比 `Feed` 的否定更强.
> 2. **`slotOnly→¬raiseCopy`**: 只改槽的更新 (`SlotOnly`, `raiseᴮ` 与 `raise₀ᴮ` 都是, `refl`) 不保 `CopyCoh` (`RaiseCopy`). **`offF→¬raiseCopyF`**: 证据无关写法里满足 `OffF` (只升 $c_0$ 本身) 的更新也不保 `CopyCoh`. 前提都有实例: `raise₀ᴮ`, `raiseᴮ` (接口已有), `raiseFᵒ` (本篇 §3, 满足 `OffF` 的 `RaiseF`).
> 3. **被否定的律是可满足的 (非空真)**: 升 $c_0$ 之上拷贝的更新写得出.
>    - 证据无关写法 `raiseF⁺ : RaiseF` (§4): 槽在 $c\equiv c_0$ 处接 $\delta\,c$, 分量 `hs c` 的拷贝在 $c\equiv c_0$ 处也接 $\delta\,c$, 只用判定的是/否. **无条件**保 `Coh≡` 与 `CopyCoh` (`copyF⁺`), 并给出接口的 `Feedᶠ (Coh≡ ∧ CopyCoh)` (`feedF⁺`).
>    - 单个增量写法 `raise⁺ᴮ : RaiseB` (§5, 四条律无条件): 保 `CopyCoh` 要 `IncIrr` (`irr→raiseCopy⁺`, 条件定理), 即 [LocUipNegLoop](LocUipNegLoop.lagda.md) 的 `LoopFix`; 在见证世界上无条件 (`feed⁺-inst`).
>
> **只否定什么.** 只否定 "回灌之后 `hs c₀` 的分量的旧种类部分不动" 与 "保 `CopyCoh`" 同时成立 (以及推出前者的 `SlotOnly`, `OffF`). **不否定**: 接口的 `Feed`/`Feedᶠ` 本身 (后者由 `feedF⁺` 无条件成立); 升 $c_0$ 之上拷贝的更新; 不要求 `CopyCoh` 的回灌. `CopyCoh` 只写了 `hs` 这一步 (接口原文); ℕ-极限与 $\Omega$-极限分量里的拷贝本篇不处理.
>
> **律为什么是构造一路需要的.** `CopyCoh` 是接口写下的相干 (接口文字: "`HtTowerNStage.no-wmatch` 那一线要的 '同一种类一个界'"): `no-wmatch` [定理] 说逐分量独立的界给不出对角的并要的世界对应; 坐标类型同为 `HB (G₀ c₀)` 的槽种类与它在 `hs c₀` 里的拷贝, 在对角的并里是同一个种类 [判断, 与 `no-wmatch` 的 `κ0`/`κ1` 同形]. 读回值有界是 `HtTowerFFold.κc₁` 回灌一格的形状 (新世界的界是读回值, 下一格在其上读). `FeedKeep` 的 "不动" 是 `SlotOnly` 与 `OffF` 在 `hs c₀` 处的共同推论.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipNegFeed where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; wf; irr; lt→≢)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCmp using (dec₀-diag; <ᴮ-tr)
open import OCF.Align.AdmWCoh using (raise₀ᴮ; raise₀; incD; Lg-incD; incD-off; dD; at₀; below₀; wz; lg-wz)
open import OCF.Align.AdmWRaise using (raiseᴮ)
open import OCF.Align.LocUipIf
open Slot
open RaiseIf
```

## §1 见证世界

外层 $(0, 1)$: 坐标 $0$ (证据 `hsuc hself`) 与 $1$ (证据 `hself`) 都可入. 分量全 $0$. 拷贝: `hs c` 的分量的第一分量是 `(wz (up c) , hz)`, 与 `c` 的分量定义相等, 所以 `CopyCoh` 是 `refl`.

```agda
w₂ : Out
w₂ = azero , hs hz

lo₂ : LgO w₂
lo₂ = tt , tt

v₂ : Cmp w₂
v₂ c p = wz (up c) , hz

lgW₂ : LgWᴮ (w₂ , v₂)
lgW₂ = lo₂ , λ c p → lg-wz (up c) , tt

copy₂ : CopyCoh (w₂ , v₂)
copy₂ c₀ p₀ p₁ = refl

coh₂ : Coh≡ (w₂ , v₂)
coh₂ c p p′ = refl

q₀ : AdmE w₂ hz
q₀ = hsuc hself

q₁ : AdmE w₂ (hs hz)
q₁ = hself

no-hs : ∀ {w} → ¬ (_⊲[_]_ {S₀} (hs hz) w hz)
no-hs ()
```

## §2 回灌不动 `hs c₀` 的旧种类部分, 就不保拷贝相干

`FeedKeep Coh`: 接口的 `Feed Coh`, 外加 "新世界在 `hs c₀` 的每个分量的旧种类部分与旧世界相同".

```agda
FeedKeep : (Wᴮ → Set) → Set
FeedKeep Coh = ∀ w (lo : LgO w) (v : Cmp w) c₀ (p₀ : AdmE w c₀) (δ : HB (G₀ c₀)) → LgB δ → LgWᴮ (w , v) → Coh (w , v) →
  Σ (Cmp w) (λ v′ → ((w , v) ≤ᴮ (w , v′)) × LgWᴮ (w , v′) × Coh (w , v′) ×
                    Bdᴮ (c₀ , inj₂ tt) (proj₂ (v c₀ p₀) ⊞ δ) (w , v′) ×
                    (∀ (p₁ : AdmE w (hs c₀)) → proj₁ (v′ (hs c₀) p₁) ≡ proj₁ (v (hs c₀) p₁)))

¬feedKeep : ∀ (Coh : Wᴮ → Set) → Coh (w₂ , v₂) → (∀ W → Coh W → CopyCoh W) → ¬ FeedKeep Coh
¬feedKeep Coh c₂ toCopy fk with fk w₂ lo₂ v₂ hz q₀ (hs hz) tt lgW₂ c₂
... | v′ , _ , _ , coh′ , (p , q) , keep =
  no-hs (subst (λ t → hs hz ⊲[ proj₁ (v′ hz p) ] t)
               (trans (sym (toCopy (w₂ , v′) coh′ hz p q₁)) (cong proj₂ (keep q₁))) q)

-- 两个实例: 只要拷贝相干; 拷贝相干且跨证据相干
¬feedKeep-copy : ¬ FeedKeep CopyCoh
¬feedKeep-copy = ¬feedKeep CopyCoh copy₂ (λ W c → c)

¬feedKeep-both : ¬ FeedKeep (λ W → Coh≡ W × CopyCoh W)
¬feedKeep-both = ¬feedKeep (λ W → Coh≡ W × CopyCoh W) (coh₂ , copy₂) (λ W c → proj₂ c)
```

**只改槽的更新不保拷贝相干.** 接口的 `SlotOnly`, `RaiseCopy`.

```agda
slotOnly→¬raiseCopy : ∀ R → SlotOnly R → ¬ RaiseCopy R
slotOnly→¬raiseCopy R so rc =
  no-hs (subst (λ t → hs hz ⊲[ proj₁ (raiseB R w₂ lo₂ v₂ hz q₀ (hs hz) hz q₀) ] t)
               (trans (sym (rc w₂ lo₂ v₂ hz q₀ (hs hz) tt copy₂ hz q₀ q₁))
                      (cong proj₂ (so w₂ lo₂ v₂ hz q₀ (hs hz) (hs hz) q₁)))
               (subst (λ X → hs hz ⊲[ proj₁ X ] proj₂ X) (sym (at R w₂ lo₂ v₂ hz q₀ (hs hz))) hself))

¬raiseCopy-raise₀ : ¬ RaiseCopy raise₀ᴮ
¬raiseCopy-raise₀ = slotOnly→¬raiseCopy raise₀ᴮ (λ w lo v c₀ p₀ δ c p → refl)

¬raiseCopy-raiseᴮ : ¬ RaiseCopy raiseᴮ
¬raiseCopy-raiseᴮ = slotOnly→¬raiseCopy raiseᴮ (λ w lo v c₀ p₀ δ c p → refl)
```

## §3 证据无关写法: 只升 $c_0$ 本身的更新 `raiseFᵒ`, 也不保拷贝相干

增量是族 `Inc`; 判定说 "是" 就接 $\delta\,c$, 说 "否" 就接 $0$. 只用判定的是/否, 所以跨证据相干是无条件的 (`bD-irr`, 两个判定 "一是一否" 时矛盾).

```agda
bD : ∀ {c₀ c : HB S₀} → (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c) → Inc → HB (G₀ c)
bD {c = c} (inj₁ _) δ = δ c
bD (inj₂ _) δ = hz

Lg-bD : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → LgB (δ c₀) → LgB (bD d δ)
Lg-bD (inj₁ refl) δ l = l
Lg-bD (inj₂ _) δ l = tt

bD-off : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → ¬ (c₀ ≡ c) → bD d δ ≡ hz
bD-off (inj₁ e) δ ne = ⊥-elim (ne e)
bD-off (inj₂ _) δ ne = refl

bD-irr : ∀ {c₀ c : HB S₀} (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → bD d δ ≡ bD d′ δ
bD-irr (inj₁ _) (inj₁ _) δ = refl
bD-irr (inj₁ e) (inj₂ ne) δ = ⊥-elim (ne e)
bD-irr (inj₂ ne) (inj₁ e) δ = ⊥-elim (ne e)
bD-irr (inj₂ _) (inj₂ _) δ = refl

bD-diag : ∀ w (lo : LgO w) {c₀} (p₀ : AdmE w c₀) δ → bD (dD w lo p₀ p₀) δ ≡ δ c₀
bD-diag w lo p₀ δ = cong (λ t → bD t δ) (dec₀-diag p₀ (proj₁ lo) (proj₂ lo))

lt-ne : ∀ {c c₀ : HB S₀} → c <ᴮ c₀ → ¬ (c₀ ≡ c)
lt-ne lt refl = irr (wf _) lt

raiseFᵒ : RaiseF
raiseFᵒ = record
  { raiseF = λ w lo v c₀ p₀ δ c p → proj₁ (v c p) , (proj₂ (v c p) ⊞ bD (dD w lo p p₀) δ)
  ; atF = λ w lo v c₀ p₀ δ → cong (λ t → proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ t)) (bD-diag w lo p₀ δ)
  ; belowF = λ w lo v c₀ p₀ δ c p lt → cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (bD-off (dD w lo p p₀) δ (lt-ne lt))
  ; monoF = λ w lo v c₀ p₀ δ → ≤w-rf (step S₀) , λ c p → p , (≤w-rf (G₀ c) , ⊞-fst (proj₂ (v c p)) (bD (dD w lo p p₀) δ))
  ; legalF = λ w lo v c₀ p₀ δ l lW → proj₁ lW , λ c p → proj₁ (proj₂ lW c p) ,
      Lg-⊞ (proj₂ (v c p)) (bD (dD w lo p p₀) δ) (proj₂ (proj₂ lW c p)) (Lg-bD (dD w lo p p₀) δ l)
  ; cohF = λ w lo v c₀ p₀ δ coh c p p′ →
      cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (bD-irr (dD w lo p p₀) (dD w lo p′ p₀) δ) }

offFᵒ : OffF raiseFᵒ
offFᵒ w lo v c₀ p₀ δ c p ne = cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (bD-off (dD w lo p p₀) δ ne)

RaiseCopyF : RaiseF → Set
RaiseCopyF R = ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → CopyCoh (w , v) → CopyCoh (w , raiseF R w lo v c₀ p₀ δ)

δ₁ : Inc
δ₁ c = hs hz

offF→¬raiseCopyF : ∀ R → OffF R → ¬ RaiseCopyF R
offF→¬raiseCopyF R of rc =
  no-hs (subst (λ t → hs hz ⊲[ proj₁ (raiseF R w₂ lo₂ v₂ hz q₀ δ₁ hz q₀) ] t)
               (trans (sym (rc w₂ lo₂ v₂ hz q₀ δ₁ tt copy₂ hz q₀ q₁))
                      (cong (λ X → proj₂ (proj₁ X)) (of w₂ lo₂ v₂ hz q₀ δ₁ (hs hz) q₁ (λ ()))))
               (subst (λ X → hs hz ⊲[ proj₁ X ] proj₂ X) (sym (atF R w₂ lo₂ v₂ hz q₀ δ₁)) hself))

¬raiseCopyF-ᵒ : ¬ RaiseCopyF raiseFᵒ
¬raiseCopyF-ᵒ = offF→¬raiseCopyF raiseFᵒ offFᵒ
```

## §4 升 $c_0$ 之上拷贝的更新 `raiseF⁺`: 无条件保两种相干

分量 `hs c` (证据 $p$) 的拷贝接 `bD (dD (pr p) p₀) δ`, 其中 `pr p : c ⊲ b` 是 `hs c ⊲ b` 去掉一个后继. 判定 "$c_0\equiv c$" 的是/否与证据无关, 所以拷贝与 $c$ 的槽接的是同一个东西.

```agda
pr : ∀ {w : Out} {c} → AdmE w (hs c) → AdmE w c
pr p = ⊲ᴮ-tr (hsuc hself) p

module PlusF (w : Out) (lo : LgO w) (v : Cmp w) (c₀ : HB S₀) (p₀ : AdmE w c₀) (δ : Inc) where
  tF : ∀ c → AdmE w (hs c) → HB (G₀ c)
  tF c p = bD (dD w lo (pr p) p₀) δ

  cpyF : (c : HB S₀) → AdmE w c → Wd (step (G₀ c)) → Wd (step (G₀ c))
  cpyF hz p u = u
  cpyF (hs c) p u = (proj₁ (proj₁ u) , (proj₂ (proj₁ u) ⊞ tF c p)) , proj₂ u
  cpyF (hl f) p u = u
  cpyF (hΩ κ g) p u = u

  slotF : ∀ c → AdmE w c → Wd (step (G₀ c))
  slotF c p = proj₁ (v c p) , (proj₂ (v c p) ⊞ bD (dD w lo p p₀) δ)

  rF : Cmp w
  rF c p = cpyF c p (slotF c p)

  proj₂-cpy : ∀ c p u → proj₂ (cpyF c p u) ≡ proj₂ u
  proj₂-cpy hz p u = refl
  proj₂-cpy (hs c) p u = refl
  proj₂-cpy (hl f) p u = refl
  proj₂-cpy (hΩ κ g) p u = refl

open PlusF using (rF; tF; slotF; proj₂-cpy)

ne-hs : ∀ {c : HB S₀} → ¬ (hs c ≡ c)
ne-hs e = lt→≢ <s₀ (sym e)

<ᴮ-hs : ∀ {c c₀ : HB S₀} → hs c <ᴮ c₀ → ¬ (c₀ ≡ c)
<ᴮ-hs {c} lt refl = irr (wf _) (<ᴮ-tr <s₀ lt)

atF⁺ : ∀ w lo v c₀ p₀ δ → rF w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ c₀)
atF⁺ w lo v hz p₀ δ = cong (λ t → proj₁ (v hz p₀) , (proj₂ (v hz p₀) ⊞ t)) (bD-diag w lo p₀ δ)
atF⁺ w lo v (hs c) p₀ δ =
  cong₂ (λ t t′ → (proj₁ (proj₁ (v (hs c) p₀)) , (proj₂ (proj₁ (v (hs c) p₀)) ⊞ t)) , (proj₂ (v (hs c) p₀) ⊞ t′))
        (bD-off (dD w lo (pr p₀) p₀) δ ne-hs) (bD-diag w lo p₀ δ)
atF⁺ w lo v (hl f) p₀ δ = cong (λ t → proj₁ (v (hl f) p₀) , (proj₂ (v (hl f) p₀) ⊞ t)) (bD-diag w lo p₀ δ)
atF⁺ w lo v (hΩ κ g) p₀ δ = cong (λ t → proj₁ (v (hΩ κ g) p₀) , (proj₂ (v (hΩ κ g) p₀) ⊞ t)) (bD-diag w lo p₀ δ)

belowF⁺ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → rF w lo v c₀ p₀ δ c p ≡ v c p
belowF⁺ w lo v c₀ p₀ δ hz p lt = cong (λ t → proj₁ (v hz p) , (proj₂ (v hz p) ⊞ t)) (bD-off (dD w lo p p₀) δ (lt-ne lt))
belowF⁺ w lo v c₀ p₀ δ (hs c) p lt =
  cong₂ (λ t t′ → (proj₁ (proj₁ (v (hs c) p)) , (proj₂ (proj₁ (v (hs c) p)) ⊞ t)) , (proj₂ (v (hs c) p) ⊞ t′))
        (bD-off (dD w lo (pr p) p₀) δ (<ᴮ-hs lt)) (bD-off (dD w lo p p₀) δ (lt-ne lt))
belowF⁺ w lo v c₀ p₀ δ (hl f) p lt = cong (λ t → proj₁ (v (hl f) p) , (proj₂ (v (hl f) p) ⊞ t)) (bD-off (dD w lo p p₀) δ (lt-ne lt))
belowF⁺ w lo v c₀ p₀ δ (hΩ κ g) p lt = cong (λ t → proj₁ (v (hΩ κ g) p) , (proj₂ (v (hΩ κ g) p) ⊞ t)) (bD-off (dD w lo p p₀) δ (lt-ne lt))

monoF-c : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → _≤w_ (step (G₀ c)) (v c p) (rF w lo v c₀ p₀ δ c p)
monoF-c w lo v c₀ p₀ δ hz p = ≤w-rf (G₀ hz) , ⊞-fst (proj₂ (v hz p)) (bD (dD w lo p p₀) δ)
monoF-c w lo v c₀ p₀ δ (hs c) p =
  (≤w-rf (G₀ c) , ⊞-fst (proj₂ (proj₁ (v (hs c) p))) (tF w lo v c₀ p₀ δ c p)) , ⊞-fst (proj₂ (v (hs c) p)) (bD (dD w lo p p₀) δ)
monoF-c w lo v c₀ p₀ δ (hl f) p = ≤w-rf (G₀ (hl f)) , ⊞-fst (proj₂ (v (hl f) p)) (bD (dD w lo p p₀) δ)
monoF-c w lo v c₀ p₀ δ (hΩ κ g) p = ≤w-rf (G₀ (hΩ κ g)) , ⊞-fst (proj₂ (v (hΩ κ g) p)) (bD (dD w lo p p₀) δ)

legalF-c : ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → ∀ c (p : AdmE w c) → LgW (step (G₀ c)) (v c p) → LgW (step (G₀ c)) (rF w lo v c₀ p₀ δ c p)
legalF-c w lo v c₀ p₀ δ l hz p lw = proj₁ lw , Lg-⊞ (proj₂ (v hz p)) (bD (dD w lo p p₀) δ) (proj₂ lw) (Lg-bD (dD w lo p p₀) δ l)
legalF-c w lo v c₀ p₀ δ l (hs c) p lw =
  (proj₁ (proj₁ lw) , Lg-⊞ (proj₂ (proj₁ (v (hs c) p))) (tF w lo v c₀ p₀ δ c p) (proj₂ (proj₁ lw)) (Lg-bD (dD w lo (pr p) p₀) δ l)) ,
  Lg-⊞ (proj₂ (v (hs c) p)) (bD (dD w lo p p₀) δ) (proj₂ lw) (Lg-bD (dD w lo p p₀) δ l)
legalF-c w lo v c₀ p₀ δ l (hl f) p lw = proj₁ lw , Lg-⊞ (proj₂ (v (hl f) p)) (bD (dD w lo p p₀) δ) (proj₂ lw) (Lg-bD (dD w lo p p₀) δ l)
legalF-c w lo v c₀ p₀ δ l (hΩ κ g) p lw = proj₁ lw , Lg-⊞ (proj₂ (v (hΩ κ g) p)) (bD (dD w lo p p₀) δ) (proj₂ lw) (Lg-bD (dD w lo p p₀) δ l)

cohF-c : ∀ w lo v c₀ p₀ δ → Coh≡ (w , v) → Coh≡ (w , rF w lo v c₀ p₀ δ)
cohF-c w lo v c₀ p₀ δ coh hz p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh hz p p′) (bD-irr (dD w lo p p₀) (dD w lo p′ p₀) δ)
cohF-c w lo v c₀ p₀ δ coh (hs c) p p′ =
  h (coh (hs c) p p′) (bD-irr (dD w lo (pr p) p₀) (dD w lo (pr p′) p₀) δ) (bD-irr (dD w lo p p₀) (dD w lo p′ p₀) δ)
  where
  h : ∀ {X X′ t t′ u u′} → X ≡ X′ → t ≡ t′ → u ≡ u′ →
      _≡_ {A = Wd (step (G₀ (hs c)))} ((proj₁ (proj₁ X) , (proj₂ (proj₁ X) ⊞ t)) , (proj₂ X ⊞ u))
                                     ((proj₁ (proj₁ X′) , (proj₂ (proj₁ X′) ⊞ t′)) , (proj₂ X′ ⊞ u′))
  h refl refl refl = refl
cohF-c w lo v c₀ p₀ δ coh (hl f) p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh (hl f) p p′) (bD-irr (dD w lo p p₀) (dD w lo p′ p₀) δ)
cohF-c w lo v c₀ p₀ δ coh (hΩ κ g) p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh (hΩ κ g) p p′) (bD-irr (dD w lo p p₀) (dD w lo p′ p₀) δ)

raiseF⁺ : RaiseF
raiseF⁺ = record
  { raiseF = rF
  ; atF = atF⁺
  ; belowF = belowF⁺
  ; monoF = λ w lo v c₀ p₀ δ → ≤w-rf (step S₀) , λ c p → p , monoF-c w lo v c₀ p₀ δ c p
  ; legalF = λ w lo v c₀ p₀ δ l lW → proj₁ lW , λ c p → legalF-c w lo v c₀ p₀ δ l c p (proj₂ lW c p)
  ; cohF = cohF-c }

-- 无条件保拷贝相干
copyF⁺ : RaiseCopyF raiseF⁺
copyF⁺ w lo v c₀ p₀ δ l cc c p p₁ =
  trans (cong₂ _⊞_ (cc c p p₁) (bD-irr (dD w lo (pr p₁) p₀) (dD w lo p p₀) δ))
        (sym (proj₂-cpy w lo v c₀ p₀ δ c p (slotF w lo v c₀ p₀ δ c p)))

-- 接口的回灌一步 (族增量), 带两种相干, 无条件
feedF⁺ : Feedᶠ (λ W → Coh≡ W × CopyCoh W)
feedF⁺ w lo v c₀ p₀ δ l lW (coh , cc) =
  rF w lo v c₀ p₀ δ ,
  monoF raiseF⁺ w lo v c₀ p₀ δ ,
  legalF raiseF⁺ w lo v c₀ p₀ δ l lW ,
  (cohF-c w lo v c₀ p₀ δ coh , copyF⁺ w lo v c₀ p₀ δ l cc) ,
  (p₀ , subst (λ X → (proj₂ (v c₀ p₀) ⊞ δ c₀) ⊲[ proj₁ X ] proj₂ X) (sym (atF⁺ w lo v c₀ p₀ δ)) hself)

-- raiseF⁺ 确实动了 c₀ 之上 (见证世界上 hs c₀ 的拷贝从 0 变成 1)
up-moves : proj₂ (proj₁ (rF w₂ lo₂ v₂ hz q₀ δ₁ (hs hz) q₁)) ≡ hs hz
up-moves = refl
```

## §5 单个增量写法 `raise⁺ᴮ`: 四条律无条件, 保拷贝相干要 `IncIrr`

同 §4, 增量换成单个 $\delta : $ `HB (G₀ c₀)`, 用 `incD` (沿判定给的相等证明搬运). 保拷贝相干时, 拷贝与槽接的是两条相等证明搬出的 $\delta$, 要 `IncIrr`.

```agda
module Plus (w : Out) (lo : LgO w) (v : Cmp w) (c₀ : HB S₀) (p₀ : AdmE w c₀) (δ : HB (G₀ c₀)) where
  tcp : ∀ c → AdmE w (hs c) → HB (G₀ c)
  tcp c p = incD (dD w lo (pr p) p₀) δ

  cpy : (c : HB S₀) → AdmE w c → Wd (step (G₀ c)) → Wd (step (G₀ c))
  cpy hz p u = u
  cpy (hs c) p u = (proj₁ (proj₁ u) , (proj₂ (proj₁ u) ⊞ tcp c p)) , proj₂ u
  cpy (hl f) p u = u
  cpy (hΩ κ g) p u = u

  raise⁺ : Cmp w
  raise⁺ c p = cpy c p (raise₀ w lo v c₀ p₀ δ c p)

  proj₂-cpy′ : ∀ c p u → proj₂ (cpy c p u) ≡ proj₂ u
  proj₂-cpy′ hz p u = refl
  proj₂-cpy′ (hs c) p u = refl
  proj₂-cpy′ (hl f) p u = refl
  proj₂-cpy′ (hΩ κ g) p u = refl

open Plus using (raise⁺; tcp; proj₂-cpy′)

at⁺ : ∀ w lo v c₀ p₀ δ → raise⁺ w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ)
at⁺ w lo v hz p₀ δ = at₀ w lo v hz p₀ δ
at⁺ w lo v (hs c) p₀ δ =
  trans (cong (λ t → (proj₁ (proj₁ (raise₀ w lo v (hs c) p₀ δ (hs c) p₀)) , (proj₂ (proj₁ (raise₀ w lo v (hs c) p₀ δ (hs c) p₀)) ⊞ t)) ,
                     proj₂ (raise₀ w lo v (hs c) p₀ δ (hs c) p₀))
              (incD-off (dD w lo (pr p₀) p₀) δ ne-hs))
        (at₀ w lo v (hs c) p₀ δ)
at⁺ w lo v (hl f) p₀ δ = at₀ w lo v (hl f) p₀ δ
at⁺ w lo v (hΩ κ g) p₀ δ = at₀ w lo v (hΩ κ g) p₀ δ

below⁺ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → raise⁺ w lo v c₀ p₀ δ c p ≡ v c p
below⁺ w lo v c₀ p₀ δ hz p lt = below₀ w lo v c₀ p₀ δ hz p lt
below⁺ w lo v c₀ p₀ δ (hs c) p lt =
  trans (cong (λ t → (proj₁ (proj₁ (raise₀ w lo v c₀ p₀ δ (hs c) p)) , (proj₂ (proj₁ (raise₀ w lo v c₀ p₀ δ (hs c) p)) ⊞ t)) ,
                     proj₂ (raise₀ w lo v c₀ p₀ δ (hs c) p))
              (incD-off (dD w lo (pr p) p₀) δ (<ᴮ-hs lt)))
        (below₀ w lo v c₀ p₀ δ (hs c) p lt)
below⁺ w lo v c₀ p₀ δ (hl f) p lt = below₀ w lo v c₀ p₀ δ (hl f) p lt
below⁺ w lo v c₀ p₀ δ (hΩ κ g) p lt = below₀ w lo v c₀ p₀ δ (hΩ κ g) p lt

mono-c : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → _≤w_ (step (G₀ c)) (v c p) (raise⁺ w lo v c₀ p₀ δ c p)
mono-c w lo v c₀ p₀ δ hz p = ≤w-rf (G₀ hz) , ⊞-fst (proj₂ (v hz p)) (incD (dD w lo p p₀) δ)
mono-c w lo v c₀ p₀ δ (hs c) p =
  (≤w-rf (G₀ c) , ⊞-fst (proj₂ (proj₁ (v (hs c) p))) (tcp w lo v c₀ p₀ δ c p)) , ⊞-fst (proj₂ (v (hs c) p)) (incD (dD w lo p p₀) δ)
mono-c w lo v c₀ p₀ δ (hl f) p = ≤w-rf (G₀ (hl f)) , ⊞-fst (proj₂ (v (hl f) p)) (incD (dD w lo p p₀) δ)
mono-c w lo v c₀ p₀ δ (hΩ κ g) p = ≤w-rf (G₀ (hΩ κ g)) , ⊞-fst (proj₂ (v (hΩ κ g) p)) (incD (dD w lo p p₀) δ)

lg-c : ∀ w lo v c₀ p₀ δ → LgB δ → ∀ c (p : AdmE w c) → LgW (step (G₀ c)) (v c p) → LgW (step (G₀ c)) (raise⁺ w lo v c₀ p₀ δ c p)
lg-c w lo v c₀ p₀ δ l hz p lw = proj₁ lw , Lg-⊞ (proj₂ (v hz p)) (incD (dD w lo p p₀) δ) (proj₂ lw) (Lg-incD (dD w lo p p₀) δ l)
lg-c w lo v c₀ p₀ δ l (hs c) p lw =
  (proj₁ (proj₁ lw) , Lg-⊞ (proj₂ (proj₁ (v (hs c) p))) (tcp w lo v c₀ p₀ δ c p) (proj₂ (proj₁ lw)) (Lg-incD (dD w lo (pr p) p₀) δ l)) ,
  Lg-⊞ (proj₂ (v (hs c) p)) (incD (dD w lo p p₀) δ) (proj₂ lw) (Lg-incD (dD w lo p p₀) δ l)
lg-c w lo v c₀ p₀ δ l (hl f) p lw = proj₁ lw , Lg-⊞ (proj₂ (v (hl f) p)) (incD (dD w lo p p₀) δ) (proj₂ lw) (Lg-incD (dD w lo p p₀) δ l)
lg-c w lo v c₀ p₀ δ l (hΩ κ g) p lw = proj₁ lw , Lg-⊞ (proj₂ (v (hΩ κ g) p)) (incD (dD w lo p p₀) δ) (proj₂ lw) (Lg-incD (dD w lo p p₀) δ l)

raise⁺ᴮ : RaiseB
raise⁺ᴮ = record
  { raiseB = raise⁺
  ; at = at⁺
  ; below = below⁺
  ; mono = λ w lo v c₀ p₀ δ l → ≤w-rf (step S₀) , (λ c p → p , mono-c w lo v c₀ p₀ δ c p)
  ; legal = λ w lo v c₀ p₀ δ l lW → proj₁ lW , (λ c p → lg-c w lo v c₀ p₀ δ l c p (proj₂ lW c p)) }

-- 保拷贝相干: 条件 IncIrr
irr→raiseCopy⁺ : IncIrr → RaiseCopy raise⁺ᴮ
irr→raiseCopy⁺ ir w lo v c₀ p₀ δ l cc c p p₁ =
  trans (cong₂ _⊞_ (cc c p p₁) (ir w lo p₀ (pr p₁) p δ))
        (sym (proj₂-cpy′ w lo v c₀ p₀ δ c p (raise₀ w lo v c₀ p₀ δ c p)))

-- 见证世界上无条件: 读回值 1 在拷贝之下有界
feed⁺-inst : proj₂ (proj₁ (raise⁺ w₂ lo₂ v₂ hz q₀ (hs hz) (hs hz) q₁)) ≡ hz ⊞ hs hz
feed⁺-inst = refl
```

## §6 结论 (按档)

- **[定理]** `¬feedKeep` (一般形, 两个实例 `¬feedKeep-copy`, `¬feedKeep-both`): 保拷贝相干的回灌必须改 `hs c₀` 的分量的旧种类部分.
- **[定理]** `slotOnly→¬raiseCopy`, `¬raiseCopy-raise₀`, `¬raiseCopy-raiseᴮ`: 只改槽的更新 (含接口已有的两个) 不保 `CopyCoh`. `offF→¬raiseCopyF`, `¬raiseCopyF-ᵒ`: 只升 $c_0$ 本身的族增量更新同样.
- **[定理]** `raiseFᵒ`, `offFᵒ`: 满足 `OffF` 的 `RaiseF` 存在, 无条件保 `Coh≡` (前提实例).
- **[定理]** `raiseF⁺`, `copyF⁺`, `feedF⁺`: 升 $c_0$ 之上拷贝的族增量更新存在, 无条件保 `Coh≡` 与 `CopyCoh`, 给出接口的 `Feedᶠ (Coh≡ ∧ CopyCoh)`. 所以被否定的律可满足, 否定只落在 "只升 $c_0$" 上.
- **[定理, 条件]** `raise⁺ᴮ : RaiseB` 无条件; `irr→raiseCopy⁺ : IncIrr → RaiseCopy raise⁺ᴮ`. 单个增量写法下, 升拷贝也要 [LocUipNegLoop](LocUipNegLoop.lagda.md) 的 `LoopFix` (`irr⇔fix`).
- **[判断]** `CopyCoh` 是回灌要的相干 (理由见文件头); 本篇只对 `hs` 这一步陈述, 极限分量里的拷贝 (`Lev (up (hl f))` 的第 $n$ 个分量) 也要同样处理, 未写.
