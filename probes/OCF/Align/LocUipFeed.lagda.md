# 只升 $c_0$ 够不够 (一): 回灌要的律, 拷贝, 一级回灌

> 不含记号. 入口 [LocUip](LocUip.lagda.md), 接口 [LocUipIf](LocUipIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **§1 回灌一步要的律 `Feed`.** 由 `HtTowerFFold.κc₁` 的形状: 读出节点种类的界, 新世界的界盖住读回值, 新世界变大且合法. 在 `Slot` 上, 节点种类是 $(c_0, \text{槽})$, 界在分量 $(c_0,p_0)$ 的槽里. 三条定理:
>
> - `feed-free : Feed (λ _ → ⊤)`: 不要相干时, `raise₀ᴮ` (只升 $c_0$) 够用, 无条件.
> - `feedᶠ : Feedᶠ Coh≡`: 族增量, 要相干, `raiseFᴮ` 够用, 无条件.
> - `irr→feed : IncIrr → Feed Coh≡`: 单个增量, 要相干, `raise₀ᴮ` 在 `IncIrr` 之下够用 (条件; `IncIrr` 由 `UIPᴸ` 推出, 见 [LocUipHed](LocUipHed.lagda.md)).
>
> 所以就 "读的那个界" 而言, 只升 $c_0$ 本身够了.
>
> **§2 $c_0$ 之上的拷贝.** `hs c₀` 的分量里装着 $c_0$ 槽种类的一份拷贝 (`CopyCoh`). 定理 `slotOnly→¬copy`: **只改槽的更新都不保拷贝相干** (对一切满足 `at` 与 `SlotOnly` 的 `RaiseB`); `raiseᴮ` 与 `raise₀ᴮ` 都只改槽 (`slotOnly-raiseᴮ`, `slotOnly-raise₀ᴮ`, `refl`). 正面: 族增量的 `raiseFCᴮ` 同时升 $c_0$ 的槽与 `hs c₀` 分量里的拷贝, 五条律加 `copyFC` (保 `CopyCoh`) 都无条件成立. 它按构造子 `hs` 匹配坐标找拷贝, 只判定 "是不是 $c_0$" (可入证据之下). 所以: **若回灌要保拷贝相干, 就必须升 $c_0$ 之上的分量** (定理: 只升槽的不行), 而 `hs` 这一步能做到 (定理). 极限坐标里的拷贝 (`hl f` 的分量是 `sup ℕ`, 每个 $n$ 一份) 没有写, 见入口的第一个障碍.
>
> **§3 一级回灌.** 读回作参数 (`R n u`: 第 $n$ 格在当前分量函数 $u$ 上读回的族增量). 链 $s_0 = 0$, $s_{n+1} = s_n \boxplus R\,n\,(v_n)$, 世界 $v_n$ = 从基世界一次升到 $s_n$ (不是逐次叠加; 这样每个 $v_n$ 的槽字面是 $b \boxplus s_n$, 极限 $b\boxplus \lim s = \lim (b\boxplus s_n)$ 是定义). 定理: 每个 $v_n$ 合法, 相干; $v_n \le v_{n+1}$, $v_n\le v_\omega$; 第 $n$ 格 $b\boxplus s_n\,c_0$ 在 $v_n$ 里有界, 它们的 ℕ-极限在 $v_\omega$ 里有界.
>
> **§4 κ₂ 处.** $c_0 = 1$ (`hs hz`): `Slot` 在坐标 $1$ 的分量是 `step (step S₀)` (`same-κ₂`, `refl`, 与 `ChainZNeg` 的 `κ₂` 所在的 `Lev (up 2)` 定义地相同), 槽种类的坐标是 `HB S₁`. 读回取含新种类节点的 `Ωtop S₀`. 定理 `κ₂-yes`: 一级回灌后的合法相干世界里, 含新种类 $\Omega$-节点的格 (`¬ NoNew`) 有界. 对照 `ChainZNeg.no-chain` (在 `dW 1` 经 `growL′` 生成的世界里, 这样的格从不有界): 两者的世界不同族, 不矛盾; 本篇说明 `SupB` + 选择性更新绕开了 `no-chain` 杀掉的那一族世界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LocUipFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <Ω₀; wf; irr; lt→≢)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCmp using (<ᴮ-tr)
open import OCF.Align.AdmWRaise using (raiseᴮ)
open import OCF.Align.AdmWCoh
  using (incD; dD; raise₀; raise₀ᴮ; fin; ω₀; wO; lo₀; v₀; lgW₀; coh≡₀; δ₃; Lg-δ₃; a₂; b₀)
  renaming (p₀ to p₃)
open import OCF.Align.DiagK3One using (NoNew)
open import OCF.Align.LocUipIf
open import OCF.Align.LocUipFam using (incF; incF-irr; incF-at; incF-off; Lg-incF; rF; raiseFᴮ)
open Slot
open RaiseIf
```

## §1 回灌一步要的律

读回值在新世界里有界, 由 `at` 律搬 `hself`.

```agda
bd-at : ∀ w (v′ : Cmp w) c₀ (p₀ : AdmE w c₀) (X : Wd (step (G₀ c₀))) → v′ c₀ p₀ ≡ X →
        Bdᴮ (c₀ , inj₂ tt) (proj₂ X) (w , v′)
bd-at w v′ c₀ p₀ X e = p₀ , subst (λ Y → proj₂ X ⊲[ proj₁ Y ] proj₂ Y) (sym e) hself

feed-free : Feed (λ _ → ⊤)
feed-free w lo v c₀ p₀ δ l lW _ =
  raise₀ w lo v c₀ p₀ δ ,
  mono raise₀ᴮ w lo v c₀ p₀ δ l , legal raise₀ᴮ w lo v c₀ p₀ δ l lW , tt ,
  bd-at w (raise₀ w lo v c₀ p₀ δ) c₀ p₀ _ (at raise₀ᴮ w lo v c₀ p₀ δ)

feedᶠ : Feedᶠ Coh≡
feedᶠ w lo v c₀ p₀ δ l lW coh =
  rF w lo v c₀ p₀ δ ,
  monoF raiseFᴮ w lo v c₀ p₀ δ , legalF raiseFᴮ w lo v c₀ p₀ δ l lW , cohF raiseFᴮ w lo v c₀ p₀ δ coh ,
  bd-at w (rF w lo v c₀ p₀ δ) c₀ p₀ _ (atF raiseFᴮ w lo v c₀ p₀ δ)

irr→feed : IncIrr → Feed Coh≡
irr→feed irr w lo v c₀ p₀ δ l lW coh =
  raise₀ w lo v c₀ p₀ δ ,
  mono raise₀ᴮ w lo v c₀ p₀ δ l , legal raise₀ᴮ w lo v c₀ p₀ δ l lW ,
  (λ c p p′ → cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (irr w lo p₀ p p′ δ)) ,
  bd-at w (raise₀ w lo v c₀ p₀ δ) c₀ p₀ _ (at raise₀ᴮ w lo v c₀ p₀ δ)
```

## §2 拷贝

**只改槽的更新不保拷贝相干.** 世界 `(wO, v₀)` (全 0, `AdmWCoh` §2) 拷贝相干 (`copy₀`, `refl`). 在 $c_0 = 3$ 升一个含新节点的 $\delta_3$; `hs 3 = 4` 可入 (`p₄`, 经外层坐标 $1$, 即 $\omega$ 的第 4 项). 更新后 $4$ 的分量里的拷贝仍是 $0$ (只改槽), $3$ 的槽是 $0\boxplus\delta_3$, 两者构造子不同.

```agda
slotOnly-raiseᴮ : SlotOnly raiseᴮ
slotOnly-raiseᴮ w lo v c₀ p₀ δ c p = refl

slotOnly-raise₀ᴮ : SlotOnly raise₀ᴮ
slotOnly-raise₀ᴮ w lo v c₀ p₀ δ c p = refl

copy₀ : CopyCoh (wO , v₀)
copy₀ c₀ p₀ p₁ = refl

p₄ : AdmE wO (fin 4)
p₄ = hLim {c = asuc azero} (C.suc C.self) (hlim 4 hself)

slot≢ : ¬ (_≡_ {A = HB (G₀ (fin 3))} hz (hz ⊞ δ₃))
slot≢ ()

slotOnly→¬copy : ∀ (R : RaiseB) → SlotOnly R → ¬ RaiseCopy R
slotOnly→¬copy R so rc = slot≢
  (trans (sym (cong proj₂ (so wO lo₀ v₀ (fin 3) p₃ δ₃ (fin 4) p₄)))
         (trans (rc wO lo₀ v₀ (fin 3) p₃ δ₃ Lg-δ₃ copy₀ (fin 3) p₃ p₄)
                (cong proj₂ (at R wO lo₀ v₀ (fin 3) p₃ δ₃))))

¬copy-raiseᴮ : ¬ RaiseCopy raiseᴮ
¬copy-raiseᴮ = slotOnly→¬copy raiseᴮ slotOnly-raiseᴮ

¬copy-raise₀ᴮ : ¬ RaiseCopy raise₀ᴮ
¬copy-raise₀ᴮ = slotOnly→¬copy raise₀ᴮ slotOnly-raise₀ᴮ
```

**同时升拷贝的族更新 `raiseFCᴮ`.** 分量 $(c,p)$: 槽照 `rF`; 若 $c$ 的构造子是 `hs`, $c = \mathrm{hs}\,c'$, 则 $c'$ 也可入 (证据 `pr p`), 分量的旧种类部分 `Wd (G₀ (hs c′)) = Wd (G₀ c′) × HB (G₀ c′)` 的第二个分量 (拷贝) 在 "$c'$ 是 $c_0$" 时接 $\delta\,c'$.

```agda
pr : ∀ {w : Out} {c : HB S₀} → AdmE w (hs c) → AdmE w c
pr p = ⊲ᴮ-tr (hsuc hself) p

inner : ∀ w → LgO w → (c₀ : HB S₀) → AdmE w c₀ → Inc → ∀ c → AdmE w c → Wd (G₀ c) → Wd (G₀ c)
inner w lo c₀ p₀ δ hz p u = u
inner w lo c₀ p₀ δ (hs c) p (u , s) = u , (s ⊞ incF (dD w lo (pr p) p₀) δ)
inner w lo c₀ p₀ δ (hl f) p u = u
inner w lo c₀ p₀ δ (hΩ κ g) p u = u

inner-off : ∀ w lo c₀ p₀ δ c (p : AdmE w c) u → (∀ c′ → c ≡ hs c′ → ¬ (c₀ ≡ c′)) → inner w lo c₀ p₀ δ c p u ≡ u
inner-off w lo c₀ p₀ δ hz p u h = refl
inner-off w lo c₀ p₀ δ (hs c) p (u , s) h = cong (λ t → u , (s ⊞ t)) (incF-off (dD w lo (pr p) p₀) δ (h c refl))
inner-off w lo c₀ p₀ δ (hl f) p u h = refl
inner-off w lo c₀ p₀ δ (hΩ κ g) p u h = refl

inner-irr : ∀ w lo c₀ p₀ δ c (p p′ : AdmE w c) u → inner w lo c₀ p₀ δ c p u ≡ inner w lo c₀ p₀ δ c p′ u
inner-irr w lo c₀ p₀ δ hz p p′ u = refl
inner-irr w lo c₀ p₀ δ (hs c) p p′ (u , s) =
  cong (λ t → u , (s ⊞ t)) (incF-irr (dD w lo (pr p) p₀) (dD w lo (pr p′) p₀) δ)
inner-irr w lo c₀ p₀ δ (hl f) p p′ u = refl
inner-irr w lo c₀ p₀ δ (hΩ κ g) p p′ u = refl

inner-≤ : ∀ w lo c₀ p₀ δ c (p : AdmE w c) u → _≤w_ (G₀ c) u (inner w lo c₀ p₀ δ c p u)
inner-≤ w lo c₀ p₀ δ hz p u = ≤w-rf (G₀ hz)
inner-≤ w lo c₀ p₀ δ (hs c) p (u , s) = ≤w-rf (G₀ c) , ⊞-fst s (incF (dD w lo (pr p) p₀) δ)
inner-≤ w lo c₀ p₀ δ (hl f) p u = ≤w-rf (G₀ (hl f))
inner-≤ w lo c₀ p₀ δ (hΩ κ g) p u = ≤w-rf (G₀ (hΩ κ g))

inner-lg : ∀ w lo c₀ p₀ δ → LgB (δ c₀) → ∀ c (p : AdmE w c) u → LgW (G₀ c) u → LgW (G₀ c) (inner w lo c₀ p₀ δ c p u)
inner-lg w lo c₀ p₀ δ l hz p u lu = lu
inner-lg w lo c₀ p₀ δ l (hs c) p (u , s) (lu , ls) = lu , Lg-⊞ s (incF (dD w lo (pr p) p₀) δ) ls (Lg-incF (dD w lo (pr p) p₀) δ l)
inner-lg w lo c₀ p₀ δ l (hl f) p u lu = lu
inner-lg w lo c₀ p₀ δ l (hΩ κ g) p u lu = lu

rFC : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → Inc → Cmp w
rFC w lo v c₀ p₀ δ c p = inner w lo c₀ p₀ δ c p (proj₁ (v c p)) , (proj₂ (v c p) ⊞ incF (dD w lo p p₀) δ)

-- c₀ 不是 hs c′ (c′ ≡ c₀): 否则 c′ ≡ hs c′
not-hs-self : ∀ {c₀ : HB S₀} c′ → c₀ ≡ hs c′ → ¬ (c₀ ≡ c′)
not-hs-self c′ e₁ e₂ = lt→≢ (<s₀ {b = c′}) (trans (sym e₂) e₁)

atFC : ∀ w lo v c₀ p₀ δ → rFC w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ c₀)
atFC w lo v c₀ p₀ δ =
  cong₂ _,_ (inner-off w lo c₀ p₀ δ c₀ p₀ (proj₁ (v c₀ p₀)) not-hs-self)
            (cong (λ t → proj₂ (v c₀ p₀) ⊞ t) (incF-at (dD w lo p₀ p₀) δ))

belowFC : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → rFC w lo v c₀ p₀ δ c p ≡ v c p
belowFC w lo v c₀ p₀ δ c p lt =
  cong₂ _,_ (inner-off w lo c₀ p₀ δ c p (proj₁ (v c p)) h)
            (cong (λ t → proj₂ (v c p) ⊞ t) (incF-off (dD w lo p p₀) δ (λ { refl → irr (wf _) lt })))
  where
  h : ∀ c′ → c ≡ hs c′ → ¬ (c₀ ≡ c′)
  h c′ refl refl = irr (wf _) (<ᴮ-tr (<s₀ {b = c₀}) lt)

monoFC : ∀ w lo v c₀ p₀ δ → (w , v) ≤ᴮ (w , rFC w lo v c₀ p₀ δ)
monoFC w lo v c₀ p₀ δ =
  ≤w-rf (step S₀) ,
  λ c p → p , (inner-≤ w lo c₀ p₀ δ c p (proj₁ (v c p)) , ⊞-fst (proj₂ (v c p)) (incF (dD w lo p p₀) δ))

legalFC : ∀ w lo v c₀ p₀ δ → LgB (δ c₀) → LgWᴮ (w , v) → LgWᴮ (w , rFC w lo v c₀ p₀ δ)
legalFC w lo v c₀ p₀ δ l lW =
  proj₁ lW ,
  λ c p → inner-lg w lo c₀ p₀ δ l c p (proj₁ (v c p)) (proj₁ (proj₂ lW c p)) ,
          Lg-⊞ (proj₂ (v c p)) (incF (dD w lo p p₀) δ) (proj₂ (proj₂ lW c p)) (Lg-incF (dD w lo p p₀) δ l)

cohFC : ∀ w lo v c₀ p₀ δ → Coh≡ (w , v) → Coh≡ (w , rFC w lo v c₀ p₀ δ)
cohFC w lo v c₀ p₀ δ coh c p p′ =
  cong₂ _,_ (trans (cong (inner w lo c₀ p₀ δ c p) (cong proj₁ (coh c p p′))) (inner-irr w lo c₀ p₀ δ c p p′ (proj₁ (v c p′))))
            (cong₂ _⊞_ (cong proj₂ (coh c p p′)) (incF-irr (dD w lo p p₀) (dD w lo p′ p₀) δ))

raiseFCᴮ : RaiseF
raiseFCᴮ = record { raiseF = rFC ; atF = atFC ; belowF = belowFC ; monoF = monoFC ; legalF = legalFC ; cohF = cohFC }

-- 保拷贝相干 (不要 Coh≡)
copyFC : ∀ w lo v c₀ p₀ δ → CopyCoh (w , v) → CopyCoh (w , rFC w lo v c₀ p₀ δ)
copyFC w lo v c₀ p₀ δ cc d q₀ q₁ =
  cong₂ _⊞_ (cc d q₀ q₁) (incF-irr (dD w lo (pr q₁) p₀) (dD w lo q₀ p₀) δ)
```

## §3 一级回灌

```agda
module Chain (w : Out) (lo : LgO w) (v : Cmp w) (c₀ : HB S₀) (p₀ : AdmE w c₀)
             (R : ℕ → Cmp w → Inc) (lR : ∀ n u → LgB (R n u c₀)) where
  s  : ℕ → Inc
  vs : ℕ → Cmp w
  s zero c = hz
  s (suc n) c = s n c ⊞ R n (vs n) c
  vs n = rF w lo v c₀ p₀ (s n)

  sω : Inc
  sω c = hl (λ n → s n c)

  vω : Cmp w
  vω = rF w lo v c₀ p₀ sω

  lg-s : ∀ n → LgB (s n c₀)
  lg-s zero = tt
  lg-s (suc n) = Lg-⊞ (s n c₀) (R n (vs n) c₀) (lg-s n) (lR n (vs n))

  lg-sω : LgB (sω c₀)
  lg-sω = (λ n → ⊞-fst (s n c₀) (R n (vs n) c₀)) , lg-s

  -- 增量按位置变大, 世界就变大
  rF-mono : (δ δ′ : Inc) → (∀ c {u : Wd (G₀ c)} → δ c ⊲[ u ] δ′ c) → (w , rF w lo v c₀ p₀ δ) ≤ᴮ (w , rF w lo v c₀ p₀ δ′)
  rF-mono δ δ′ le = ≤w-rf (step S₀) , λ c p → p , (≤w-rf (G₀ c) , ⊞-⊲ (proj₂ (v c p)) (h (dD w lo p p₀)))
    where
    h : ∀ {c} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) {u : Wd (G₀ c)} → incF d δ ⊲[ u ] incF d δ′
    h {c} (inj₁ _) = le c
    h (inj₂ _) = hself

  legal-n : LgWᴮ (w , v) → ∀ n → LgWᴮ (w , vs n)
  legal-n lW n = legalF raiseFᴮ w lo v c₀ p₀ (s n) (lg-s n) lW

  legal-ω : LgWᴮ (w , v) → LgWᴮ (w , vω)
  legal-ω lW = legalF raiseFᴮ w lo v c₀ p₀ sω lg-sω lW

  coh-n : Coh≡ (w , v) → ∀ n → Coh≡ (w , vs n)
  coh-n coh n = cohF raiseFᴮ w lo v c₀ p₀ (s n) coh

  coh-ω : Coh≡ (w , v) → Coh≡ (w , vω)
  coh-ω coh = cohF raiseFᴮ w lo v c₀ p₀ sω coh

  step-≤ : ∀ n → (w , vs n) ≤ᴮ (w , vs (suc n))
  step-≤ n = rF-mono (s n) (s (suc n)) (λ c → ⊞-fst (s n c) (R n (vs n) c))

  lim-≤ : ∀ n → (w , vs n) ≤ᴮ (w , vω)
  lim-≤ n = rF-mono (s n) sω (λ c → hlim n hself)

  base-≤ : (w , v) ≤ᴮ (w , vs zero)
  base-≤ = monoF raiseFᴮ w lo v c₀ p₀ (s zero)

  -- 第 n 格: 读到的界接 s n
  cell : ℕ → HB (G₀ c₀)
  cell n = proj₂ (v c₀ p₀) ⊞ s n c₀

  cell-bd : ∀ n → Bdᴮ (c₀ , inj₂ tt) (cell n) (w , vs n)
  cell-bd n = bd-at w (vs n) c₀ p₀ _ (atF raiseFᴮ w lo v c₀ p₀ (s n))

  -- 链的 ℕ-极限: 定义地就是 b ⊞ sω
  cellω : HB (G₀ c₀)
  cellω = hl cell

  cellω-bd : Bdᴮ (c₀ , inj₂ tt) cellω (w , vω)
  cellω-bd = bd-at w vω c₀ p₀ _ (atF raiseFᴮ w lo v c₀ p₀ sω)

  cell-in-ω : ∀ n {u : Wd (G₀ c₀)} → cell n ⊲[ u ] cellω
  cell-in-ω n = hlim n hself
```

## §4 κ₂ 处: 含新种类节点的格有界

```agda
-- Slot 在坐标 1 的分量, 与 ChainZNeg 的 κ₂ 所在的 Lev (up 2) 定义地相同; 槽的坐标是 HB S₁
same-κ₂ : step (G₀ (hs hz)) ≡ G₀ (hs (hs hz))
same-κ₂ = refl

coord-κ₂ : E (step (G₀ (hs hz))) (inj₂ tt) ≡ HB (step S₀)
coord-κ₂ = refl

p₁ : AdmE wO (hs hz)
p₁ = hLim {c = azero} (C.suc (C.suc C.self)) (hsuc (hsuc hself))

famΩ : Inc
famΩ hz = hz
famΩ (hs hz) = Ωtop S₀
famΩ (hs (hs _)) = hz
famΩ (hs (hl _)) = hz
famΩ (hs (hΩ _ _)) = hz
famΩ (hl _) = hz
famΩ (hΩ _ _) = hz

module K₂ = Chain wO lo₀ v₀ (hs hz) p₁ (λ n u → famΩ) (λ n u → Lg-Ωtop S₀)

κ₂-yes : LgWᴮ (wO , K₂.vs 1) × Coh≡ (wO , K₂.vs 1) ×
         Bdᴮ (hs hz , inj₂ tt) (K₂.cell 1) (wO , K₂.vs 1) × ¬ NoNew (K₂.cell 1)
κ₂-yes = K₂.legal-n lgW₀ 1 , K₂.coh-n coh≡₀ 1 , K₂.cell-bd 1 , λ ()

-- 每一格都含新节点, 都有界; 极限也有界
κ₂-all : ∀ n → Bdᴮ (hs hz , inj₂ tt) (K₂.cell (suc n)) (wO , K₂.vs (suc n)) × ¬ NoNew (K₂.cell (suc n))
κ₂-all n = K₂.cell-bd (suc n) , λ ()

-- 结构上的严格增长 (子项序, 不是序数值): 第 n 格是第 n+1 格在坐标 0 处的分支
κ₂-strict : ∀ n → K₂.cell n <ᴮ K₂.cell (suc n)
κ₂-strict n = <Ω₀ hz
```
