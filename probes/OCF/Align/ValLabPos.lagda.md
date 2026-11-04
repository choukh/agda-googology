# 值验收 (五): 类 `VA`, `VV`, 还能证的部分

> **验收文件, 读记号.** 入口 [ValLab](ValLab.lagda.md).
>
> - `VA X t`: 规则现在写的值验收: 存在带字面标签 $t$ 的 $Y$, 与 $X$ 互相 $\sqsubseteq^0$. `VV X t`: 换成值前序 $\preccurlyeq$. `va→vv`; 反过来不成立 (`suc-sep`).
> - `va-sub`: `VA X t` 推出 $X$ 的每个 $\prec$ 子树都带字面标签. 这就是 [ValLabNeg](ValLabNeg.lagda.md) 的来源.
> - `va-chain`, `vv-chain`: 对一切 `HtB`, 链行 $m$: 若 $V_{F_i}0$ 与 $Z_{a+i}$ 一致 (`VA` 要 $\cong$, `VV` 只要 $\approx^{\mathsf v}$), $Z_n$ 带 $t[n]$, 则 $V_m0$ 过验收, 参照树是 `lim Z`. **第 0 行的头在这里被吃掉**, 不用看 $t[0]$. 这是 `PxV` 的链行.
> - `vv-ω²-if`: **条件定理.** $\psi_0(\Omega_{\psi_1(2)})$ 的 $\preccurlyeq$ 验收, 条件是第 $k\ge 2$ 项的参照树存在且与位置 `blk (k-1) end` 的行同值. 第 1, 2 项无条件 (`hyp-2` 与 `head-ω²1`).
> - `suc-sep`: 最小的分离例: $X=\mathrm{suc}\,V$, $Y=\mathrm{suc}$ `Tᴸ`. $Y$ 带字面标签 $\psi_0(\Omega_{\psi_1(1)\cdot2})+1$, $X\approx^{\mathsf v}Y$, 但 $X$ 对任何读法都没有 `VA`. 这条就是 `⊑-not-suc`, 落在主线的树上.
> - `no-NF-ω·2`: $\psi_0(\Omega_{\psi_1(1)\cdot2})$ 不是 `NF₁`: 标签类 `Lq` 的出口 `labelᵠ` 要 `NF₁`, 所以它到不了 $\psi_1(1)\cdot2$ 及以上. `label-Tᴸ` 绕开它是因为只取极限, 不进折叠.
> - `rule-ctl`: `chain-rule` 不空: 在带标签的 $\psi_0(\Omega_{\psi_1(1)})$ 上它成立, $k=2$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLabPos where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅)
import OCF.Align.EBO as E
open E using (T; fsn; cof; cω; c1; sucT; pred; natT; Ωt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NFᴾ₁; n∷; nψ; Sb; sψ; sC; sΩ; sΩ²; ψ¹; Ω₁; Ωᵐ; n[])
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.ValueJudgeBase using (_≼_; ≼-refl; ≼-trans; ≼lim; ⊑→≼; ≅→≼; _≈ᵛ_) renaming (s≼s to vs≼s)
open import OCF.Align.LadderOrdBase using (HtB; View; chain)
open import OCF.Align.LadderOrdPos hiding (Sb)
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂; e²)
open import OCF.Align.LadderInfTop2 using (top)
import OCF.Align.LadderOrdMain
import OCF.Align.OrdLabChain
import OCF.Align.ValLabRow
open import OCF.Align.ValLabBase
open import OCF.Align.ValLabNeg using (z⁰; Zl; Cofs; no-any-M₂; no-any-pos; no-val-M₂; no-val-ω²-top; no-val-ω·3; no-val-ω^ω; no-val-ε₀; module G₂; module G²; module G₃; module Gω; module Gε; module V²)
open import OCF.Align.ValLabNegTop using (no-val-T⊤)
open import OCF.Align.CrossMClosed using (T⊤)
open import OCF.Align.OrdLabRead using (tω·2; tω²; module Cω; module C²; ev₀)
open import OCF.Align.OrdLabReadTop using (Tᴸ; label-Tᴸ; same-M₂; same-pos; tail-pos; pos-row; top-row; head-ω²1; tail-ω²2)
open import OCF.Align.OrdLabAccept using (ord-∞)
```

## §1 两个类

```agda
VA : Ordᶜ zero → T → Set
VA X t = Σ (Ordᶜ zero) λ Y → Lab Y t × (X ⊑⁰ Y) × (Y ⊑⁰ X)

VV : Ordᶜ zero → T → Set
VV X t = Σ (Ordᶜ zero) λ Y → Lab Y t × (X ≼ Y) × (Y ≼ X)

va→vv : ∀ {X t} → VA X t → VV X t
va→vv {X} (Y , L , a , b) = Y , L , ⊑→≼ X a , ⊑→≼ Y b

va-sub : ∀ {X c : Ordᶜ zero} {t} → VA X t → c ≺ X → Σ T (Lab c)
va-sub (Y , L , a , b) q = lab-≺ (a q) L
```

## §2 链行

```agda
module Chain (𝕊 : HtB) where
  private module R = OCF.Align.ValLabRow 𝕊
  private module C = OCF.Align.OrdLabChain 𝕊
  open HtB 𝕊 using (view; _<ᴸ_)

  private
    to-X : ∀ {X Y} (Rw : C.ChainRow X Y) n → C.ChainRow.h Rw n ⊑⁰ X
    to-X Rw n = ⊑-trans (⊑-lim n (≅→⊑ (≅-refl⁰ _))) (≅→⊑ (≅-sym (C.ChainRow.eq Rw)))

    up⊑ : ∀ {Z : ℕ → Ordᶜ zero} → (∀ n → Z n ⊑⁰ Z (suc n)) → ∀ a n → Z n ⊑⁰ Z (a + n)
    up⊑ st zero n = λ h → h
    up⊑ st (suc a) n = ⊑-trans (up⊑ st a n) (st (a + n))

    up≼ : ∀ {Z : ℕ → Ordᶜ zero} → (∀ n → Z n ≼ Z (suc n)) → ∀ a n → Z n ≼ Z (a + n)
    up≼ {Z} st zero n = ≼-refl (Z n)
    up≼ st (suc a) n = ≼-trans (up≼ st a n) (st (a + n))

  -- 带 a 个错位: F i 对应 Z (a + i)
  va-chain : ∀ {m F qf t} → view m ≡ chain F qf → cof t ≡ cω → (a : ℕ) (Z : ℕ → Ordᶜ zero) → (∀ n → Lab (Z n) (fsn t n)) → (∀ n → Z n ⊑⁰ Z (suc n)) →
             (∀ i → R.V (F i) zero ≅ Z (a + i)) → VA (R.V m zero) t
  va-chain {m} {F} {qf} {t} c ct a Z L st e = lim Z , lω ct (≅-refl⁰ _) L , sub , sup
    where
    Rw = C.chain-row {m} {F} {qf} c _ zero
    Xe : R.V m zero ≅ lim (C.ChainRow.h Rw)
    Xe = ≅-trans (≅-sym (R.V-G m zero (R.GV m zero))) (C.ChainRow.eq Rw)
    hs′ : ∀ i → C.ChainRow.h Rw (suc i) ≅ Z (a + i)
    hs′ i = ≅-trans (C.ChainRow.rest Rw i) (≅-trans (R.V-G (F i) zero (R.GV (F i) zero)) (e i))
    up′ : ∀ n → C.ChainRow.h Rw n ⊑⁰ lim Z
    up′ zero = ⊑-trans (C.ChainRow.step Rw 0) (⊑-trans (≅→⊑ (hs′ 0)) (⊑-lim (a + 0) (≅→⊑ (≅-refl⁰ _))))
    up′ (suc n) = ⊑-trans (≅→⊑ (hs′ n)) (⊑-lim (a + n) (≅→⊑ (≅-refl⁰ _)))
    sub : R.V m zero ⊑⁰ lim Z
    sub = ⊑-trans (≅→⊑ Xe) (lim-⊑ up′)
    sup : lim Z ⊑⁰ R.V m zero
    sup = lim-⊑ (λ n → ⊑-trans (up⊑ st a n) (⊑-trans (≅→⊑ (≅-sym (hs′ n))) (⊑-trans (to-X Rw (suc n)) (≅→⊑ (≅-sym (≅-trans (≅-sym (R.V-G m zero (R.GV m zero))) (≅-refl⁰ _)))))))

  vv-chain : ∀ {m F qf t} → view m ≡ chain F qf → cof t ≡ cω → (a : ℕ) (Z : ℕ → Ordᶜ zero) → (∀ n → Lab (Z n) (fsn t n)) → (∀ n → Z n ≼ Z (suc n)) →
             (∀ i → R.V (F i) zero ≈ᵛ Z (a + i)) → VV (R.V m zero) t
  vv-chain {m} {F} {qf} {t} c ct a Z L st e = lim Z , lω ct (≅-refl⁰ _) L , sub , sup
    where
    Rw = C.chain-row {m} {F} {qf} c _ zero
    Xe : R.V m zero ≅ lim (C.ChainRow.h Rw)
    Xe = ≅-trans (≅-sym (R.V-G m zero (R.GV m zero))) (C.ChainRow.eq Rw)
    h = C.ChainRow.h Rw
    hu : ∀ i → h (suc i) ≼ Z (a + i)
    hu i = ≼-trans (≅→≼ (≅-trans (C.ChainRow.rest Rw i) (R.V-G (F i) zero (R.GV (F i) zero)))) (proj₁ (e i))
    hd : ∀ i → Z (a + i) ≼ h (suc i)
    hd i = ≼-trans (proj₂ (e i)) (≅→≼ (≅-sym (≅-trans (C.ChainRow.rest Rw i) (R.V-G (F i) zero (R.GV (F i) zero)))))
    up′ : ∀ n → h n ≼ lim Z
    up′ zero = ≼-trans (⊑→≼ (h 0) (C.ChainRow.step Rw 0)) (≼lim (a + 0) (hu 0))
    up′ (suc n) = ≼lim (a + n) (hu n)
    sub : R.V m zero ≼ lim Z
    sub = ≼-trans (≅→≼ Xe) (OCF.Align.ValueJudgeBase.l≼ up′)
    sup : lim Z ≼ R.V m zero
    sup = OCF.Align.ValueJudgeBase.l≼ (λ n → ≼-trans (up≼ st a n) (≼-trans (hd n) (≼-trans (≼lim (suc n) (≼-refl _)) (≅→≼ (≅-sym Xe)))))
```

## §3 已有的两个 `VA`

与 [OrdLabReadTop](OrdLabReadTop.lagda.md) 的 `same-M₂`, `same-pos` 同内容, 写成类的成员. 这也是 `VA` 在链行以外第一个到不了的地方: 见 §5.

```agda
va-M₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → VA (forceᴺ _ (G₂.GᴺTᵠ end zero ev z)) tω·2
va-M₂ ev z = Tᴸ ev z , label-Tᴸ ev z , proj₁ (same-M₂ ev z) , proj₂ (same-M₂ ev z)

va-pos : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → VA (forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev z)) tω·2
va-pos ev z = Tᴸ ev z , label-Tᴸ ev z , proj₁ (same-pos ev z) , proj₂ (same-pos ev z)
```

## §4 分离: $\preccurlyeq$ 过, $\sqsubseteq^0$ 不过

```agda
lab-suc⁺ : ∀ {Y t} → (x : E.PT) (ys : T) → t ≡ x ∷ ys → Lab Y t → Lab (suc Y) (x ∷ sucT ys)
lab-suc⁺ x [] refl L = l1 refl (s≅ (≅-refl⁰ _)) L
lab-suc⁺ x (y ∷ ys) refl L = l1 (cof-suc y ys) (s≅ (≅-refl⁰ _)) (subst (Lab _) (sym (pred-s x y ys)) L)
  where
  cof-suc : ∀ y ys → cof (y ∷ sucT ys) ≡ c1
  cof-suc y [] = refl
  cof-suc y (w ∷ ws) = cof-suc w ws
  pred-s : ∀ x y ys → pred (x ∷ sucT (y ∷ ys)) ≡ x ∷ y ∷ ys
  pred-s x y [] = refl
  pred-s x y (w ∷ ws) = cong (x ∷_) (pred-s y w ws)

X₂ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Ordᶜ zero
X₂ ev z = forceᴺ _ (G₂.GᴺTᵠ end zero ev z)

suc-sep : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → VV (suc (X₂ ev z)) (sucT tω·2) × (∀ t → VA (suc (X₂ ev z)) t → ⊥)
suc-sep ev z = (suc (Tᴸ ev z) , lab-suc⁺ _ [] refl (label-Tᴸ ev z) , vs≼s (⊑→≼ (X₂ ev z) (proj₁ (same-M₂ ev z))) , vs≼s (⊑→≼ (Tᴸ ev z) (proj₂ (same-M₂ ev z)))) ,
               (λ t A → no-any-M₂ ev z (proj₁ (va-sub A (≺z (≅-refl⁰ _)))) (proj₂ (va-sub A (≺z (≅-refl⁰ _)))))
```

## §5 `VA` 到不了的地方, 写成类

```agda
no-VA : ∀ {X t} → (∀ {Y s} → Lab Y s → X ⊑⁰ Y → ⊥) → VA X t → ⊥
no-VA n (Y , L , a , b) = n L a

no-VA-T⊤ : ∀ t → VA T⊤ t → ⊥
no-VA-T⊤ t = no-VA no-val-T⊤

no-VA-ω² : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) t → VA (forceᴺ _ (G².GᴺTᵠ end zero ev z)) t → ⊥
no-VA-ω² ev z t = no-VA (no-val-ω²-top ev z)

no-VA-M₂ : ∀ {α} → zero <ᴵ α → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) t → VA (forceᴺ _ (G₂.GᴺTᵠ end α ev z)) t → ⊥
no-VA-M₂ q ev z t = no-VA (no-val-M₂ q ev z)

no-VA-ω·3 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) t → VA (forceᴺ _ (G₃.GᴺTᵠ end zero ev z)) t → ⊥
no-VA-ω·3 ev z t = no-VA (no-val-ω·3 ev z)

no-VA-ω^ω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) t → VA (forceᴺ _ (Gω.GᴺTᵠ end zero ev z)) t → ⊥
no-VA-ω^ω ev z t = no-VA (no-val-ω^ω ev z)

no-VA-ε₀ : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) t → VA (forceᴺ _ (Gε.GᴺTᵠ end zero ev z)) t → ⊥
no-VA-ε₀ ev z t = no-VA (no-val-ε₀ ev z)
```

## §6 $\psi_0(\Omega_{\psi_1(2)})$ 的条件定理

`top-row` 的第 $i+1$ 项是位置 `blk i end` 的行. 记号的第 $i+1$ 项是 $\psi_0(\Omega_{\psi_1(1)\cdot(i+1)})$. $i=0$ 字面一致, $i=1$ 是 `same-pos`, $i\ge2$ 是条件.

```agda
private module Ch² = Chain (HB ω²ᶜ)

vv-ω²-if : (Z : ℕ → Ordᶜ zero) → (∀ n → Lab (Z n) (fsn tω² n)) → (∀ n → Z n ≼ Z (suc n)) →
           (∀ i → V².V (low (blk i end)) zero ≈ᵛ Z (suc i)) → VV (V².V end zero) tω²
vv-ω²-if Z L st e = Ch².vv-chain {end} {λ i → low (blk i end)} {λ i → tt} refl refl 1 Z L st e

-- 条件的 i = 1 无条件: 位置 ω·2 与 Tᴸ
≈-of : ∀ {V F Y : Ordᶜ zero} → F ≅ V → F ⊑⁰ Y → Y ⊑⁰ F → V ≈ᵛ Y
≈-of {V} {F} {Y} e a b = ≼-trans (≅→≼ (≅-sym e)) (⊑→≼ F a) , ≼-trans (⊑→≼ Y b) (≅→≼ e)

hyp-2 : V².V (low (blk 1 end)) zero ≈ᵛ Tᴸ ev₀ zero
hyp-2 = ≈-of (V².Vev (low (blk 1 end)) zero ev₀ zero) (proj₁ (same-pos ev₀ zero)) (proj₂ (same-pos ev₀ zero))
```

## §7 标准形

`Sb` 不含 $\psi_1(1)+\psi_1(1)$.

```agda
no-Ωᵐψ : ∀ n {c} → Ctbl c → Ωᵐ n c ≡ ψ¹ ∷ [] → ⊥
no-Ωᵐψ zero c[] ()
no-Ωᵐψ zero (c∷ cc) ()
no-Ωᵐψ (suc n) cc ()

no-Sb-ψ¹ψ¹ : ∀ {u} → u ≡ ψ¹ ∷ ψ¹ ∷ [] → Sb u → ⊥
no-Sb-ψ¹ψ¹ e (sψ n cc) = no-Ωᵐψ n cc (cong tl′ e)
  where
  tl′ : T → T
  tl′ [] = []
  tl′ (_ ∷ r) = r
no-Sb-ψ¹ψ¹ () (sC c[])
no-Sb-ψ¹ψ¹ () (sC (c∷ cc))
no-Sb-ψ¹ψ¹ () (sΩ cc)
no-Sb-ψ¹ψ¹ () (sΩ² n cc)

no-NF-ω·2 : NF₁ tω·2 → ⊥
no-NF-ω·2 (n∷ (nψ _ _ (n∷ (nψ _ s _ _) _ _) _) _ _) = no-Sb-ψ¹ψ¹ refl s
```

## §8 正对照: `chain-rule` 不空

码 `ωᶜ` 的顶带标签 $\psi_0(\Omega_{\psi_1(1)})$. 那里 $h_1=\psi_0(\Omega_\Omega)$ 走两步到 $\omega$, $h_2=\psi_0(\Omega_{\Omega\cdot2})$ 走两步到 $h_1$.

```agda
private
  module W = OCF.Align.ValLabRow (HB ωᶜ)
  module Gωᶜ = OCF.Align.LadderOrdMain (HB ωᶜ)

tψ : T
tψ = ψᵗ [] (Ωt (ψ¹ ∷ [])) ∷ []

ctl-gen : ∀ {h : ℕ → Ordᶜ zero} → Lab (lim h) tψ → Lab (h 0) ω̂ →
          Σ (Ordᶜ zero) λ y → Σ (Ordᶜ zero) λ w → Zk 2 (h 1) w × Zk 2 (h 2) y × (y ≅ h 1)
ctl-gen {h} L l₀ = proj₁ Y₂ , proj₁ Y₁ , proj₁ (proj₂ Y₁) , proj₁ (proj₂ Y₂) , chain-rule L l₀ (proj₂ (proj₂ Y₁)) (proj₁ (proj₂ Y₁)) (proj₁ (proj₂ Y₂))
  where
  Ls = proj₂ (lim-lab L (≅-refl⁰ _))
  Y₁ = Zl 2 (fsn tψ 1) (Ls 1) (refl , (refl , tt))
  Y₂ = Zl 2 (fsn tψ 2) (Ls 2) (refl , (refl , tt))

-- 行是变量: 检查器不展开证书
Ctl : ∀ {X Y} → Cω.ChainRow X Y → Set
Ctl Rw = Σ (Ordᶜ zero) λ y → Σ (Ordᶜ zero) λ w → Zk 2 (Cω.ChainRow.h Rw 1) w × Zk 2 (Cω.ChainRow.h Rw 2) y × (y ≅ Cω.ChainRow.h Rw 1)

ctl-row : ∀ {X Y} (Rw : Cω.ChainRow X Y) → Lab X tψ → Ctl Rw
ctl-row Rw L = ctl-gen {Cω.ChainRow.h Rw} (Lab-≅ (≅-sym (Cω.ChainRow.eq Rw)) L) (W.ω-of Rw)

Rω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Cω.ChainRow (forceᴺ _ (Gωᶜ.GᴺTᵠ end zero ev z)) (λ i → forceᴺ _ (Gωᶜ.GᴺTᵠ (low (blk i end)) zero ev z))
Rω ev z = Cω.chain-row {end} {λ i → low (blk i end)} {λ i → tt} refl ev z

rule-ctl : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Ctl (Rω ev z)
rule-ctl ev z = ctl-row (Rω ev z) (ord-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< {α = zero} z≅ ev z)
```
