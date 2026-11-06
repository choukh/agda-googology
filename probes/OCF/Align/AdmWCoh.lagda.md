# 可入下标上的比较式更新 (三): 坐标比较 `cmpK` 与拷贝

> 不含记号. 入口 [AdmW](AdmW.lagda.md), 接口 [AdmWIf](AdmWIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延 (§5 的 `UIPᴴ` 是前提, 不是公设; 它由函数外延推出, 见 [AdmWUip](AdmWUip.lagda.md), 条件).
>
> 第二条引理问: `SupB` 上能不能写坐标比较 `CmpK` (同一种类 $(c,k)$ 的两个坐标 $x, x'$, 各带外层证据 $(p,e)$, $(p',e')$).
>
> **需要证据相等的那一步.** `cmpK` 唯一的办法是在某一个分量里比较 (分量是种类结构 `F c` 的世界, `F c` 的 `cmpK` 只比较同一个世界里有界的坐标). $x$ 在分量 $(c,p)$ 里有界, $x'$ 在分量 $(c,p')$ 里有界. 若 $p$ 与 $p'$ 是同一个证据, 比较是定义 (`cmpK-same`). 若不是, 要把 $e'$ 搬进分量 $(c,p)$, 这一步需要两个分量之间的关系: $p\equiv p'$, 或者跨证据的相干 (`Coh≡`: 分量相等; `Coh≤`: 分量互相变大). **有相干就有 `cmpK`** (`coh≡→cmpK`, `coh≤→cmpK`, 定理). 逐分量的合法性不给相干 (这是 `AdmWNegCopy.copy→⊥` 的内容, 否定一路).
>
> **相干能不能由更新保持.** 两种更新, 两个结果:
>
> 1. **沿路径嵌入的更新 `raiseᴮ`** ([AdmWRaise](AdmWRaise.lagda.md), 诊断 §3.3 的原文: $c_0$ 之上的分量沿 `cmpB₀` 返回的路径用 `emb⊲` 嵌入): **不保相干** (`raise-splits`, 定理). 实例: 合法的相干世界, 坐标 $\omega$ 有两个证据 (经 $\Omega$-结点的坐标 $1$ 与 $2$), `cmpB₀` 对两个证据经界的单调 `mo` 返回两条不同的路径 $3\lhd\omega$ (`hlim 3 …` 与 `hlim 4 …`), 增量嵌进 `sup ℕ` 的第 3 与第 4 个分量, 两个槽 `hΩ (3, new) _` 与 `hΩ (4, old new) _` 互不为第一位置. 推论: `raiseᴮ` 不满足 `RaiseCoh Coh≤` 与 `RaiseCoh Coh≡` (`¬raise-coh≤`, `¬raise-coh≡`), 且更新后的世界里种类 $(\omega,\text{new})$ 的两个坐标不可比 (`raised-no-cmp`), 所以 `CmpK` 在这个合法世界上不成立.
> 2. **只升 $c_0$ 本身的更新 `raise₀ᴮ`** (同一坐标的一切拷贝接 $\delta$, 别的坐标不动; 判定 "是不是 $c_0$" 用 `dec₀`, 这是 `bdec` 的同形物): 四条律都是定理 (`raise₀ᴮ : RaiseB`), 外加**可入下标上的 `off` 律** (`off₀`: 可入的 $c\ne c_0$ 处不动, 对照 `DiagKLev.UpdS` 的 `offS`, 那里对裸下标推出弱判定). 它保 `Coh≡` **当且仅当**同一坐标的两条相等证明 $c_0\equiv c$ 搬出的增量相同; 在 `UIPᴴ` (高度的相等证明唯一) 之下这成立 (`uip→raise₀-coh`, 条件定理). 不加 `UIPᴴ` 我没有证出来: 两个拷贝的增量是 `subst e δ` 与 `subst e′ δ`, $e, e' : c_0\equiv c$ 来自两个证据各自的比较; 证它们相等就是 `HB S₀` 上的 UIP (有函数分支, 没有 Hedberg). 这是诊断 §3.3 义务 2 的确切位置.
>
> **合起来 (条件定理 `dirA-cond`)**: 在 `UIPᴴ` 之下, `Slot` 上有满足四条律且保 `Coh≡` 的更新, 且在 `Coh≡` 世界上有 `CmpK`. 前提可满足: `UIPᴴ` 由函数外延推出 ([AdmWUip](AdmWUip.lagda.md) 的 `fe→uip`, 条件: Funext); 相干的合法世界有实例 (`v₀`, `lgW₀`, `coh≡₀`).
>
> **范围.** `raise-splits` 只否定 `raiseᴮ` (沿 `cmpB₀` 的路径用 `emb⊲` 嵌入) 保相干; 不否定别的嵌入, 不否定 `raise₀ᴮ`. `raised-no-cmp` 只说 `CmpK` 在这一个合法世界上不成立; 它不否定 `CmpKᶜ` (相干世界上的比较, 那是定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWCoh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; wf; irr)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCmp
open import OCF.Align.AdmWRaise using (raise; raiseᴮ)
open RaiseIf
```

## §1 有相干就有 `cmpK`

```agda
module _ (S : KS) (κ : K S) (F : E S κ → KS) where
  open SupB S κ F

  cmpK-same : ∀ {c k x x′} {W : Wᴮ} (p : Bd S κ c (proj₁ W)) →
    Bd (F c) k x (proj₂ W c p) → Bd (F c) k x′ (proj₂ W c p) → LgWᴮ W →
    Prᴮ (c , k) W x′ x ⊎ Prᴮ (c , k) W x x′
  cmpK-same {c} p e e′ lW with cmpK (F c) e e′ (proj₂ lW c p)
  ... | inj₁ r = inj₁ (p , r)
  ... | inj₂ r = inj₂ (p , r)

  coh≡→cmpK : CmpKᶜ Coh≡
  coh≡→cmpK {k = c , k} {W = W} (p , e) (p′ , e′) lW coh =
    cmpK-same {W = W} p e (subst (λ X → Bd (F c) k _ X) (coh c p′ p) e′) lW

  coh≤→cmpK : CmpKᶜ Coh≤
  coh≤→cmpK {k = c , k} {W = W} (p , e) (p′ , e′) lW coh =
    cmpK-same {W = W} p e (Bd↑ (F c) (coh c p′ p) e′) lW

  coh≡→coh≤ : ∀ W → Coh≡ W → Coh≤ W
  coh≡→coh≤ W coh c p p′ = subst (λ X → _≤w_ (F c) (proj₂ W c p) X) (coh c p p′) (≤w-rf (F c))
```

## §2 一个相干的合法世界

外层世界 $(a_2, b_0)$: $a_2 = 2$ (在 `A` 里), $b_0 = \Omega$-结点, 分支 $g_0\,0 = 3$, 其余坐标 $g_0 = \omega$. 界的单调 `mo₀` 是合法性数据: 从坐标 $0$ 到坐标 $1$ 给 $3\lhd\omega$ 的路径 `hlim 3 hself`, 从坐标 $0$ 到坐标 $2$ 给 `hlim 4 (hsuc hself)` (两条都是 $3\lhd\omega$ 的路径, 只是走 $\omega$ 的不同项). 分量都取 "全 0" (`wz`), 与证据无关, 所以相干.

```agda
fin : ℕ → HB S₀
fin zero = hz
fin (suc n) = hs (fin n)

ω₀ : HB S₀
ω₀ = hl fin

lg-fin : ∀ n → LgB (fin n)
lg-fin zero = tt
lg-fin (suc n) = lg-fin n

Lg-ω₀ : LgB ω₀
Lg-ω₀ = (λ n → hsuc hself) , lg-fin

g₀ : A → HB S₀
g₀ azero = fin 3
g₀ (asuc _) = ω₀
g₀ (alim _) = ω₀

mo₀ : ∀ {w c c′} → Lg w → c ⊲ w → c′ ⊲ w → c ⊲ c′ → g₀ c ⊲[ w ] g₀ c′
mo₀ {c = azero} {c′ = azero} _ _ _ _ = hself
mo₀ {c = azero} {c′ = asuc azero} _ _ _ _ = hlim 3 hself
mo₀ {c = azero} {c′ = asuc (asuc _)} _ _ _ _ = hlim 4 (hsuc hself)
mo₀ {c = azero} {c′ = asuc (alim _)} _ _ _ _ = hlim 3 hself
mo₀ {c = azero} {c′ = alim _} _ _ _ _ = hlim 3 hself
mo₀ {c = asuc _} {c′ = azero} _ _ _ ()
mo₀ {c = asuc _} {c′ = asuc _} _ _ _ _ = hself
mo₀ {c = asuc _} {c′ = alim _} _ _ _ _ = hself
mo₀ {c = alim _} {c′ = azero} _ _ _ ()
mo₀ {c = alim _} {c′ = asuc _} _ _ _ _ = hself
mo₀ {c = alim _} {c′ = alim _} _ _ _ _ = hself

lg-g₀ : ∀ c → Lg c → LgB (g₀ c)
lg-g₀ azero _ = tt
lg-g₀ (asuc _) _ = Lg-ω₀
lg-g₀ (alim _) _ = Lg-ω₀

b₀ : HB S₀
b₀ = hΩ tt g₀

Lg-b₀ : LgB b₀
Lg-b₀ = mo₀ , lg-g₀

a₂ : A
a₂ = asuc (asuc azero)

wO : Out
wO = a₂ , b₀

lo₀ : LgO wO
lo₀ = tt , Lg-b₀

-- 全 0 的世界
wz : ∀ {S} (x : HB S) → Wd (Lev x)
wz hz = azero
wz (hs x) = wz x , hz
wz (hl f) = λ n → wz (f n)
wz (hΩ κ g) = λ c → wz (g c)

lg-wz : ∀ {S} (x : HB S) → LgW (Lev x) (wz x)
lg-wz hz = tt
lg-wz (hs x) = lg-wz x , tt
lg-wz (hl f) = λ n → lg-wz (f n)
lg-wz (hΩ κ g) = λ c → lg-wz (g c)

open Slot

v₀ : Cmp wO
v₀ c p = wz (up c) , hz

lgW₀ : LgWᴮ (wO , v₀)
lgW₀ = lo₀ , λ c p → lg-wz (up c) , tt

coh≡₀ : Coh≡ (wO , v₀)
coh≡₀ c p p′ = refl

coh≤₀ : Coh≤ (wO , v₀)
coh≤₀ = coh≡→coh≤ (step S₀) (inj₂ tt) (λ c → step (G₀ c)) (wO , v₀) coh≡₀
```

## §3 沿路径嵌入的更新拆开拷贝

$c_0 = 3$, 证据 $p_0$ 经坐标 $0$; 增量 $\delta_3$ 是 `G₀ 3 = step³ S₀` 里一个新种类的 $\Omega$-结点. 坐标 $\omega$ 的两个证据 `pω₁` (经坐标 $1$), `pω₂` (经坐标 $2$).

```agda
p₀ : AdmE wO (fin 3)
p₀ = hLim {c = azero} (C.suc (C.suc C.self)) hself

pω₁ pω₂ : AdmE wO ω₀
pω₁ = hLim {c = asuc azero} (C.suc C.self) hself
pω₂ = hLim {c = a₂} C.self hself

δ₃ : HB (G₀ (fin 3))
δ₃ = hΩ (inj₂ tt) (λ _ → hz)

Lg-δ₃ : LgB δ₃
Lg-δ₃ = (λ lw e e′ r → hself) , (λ c lc → tt)

v₁ : Cmp wO
v₁ = raise wO lo₀ v₀ (fin 3) p₀ δ₃

-- 两个槽 (定义地算出)
s₁ s₂ : HB (G₀ ω₀)
s₁ = hΩ (3 , inj₂ tt) (λ _ → hz)
s₂ = hΩ (4 , inj₁ (inj₂ tt)) (λ _ → hz)

slot₁ : proj₂ (v₁ ω₀ pω₁) ≡ s₁
slot₁ = refl

slot₂ : proj₂ (v₁ ω₀ pω₂) ≡ s₂
slot₂ = refl

no12 : ∀ {w} → ¬ (s₁ ⊲[ w ] s₂)
no12 (hLim e ())

no21 : ∀ {w} → ¬ (s₂ ⊲[ w ] s₁)
no21 (hLim e ())

raise-splits : LgWᴮ (wO , v₀) × Coh≡ (wO , v₀) × LgB δ₃ × ¬ Coh≤ (wO , v₁)
raise-splits = lgW₀ , coh≡₀ , Lg-δ₃ , λ coh → no12 (proj₂ (coh ω₀ pω₁ pω₂))

¬raise-coh≤ : ¬ RaiseCoh Coh≤ raiseᴮ
¬raise-coh≤ rc = proj₂ (proj₂ (proj₂ raise-splits)) (rc wO lo₀ v₀ (fin 3) p₀ δ₃ Lg-δ₃ coh≤₀)

¬raise-coh≡ : ¬ RaiseCoh Coh≡ raiseᴮ
¬raise-coh≡ rc = proj₂ (proj₂ (proj₂ raise-splits))
  (coh≡→coh≤ (step S₀) (inj₂ tt) (λ c → step (G₀ c)) (wO , v₁) (rc wO lo₀ v₀ (fin 3) p₀ δ₃ Lg-δ₃ coh≡₀))
```

**更新后的世界里 `cmpK` 失败.** 更新后的世界合法 (`legal`). 种类 $(\omega, \text{new})$ 的坐标 $s_1$ 在证据 `pω₁` 的分量里有界, $s_2$ 在 `pω₂` 的分量里有界; 在任何证据的分量里两者都不互为第一位置.

```agda
lgW₁ : LgWᴮ (wO , v₁)
lgW₁ = legal raiseᴮ wO lo₀ v₀ (fin 3) p₀ δ₃ Lg-δ₃ lgW₀

bd₁ : Bdᴮ (ω₀ , inj₂ tt) s₁ (wO , v₁)
bd₁ = pω₁ , hself

bd₂ : Bdᴮ (ω₀ , inj₂ tt) s₂ (wO , v₁)
bd₂ = pω₂ , hself

raised-no-cmp : ¬ (Prᴮ (ω₀ , inj₂ tt) (wO , v₁) s₂ s₁ ⊎ Prᴮ (ω₀ , inj₂ tt) (wO , v₁) s₁ s₂)
raised-no-cmp (inj₁ (p , r)) = no21 r
raised-no-cmp (inj₂ (p , r)) = no12 r

¬cmpK : ¬ CmpK
¬cmpK cK = raised-no-cmp (cK bd₁ bd₂ lgW₁)
```

## §4 只升 $c_0$ 本身的更新

```agda
incD : ∀ {c₀ c : HB S₀} → (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c) → HB (G₀ c₀) → HB (G₀ c)
incD (inj₁ e) δ = subst (λ z → HB (G₀ z)) e δ
incD (inj₂ _) δ = hz

Lg-incD : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → LgB δ → LgB (incD d δ)
Lg-incD (inj₁ refl) δ l = l
Lg-incD (inj₂ _) δ l = tt

incD-off : ∀ {c₀ c : HB S₀} (d : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → ¬ (c₀ ≡ c) → incD d δ ≡ hz
incD-off (inj₁ e) δ ne = ⊥-elim (ne e)
incD-off (inj₂ _) δ ne = refl

dD : ∀ w → LgO w → ∀ {c₀ c} → AdmE w c → AdmE w c₀ → (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)
dD w lo p p₀ = dec₀ (cmpB₀ p p₀ (proj₁ lo) (proj₂ lo))

raise₀ : ∀ w → LgO w → Cmp w → (c₀ : HB S₀) → AdmE w c₀ → HB (G₀ c₀) → Cmp w
raise₀ w lo v c₀ p₀ δ c p = proj₁ (v c p) , (proj₂ (v c p) ⊞ incD (dD w lo p p₀) δ)

at₀ : ∀ w lo v c₀ p₀ δ → raise₀ w lo v c₀ p₀ δ c₀ p₀ ≡ (proj₁ (v c₀ p₀) , proj₂ (v c₀ p₀) ⊞ δ)
at₀ w lo v c₀ p₀ δ = cong (λ t → proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ incD t δ)) (dec₀-diag p₀ (proj₁ lo) (proj₂ lo))

-- 可入下标上的 off 律
off₀ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → ¬ (c₀ ≡ c) → raise₀ w lo v c₀ p₀ δ c p ≡ v c p
off₀ w lo v c₀ p₀ δ c p ne = cong (λ t → proj₁ (v c p) , (proj₂ (v c p) ⊞ t)) (incD-off (dD w lo p p₀) δ ne)

below₀ : ∀ w lo v c₀ p₀ δ c (p : AdmE w c) → c <ᴮ c₀ → raise₀ w lo v c₀ p₀ δ c p ≡ v c p
below₀ w lo v c₀ p₀ δ c p lt = off₀ w lo v c₀ p₀ δ c p (λ { refl → irr (wf _) lt })

mono₀ : ∀ w lo v c₀ p₀ δ → LgB δ → (w , v) ≤ᴮ (w , raise₀ w lo v c₀ p₀ δ)
mono₀ w lo v c₀ p₀ δ l =
  ≤w-rf (step S₀) , λ c p → p , (≤w-rf (G₀ c) , ⊞-fst (proj₂ (v c p)) (incD (dD w lo p p₀) δ))

legal₀ : ∀ w lo v c₀ p₀ δ → LgB δ → LgWᴮ (w , v) → LgWᴮ (w , raise₀ w lo v c₀ p₀ δ)
legal₀ w lo v c₀ p₀ δ l lW =
  proj₁ lW ,
  λ c p → proj₁ (proj₂ lW c p) ,
          Lg-⊞ (proj₂ (v c p)) (incD (dD w lo p p₀) δ) (proj₂ (proj₂ lW c p)) (Lg-incD (dD w lo p p₀) δ l)

raise₀ᴮ : RaiseB
raise₀ᴮ = record { raiseB = raise₀ ; at = at₀ ; below = below₀ ; mono = mono₀ ; legal = legal₀ }
```

## §5 `UIPᴴ` 之下 `raise₀ᴮ` 保相干

```agda
UIPᴴ : Set
UIPᴴ = ∀ {x y : HB S₀} (e e′ : x ≡ y) → e ≡ e′

incD-irr : UIPᴴ → ∀ {c₀ c : HB S₀} (d d′ : (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)) δ → incD d δ ≡ incD d′ δ
incD-irr u (inj₁ e) (inj₁ e′) δ = cong (λ q → subst (λ z → HB (G₀ z)) q δ) (u e e′)
incD-irr u (inj₁ e) (inj₂ ne) δ = ⊥-elim (ne e)
incD-irr u (inj₂ ne) (inj₁ e) δ = ⊥-elim (ne e)
incD-irr u (inj₂ _) (inj₂ _) δ = refl

uip→raise₀-coh : UIPᴴ → RaiseCoh Coh≡ raise₀ᴮ
uip→raise₀-coh u w lo v c₀ p₀ δ l coh c p p′ =
  cong₂ (λ X t → proj₁ X , (proj₂ X ⊞ t)) (coh c p p′) (incD-irr u (dD w lo p p₀) (dD w lo p′ p₀) δ)

-- 合起来: UIPᴴ 之下, 有保相干的更新, 且相干世界上有坐标比较
dirA-cond : UIPᴴ → Σ RaiseB (RaiseCoh Coh≡) × CmpKᶜ Coh≡
dirA-cond u = (raise₀ᴮ , uip→raise₀-coh u) , coh≡→cmpK (step S₀) (inj₂ tt) (λ c → step (G₀ c))
```
