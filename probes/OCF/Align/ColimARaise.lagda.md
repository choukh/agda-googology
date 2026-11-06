# 只对可入层号给分量 (二): 可入层号上的更新, 无限层号, 一步回灌

> 不含记号. 入口 [ColimA](ColimA.lagda.md), 接口 [ColimAIf](ColimAIf.lagda.md) §5. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP (§3 的 `UIPS` 只作前提, 条件).
>
> - **`raiseA′`** (定理): 对一切 `S`, 一切合法外层世界 $w$ 与合法外层界 $X$, 有满足接口 `RaiseA′` 七条律的更新 (`baseA`, `atA`, `offA`, `monoA`, `legalA`, `cohA`). 判定 "$y_0 \equiv y$" 用 `bdec` (两个层号都带 $X$ 之下的证据). 增量是可入层号上的族: 判为相等时取族在 $(y, p)$ 处的值, **不沿相等证明搬运**, 所以 `atA` 不要对角引理, `cohA` 不要 UIP (LocUip 的族增量写法; 对照 `AdmWCoh.uip→raise₀-coh`, `LocUipFam.cohF′`).
> - **无限层号** (定理): `raiseA′` 对一切层号都给出更新, 包括 `ColimW` 的第一个障碍 `up ω₀`. 特别地 `raiseA′-wα : ∀ α → RaiseA′ x₀ (wα α)`: `ColimWNeg.raiseA→WLPO` 的前提族 (换成本接口) 是定理.
> - **单个增量** (§3, 条件定理): 增量是单个高度时, 判为相等要沿判定给的相等证明搬运 (`inc1`); 在 `UIPS` (层号高度的相等证明唯一) 之下有 `RaiseA1` (`uip→raiseA1`). 这是 `AdmWCoh` 的墙的同一位置; 族增量绕开了它.
> - **一步回灌** (§4, 定理): 最小世界在层号 `finH 1` 上接族 `topF` (每个后继层号放 "它之上的第一个 Ω", `topA`): 合法, 变大, 相干; `κ₂` 处含新种类节点的格有界 (`cell₂`, `root₂`), 拷贝 `κ₂′` 处同一个格也有界 (`cell₂′`, 由 `atA` 直接得到, 不经相干). 在第一个无限层号 `up ω₀` 上同样 (`cellω`, `cellω′`, `rootω`).
> - **ω 条** (§5, 定理): 在 `up ω₀` 上接 $n$ 份 `topA` 得 $W_n$, 接它们的 ℕ-极限得 $W_\omega$; 都合法且相干, $W_n \le W_{n+1}$, $W_n \le W_\omega$; 第 $n$ 格在 $W_n$ 里有界, 极限格在 $W_\omega$ 里有界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimARaise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.StallDxBdec using (bdec)
open import OCF.Align.ColimWIf using (AdmL; S₁; finH; x₀; ω₀)
open import OCF.Align.ColimWRaise using (RootNew)
open import OCF.Align.ColimWNeg using (wω; Lg-wω; wα; Lg-wα)
open import OCF.Align.ColimAIf
open import OCF.Align.ColimAKS
```

## §1 判定与族增量

```agda
hs-inj : ∀ {S} {a b : HB S} → hs a ≡ hs b → a ≡ b
hs-inj refl = refl

module _ {S : KS} (X : HB S) (w : Wd S) (lw : LgW S w) (lX : LgB X) where
  open Adm X w

  -- 同一合法界 X 之下, 同一合法外层世界 w 里, 两个可入层号的相等可判定
  decA : ∀ {y y₀} → AdmL X w y → AdmL X w y₀ → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)
  decA p p₀ with bdec p p₀ lw lX
  ... | inj₁ e = inj₁ (sym (hs-inj e))
  ... | inj₂ ne = inj₂ (λ e → ne (cong hs (sym e)))
```

族增量: 判为相等时取族在 $(y, p)$ 处的值, 不用相等证明.

```agda
  incA : ∀ {y₀ y} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → IncA → AdmL X w y → HB (LevA w y)
  incA {y = y} (inj₁ _) δ p = δ y p
  incA (inj₂ _) δ p = hz

  at-d : ∀ {y₀ y} (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ (p : AdmL X w y) → y₀ ≡ y → incA d δ p ≡ δ y p
  at-d (inj₁ _) δ p e = refl
  at-d (inj₂ ne) δ p e = ⊥-elim (ne e)

  off-d : ∀ {y₀ y} (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ (p : AdmL X w y) → ¬ (y₀ ≡ y) → incA d δ p ≡ hz
  off-d (inj₁ e) δ p ne = ⊥-elim (ne e)
  off-d (inj₂ _) δ p ne = refl

  Lg-incA : ∀ {y₀ y} (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ (p : AdmL X w y) → (∀ q → LgB (δ y₀ q)) → LgB (incA d δ p)
  Lg-incA (inj₁ refl) δ p l = l p
  Lg-incA (inj₂ _) δ p l = tt

  incA-irr : ∀ {y₀ y} (d d′ : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ (p p′ : AdmL X w y) → CohI δ → incA d δ p ≡ incA d′ δ p′
  incA-irr (inj₁ _) (inj₁ _) δ p p′ cI = cI _ p p′
  incA-irr (inj₁ e) (inj₂ ne) δ p p′ cI = ⊥-elim (ne e)
  incA-irr (inj₂ ne) (inj₁ e) δ p p′ cI = ⊥-elim (ne e)
  incA-irr (inj₂ _) (inj₂ _) δ p p′ cI = refl
```

## §2 更新与七条律

```agda
  rA : GWA X w → (y₀ : HB S) → AdmL X w y₀ → IncA → GWA X w
  rA W y₀ p₀ δ = proj₁ W , λ y p → proj₂ W y p ⊞ incA (decA p p₀) δ p

  raiseA′ : RaiseA′
  raiseA′ = record
    { raiseA = rA
    ; baseA = λ W y₀ p₀ δ → refl
    ; atA = λ W y₀ p₀ δ y p e → cong (λ t → proj₂ W y p ⊞ t) (at-d (decA p p₀) δ p e)
    ; offA = λ W y₀ p₀ δ y p ne → cong (λ t → proj₂ W y p ⊞ t) (off-d (decA p p₀) δ p ne)
    ; monoA = λ W y₀ p₀ δ → C.self , (λ y p → ⊞-fst (proj₂ W y p) (incA (decA p p₀) δ p))
    ; legalA = λ W y₀ p₀ δ lδ lW →
        proj₁ lW , (λ y p → Lg-⊞ (proj₂ W y p) (incA (decA p p₀) δ p) (proj₂ lW y p) (Lg-incA (decA p p₀) δ p lδ))
    ; cohA = λ W y₀ p₀ δ cI coh y p p′ →
        cong₂ _⊞_ (coh y p p′) (incA-irr (decA p p₀) (decA p′ p₀) δ p p′ cI) }
```

**无限层号, 与 `ColimWNeg` 的前提族.** `raiseA′` 对一切层号都给出更新; 对 `ColimWNeg` 的那一族外层世界 `wα α` (每个都合法), 一致地构造出来.

```agda
raiseA′-wα : ∀ α → Adm.RaiseA′ x₀ (wα α)
raiseA′-wα α = raiseA′ x₀ (wα α) (Lg-wα α) (Lg-Ωtop S₀)
```

`ColimWNeg.SepA.look` 读 `proj₂ (Fα α) (up ω₀)`: 世界在**裸**层号 `up ω₀` 处的值. 在本接口里这个读法写不出: `GWA` 在 `up ω₀` 处的分量要一个证据 `AdmL x₀ (wα α) (up ω₀)`, 而它只在 $\alpha$ 某处为真时有 (`ColimWNeg.adm₁ α k e`, 要 $k$ 与 `α k ≡ true`). 有了证据, "是不是 $y_0$" 由 `decA` 直接判定, 不需要更新. 这就是诊断 §2.2 的 W⁺ 在 `GW` 上的形式. 判断 (元层): 若有对本接口的 `FE₀ → (∀ α → RaiseA′ x₀ (wα α)) → WLPO`, 与 `raiseA′-wα` 合起来就得 `FE₀ → WLPO`, 而有外延而 WLPO 不成立的模型 (实现性) 里它不成立; 所以 `raiseA-sep` 那样的论证对本接口不存在.

## §3 单个增量: 要沿相等证明搬运 (条件定理)

```agda
module _ {S : KS} (X : HB S) (w : Wd S) (lw : LgW S w) (lX : LgB X) where
  open Adm X w

  UIPS : Set
  UIPS = ∀ {a b : HB S} (e e′ : a ≡ b) → e ≡ e′

  inc1 : ∀ {y₀ y} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → HB (LevA w y₀) → HB (LevA w y)
  inc1 (inj₁ e) δ = subst (λ (z : HB S) → HB (LevA w z)) e δ
  inc1 (inj₂ _) δ = hz

  inc1-off : ∀ {y₀ y} (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ → ¬ (y₀ ≡ y) → inc1 d δ ≡ hz
  inc1-off (inj₁ e) δ ne = ⊥-elim (ne e)
  inc1-off (inj₂ _) δ ne = refl

  inc1-at : UIPS → ∀ {y₀} (d : (y₀ ≡ y₀) ⊎ ¬ (y₀ ≡ y₀)) δ → inc1 d δ ≡ δ
  inc1-at u (inj₁ e) δ = cong (λ q → subst (λ (z : HB S) → HB (LevA w z)) q δ) (u e refl)
  inc1-at u (inj₂ ne) δ = ⊥-elim (ne refl)

  inc1-irr : UIPS → ∀ {y₀ y} (d d′ : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ → inc1 d δ ≡ inc1 d′ δ
  inc1-irr u (inj₁ e) (inj₁ e′) δ = cong (λ q → subst (λ (z : HB S) → HB (LevA w z)) q δ) (u e e′)
  inc1-irr u (inj₁ e) (inj₂ ne) δ = ⊥-elim (ne e)
  inc1-irr u (inj₂ ne) (inj₁ e) δ = ⊥-elim (ne e)
  inc1-irr u (inj₂ _) (inj₂ _) δ = refl

  r1 : GWA X w → (y₀ : HB S) → AdmL X w y₀ → HB (LevA w y₀) → GWA X w
  r1 W y₀ p₀ δ = proj₁ W , λ y p → proj₂ W y p ⊞ inc1 (decA X w lw lX p p₀) δ

  uip→raiseA1 : UIPS → RaiseA1
  uip→raiseA1 u = record
    { raise1 = r1
    ; at1 = λ W y₀ p₀ δ → cong (λ t → proj₂ W y₀ p₀ ⊞ t) (inc1-at u (decA X w lw lX p₀ p₀) δ)
    ; off1 = λ W y₀ p₀ δ y p ne → cong (λ t → proj₂ W y p ⊞ t) (inc1-off (decA X w lw lX p p₀) δ ne)
    ; coh1 = λ W y₀ p₀ δ coh y p p′ →
        cong₂ _⊞_ (coh y p p′) (inc1-irr u (decA X w lw lX p p₀) (decA X w lw lX p′ p₀) δ) }
```

前提可满足: `S = S₀` 时 `UIPS` 就是 `AdmWCoh.UIPᴴ`, 由函数外延推出 (`AdmWUip.fe→uip`, 条件: Funext); 一般的 `S` 我没有给实例 (判断: 有 K 的模型里成立). 不加 `UIPS`, `at1` 要 `decA p₀ p₀` 给出的相等证明 $e : y_0\equiv y_0$ 搬运恒等, `coh1` 要两条证明搬出同一个值; 这与 `LocUipNegLoop` 的 `LoopFix`, `IncIrr` 同类 (那里证明了等价于外延性内容), 这里没有证, 也没有否定.

## §4 一步回灌: `κ₂` 与 `κω` 处含新节点的格有界

`topA y`: 后继层号 `hs y′` 放 `Ωtop (LevA w y′)` (它之上的第一个 Ω, 含新种类的节点); ℕ-极限层号放第 1 项的 `topA` 经 `ι 1`; 其余放 $0$. 族 `topF` 与证据无关, 所以相干 (`refl`).

```agda
module _ {S : KS} (w : Wd S) where
  topA : (y : HB S) → HB (LevA w y)
  topA hz = hz
  topA (hs y) = Ωtop (LevA w y)
  topA (hl f) = ι {I = ℕ} {F = λ n → LevA w (f n)} 1 (topA (f 1))
  topA (hΩ κ g) = hz

  Lg-topA : ∀ y → LgB (topA y)
  Lg-topA hz = tt
  Lg-topA (hs y) = Lg-Ωtop (LevA w y)
  Lg-topA (hl f) = Lg-ι {I = ℕ} {F = λ n → LevA w (f n)} 1 (topA (f 1)) (Lg-topA (f 1))
  Lg-topA (hΩ κ g) = tt

module _ {S : KS} {X : HB S} {w : Wd S} where
  topF : Adm.IncA X w
  topF y p = topA w y

  cohTop : Adm.CohI X w topF
  cohTop y p p′ = refl
```

最小实例: $X = x_0$, 外层世界 `wω`. 层号 `finH 1` 经 `κ₂` 的证据 `p₂`; `κ₂′` 的证据 `p₂′`; `up ω₀` 经 `κω` 的证据 `pω`, `κω′` 的证据 `pω′`.

```agda
open Adm x₀ wω

Rω : RaiseA′
Rω = raiseA′ x₀ wω Lg-wω (Lg-Ωtop S₀)

open RaiseA′ Rω

Wz : GWA x₀ wω
Wz = W₀ x₀ wω

lgWz : LgGA Wz
lgWz = lgW₀ x₀ wω

cohWz : CohA Wz
cohWz = cohW₀ x₀ wω

p₂ p₂′ : AdmL x₀ wω (finH 1)
p₂ = hLim {c = finH 2} e₂ hself
p₂′ = hLim {c = finH 3} e₃ (hsuc hself)

pω′ : AdmL x₀ wω (up ω₀)
pω′ = hLim {c = hs (hs ω₀)} eω′ (hsuc hself)

-- 一步: 在层号 finH 1 上接 topF
W₁ : GWA x₀ wω
W₁ = raiseA Wz (finH 1) p₂ topF

lgW₁ : LgGA W₁
lgW₁ = legalA Wz (finH 1) p₂ topF (λ q → Lg-topA {S₁} wω (finH 1)) lgWz

grow₁ : Wz ≤GA W₁
grow₁ = monoA Wz (finH 1) p₂ topF

cohW₁ : CohA W₁
cohW₁ = cohA Wz (finH 1) p₂ topF cohTop cohWz

cell₂ : Bd L₀ κ₂ (hz ⊞ topA {S₁} wω (finH 1)) (restrA x₀ hself W₁)
cell₂ = subst (λ t → _⊲[_]_ {LevA wω (finH 1)} (hz ⊞ topA {S₁} wω (finH 1)) (restrA (finH 1) (dnS p₂) W₁) t)
              (sym (atA Wz (finH 1) p₂ topF (finH 1) p₂ refl)) hself

-- 拷贝: 由 atA 对一切证据直接得到, 不经相干
cell₂′ : Bd L₀ κ₂′ (hz ⊞ topA {S₁} wω (finH 1)) (restrA x₀ hself W₁)
cell₂′ = subst (λ t → _⊲[_]_ {LevA wω (finH 1)} (hz ⊞ topA {S₁} wω (finH 1)) (restrA (finH 1) (dnS p₂′) W₁) t)
               (sym (atA Wz (finH 1) p₂ topF (finH 1) p₂′ refl)) hself

root₂ : RootNew {S₀} (hz ⊞ topA {S₁} wω (finH 1))
root₂ = tt
```

**第一个无限层号.** 在 `up ω₀` 上接 `topF`. 格的根是 ℕ-极限级第 1 个分量里新种类的 Ω-节点 (`rootω`, `refl`).

```agda
Wω₁ : GWA x₀ wω
Wω₁ = raiseA Wz (up ω₀) pω topF

lgWω₁ : LgGA Wω₁
lgWω₁ = legalA Wz (up ω₀) pω topF (λ q → Lg-topA {S₁} wω (up ω₀)) lgWz

growω₁ : Wz ≤GA Wω₁
growω₁ = monoA Wz (up ω₀) pω topF

cohWω₁ : CohA Wω₁
cohWω₁ = cohA Wz (up ω₀) pω topF cohTop cohWz

cellω : Bd L₀ κω (hz ⊞ topA {S₁} wω (up ω₀)) (restrA x₀ hself Wω₁)
cellω = subst (λ t → _⊲[_]_ {LevA wω (up ω₀)} (hz ⊞ topA {S₁} wω (up ω₀)) (restrA (up ω₀) (dnS pω) Wω₁) t)
              (sym (atA Wz (up ω₀) pω topF (up ω₀) pω refl)) hself

cellω′ : Bd L₀ κω′ (hz ⊞ topA {S₁} wω (up ω₀)) (restrA x₀ hself Wω₁)
cellω′ = subst (λ t → _⊲[_]_ {LevA wω (up ω₀)} (hz ⊞ topA {S₁} wω (up ω₀)) (restrA (up ω₀) (dnS pω′) Wω₁) t)
               (sym (atA Wz (up ω₀) pω topF (up ω₀) pω′ refl)) hself

rootω : hz ⊞ topA {S₁} wω (up ω₀) ≡ hΩ (1 , inj₂ tt) (λ c → hz ⊞ ι {I = ℕ} {F = λ n → LevA wω (up (finH n))} 1 (up c))
rootω = refl

-- 别的层号不动 (层号 finH 1 在 Wω₁ 里仍是 0)
offω : proj₂ Wω₁ (finH 1) p₂ ≡ hz
offω = offA Wz (up ω₀) pω topF (finH 1) p₂ (λ ())
```

## §5 ω 条

$s_n\,y$ 是 $n$ 份 `topA y` 的接长, $s_\omega\,y$ 是它们的 ℕ-极限. $W_n$, $W_\omega$ 都是从 $W_0$ 一次接上 (不是逐次叠加), 所以格字面是 $0 \boxplus s_n$, 极限格 $0\boxplus s_\omega = \lim (0 \boxplus s_n)$ 是定义.

```agda
module _ {S : KS} (w : Wd S) where
  sA : ℕ → (y : HB S) → HB (LevA w y)
  sA zero y = hz
  sA (suc n) y = sA n y ⊞ topA w y

  sω : (y : HB S) → HB (LevA w y)
  sω y = hl (λ n → sA n y)

  Lg-sA : ∀ n y → LgB (sA n y)
  Lg-sA zero y = tt
  Lg-sA (suc n) y = Lg-⊞ (sA n y) (topA w y) (Lg-sA n y) (Lg-topA w y)

  Lg-sω : ∀ y → LgB (sω y)
  Lg-sω y = (λ n → ⊞-fst (sA n y) (topA w y)) , (λ n → Lg-sA n y)

Wn : ℕ → GWA x₀ wω
Wn n = raiseA Wz (up ω₀) pω (λ y p → sA {S₁} wω n y)

Wωω : GWA x₀ wω
Wωω = raiseA Wz (up ω₀) pω (λ y p → sω {S₁} wω y)

lgWn : ∀ n → LgGA (Wn n)
lgWn n = legalA Wz (up ω₀) pω (λ y p → sA {S₁} wω n y) (λ q → Lg-sA {S₁} wω n (up ω₀)) lgWz

lgWωω : LgGA Wωω
lgWωω = legalA Wz (up ω₀) pω (λ y p → sω {S₁} wω y) (λ q → Lg-sω {S₁} wω (up ω₀)) lgWz

cohWn : ∀ n → CohA (Wn n)
cohWn n = cohA Wz (up ω₀) pω (λ y p → sA {S₁} wω n y) (λ y p p′ → refl) cohWz

cohWωω : CohA Wωω
cohWωω = cohA Wz (up ω₀) pω (λ y p → sω {S₁} wω y) (λ y p p′ → refl) cohWz
```

**单调.** 同一个判定 $d$ 下比较两个增量: 判为相等时 $0\boxplus s_n \lhd 0 \boxplus s_{n+1}$ (`⊞-fst`), $0\boxplus s_n \lhd 0\boxplus s_\omega$ (`hlim n`); 判为不等时都是 $0$.

```agda
module _ {y : HB S₁} {u : Wd (LevA wω y)} where
  step-d : (d : (up ω₀ ≡ y) ⊎ ¬ (up ω₀ ≡ y)) (p : AdmL x₀ wω y) (n : ℕ) →
    _⊲[_]_ {LevA wω y} (hz ⊞ incA x₀ wω Lg-wω (Lg-Ωtop S₀) d (λ y′ q → sA {S₁} wω n y′) p) u
                       (hz ⊞ incA x₀ wω Lg-wω (Lg-Ωtop S₀) d (λ y′ q → sA {S₁} wω (suc n) y′) p)
  step-d (inj₁ _) p n = ⊞-⊲ hz (⊞-fst (sA {S₁} wω n y) (topA {S₁} wω y))
  step-d (inj₂ _) p n = hself

  lim-d : (d : (up ω₀ ≡ y) ⊎ ¬ (up ω₀ ≡ y)) (p : AdmL x₀ wω y) (n : ℕ) →
    _⊲[_]_ {LevA wω y} (hz ⊞ incA x₀ wω Lg-wω (Lg-Ωtop S₀) d (λ y′ q → sA {S₁} wω n y′) p) u
                       (hz ⊞ incA x₀ wω Lg-wω (Lg-Ωtop S₀) d (λ y′ q → sω {S₁} wω y′) p)
  lim-d (inj₁ _) p n = hlim n hself
  lim-d (inj₂ _) p n = hself

Wn≤ : ∀ n → Wn n ≤GA Wn (suc n)
Wn≤ n = C.self , λ y p → step-d (decA x₀ wω Lg-wω (Lg-Ωtop S₀) p pω) p n

Wn≤ω : ∀ n → Wn n ≤GA Wωω
Wn≤ω n = C.self , λ y p → lim-d (decA x₀ wω Lg-wω (Lg-Ωtop S₀) p pω) p n
```

**格.** 第 $n$ 格 $0\boxplus s_n$ 在 $W_n$ 里 `κω` 处有界; 极限格在 $W_\omega$ 里有界; 拷贝 `κω′` 处同样.

```agda
celln : ∀ n → Bd L₀ κω (hz ⊞ sA {S₁} wω n (up ω₀)) (restrA x₀ hself (Wn n))
celln n = subst (λ t → _⊲[_]_ {LevA wω (up ω₀)} (hz ⊞ sA {S₁} wω n (up ω₀)) (restrA (up ω₀) (dnS pω) (Wn n)) t)
                (sym (atA Wz (up ω₀) pω (λ y p → sA {S₁} wω n y) (up ω₀) pω refl)) hself

cellωω : Bd L₀ κω (hz ⊞ sω {S₁} wω (up ω₀)) (restrA x₀ hself Wωω)
cellωω = subst (λ t → _⊲[_]_ {LevA wω (up ω₀)} (hz ⊞ sω {S₁} wω (up ω₀)) (restrA (up ω₀) (dnS pω) Wωω) t)
               (sym (atA Wz (up ω₀) pω (λ y p → sω {S₁} wω y) (up ω₀) pω refl)) hself

cellωω′ : Bd L₀ κω′ (hz ⊞ sω {S₁} wω (up ω₀)) (restrA x₀ hself Wωω)
cellωω′ = subst (λ t → _⊲[_]_ {LevA wω (up ω₀)} (hz ⊞ sω {S₁} wω (up ω₀)) (restrA (up ω₀) (dnS pω′) Wωω) t)
                (sym (atA Wz (up ω₀) pω (λ y p → sω {S₁} wω y) (up ω₀) pω′ refl)) hself
```
