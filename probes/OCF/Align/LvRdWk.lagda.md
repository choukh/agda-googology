# 读回包 (六): W1 与 W2 合并, 码的弱化, "层号由回灌给出" 的形状

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md) §7, §8. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **码的弱化** (`LvFb` 接手清单第 3 条). 外层界沿字面路径 $p : b\lhd_{[a]} b'$ 长高时, 界 $b$ 之下的码 $k$ 弱化成 $b'$ 之下的码 `wk p k = cd (pth k ⨾ p)` ([LvFbCode](LvFbCode.lagda.md) 的 `cd`, `pth`). 关键的一步是两条结构引理: 复合路径的码是把 $k$ 的码接在 $p$ 的码的末端 (`cdB-tr`, 对 $p$ 归纳), 码到路径再回到码是恒等 (`cdB-pB`, 对码归纳). 由此:
>
> - `wk-code`: `proj₁ (wk p k) ≡ graft (cdB p) (proj₁ k)` (定理);
> - `wk-tgt` (目标不变), **`wk-inj`** (单射: 接上同一前缀的两个码相等则原码相等, `graft-inj`), **`wk-≟`** (与 `code-≟` 相容: 两边判定的结果相同), `wk-tr` (对路径复合函子, `graft-assoc`). 合为接口的 `WkLaw` 的实例 `wkLaw`.
>
> 律的定义域: `wk-inj`, `wk-≟` 只比较同一个界 $b$ 之下的两个码, 弱化沿同一条字面证据 $p$; 比较的是码 (数据), 不是坐标.
>
> **外层界取部分和 (W1), 下标取码 (W2)**: `St a σ` 给出 `Stages a`: 界 $B_0=0$, $B_{s+1}=B_s\boxplus\sigma_s$; 第 $s+1$ 站的码 $\kappa_s$ = `cd (⊞-fst (B s) (σ s))`, 在新界之下, 目标是旧界 (`κ-tgt`, 定理).
>
> **形状** (接口 `LvShape`): 两个实例.
>
> - `lvShape₁`: $\sigma_s = 1$ (读法 `σ-of` 是常数). 此时 $B_s = \mathrm{fin}\,s$ (`B-fin`), 第 $s+1$ 站的码的目标就是 $\mathrm{fin}\,s$ (`lvl₁`): 有限级折叠所在的坐标. 这里 "由回灌给出" 是空的 (常数读法).
> - **`lvShapeδ`**: $\sigma_s = \sigma_0(H_s)$, $H_s$ 是第 $s+1$ 级级顶的回灌输出降到 `Ht` (`LvRdFold.Hn`), $\sigma_0$ 把 `Ht` 的高度经第 1 级的翻译读成第 2 层的树, 在 $\Lambda = 2$ 里求值到第 1 层, 读成 `H₀` (与 `dω` 同法, 低一级). 读法与站号无关. 于是第 $s+1$ 站的层号 (码的目标) 是 $\sigma_0(H_0)\boxplus\cdots\boxplus\sigma_0(H_{s-1})$ (`lvlδ`): **层号由此前各站回灌的输出给出, 不是外部的 ℕ**.
>
> **范围 (坦白).** `lvShapeδ` 给出的是码与界, 没有在这些坐标上做折叠: 坐标 $B_s$ 是一般的可数高度 (可含 $\Omega$-结点), 在它上面折叠要坐标 $B_s$ 处的读回包 (`Lev`-式的种类结构对一般高度的读回), 本路只写了有限, $\omega$, $\omega+1$ (`LvRdPkg`). 这是第一个障碍. 闭项 `T∞ω1` 的折叠用的是 `lvShape₁` 那一列坐标 (有限) 加 $\omega$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdWk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; H₀; D; n0; ≤rf; accᴸ)
open import OCF.Align.HtTowerFRead using (rd; Lg-rd)
open import OCF.Align.HtTowerFClosed using (module At; W₁; one)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.AdmWCoh using (fin)
open import OCF.Align.LvFbCode
  using (RA; aH; aP; aL; RB; bH; bP; bL; bΩ; vA; vB; tA; pA; pB; cdA; cdB; cd; cd-tgt; Code; tgt; pth; code-≟; vB-prop; tlB; _⊲₀[_]_)
open import OCF.Align.LvRdIf using (WkLaw; Stages; LvShape)
open import OCF.Align.LvRdPkg using (tr; RdF)
open import OCF.Align.LvRdFold using (lgly; one⊲ly; Hn)
```

## §1 码与路径的两条结构引理

```agda
graft : RB → RB → RB
graft bH r = r
graft (bP r₀) r = bP (graft r₀ r)
graft (bL n r₀) r = bL n (graft r₀ r)
graft (bΩ ra r₀) r = bΩ ra (graft r₀ r)

graft-inj : ∀ r₀ {r r′} → graft r₀ r ≡ graft r₀ r′ → r ≡ r′
graft-inj bH e = e
graft-inj (bP r₀) e = graft-inj r₀ (cong tlB e)
graft-inj (bL n r₀) e = graft-inj r₀ (cong tlB e)
graft-inj (bΩ ra r₀) e = graft-inj r₀ (cong tlB e)

graft-assoc : ∀ r₀ r₁ r → graft (graft r₀ r₁) r ≡ graft r₀ (graft r₁ r)
graft-assoc bH r₁ r = refl
graft-assoc (bP r₀) r₁ r = cong bP (graft-assoc r₀ r₁ r)
graft-assoc (bL n r₀) r₁ r = cong (bL n) (graft-assoc r₀ r₁ r)
graft-assoc (bΩ ra r₀) r₁ r = cong (bΩ ra) (graft-assoc r₀ r₁ r)

-- 复合路径的码: 后一段的码末端接上前一段的码
cdB-tr : ∀ {a c b b′} (q : c ⊲₀[ a ] b) (p : b ⊲₀[ a ] b′) → cdB (⊲ᴮ-tr q p) ≡ graft (cdB p) (cdB q)
cdB-tr q hself = refl
cdB-tr q (hsuc p) = cong bP (cdB-tr q p)
cdB-tr q (hlim n p) = cong (bL n) (cdB-tr q p)
cdB-tr q (hLim e p) = cong (bΩ (cdA e)) (cdB-tr q p)

-- 码 → 路径 → 码 是恒等
cdA-pA : ∀ a r (v : vA a r) → cdA (pA a r v) ≡ r
cdA-pA a aH v = refl
cdA-pA (asuc a) (aP r) v = cong aP (cdA-pA a r v)
cdA-pA azero (aP r) ()
cdA-pA (alim f) (aP r) ()
cdA-pA (alim f) (aL n r) v = cong (aL n) (cdA-pA (f n) r v)
cdA-pA azero (aL n r) ()
cdA-pA (asuc a) (aL n r) ()

cdB-pB : ∀ a b r (v : vB a b r) → cdB (pB a b r v) ≡ r
cdB-pB a b bH v = refl
cdB-pB a (hs b) (bP r) v = cong bP (cdB-pB a b r v)
cdB-pB a hz (bP r) ()
cdB-pB a (hl f) (bP r) ()
cdB-pB a (hΩ κ g) (bP r) ()
cdB-pB a (hl f) (bL n r) v = cong (bL n) (cdB-pB a (f n) r v)
cdB-pB a hz (bL n r) ()
cdB-pB a (hs b) (bL n r) ()
cdB-pB a (hΩ κ g) (bL n r) ()
cdB-pB a (hΩ κ g) (bΩ ra r) (va , v) = cong₂ bΩ (cdA-pA a ra va) (cdB-pB a (g (tA a ra va)) r v)
cdB-pB a hz (bΩ ra r) ()
cdB-pB a (hs b) (bΩ ra r) ()
cdB-pB a (hl f) (bΩ ra r) ()

code-ext : ∀ {a b} (k k′ : Code a b) → proj₁ k ≡ proj₁ k′ → k ≡ k′
code-ext {a} {b} (r , v) (r′ , v′) refl = cong (r ,_) (vB-prop a b r v v′)
```

## §2 弱化与它的律

```agda
wk : ∀ {a b b′} → b ⊲₀[ a ] b′ → Code a b → Code a b′
wk p k = cd (⊲ᴮ-tr (pth k) p)

wk-code : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k → proj₁ (wk p k) ≡ graft (cdB p) (proj₁ k)
wk-code {a} {b} p k = trans (cdB-tr (pth k) p) (cong (graft (cdB p)) (cdB-pB a b (proj₁ k) (proj₂ k)))

wk-tgt : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k → tgt (wk p k) ≡ tgt k
wk-tgt p k = cd-tgt (⊲ᴮ-tr (pth k) p)

wk-inj : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k k′ → wk p k ≡ wk p k′ → k ≡ k′
wk-inj p k k′ e = code-ext k k′ (graft-inj (cdB p) (trans (sym (wk-code p k)) (trans (cong proj₁ e) (wk-code p k′))))

open import Relation.Nullary.Decidable using (isYes)

wk-≟ : ∀ {a b b′} (p : b ⊲₀[ a ] b′) k k′ → isYes (code-≟ (wk p k) (wk p k′)) ≡ isYes (code-≟ k k′)
wk-≟ p k k′ with code-≟ k k′ | code-≟ (wk p k) (wk p k′)
... | yes e | yes _ = refl
... | yes e | no ne = ⊥-elim (ne (cong (wk p) e))
... | no ne | yes e = ⊥-elim (ne (wk-inj p k k′ e))
... | no _ | no _ = refl

wk-tr : ∀ {a b b′ b″} (p : b ⊲₀[ a ] b′) (q : b′ ⊲₀[ a ] b″) k → wk q (wk p k) ≡ wk (⊲ᴮ-tr p q) k
wk-tr p q k = code-ext (wk q (wk p k)) (wk (⊲ᴮ-tr p q) k)
  (trans (wk-code q (wk p k))
  (trans (cong (graft (cdB q)) (wk-code p k))
  (sym (trans (wk-code (⊲ᴮ-tr p q) k)
       (trans (cong (λ z → graft z (proj₁ k)) (cdB-tr p q)) (graft-assoc (cdB q) (cdB p) (proj₁ k)))))))

wkLaw : WkLaw
wkLaw = record { wk = wk ; wk-tgt = wk-tgt ; wk-inj = wk-inj ; wk-≟ = wk-≟ ; wk-tr = wk-tr }
```

## §3 外层界取部分和, 下标取码

```agda
module St (a : A) (σ : ℕ → HB S₀) (lσ : ∀ s → LgB (σ s)) where
  B : ℕ → HB S₀
  B zero = hz
  B (suc s) = B s ⊞ σ s

  κ : ∀ s → Code a (B (suc s))
  κ s = cd (⊞-fst {w = a} (B s) (σ s))

  κ-tgt : ∀ s → tgt (κ s) ≡ B s
  κ-tgt s = cd-tgt (⊞-fst {w = a} (B s) (σ s))

  stages : Stages a
  stages = record { B = B ; σ = σ ; lgσ = lσ ; B-s = λ s → refl ; κ = κ ; κ-tgt = κ-tgt }
```

## §4 形状的两个实例

```agda
-- σ ≡ 1: 层号就是有限级折叠所在的坐标
module S₁ = St azero (λ _ → hs hz) (λ _ → tt)

B-fin : ∀ s → S₁.B s ≡ fin s
B-fin zero = refl
B-fin (suc s) = cong hs (B-fin s)

lvl₁ : ∀ s → tgt (S₁.κ s) ≡ fin s
lvl₁ s = trans (S₁.κ-tgt s) (B-fin s)

lvShape₁ : LvShape azero
lvShape₁ = record { St = S₁.stages ; out = Hn ; σ-of = λ _ → hs hz ; σ-is = λ s → refl }

-- σ 由回灌输出给出: Ht 的高度经第 1 级翻译读成第 2 层的树, 在 Λ = 2 里求值到第 1 层, 读成 H₀
module Ev₁ where
  open At (ly 2) (lgly 2) (one⊲ly 1)
  ev₁ : D (ly 2) (azero , hz) → H₀
  ev₁ X = rd (tt , tt) hz (yc (Run {W = W₁} accᴸ X (z⊲ one , hself) (tt , tt) hself Act n0 Y₀) (tg ≤rf (hsuc hself) (tt , tt)))

σ₀ : Ht → HB S₀
σ₀ h = Ev₁.ev₁ (tr (RdF 1) h)

lσ₀ : ∀ h → LgB (σ₀ h)
lσ₀ h = Lg-rd (tt , tt) hz _ tt

module Sδ = St azero (λ s → σ₀ (Hn s)) (λ s → lσ₀ (Hn s))

lvShapeδ : LvShape azero
lvShapeδ = record { St = Sδ.stages ; out = Hn ; σ-of = σ₀ ; σ-is = λ s → refl }

-- 第 s+1 站的层号是此前各站回灌输出的读法的部分和
lvlδ : ∀ s → (tgt (Sδ.κ s) ≡ Sδ.B s) × (Sδ.B (suc s) ≡ Sδ.B s ⊞ σ₀ (Hn s))
lvlδ s = Sδ.κ-tgt s , refl
```
