# 最高层含与站层号同形的层, 否定一路 (四): 对构造一路实例的检查

> 不含记号. 入口 [NegLamIso](NegLamIso.lagda.md). 只读导入构造一路的 [LamIsoPsi](LamIsoPsi.lagda.md), [LamIsoL](LamIsoL.lagda.md) (23:02 版, 不改), 与本路的 [NegLamIsoPre](NegLamIsoPre.lagda.md), [NegLamIsoAcc](NegLamIsoAcc.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> 构造一路的实例: `L 0 = 0`, `L 1 = 1`, `L (2+n)` 的顶是第 $2+n$ 站左分量的新种类, 第 $c$ 支是 $\Psi_n$ (前缀 `L (1+n)`, 提供者是第 $2+n$ 站的分量); $\Lambda_L=\mathrm{hl}\,L$, $\Lambda'=\Lambda_L\boxplus\Lambda_F$; `prtL : ∀ n → Prt SLs (L n) (st n)`; 头 $n$ 的级层 `L n`, 读回 `readS (toS (prtL n)) idE`.
>
> **结果 (定理).**
>
> 1. **$\Lambda_L$ 里没有站的头 (§1, `L-no-head`, `ΛL-no-head`).** 一切 `L n` 的 $\Omega$-结点的种类都是站里的旧种类 (`Est m` 的像经 `subst` 与复合), 不是任何站的头 `νS m`. 证明对 $\Psi$ 的递归: 每个新结点的种类来自 "好" 的嵌入 (`Good`: 像里没有头), `subst` 与复合保持好.
> 2. **站的头只在前缀之后出现 (§2, `heads-prefixed`).** $\Lambda'$ 里 (任一世界) 外层是某站的头的第一位置, 字面上都是 $\Lambda_L\boxplus b'$, $b'\lhd\Lambda_F$. **`Sg-gone`**: 对一切 $m$, 一切世界, 站层 $S_{m+1}$ 不是 $\Lambda'$ 的第一位置. 所以 `LeanLvTmS` 的级层 $S_1$ 在 $\Lambda'$ 上不能再用 (构造一路的计划也没有用它: 头 0, 1 用 `L 0`, `L 1`, 头 $n\ge2$ 用 `L n`).
> 3. **规范读法下的自己的级层都在 $\Lambda_L$ 里 (§3, `own-in-ΛL`).** $x\lhd\Lambda'$ 且 `ofL x ≈ st n` ⟹ $x\lhd\Lambda_L$. (由 `NegLamIsoAcc.prefix-reads`: 带前缀 $\Lambda_L$ 的层, 前缀读成 `ll _`, 不是站层号.)
>
> **只否定什么.** 不否定构造一路的任何东西; 都是对实例的形状定理 (一条刻画, 一条 "不再是第一位置"). `Sg-gone` 只说旧的站层不在 $\Lambda'$ 的第一位置里, 不说站的头的回灌是否触发 (头的结点仍在 $\Lambda_F$ 那一段里, 带前缀).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbSt using (FS; SLs; νS; ΛF; Λs) renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Emb; j; cv)
open import OCF.Lean.LeanLvEmb using (stepE; supE; _∘E_; botE)
open import OCF.Lean.LamIsoPsi SLs
open import OCF.Lean.LamIsoL using (Est; Gt; Et; Sr; g₀; L; ΛL; Λ′; tw-eq)
open import OCF.Lean.NegLeanLvPre using (ofL; _≈_; ≈-≡; st-shape; Sg)
open import OCF.Lean.NegLamIsoPre using (HasP; here; inS; inL; inΩ; has⊲)
open import OCF.Lean.NegLamIsoAcc using (⊞-inv; New; prefix-reads; up-nn)
```

## §1 $\Lambda_L$ 里没有站的头

```agda
Head : K X → Set
Head (inj₁ (_ , inj₂ _)) = ⊤
Head (inj₁ (_ , inj₁ _)) = ⊥
Head (inj₂ _) = ⊥

Good : ∀ {S} → Emb S X → Set
Good E = ∀ κ → ¬ Head (j E κ)

good-∘ : ∀ {S₁ S₂} (F : Emb S₂ X) (G : Emb S₁ S₂) → Good F → Good (F ∘E G)
good-∘ F G gF κ = gF (j G κ)

good-subst : ∀ {H H′ : HB SL} (e : H ≡ H′) (E₀ : Emb (Lv (ofHB H)) X) → Good E₀ →
  Good (subst (λ H → Emb (Lv (ofHB H)) X) e E₀)
good-subst refl E₀ g = g

good-Est : ∀ m → Good (Est m)
good-Est m κ ()

good-bot : Good (botE {X})
good-bot (() , _)

good-Gt : ∀ n → Good (Gt n)
good-Gt n = good-subst (tw-eq n) (Est (suc (suc n))) (good-Est (suc (suc n)))

good-Et : ∀ n → Good (Et n)
good-Et n = good-∘ (Gt n) (lft lz (g₀ n)) (good-Gt n)

good-Sr : ∀ n c → Good (Sr n c)
good-Sr n c = good-∘ (Gt n) (rgt lz (g₀ n) (hs c)) (good-Gt n)

module _ {m A k} (Q : Src (suc m) A k) (gQ : ∀ y → Good (Q y)) (y : HB (Lv k)) where
  good-Qt : Good (Qt Q y)
  good-Qt = good-subst (eqH m (Zf A k y)) (Q y) (gQ y)

  good-Pv : Good (Pv Q y)
  good-Pv = good-∘ (Qt Q y) (lft (ofHB (Zf A k y)) (Gb Q y)) good-Qt

  good-Qn : ∀ e → Good (Qn Q y e)
  good-Qn e = good-∘ (Qt Q y) (rgt (ofHB (Zf A k y)) (Gb Q y) (hs e)) good-Qt

Ψ-head : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) → Good E₀ → (∀ y → Good (Q y)) →
  ∀ y → HasP Head (Ψ m b Q E₀ y) → HasP Head b
Ψ-head m b Q E₀ gE gQ hz h = h
Ψ-head m b Q E₀ gE gQ (hl f) (inL n h) = Ψ-head m b Q E₀ gE gQ (f n) h
Ψ-head m b Q E₀ gE gQ (hΩ κ g) (here p) with gE κ p
... | ()
Ψ-head m b Q E₀ gE gQ (hΩ κ g) (inΩ e h) = Ψ-head m b Q E₀ gE gQ (g (cv E₀ e)) h
Ψ-head zero b Q E₀ gE gQ (hs y) (inS h) = Ψ-head zero b Q E₀ gE gQ y h
Ψ-head (suc m) b Q E₀ gE gQ (hs y) (here p) with good-Pv Q gQ y (inj₂ tt) p
... | ()
Ψ-head (suc m) b Q E₀ gE gQ (hs y) (inΩ e h) =
  Ψ-head (suc m) b Q E₀ gE gQ y
    (Ψ-head m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) (good-∘ (Pv Q y) stepE (good-Pv Q gQ y)) (good-Qn Q gQ y) _ h)

L-no-head : ∀ n → ¬ HasP Head (L n)
L-no-head zero ()
L-no-head (suc zero) (inS ())
L-no-head (suc (suc n)) (here p) with good-Et n (inj₂ tt) p
... | ()
L-no-head (suc (suc n)) (inΩ c h) =
  L-no-head (suc n) (Ψ-head n (L (suc n)) (Sr n) botE good-bot (good-Sr n) _ h)

ΛL-no-head : ¬ HasP Head ΛL
ΛL-no-head (inL n h) = L-no-head n h
```

## §2 站的头只在前缀之后

`BD x y`: 沿底坐标从 $x$ 下降到 $y$. `a ⊞ b` 沿底坐标下降到 $a$.

```agda
module _ {S : KS} where
  data BD : HB S → HB S → Set where
    bz : ∀ {x} → BD x x
    bs : ∀ {x y} → BD x y → BD (hs x) y
    bl : ∀ {f y} → BD (f 0) y → BD (hl f) y
    bΩ : ∀ {κ g y} → BD (g (bot S κ)) y → BD (hΩ κ g) y

  ⊞-BD : ∀ a b → BD (a ⊞ b) a
  ⊞-BD a hz = bz
  ⊞-BD a (hs b) = bs (⊞-BD a b)
  ⊞-BD a (hl f) = bl (⊞-BD a (f 0))
  ⊞-BD a (hΩ κ g) = bΩ (⊞-BD a (g (bot S κ)))

Sg-BD : ∀ m {y} → BD (Sg m) y → (y ≡ hz) ⊎ Σ ℕ (λ k → y ≡ Sg k)
Sg-BD zero bz = inj₂ (zero , refl)
Sg-BD zero (bs bz) = inj₁ refl
Sg-BD (suc m) bz = inj₂ (suc m , refl)
Sg-BD (suc m) (bΩ d) = Sg-BD m d

hl-not-Sg : ∀ {f : ℕ → HB X} k → ¬ (hl f ≡ Sg k)
hl-not-Sg zero ()
hl-not-Sg (suc k) ()

prefixed : ∀ {x} → BD x ΛL → ∀ m → ¬ (x ≡ Sg m)
prefixed d m refl with Sg-BD m d
... | inj₁ ()
... | inj₂ (k , e) = hl-not-Sg k e

heads-prefixed : ∀ {w x} → x ⊲[ w ] Λ′ → HasP Head x → Σ (HB X) (λ b′ → (x ≡ ΛL ⊞ b′) × (b′ ⊲[ w ] ΛF))
heads-prefixed {x = x} p h with ⊞-inv ΛL ΛF p
... | inj₁ q = ⊥-elim′ (ΛL-no-head (has⊲ Head h q))
  where
  ⊥-elim′ : ∀ {A : Set} → ⊥ → A
  ⊥-elim′ ()
... | inj₂ r = r

Sg-head : ∀ m → HasP Head (Sg (suc m))
Sg-head m = here tt

Sg-gone : ∀ m {w} → ¬ (Sg (suc m) ⊲[ w ] Λ′)
Sg-gone m p with heads-prefixed p (Sg-head m)
... | b′ , e , _ = prefixed (subst (λ t → BD t ΛL) (sym e) (⊞-BD ΛL b′)) (suc m) refl
```

## §3 规范读法下的自己的级层都在 $\Lambda_L$ 里

```agda
ll-not-st : ∀ (f : ℕ → LH) j → ¬ (ll f ≈ stL j)
ll-not-st f zero ()
ll-not-st f (suc zero) ()
ll-not-st f (suc (suc i)) p with ≈-≡ _ p (proj₁ (proj₂ (st-shape i)))
... | ()

ΛF-nn : ∀ {w b′} → b′ ⊲[ w ] ΛF → ¬ HasP New b′
ΛF-nn q h = up-nn Λs (has⊲ New h q)

own-in-ΛL : ∀ {w x} n → x ⊲[ w ] Λ′ → ofL x ≈ stL n → x ⊲[ w ] ΛL
own-in-ΛL n p o with ⊞-inv ΛL ΛF p
... | inj₁ q = q
... | inj₂ (b′ , refl , q) with prefix-reads ΛL b′ n (ΛF-nn q) o
...   | j′ , r = ⊥-elim′ (ll-not-st _ j′ r)
  where
  ⊥-elim′ : ∀ {A : Set} → ⊥ → A
  ⊥-elim′ ()
```

**前提实例.** `heads-prefixed` 的前提: $\Lambda'$ 的第一位置里外层是头的层, 例如 $\Lambda_L\boxplus S_1$ (`inst-head`, 对一切世界). `own-in-ΛL` 的前提: `L 0` ($\Lambda'$ 的第一位置, 规范读法是 `st 0`; `inst-own`).

```agda
inst-head : ∀ {w} → (ΛL ⊞ Sg 1 ⊲[ w ] Λ′) × HasP Head (ΛL ⊞ Sg 1)
inst-head = hlim 1 hself , here tt

inst-own : ∀ {w} → (L 0 ⊲[ w ] Λ′) × (ofL (L 0) ≈ stL 0)
inst-own = ⊲ᴮ-tr (hlim 0 hself) (⊞-fst ΛL ΛF) , tt
```

## §4 结论 (按档)

- **[定理, 对实例]** **`L-no-head`**, `ΛL-no-head` (`Ψ-head`, `Good` 一族); **`heads-prefixed`**, **`Sg-gone`** (`⊞-BD`, `Sg-BD`); **`own-in-ΛL`**.
- **[判断]** (i) 头 $n$ 的级层 `L n` 在 $\Lambda_L$ 里, 头 $n$ 的 $\Omega$-结点在 $\Lambda_L$ 之后的 $\Lambda_F$ 段里: 级层是头的字面前缀, 这是 `LvRd.ℓ⊲` 要的 (对一切世界第一位置). (ii) $\Lambda'$ 的值相对 $\Lambda_F$ 是 "前面加了 $\Lambda_L$"; 按序数加法的直觉, 若 $\Lambda_L$ 的值小于 $\Lambda_F$ 的值且后者加法不可分解, 两者的值相同 (判断, 无定理; 本路没有 `HB (step SLs)` 上的值的序). 闭项的增长要从读回来, 不从最高层的大小来.
