# LeanLv (四): 形状定理 — 头 2 按自己的级; 读回产出不止一种种类; 回灌行被执行

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md). 第 4 层 (只新增定理, 不改定义). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对象是主候选 [LeanLvTmS](LeanLvTmS.lagda.md) 的 `TVs` (计划 `planS`, 读回 `RLs m`). 对照: 否定一路 `NegLeanFbInst.rdX-one-kind` (LeanFb 的头 $n\ge2$ 的读回只产出一个级 0 种类的 $\Omega$-结点).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbTm using (bkS)
import OCF.Lean.LeanFbTm
open import OCF.Lean.LeanLvIf
open import OCF.Lean.LeanLvEmb
open import OCF.Lean.LeanLvTm using (σ₂)
open import OCF.Lean.LeanLvTmS
import OCF.Lean.LeanTFold as Fold
open Tree SLs hiding (inS)
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fbS
```

## §1 每个头都有回灌; 头 $n\ge2$ 的级层是 `Sg 1`

```agda
IsL : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set
IsL (inj₁ _) = ⊤
IsL (inj₂ _) = ⊥

heads-fed : ∀ n → IsL (planS (νS n))
heads-fed zero = tt
heads-fed (suc zero) = tt
heads-fed (suc (suc m)) = tt

lv-layer : ∀ m → LvRd.ℓ (RLs m) ≡ Sg 1
lv-layer m = refl

-- 级层不是 1 (LeanFb 的头 n≥2 的级层是 hs hz)
Sg1≢1 : ¬ (Sg 1 ≡ hs hz)
Sg1≢1 ()
```

**头 2 按自己的级 (定理, `refl`).** 头 2 的回灌带的同形的层号就是它的坐标的层号 `st 2`, 嵌入是恒等, 读回的目标就是坐标的种类结构. 对 $m\ge1$ 层号仍是 `st 2`, 不是 `st (2+m)` (否定一路 `NegLeanLvBlind.no-sim`: 在基世界里是 `ΛF` 第一位置的层与 `st (3+n)` 之间没有 `Sim`).

```agda
own2-x : LvSim.x (lvSims 0) ≡ stL 2
own2-x = refl

own2-em : LvSim.em (lvSims 0) ≡ idE
own2-em = refl

own2-Q : Feed.Q (feedLs 0) ≡ Lv (stL 2)
own2-Q = refl

lvm-x : ∀ m → LvSim.x (lvSims m) ≡ stL 2
lvm-x m = refl
```

## §2 读回产出不止一种种类

级层 `Sg 1` 上, 基世界里的三份数据 (分支都取常值 $1$):

- `x₀`: 过坐标 $0$ 那一支 ($1+0$) 里的第 $0$ 层的结点 (`sL bot (hsuc hself)`);
- `x₂`: 过坐标 $0$ 那一支本身的结点 (`sL bot hself`; 这是 $\Omega_{\mathrm{Sg}\,1}$ 的主结点的形状);
- `x₀ ⨾ x₂`.

**只在 `emb2 m` 的像里** (否定一路 `NegLeanLvS.img-readS⁺`, `no-top3-RLs`: 头 3 的读回不产出 `Lv (st 3)` 里坐标为 `HB (Lv (st 2))` 的种类). 读回 (头 $2+m$, `RLs m`) 分别产出种类 `j (emb2 m) κa` 与 `j (emb2 m) κb` 的 $\Omega$-结点, $\kappa_a=$ `(inj₂ hz , inj₂ tt)` (坐标 `HB S⊥`, 级 `lz`), $\kappa_b=$ `(inj₂ (hs hz) , inj₂ tt)` (坐标 `HB (step S⊥)`, 级 `ls lz`); `x₀ ⨾ x₂` 的读回同时含两者.

```agda
κa κb : K (Lv (stL 2))
κa = inj₂ hz , inj₂ tt
κb = inj₂ (hs hz) , inj₂ tt

κa-co : E (Lv (stL 2)) κa ≡ HB S⊥
κa-co = refl

κb-co : E (Lv (stL 2)) κb ≡ HB (step S⊥)
κb-co = refl

κa≢κb : ¬ (κa ≡ κb)
κa≢κb e = hz≢ (cong pick e)
  where
  pick : K (Lv (stL 2)) → HB S⊥
  pick (inj₁ _ , _) = hz
  pick (inj₂ c , _) = c
  hz≢ : ¬ (hz ≡ hs hz)
  hz≢ ()

bd0 : Bd L₀ (inj₁ (νS 0)) hz (w₀ L₀)
bd0 = botBd L₀ (inj₁ (νS 0)) (w₀ L₀)

x₀ x₂ : D (Sg 1) (w₀ L₀)
x₀ = ni (sL {κ = inj₁ (νS 0)} {c = hz} bd0 (hsuc hself)) (λ _ _ _ → n1)
x₂ = ni (sL {κ = inj₁ (νS 0)} {c = hz} bd0 hself) (λ _ _ _ → n1)

rd-a : ∀ m → HasK (j (emb2 m) κa) (LvRd.δ (RLs m) (lw₀ L₀) x₀)
rd-a m = here

rd-b : ∀ m → HasK (j (emb2 m) κb) (LvRd.δ (RLs m) (lw₀ L₀) x₂)
rd-b m = here

rd-ab0 : HasK κa (LvRd.δ (RLs 0) (lw₀ L₀) (x₀ ⨾ x₂)) × HasK κb (LvRd.δ (RLs 0) (lw₀ L₀) (x₀ ⨾ x₂))
rd-ab0 = inΩ hz here , here
```

**两个种类不同 (定理).** $m=0$ (头 2) 与 $m=1$ (头 3) 时 `j (emb2 m) κa` 与 `j (emb2 m) κb` 不同 (第一分量 $0\ne1$). 一般的 $m$ 没有证 (要 `emb2 m` 保持第一分量, 判断成立; 没有写).

```agda
pick2 : K (Lv (stL 2)) → HB S⊥
pick2 (inj₁ _ , _) = hz
pick2 (inj₂ c , _) = c

pick3 : K (Lv (stL 3)) → HB S⊥
pick3 (inj₁ _ , _) = hz
pick3 (inj₂ c , _) = c

hz≢1 : ¬ (hz ≡ hs {S⊥} hz)
hz≢1 ()

kinds0 : ¬ (j (emb2 0) κa ≡ j (emb2 0) κb)
kinds0 e = hz≢1 (cong pick2 e)

kinds1 : ¬ (j (emb2 1) κa ≡ j (emb2 1) κb)
kinds1 e = hz≢1 (cong pick3 e)
```

**对照 `Sim` 版 (定理, `refl`).** [LeanLvTm](LeanLvTm.lagda.md) 的 `TV` 沿 `Sim` 读: 过一支本身的结点 `x₂` 有损, 读成 $1$ (分支在输入 $0$ 上的值). `Sim⁺` 版读成 $\kappa_b$ 的 $\Omega$-结点 (`rd-b`).

```agda
import OCF.Lean.LeanLvTm as V1

x₂-lossy-Sim : LvRd.δ (V1.RLv 0) (lw₀ L₀) x₂ ≡ hs hz
x₂-lossy-Sim = refl
```

## §3 回灌那一行被执行

**一步 (定理, `refl`).** 头种类 `inj₁ (νS n)` 的闭包结点在第 0 层目标上走 `RKa ac (fbS (νS n))`, 而 `fbS (νS n)` 对一切 $n$ 是回灌 (`heads-fed`); 对 $n=2+m$, 它的级层是 `Sg 1` (`lv-layer`).

```agda
exec-head : ∀ {ly W₀ W m} n (ac : AccY ly) (z : ZK ly (inj₁ (νS n))) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
  (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (Tq : Tg W hz m) →
  yc (RunC ac (inj₁ (νS n)) z u q₀ lW lL A₀ w Y) Tq ≡ RKa ac (fbS (νS n)) u q₀ lW lL A₀ w Y Tq
exec-head n ac z u q₀ lW lL A₀ w Y Tq = refl
```

**在闭项本身的计算里 (定理, `refl`).** 路径同 `LeanFbShape.exec-TF2` (由否定一路 `NegLeanFbInst` 先找到): `ΨVs` 沿它的子项字面地是头 2 的回灌行 `RKa _ (fbS (νS 2)) …`; 这一行的级层是 `Sg 1`, 读回是 `RLs 0`.

```agda
data Dir : Set where
  dL dR : Dir
  dN : ℕ → Dir

nav : ∀ {W} → List Dir → D hz W → D hz W
nav [] x = x
nav (dL ∷ p) (x ⨾ y) = nav p x
nav (dR ∷ p) (x ⨾ y) = nav p y
nav (dN n ∷ p) (nl d) = nav p (d n)
nav (_ ∷ p) _ = n0

exec-TVs2 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 3 ∷ dN 0 ∷ dL ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨVs ≡ RKa _ (fbS (νS 2)) _ _ _ _ _ _ _ Tq
exec-TVs2 Tq = refl

fb2 : fbS (νS 2) ≡ inj₁ (OCF.Lean.LeanFbTm.toFb (feedLs 0))
fb2 = refl

fb2-ℓ : Fb.ℓ (OCF.Lean.LeanFbTm.toFb (feedLs 0)) ≡ Sg 1
fb2-ℓ = refl
```
