# 按级回灌, 否定一路 (五): 构造一路的级读回与写入在哪里有损

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 对着接口 [KindLvIf](KindLvIf.lagda.md) ("接口定稿 2026-11-05 18:33", 变更记录: 无) 与构造一路的 [KindLvRd](KindLvRd.lagda.md) (只读导入, 不改) 写. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> `KindLvRd` 的文件头如实列了三处有损 (闭包结点读当前世界; 路径停在极限级; 写入时路径经过 $c$ 的 $\Omega$-结点). 本篇把它们写成 `refl` 陈述, 并给出后果:
>
> 1. **`wr-Ω-drop` (定理, `refl`).** 级 $c=\mathrm{h\Omega}\,\kappa_0\,h$ 时, `wrL c` 把种类 $(e,\kappa)$ 的 $\Omega$-结点整个丢掉, 只写底坐标的分支: `wrL c (hΩ (e , κ) g) ≡ wrL c (g (bot …))`. **`wr-no-ret` (定理, 否定):** 这时写入没有左逆 (任何 `r` 都有 `r ∘ wrL c ≠ id`); **`rdwr-drop`**: 读回写入的 $\Omega$-结点得到起点. 所以第 $c$ 级里经过 $c$ 的 $\Omega$-结点的种类 (以坐标为下标的并的分量里的种类), 它们作坐标时**不能**经 "写成级层数据再折叠" 回到原值.
> 2. **`rd-lim-drop` (定理, `refl`).** 级 $c$ 是极限 (`hl f` 或 `hΩ κ g`) 时, 过第 `up c` 层本身的结点读成输入为 $0$ 的分支. 与 [NegKindLvLev](NegKindLvLev.lagda.md) 的 `lv-not-self` 对照: 第 $c$ 级没有级为 $c$ 的种类, 所以这一读法在 "读进 `HB (Lev c)`" 的类型里是被逼的 (判断; 编译的部分是 `lv-not-self`).
> 3. **`rd-nc-drop` (定理, `refl`).** 闭包结点读当前世界的分支 (同 `GenFoldRd.rd₁`, `SkelDxGen.nc-old-drop`).
>
> **只否定什么.** 第 1 条只否定 "写入有左逆" (对一切 $T$, 一切 $\Omega$-头的级 $c$). 第 2, 3 条是定义相等, 只说那些结点在读回里只留一支. **不否定**: 读回的合法性与停机; 级里没有 $\Omega$-结点时写入的往返 (未研究); 构造一路的折叠与闭项的值 (没有 `ord` 的比较).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (LgDn)
module OCF.Align.NegKindLvRdW (T : KS) (Ld : LgDn T) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Align.HtTowerTy hiding (KS)
open import OCF.Align.GenFoldIf hiding (LgDn)
open import OCF.Align.GenFoldTree using (module Tree)
open Tree T
open import OCF.Align.GenFoldInst using (genLev)
open import OCF.Align.KindLvIf using (lyL)
open import OCF.Align.KindLvRd T Ld
```

## §1 写入经过级的 $\Omega$-结点: 丢掉

```agda
module WΩ (κ₀ : K T) (h : E T κ₀ → HB T) where
  c : HB T
  c = hΩ κ₀ h

  wr-Ω-drop : ∀ {W} (e : E T κ₀) (κ : K (Lev (h e))) (g : E (Lev (h e)) κ → HB (Lev c)) →
    wrL c {W} (hΩ (e , κ) g) ≡ wrL c {W} (g (bot (Lev (h e)) κ))
  wr-Ω-drop e κ g = refl

  -- 一个种类: 第 bot 个分量的底种类
  e₀ : E T κ₀
  e₀ = bot T κ₀

  κ₁ : K (Lev c)
  κ₁ = e₀ , aK (genLev (h e₀))

  y₁ : HB (Lev c)
  y₁ = hΩ κ₁ (λ _ → hz)

  wr-y₁ : ∀ {W} → wrL c {W} y₁ ≡ wrL c {W} hz
  wr-y₁ = refl

  wr-no-ret : ∀ {W} (r : D (lyL c) W → HB (Lev c)) → ¬ (∀ y → r (wrL c y) ≡ y)
  wr-no-ret r sec = ne (trans (sym (sec y₁)) (sec hz))
    where
    ne : ¬ (y₁ ≡ hz)
    ne ()

  rdwr-drop : ∀ {W} (lW : LgW L₀ W) → readL c lW hz (wrL c y₁) ≡ hz
  rdwr-drop lW = refl
```

## §2 极限级: 过级层本身的结点只读输入为 $0$ 的分支

```agda
rd-lim-drop : ∀ (f : ℕ → HB T) {W} (lW : LgW L₀ W) b (u : Br (hl f) {W} {up (hl f)} hself) →
  readL (hl f) lW b (ni (ss hself) u) ≡ readL (hl f) lW b (u ≤rf lW (inS (ss (hself {w = W})) n0))
rd-lim-drop f lW b u = refl

rd-limΩ-drop : ∀ κ (g : E T κ → HB T) {W} (lW : LgW L₀ W) b (u : Br (hΩ κ g) {W} {up (hΩ κ g)} hself) →
  readL (hΩ κ g) lW b (ni (ss hself) u) ≡ readL (hΩ κ g) lW b (u ≤rf lW (inS (ss (hself {w = W})) n0))
rd-limΩ-drop κ g lW b u = refl
```

## §3 闭包结点: 当前世界的一支

```agda
rd-nc-drop : ∀ c {W} (lW : LgW L₀ W) b κ (z : ZK T (lyL c) κ) (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D (lyL c) W′) →
  readL c lW b (nc κ z u) ≡ readL c lW b (u ≤rf lW)
rd-nc-drop c lW b κ z u = refl
```

## §4 结论 (按档)

- **[定理, `refl`]** `WΩ.wr-Ω-drop`, `WΩ.wr-y₁`, `WΩ.rdwr-drop`, `rd-lim-drop`, `rd-limΩ-drop`, `rd-nc-drop`.
- **[定理, 否定]** **`WΩ.wr-no-ret`**: 级是 $\Omega$-头时写入无左逆, 对一切 $T$, 一切 `LgDn T`, 一切 $\kappa_0$, $h$ (前提只有这些参数; 实例: $T=S_0$, `ldS₀`, $\kappa_0=$ `tt`, 任意 $h$).
- **[判断]** 塔里第 $s\ge1$ 站的级 $Y_s$ 含 $\Omega$-结点 (构造一路的求值输出的头是新种类的 $\Omega$-结点, 判断, 待对实例写成定理): 第 $s+1$ 站头种类的坐标 `HB (Lev Y_s)` 里, 经过 $Y_s$ 的 $\Omega$-结点的种类, 在写入时只剩底支.
