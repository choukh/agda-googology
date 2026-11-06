# 按级回灌 (二): 级层的数据 ↔ 第 $c$ 级的高度

> 不含记号. 入口 [KindLv](KindLv.lagda.md), 接口 [KindLvIf](KindLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 对一切种类结构 $T$ (带 `LgDn T`) 与一切级 $c$ (`HB T` 的高度), **对 $c$ 的构造子递归**:
>
> - **读回 `readL c : RdLTy T`**: 级层 $\mathrm{hs}(\mathrm{up}\,c)$ 的数据读进 `HB (Lev c)`. 过第 $k$ 层的结点 (路径 $P : k\lhd\mathrm{up}\,c$) 沿 $P$ 走 $c$ 的构造子 (`rdS`, 同时累计嵌入 `Emb (Lev c′) (Lev c)`):
>   - 停在 $c'=\mathrm{hs}\,c_1$: 读成 `step (Lev c₁)` 的**新种类**沿嵌入的 $\Omega$-结点, 坐标 $y$ 是 `HB (Lev c₁)` 的高度, 分支的输入是 $y$ 写成的第 $c_1$ 级的级层数据 (`wrL c₁ y`), 对坐标连续 (`nbJ`);
>   - 停在 $c'=0$: 读成**底种类** (`S₀`, 坐标 `A`) 沿嵌入的 $\Omega$-结点, 输入 `toD₀`, 对坐标连续 (`nbA`);
>   - 停在极限 ($c'=\mathrm{hl}\,f$ 或 $\mathrm{h\Omega}\,\kappa\,g$, 第 $c'$ 级没有以 "第 $c'$ 层数据" 为坐标的种类): **有损**, 读输入为 $0$ 的分支.
>   闭包结点 (`nc`, 种类在 `step T` 里, 坐标不是任何 `HB (Lev _)`) **有损**, 读当前世界的分支 (同 `rd₁`).
> - **写入 `wrL c : WrLTy T`**: `HB (Lev c)` 的 $\Omega$-结点按种类沿 $c$ 的构造子找到它的层 (`wrK`): 新种类 (第 $c_1$ 级) 写成过第 $\mathrm{hs}(\mathrm{up}\,c_1)$ 层的结点, 输入读回成坐标 (`readL c₁`); 底种类写成过第 $0$ 层的结点, 输入用 `sum` 读回. 种类的路径经过 $c$ 的 $\Omega$-结点 (坐标 $e$) 时, 要第 $e$ 个分量在世界的界之下的证据, 写入时没有, **有损**: 取该种类的底坐标的分支.
> - 合法由形状给出 (`Lg-readL`, 对一切数据), 起点是读回的第一位置 (`readL-fst`).
>
> **与 `rd₁`, `rd₂`, `toD₁` 的关系** (对照在 [KindLvCmp](KindLvCmp.lagda.md)): $c=0$ 时 `Lev 0 = S₀`, 级层是第 $1$ 层, `readL 0` 与 $T=S_0$ 的 `rd₁` 逐结点相同 (定理 `rdL0≈rd₁`, 结构等价); `wrL 0` 的四行与 `toD₁` 的四行同形. $c=1$ 时 `Lev 1 = step S₀`, 级层是第 $2$ 层, `readL 1` 的两种结点行与 `rd₂` 的同形 (过第 1 层读成新种类, 过第 0 层读成旧种类), 差别在新种类的闭包结点: `rd₂` 经 `encH` 读成 κH 结点, `readL` 有损.
>
> **停机.** 读回, 路径上的读回 `rdS`, 写入, 写入的种类查找 `wrK` 是一个 `mutual` 块: 同级的递归对数据或坐标结构递归; 换级的调用 (`rdS → wrL c₁`, `wrK → readL c₁`) 的级是原来的级的真子项. 检查器接受.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (LgDn)
module OCF.Align.KindLvRd (T : KS) (Ld : LgDn T) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.HtTowerTy hiding (KS)
open import OCF.Align.GenFoldIf hiding (LgDn)
open import OCF.Align.GenFoldTree using (module Tree)
open Tree T
open import OCF.Align.GenFoldInst using (genS₀; ldS₀)
open import OCF.Align.GenFoldRd S₀ genS₀ ldS₀ using (module NbA)
open NbA
open import OCF.Align.KindLvIf
open import OCF.Align.KindLvEmb

lgW≤ : ∀ {U V} → U ≤ V → LgW L₀ V → LgW L₀ U
lgW≤ p l = lgDn Ld (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l)

-- 结点的分支 (过第 k 层, 结点证据 ss P₀)
Br : (c : HB T) → ∀ {W k} → k ⊲[ W ] up c → Set
Br c {W} P₀ = ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs (lyL c) (ss P₀) W′ → D (lyL c) W′
```

## §1 读回与写入

```agda
readL  : RdLTy T
readLp : (c : HB T) → ∀ {W} → LgW L₀ W → HB (Lev c) → (ℕ → D (lyL c) W) → ℕ → HB (Lev c)
rdS    : (c₀ c : HB T) → Emb (Lev c) (Lev c₀) → ∀ {W k} → LgW L₀ W → HB (Lev c₀) →
         (P₀ : k ⊲[ W ] up c₀) → Br c₀ P₀ → k ⊲[ W ] up c → HB (Lev c₀)
wrL    : WrLTy T
wrK    : (c c′ : HB T) → (∀ {k W} → k ⊲[ W ] up c′ → k ⊲[ W ] up c) → (κ : K (Lev c′)) →
         (∀ {W} → E (Lev c′) κ → D (lyL c) W) → ∀ {W} → D (lyL c) W

readL c lW b n0 = b
readL c lW b n1 = hs b
readL c lW b (x ⨾ y) = readL c lW (readL c lW b x) y
readL c lW b (nl d) = hl (readLp c lW b d)
readL c lW b (ni (ss P) u) = rdS c c idE lW b P u P
readL c lW b (nc κ z u) = readL c lW b (u ≤rf lW)
readL c lW b (nw p x) = readL c (lgW≤ p lW) b x
readLp c lW b d zero = b
readLp c lW b d (suc n) = readL c lW (readLp c lW b d n) (d n)

rdS c₀ hz Em lW b P₀ u hself =
  hΩ (j Em tt) (λ e → nbA b (λ a h → readL c₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))) (cv Em e))
rdS c₀ (hs c₁) Em lW b P₀ u hself =
  hΩ (j Em (inj₂ tt)) (λ e → nbJ (Em ∘E stepE) b (λ y h → readL c₀ lW h (u ≤rf lW (inS (ss P₀) (wrL c₁ y)))) (cv Em e))
rdS c₀ (hs c₁) Em lW b P₀ u (hsuc P) = rdS c₀ c₁ (Em ∘E stepE) lW b P₀ u P
rdS c₀ (hl f) Em lW b P₀ u hself = readL c₀ lW b (u ≤rf lW (inS (ss P₀) n0))
rdS c₀ (hl f) Em lW b P₀ u (hlim n P) = rdS c₀ (f n) (Em ∘E supE {F = λ m → Lev (f m)} n) lW b P₀ u P
rdS c₀ (hΩ κ g) Em lW b P₀ u hself = readL c₀ lW b (u ≤rf lW (inS (ss P₀) n0))
rdS c₀ (hΩ κ g) Em lW b P₀ u (hLim {c = e} bd P) = rdS c₀ (g e) (Em ∘E supE {F = λ x → Lev (g x)} e) lW b P₀ u P

wrL c hz = n0
wrL c (hs y) = wrL c y ⨾ n1
wrL c (hl f) = nl (λ n → wrL c (f n))
wrL c (hΩ κ g) = wrK c c (λ P → P) κ (λ e → wrL c (g e))

wrK c hz pre tt g = ni (ss (pre hself)) (λ q lW′ x → g (sum azero (outS (ss (pre hself)) x)))
wrK c (hs c₁) pre (inj₂ tt) g = ni (ss (pre hself)) (λ q lW′ x → g (readL c₁ lW′ hz (outS (ss (pre hself)) x)))
wrK c (hs c₁) pre (inj₁ κ) g = wrK c c₁ (λ P → pre (hsuc P)) κ g
wrK c (hl f) pre (n , κ) g = wrK c (f n) (λ P → pre (hlim n P)) κ g
wrK c (hΩ κ₀ h) pre (e , κ) g = g (bot (Lev (h e)) κ)
```

## §2 起点是第一位置

```agda
readL-fst  : ∀ c {W} (lW : LgW L₀ W) b (x : D (lyL c) W) {w} → b ⊲[ w ] readL c lW b x
rdS-fst    : ∀ c₀ c (Em : Emb (Lev c) (Lev c₀)) {W k} (lW : LgW L₀ W) b (P₀ : k ⊲[ W ] up c₀) (u : Br c₀ P₀)
             (P : k ⊲[ W ] up c) {w} → b ⊲[ w ] rdS c₀ c Em lW b P₀ u P
readL-fst c lW b n0 = hself
readL-fst c lW b n1 = hsuc hself
readL-fst c lW b (x ⨾ y) = ⊲ᴮ-tr (readL-fst c lW b x) (readL-fst c lW (readL c lW b x) y)
readL-fst c lW b (nl d) = hlim 0 hself
readL-fst c lW b (ni (ss P) u) = rdS-fst c c idE lW b P u P
readL-fst c lW b (nc κ z u) = readL-fst c lW b (u ≤rf lW)
readL-fst c lW b (nw p x) = readL-fst c (lgW≤ p lW) b x

rdS-fst c₀ hz Em lW b P₀ u hself {w} =
  hLim (botBd (Lev c₀) (j Em tt) w)
    (nbA-fst (λ a h → readL-fst c₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))) (cv Em (bot (Lev c₀) (j Em tt))))
rdS-fst c₀ (hs c₁) Em lW b P₀ u hself {w} =
  hLim (botBd (Lev c₀) (j Em (inj₂ tt)) w)
    (nbJ-fst (Em ∘E stepE) (λ y h → readL-fst c₀ lW h (u ≤rf lW (inS (ss P₀) (wrL c₁ y)))) (cv Em (bot (Lev c₀) (j Em (inj₂ tt)))))
rdS-fst c₀ (hs c₁) Em lW b P₀ u (hsuc P) = rdS-fst c₀ c₁ (Em ∘E stepE) lW b P₀ u P
rdS-fst c₀ (hl f) Em lW b P₀ u hself = readL-fst c₀ lW b (u ≤rf lW (inS (ss P₀) n0))
rdS-fst c₀ (hl f) Em lW b P₀ u (hlim n P) = rdS-fst c₀ (f n) (Em ∘E supE {F = λ m → Lev (f m)} n) lW b P₀ u P
rdS-fst c₀ (hΩ κ g) Em lW b P₀ u hself = readL-fst c₀ lW b (u ≤rf lW (inS (ss P₀) n0))
rdS-fst c₀ (hΩ κ g) Em lW b P₀ u (hLim {c = e} bd P) = rdS-fst c₀ (g e) (Em ∘E supE {F = λ x → Lev (g x)} e) lW b P₀ u P
```

## §3 合法由形状给出

```agda
Lg-readL  : ∀ c {W} (lW : LgW L₀ W) b (x : D (lyL c) W) → LgB b → LgB (readL c lW b x)
Lg-readLp : ∀ c {W} (lW : LgW L₀ W) b (d : ℕ → D (lyL c) W) → LgB b → ∀ n → LgB (readLp c lW b d n)
Lg-rdS    : ∀ c₀ c (Em : Emb (Lev c) (Lev c₀)) {W k} (lW : LgW L₀ W) b (P₀ : k ⊲[ W ] up c₀) (u : Br c₀ P₀)
            (P : k ⊲[ W ] up c) → LgB b → LgB (rdS c₀ c Em lW b P₀ u P)
Lg-readL c lW b n0 l = l
Lg-readL c lW b n1 l = l
Lg-readL c lW b (x ⨾ y) l = Lg-readL c lW (readL c lW b x) y (Lg-readL c lW b x l)
Lg-readL c lW b (nl d) l = (λ n → readL-fst c lW (readLp c lW b d n) (d n)) , Lg-readLp c lW b d l
Lg-readL c lW b (ni (ss P) u) l = Lg-rdS c c idE lW b P u P l
Lg-readL c lW b (nc κ z u) l = Lg-readL c lW b (u ≤rf lW) l
Lg-readL c lW b (nw p x) l = Lg-readL c (lgW≤ p lW) b x l
Lg-readLp c lW b d l zero = l
Lg-readLp c lW b d l (suc n) = Lg-readL c lW (readLp c lW b d n) (d n) (Lg-readLp c lW b d l n)

Lg-rdS c₀ hz Em lW b P₀ u hself l =
  LgΩ Em tt (nbA b s) (λ lw p → nbA-mono fs p) (λ a la → Lg-nbA fs l (λ a′ h lh → Lg-readL c₀ lW h _ lh) a la)
  where
  s : A → HB (Lev c₀) → HB (Lev c₀)
  s a h = readL c₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))
  fs : ∀ a h {w} → h ⊲[ w ] s a h
  fs a h = readL-fst c₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))
Lg-rdS c₀ (hs c₁) Em lW b P₀ u hself l =
  LgΩ Em (inj₂ tt) (nbJ (Em ∘E stepE) b s) (λ lw p → nbJ-mono (Em ∘E stepE) fs p)
    (λ y ly → Lg-nbJ (Em ∘E stepE) fs l (λ y′ h lh → Lg-readL c₀ lW h _ lh) y ly)
  where
  s : HB (Lev c₁) → HB (Lev c₀) → HB (Lev c₀)
  s y h = readL c₀ lW h (u ≤rf lW (inS (ss P₀) (wrL c₁ y)))
  fs : ∀ y h {w} → h ⊲[ w ] s y h
  fs y h = readL-fst c₀ lW h (u ≤rf lW (inS (ss P₀) (wrL c₁ y)))
Lg-rdS c₀ (hs c₁) Em lW b P₀ u (hsuc P) l = Lg-rdS c₀ c₁ (Em ∘E stepE) lW b P₀ u P l
Lg-rdS c₀ (hl f) Em lW b P₀ u hself l = Lg-readL c₀ lW b (u ≤rf lW (inS (ss P₀) n0)) l
Lg-rdS c₀ (hl f) Em lW b P₀ u (hlim n P) l = Lg-rdS c₀ (f n) (Em ∘E supE {F = λ m → Lev (f m)} n) lW b P₀ u P l
Lg-rdS c₀ (hΩ κ g) Em lW b P₀ u hself l = Lg-readL c₀ lW b (u ≤rf lW (inS (ss P₀) n0)) l
Lg-rdS c₀ (hΩ κ g) Em lW b P₀ u (hLim {c = e} bd P) l = Lg-rdS c₀ (g e) (Em ∘E supE {F = λ x → Lev (g x)} e) lW b P₀ u P l
```
