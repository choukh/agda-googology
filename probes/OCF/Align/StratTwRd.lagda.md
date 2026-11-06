# 分层互递归塔 (一): 沿同形的级读回与写入

> 不含记号. 入口 [StratTw](StratTw.lagda.md), 接口 [StratTwIf](StratTwIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> [KindLvRd](KindLvRd.lagda.md) 的 `readL c`, `wrL c` 对级 $c$ (`HB T` 的高度) 的构造子递归, 输出在 `HB (Lev c)`. 这里把 "级层所在的高度" 与 "输出所在的高度" 拆开: 级层是总结构里的 $c$ (`lyL c`), 输出是前缀里的 $X$ 的级 (`HB (Lev X)`), 两者由同形证据 `σ : Sim M c X` 连起来, **对 $\sigma$ 的构造子递归**. 每一行与 `KindLvRd` 的同一行逐字对应 (只把 "对 $c$ 匹配" 换成 "对 $\sigma$ 匹配"):
>
> - 路径停在 $\sigma=$ `ss σ₁` ($c=\mathrm{hs}\,c_1$, $X=\mathrm{hs}\,X_1$): 读成 `step (Lev X₁)` 的新种类沿嵌入的 $\Omega$-结点, 坐标 $y$ 在 `HB (Lev X₁)`, 输入是 `wrS σ₁ y` (第 $c_1$ 级的级层数据);
> - 停在 `sz`: 读成底种类沿嵌入的 $\Omega$-结点 (`nbA`);
> - 停在 `sl`, `sΩ` (极限级): 有损 (读输入为 $0$ 的分支); 闭包结点 `nc` 有损.
> - 沿路径下行: `ss` 经 `stepE`; `sl σs` 在第 $n$ 项经 `supE n`; `sΩ σg` 在总结构的坐标 $e$ 处经 `supE (cv M κ e)`, 即前缀里的坐标 (这是唯一用到 `KMap.cv` 的地方).
> - 写入的种类查找 `wrKS` 同 `wrK`: 新种类写成过 `lyL c₁` 层的结点, 输入用 `readS σ₁` 读回; 路径经过 $\Omega$-级时有损 (取底坐标).
>
> **停机.** `readS`, `readSp`, `rdSS`, `wrS`, `wrKS` 一个 `mutual` 块; 换级的调用 (`rdSS → wrS σ₁`, `wrKS → readS σ₁`) 的同形证据是原来的证据的真子项; 同级的递归对数据或坐标结构递归. 检查器接受 (下面的编译).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (LgDn)
module OCF.Align.StratTwRd (T : KS) (Ld : LgDn T) where

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
open import OCF.Align.StratTwIf using (KMap; Sim; RdSTy; WrSTy)
  renaming (j to jM; cv to cvM; sz to σz; ss to σs; sl to σl; sΩ to σΩ)

lgW≤ : ∀ {U V} → U ≤ V → LgW L₀ V → LgW L₀ U
lgW≤ p l = lgDn Ld (proj₁ p) (proj₁ l) , lgB⊲ (proj₂ p) (proj₁ l) (proj₂ l)

Br : (c : HB T) → ∀ {W k} → k ⊲[ W ] up c → Set
Br c {W} P₀ = ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs (lyL c) (ss P₀) W′ → D (lyL c) W′
```

## §1 读回与写入

```agda
module SR {S′ : KS} (M : KMap S′ T) where
  readS  : ∀ {c X} → Sim M c X → ∀ {W} → LgW L₀ W → HB (Lev X) → D (lyL c) W → HB (Lev X)
  readSp : ∀ {c X} → Sim M c X → ∀ {W} → LgW L₀ W → HB (Lev X) → (ℕ → D (lyL c) W) → ℕ → HB (Lev X)
  rdSS   : ∀ {c₀ X₀} → Sim M c₀ X₀ → ∀ {c X} → Sim M c X → Emb (Lev X) (Lev X₀) → ∀ {W k} → LgW L₀ W →
           HB (Lev X₀) → (P₀ : k ⊲[ W ] up c₀) → Br c₀ P₀ → k ⊲[ W ] up c → HB (Lev X₀)
  wrS    : ∀ {c X} → Sim M c X → ∀ {W} → HB (Lev X) → D (lyL c) W
  wrKS   : ∀ {c X} → Sim M c X → ∀ {c′ X′} → Sim M c′ X′ → (∀ {k W} → k ⊲[ W ] up c′ → k ⊲[ W ] up c) →
           (κ : K (Lev X′)) → (∀ {W} → E (Lev X′) κ → D (lyL c) W) → ∀ {W} → D (lyL c) W

  readS σ lW b n0 = b
  readS σ lW b n1 = hs b
  readS σ lW b (x ⨾ y) = readS σ lW (readS σ lW b x) y
  readS σ lW b (nl d) = hl (readSp σ lW b d)
  readS σ lW b (ni (ss P) u) = rdSS σ σ idE lW b P u P
  readS σ lW b (nc κ z u) = readS σ lW b (u ≤rf lW)
  readS σ lW b (nw p x) = readS σ (lgW≤ p lW) b x
  readSp σ lW b d zero = b
  readSp σ lW b d (suc n) = readS σ lW (readSp σ lW b d n) (d n)

  rdSS σ₀ σz Em lW b P₀ u hself =
    hΩ (j Em tt) (λ e → nbA b (λ a h → readS σ₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))) (cv Em e))
  rdSS σ₀ (σs σ₁) Em lW b P₀ u hself =
    hΩ (j Em (inj₂ tt)) (λ e → nbJ (Em ∘E stepE) b (λ y h → readS σ₀ lW h (u ≤rf lW (inS (ss P₀) (wrS σ₁ y)))) (cv Em e))
  rdSS σ₀ (σs σ₁) Em lW b P₀ u (hsuc P) = rdSS σ₀ σ₁ (Em ∘E stepE) lW b P₀ u P
  rdSS σ₀ (σl σf) Em lW b P₀ u hself = readS σ₀ lW b (u ≤rf lW (inS (ss P₀) n0))
  rdSS σ₀ (σl {g = g} σf) Em lW b P₀ u (hlim n P) = rdSS σ₀ (σf n) (Em ∘E supE {F = λ m → Lev (g m)} n) lW b P₀ u P
  rdSS σ₀ (σΩ σg) Em lW b P₀ u hself = readS σ₀ lW b (u ≤rf lW (inS (ss P₀) n0))
  rdSS σ₀ (σΩ {κ} {g = g} σg) Em lW b P₀ u (hLim {c = e} bd P) =
    rdSS σ₀ (σg e) (Em ∘E supE {F = λ x → Lev (g x)} (cvM M κ e)) lW b P₀ u P

  wrS σ hz = n0
  wrS σ (hs y) = wrS σ y ⨾ n1
  wrS σ (hl f) = nl (λ n → wrS σ (f n))
  wrS σ (hΩ κ g) = wrKS σ σ (λ P → P) κ (λ e → wrS σ (g e))

  wrKS σ σz pre tt g = ni (ss (pre hself)) (λ q lW′ x → g (sum azero (outS (ss (pre hself)) x)))
  wrKS σ (σs σ₁) pre (inj₂ tt) g = ni (ss (pre hself)) (λ q lW′ x → g (readS σ₁ lW′ hz (outS (ss (pre hself)) x)))
  wrKS σ (σs σ₁) pre (inj₁ κ) g = wrKS σ σ₁ (λ P → pre (hsuc P)) κ g
  wrKS σ (σl σf) pre (n , κ) g = wrKS σ (σf n) (λ P → pre (hlim n P)) κ g
  wrKS σ (σΩ {g = g′} σg) pre (e , κ) g = g (bot (Lev (g′ e)) κ)
```

## §2 起点是第一位置

```agda
  readS-fst : ∀ {c X} (σ : Sim M c X) {W} (lW : LgW L₀ W) b (x : D (lyL c) W) {w} → b ⊲[ w ] readS σ lW b x
  rdSS-fst  : ∀ {c₀ X₀} (σ₀ : Sim M c₀ X₀) {c X} (σ : Sim M c X) (Em : Emb (Lev X) (Lev X₀)) {W k} (lW : LgW L₀ W) b
              (P₀ : k ⊲[ W ] up c₀) (u : Br c₀ P₀) (P : k ⊲[ W ] up c) {w} → b ⊲[ w ] rdSS σ₀ σ Em lW b P₀ u P
  readS-fst σ lW b n0 = hself
  readS-fst σ lW b n1 = hsuc hself
  readS-fst σ lW b (x ⨾ y) = ⊲ᴮ-tr (readS-fst σ lW b x) (readS-fst σ lW (readS σ lW b x) y)
  readS-fst σ lW b (nl d) = hlim 0 hself
  readS-fst σ lW b (ni (ss P) u) = rdSS-fst σ σ idE lW b P u P
  readS-fst σ lW b (nc κ z u) = readS-fst σ lW b (u ≤rf lW)
  readS-fst σ lW b (nw p x) = readS-fst σ (lgW≤ p lW) b x

  rdSS-fst {X₀ = X₀} σ₀ σz Em lW b P₀ u hself {w} =
    hLim (botBd (Lev X₀) (j Em tt) w)
      (nbA-fst (λ a h → readS-fst σ₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))) (cv Em (bot (Lev X₀) (j Em tt))))
  rdSS-fst {X₀ = X₀} σ₀ (σs σ₁) Em lW b P₀ u hself {w} =
    hLim (botBd (Lev X₀) (j Em (inj₂ tt)) w)
      (nbJ-fst (Em ∘E stepE) (λ y h → readS-fst σ₀ lW h (u ≤rf lW (inS (ss P₀) (wrS σ₁ y)))) (cv Em (bot (Lev X₀) (j Em (inj₂ tt)))))
  rdSS-fst σ₀ (σs σ₁) Em lW b P₀ u (hsuc P) = rdSS-fst σ₀ σ₁ (Em ∘E stepE) lW b P₀ u P
  rdSS-fst σ₀ (σl σf) Em lW b P₀ u hself = readS-fst σ₀ lW b (u ≤rf lW (inS (ss P₀) n0))
  rdSS-fst σ₀ (σl {g = g} σf) Em lW b P₀ u (hlim n P) = rdSS-fst σ₀ (σf n) (Em ∘E supE {F = λ m → Lev (g m)} n) lW b P₀ u P
  rdSS-fst σ₀ (σΩ σg) Em lW b P₀ u hself = readS-fst σ₀ lW b (u ≤rf lW (inS (ss P₀) n0))
  rdSS-fst σ₀ (σΩ {κ} {g = g} σg) Em lW b P₀ u (hLim {c = e} bd P) =
    rdSS-fst σ₀ (σg e) (Em ∘E supE {F = λ x → Lev (g x)} (cvM M κ e)) lW b P₀ u P
```

## §3 合法由形状给出

```agda
  Lg-readS  : ∀ {c X} (σ : Sim M c X) {W} (lW : LgW L₀ W) b (x : D (lyL c) W) → LgB b → LgB (readS σ lW b x)
  Lg-readSp : ∀ {c X} (σ : Sim M c X) {W} (lW : LgW L₀ W) b (d : ℕ → D (lyL c) W) → LgB b → ∀ n → LgB (readSp σ lW b d n)
  Lg-rdSS   : ∀ {c₀ X₀} (σ₀ : Sim M c₀ X₀) {c X} (σ : Sim M c X) (Em : Emb (Lev X) (Lev X₀)) {W k} (lW : LgW L₀ W) b
              (P₀ : k ⊲[ W ] up c₀) (u : Br c₀ P₀) (P : k ⊲[ W ] up c) → LgB b → LgB (rdSS σ₀ σ Em lW b P₀ u P)
  Lg-readS σ lW b n0 l = l
  Lg-readS σ lW b n1 l = l
  Lg-readS σ lW b (x ⨾ y) l = Lg-readS σ lW (readS σ lW b x) y (Lg-readS σ lW b x l)
  Lg-readS σ lW b (nl d) l = (λ n → readS-fst σ lW (readSp σ lW b d n) (d n)) , Lg-readSp σ lW b d l
  Lg-readS σ lW b (ni (ss P) u) l = Lg-rdSS σ σ idE lW b P u P l
  Lg-readS σ lW b (nc κ z u) l = Lg-readS σ lW b (u ≤rf lW) l
  Lg-readS σ lW b (nw p x) l = Lg-readS σ (lgW≤ p lW) b x l
  Lg-readSp σ lW b d l zero = l
  Lg-readSp σ lW b d l (suc n) = Lg-readS σ lW (readSp σ lW b d n) (d n) (Lg-readSp σ lW b d l n)

  Lg-rdSS {X₀ = X₀} σ₀ σz Em lW b P₀ u hself l =
    LgΩ Em tt (nbA b s) (λ lw p → nbA-mono fs p) (λ a la → Lg-nbA fs l (λ a′ h lh → Lg-readS σ₀ lW h _ lh) a la)
    where
    s : A → HB (Lev X₀) → HB (Lev X₀)
    s a h = readS σ₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))
    fs : ∀ a h {w} → h ⊲[ w ] s a h
    fs a h = readS-fst σ₀ lW h (u ≤rf lW (inS (ss P₀) (toD₀ a)))
  Lg-rdSS {X₀ = X₀} σ₀ (σs {X = X₁} σ₁) Em lW b P₀ u hself l =
    LgΩ Em (inj₂ tt) (nbJ (Em ∘E stepE) b s) (λ lw p → nbJ-mono (Em ∘E stepE) fs p)
      (λ y ly → Lg-nbJ (Em ∘E stepE) fs l (λ y′ h lh → Lg-readS σ₀ lW h _ lh) y ly)
    where
    s : HB (Lev X₁) → HB (Lev X₀) → HB (Lev X₀)
    s y h = readS σ₀ lW h (u ≤rf lW (inS (ss P₀) (wrS σ₁ y)))
    fs : ∀ y h {w} → h ⊲[ w ] s y h
    fs y h = readS-fst σ₀ lW h (u ≤rf lW (inS (ss P₀) (wrS σ₁ y)))
  Lg-rdSS σ₀ (σs σ₁) Em lW b P₀ u (hsuc P) l = Lg-rdSS σ₀ σ₁ (Em ∘E stepE) lW b P₀ u P l
  Lg-rdSS σ₀ (σl σf) Em lW b P₀ u hself l = Lg-readS σ₀ lW b (u ≤rf lW (inS (ss P₀) n0)) l
  Lg-rdSS σ₀ (σl {g = g} σf) Em lW b P₀ u (hlim n P) l = Lg-rdSS σ₀ (σf n) (Em ∘E supE {F = λ m → Lev (g m)} n) lW b P₀ u P l
  Lg-rdSS σ₀ (σΩ σg) Em lW b P₀ u hself l = Lg-readS σ₀ lW b (u ≤rf lW (inS (ss P₀) n0)) l
  Lg-rdSS σ₀ (σΩ {κ} {g = g} σg) Em lW b P₀ u (hLim {c = e} bd P) l =
    Lg-rdSS σ₀ (σg e) (Em ∘E supE {F = λ x → Lev (g x)} (cvM M κ e)) lW b P₀ u P l
```

## §4 接口的实例

```agda
rdST : RdSTy T
rdST M c X σ = SR.readS M σ

wrST : WrSTy T
wrST M c X σ = SR.wrS M σ
```
