# LeanLv (二): 沿同形的级读回与写入

> **不是主候选.** 主候选 `TVs` 用 [LeanLvRdS](LeanLvRdS.lagda.md) (沿 `Sim⁺`, 极限一支本身有后继种类时不有损). 本篇留着不改: 否定一路 `NegLeanLvEmb`, `NegLeanLvInst` 对它编译过.

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md), 接口 [LeanLvIf](LeanLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 用 `OCF/Lean` 的种类结构与一次封闭的层号重写 [StratTwRd](../Align/StratTwRd.lagda.md) / [KindLvRd](../Align/KindLvRd.lagda.md) 的读回与写入 (只读参考, 不导入). 对一切种类结构 $T$, 层 $a$ : `HB (step T)` 上的数据沿同形 `σ : Sim T a x` (接口 §2) 读进 `Lv x` 的高度, 经嵌入 `Em : Emb (Lv x) X` 放进 $X$ (接口 §3 的 `RdSTy`). 对 $\sigma$ 的构造子递归; 与 `StratTwRd` 的差: 层号是一次封闭的 `LH` (不是 `HB T` 的级), 所以 "级 $x$ 的种类结构" 是 `Lv x`, 层 $0$ 对应 `Lv lz = S⊥` (没有种类), 层的后继 `hs a` 对应 `step (Lv x)`.
>
> - **结点** `ni r u` (过第 $k$ 层): 先按结点证据 $r$ 的第一步 (`rdN`), 再沿路径 $k\lhd a'$ 与同形 $\sigma$ 一起下行 (`rdP`); 路径停下时 (`hself`) 由 `slf` 按 "上一步是后继还是极限" 决定 (`rdP` 的模式参数 `Emb (Lv (ls x)) X ⊎ ⊤`).
>   - 停在后继处 ($\sigma$ = `ss σ₁`, 结点恰好过 $a_1$): 读成 `step (Lv x₁)` 的**新种类**沿嵌入的 $\Omega$-结点; 坐标 $y$ : `HB (Lv x₁)`, 分支的输入是 $y$ 写成的层 $a_1$ 上的数据 (`wrS σ₁ y`), 对坐标连续 (`nbJ`).
>   - 下行: 后继经 `stepE`, $\mathbb N$-极限第 $n$ 项经 `supE n`, $\Omega$-极限坐标 $e$ 处经 `supE (inj₂ (cv e))` (`lΩ` 的右分量; 这是唯一用 `Sim` 的坐标映射的地方).
>   - 停在极限处 ($\mathbb N$-极限或 $\Omega$-极限的一支本身): **有损**, 读输入为 $0$ 的分支. (`Lv (lΩ k g)` 的左分量的新种类以 `HB (Lv k)` 为坐标, 它对应的层不是任何一支; 判断: 这是 `Lv` 的形状, 同 `KindLvRd` 在极限级的有损.)
> - **闭包结点** `nc` 有损 (当前世界的分支, 同 `rd₁`).
> - **写入** `wrS σ`: `HB (Lv x)` 的 $\Omega$-结点按种类沿 $\sigma$ 找层 (`wrK`): 后继处的新种类写成过 $a_1$ 的结点, 输入读回 (`readS σ₁`); 经过 $\Omega$-极限的分量: **有损** (写入时没有坐标在界之下的证据), 取底坐标的分支.
> - 合法由形状给出 (`Lg-readS`, 对一切数据), 起点是读回的第一位置 (`readS-fst`).
>
> **停机.** `readS`, `readSp`, `rdN`, `rdP`, `slf`, `wrS`, `wrK` 一起声明 (互递归): 同级的递归对数据或坐标结构递归; 换级的调用 (`rdN → wrS σ₁`, `wrK → readS σ₁`) 的同形证据是原来的证据的真子项. 检查器接受.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.LeanTBase
module OCF.Lean.LeanLvRd (T : KS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanLvIf hiding (here; inS; inL; inΩ)
open import OCF.Lean.LeanLvEmb
open Tree T

-- 层 a 上过第 k 层的结点的分支
Br : ∀ {a W k} → StH W k a → Set
Br {a} {W} r = ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs a r W′ → D a W′
```

## §1 读回与写入

```agda
readS  : RdSTy T
readSp : ∀ {a x} → Sim T a x → ∀ {X} → Emb (Lv x) X → ∀ {W} → LgW L₀ W → HB X → (ℕ → D a W) → ℕ → HB X
rdN    : ∀ {a₀ x₀} → Sim T a₀ x₀ → ∀ {X} → Emb (Lv x₀) X → ∀ {W k} → LgW L₀ W → HB X → (r₀ : StH W k a₀) → Br r₀ → HB X
rdP    : ∀ {a₀ x₀} → Sim T a₀ x₀ → ∀ {X} → Emb (Lv x₀) X → ∀ {a x} → Sim T a x → Emb (Lv x) X → Emb (Lv (ls x)) X ⊎ ⊤ →
         ∀ {W k} → LgW L₀ W → HB X → (r₀ : StH W k a₀) → Br r₀ → k ⊲[ W ] a → HB X
slf    : ∀ {a₀ x₀} → Sim T a₀ x₀ → ∀ {X} → Emb (Lv x₀) X → ∀ {a x} → Sim T a x → Emb (Lv (ls x)) X ⊎ ⊤ →
         ∀ {W} → LgW L₀ W → HB X → (r₀ : StH W a a₀) → Br r₀ → HB X
wrS    : ∀ {a x} → Sim T a x → ∀ {W} → HB (Lv x) → D a W
wrK    : ∀ {a x} → Sim T a x → ∀ {a′ x′} → Sim T a′ x′ → (∀ {W k} → StH W k a′ → StH W k a) →
         (κ : K (Lv x′)) → (∀ {W} → E (Lv x′) κ → D a W) → ∀ {W} → D a W

readS σ Em lW b n0 = b
readS σ Em lW b n1 = hs b
readS σ Em lW b (x ⨾ y) = readS σ Em lW (readS σ Em lW b x) y
readS σ Em lW b (nl d) = hl (readSp σ Em lW b d)
readS σ Em lW b (ni r u) = rdN σ Em lW b r u
readS σ Em lW b (nc κ z u) = readS σ Em lW b (u ≤rf lW)
readS σ Em lW b (nw p x) = readS σ Em (lgDn L₀ p lW) b x
readSp σ Em lW b d zero = b
readSp σ Em lW b d (suc n) = readS σ Em lW (readSp σ Em lW b d n) (d n)

rdN (ss σ₁) Em lW b (ss P) u = rdP (ss σ₁) Em σ₁ (Em ∘E stepE) (inj₁ Em) lW b (ss P) u P
rdN (sl σf) Em lW b (sl n P) u = rdP (sl σf) Em (σf n) (Em ∘E supE n) (inj₂ tt) lW b (sl n P) u P
rdN (sΩ cv′ σg) Em lW b (sL {c = e} bd P) u = rdP (sΩ cv′ σg) Em (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b (sL bd P) u P

rdP σ₀ E₀ σ Em m lW b r₀ u hself = slf σ₀ E₀ σ m lW b r₀ u
rdP σ₀ E₀ (ss σ₁) Em m lW b r₀ u (hsuc P) = rdP σ₀ E₀ σ₁ (Em ∘E stepE) (inj₁ Em) lW b r₀ u P
rdP σ₀ E₀ (sl σf) Em m lW b r₀ u (hlim n P) = rdP σ₀ E₀ (σf n) (Em ∘E supE n) (inj₂ tt) lW b r₀ u P
rdP σ₀ E₀ (sΩ cv′ σg) Em m lW b r₀ u (hLim {c = e} bd P) = rdP σ₀ E₀ (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b r₀ u P

slf σ₀ E₀ σ (inj₁ Ep) lW b r₀ u =
  hΩ (j Ep (inj₂ tt)) (λ e → nbJ (Ep ∘E stepE) b (λ y h → readS σ₀ E₀ lW h (u ≤rf lW (inS r₀ (wrS σ y)))) (cv Ep e))
slf σ₀ E₀ σ (inj₂ _) lW b r₀ u = readS σ₀ E₀ lW b (u ≤rf lW (inS r₀ n0))

wrS σ hz = n0
wrS σ (hs y) = wrS σ y ⨾ n1
wrS σ (hl f) = nl (λ n → wrS σ (f n))
wrS σ (hΩ κ g) = wrK σ σ (λ R → R) κ (λ e → wrS σ (g e))

wrK σ sz pre (() , _) g
wrK σ (ss σ₁) pre (inj₂ tt) g = ni (pre (ss hself)) (λ q lW′ v → g (readS σ₁ idE lW′ hz (outS (pre (ss hself)) v)))
wrK σ (ss σ₁) pre (inj₁ κ) g = wrK σ σ₁ (λ R → pre (ss (S→⊲ R))) κ g
wrK σ (sl σf) pre (n , κ) g = wrK σ (σf n) (λ R → pre (sl n (S→⊲ R))) κ g
wrK σ (sΩ {k = k} {g = g′} cv′ σg) pre κ g = g (bot (Lv (lΩ k g′)) κ)
```

## §2 起点是第一位置

```agda
readS-fst  : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) {W} (lW : LgW L₀ W) b (x : D a W) {w} → b ⊲[ w ] readS σ Em lW b x
rdN-fst    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) {w} →
             b ⊲[ w ] rdN σ₀ E₀ lW b r₀ u
rdP-fst    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {a x} (σ : Sim T a x) (Em : Emb (Lv x) X) (m : Emb (Lv (ls x)) X ⊎ ⊤)
             {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) (P : k ⊲[ W ] a) {w} → b ⊲[ w ] rdP σ₀ E₀ σ Em m lW b r₀ u P
slf-fst    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {a x} (σ : Sim T a x) (m : Emb (Lv (ls x)) X ⊎ ⊤)
             {W} (lW : LgW L₀ W) b (r₀ : StH W a a₀) (u : Br r₀) {w} → b ⊲[ w ] slf σ₀ E₀ σ m lW b r₀ u
readS-fst σ Em lW b n0 = hself
readS-fst σ Em lW b n1 = hsuc hself
readS-fst σ Em lW b (x ⨾ y) = ⊲ᴮ-tr (readS-fst σ Em lW b x) (readS-fst σ Em lW (readS σ Em lW b x) y)
readS-fst σ Em lW b (nl d) = hlim 0 hself
readS-fst σ Em lW b (ni r u) = rdN-fst σ Em lW b r u
readS-fst σ Em lW b (nc κ z u) = readS-fst σ Em lW b (u ≤rf lW)
readS-fst σ Em lW b (nw p x) = readS-fst σ Em (lgDn L₀ p lW) b x

rdN-fst (ss σ₁) Em lW b (ss P) u = rdP-fst (ss σ₁) Em σ₁ (Em ∘E stepE) (inj₁ Em) lW b (ss P) u P
rdN-fst (sl σf) Em lW b (sl n P) u = rdP-fst (sl σf) Em (σf n) (Em ∘E supE n) (inj₂ tt) lW b (sl n P) u P
rdN-fst (sΩ cv′ σg) Em lW b (sL {c = e} bd P) u = rdP-fst (sΩ cv′ σg) Em (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b (sL bd P) u P

rdP-fst σ₀ E₀ σ Em m lW b r₀ u hself = slf-fst σ₀ E₀ σ m lW b r₀ u
rdP-fst σ₀ E₀ (ss σ₁) Em m lW b r₀ u (hsuc P) = rdP-fst σ₀ E₀ σ₁ (Em ∘E stepE) (inj₁ Em) lW b r₀ u P
rdP-fst σ₀ E₀ (sl σf) Em m lW b r₀ u (hlim n P) = rdP-fst σ₀ E₀ (σf n) (Em ∘E supE n) (inj₂ tt) lW b r₀ u P
rdP-fst σ₀ E₀ (sΩ cv′ σg) Em m lW b r₀ u (hLim {c = e} bd P) = rdP-fst σ₀ E₀ (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b r₀ u P

slf-fst σ₀ {X = X} E₀ σ (inj₁ Ep) lW b r₀ u {w} =
  hLim (botBd X (j Ep (inj₂ tt)) w)
    (nbJ-fst (Ep ∘E stepE) (λ y h → readS-fst σ₀ E₀ lW h (u ≤rf lW (inS r₀ (wrS σ y)))) (cv Ep (bot X (j Ep (inj₂ tt)))))
slf-fst σ₀ E₀ σ (inj₂ _) lW b r₀ u = readS-fst σ₀ E₀ lW b (u ≤rf lW (inS r₀ n0))
```

## §3 合法由形状给出

```agda
Lg-readS  : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) {W} (lW : LgW L₀ W) b (x : D a W) → LgB b → LgB (readS σ Em lW b x)
Lg-readSp : ∀ {a x} (σ : Sim T a x) {X} (Em : Emb (Lv x) X) {W} (lW : LgW L₀ W) b (d : ℕ → D a W) → LgB b → ∀ n → LgB (readSp σ Em lW b d n)
Lg-rdN    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) →
            LgB b → LgB (rdN σ₀ E₀ lW b r₀ u)
Lg-rdP    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {a x} (σ : Sim T a x) (Em : Emb (Lv x) X) (m : Emb (Lv (ls x)) X ⊎ ⊤)
            {W k} (lW : LgW L₀ W) b (r₀ : StH W k a₀) (u : Br r₀) (P : k ⊲[ W ] a) → LgB b → LgB (rdP σ₀ E₀ σ Em m lW b r₀ u P)
Lg-slf    : ∀ {a₀ x₀} (σ₀ : Sim T a₀ x₀) {X} (E₀ : Emb (Lv x₀) X) {a x} (σ : Sim T a x) (m : Emb (Lv (ls x)) X ⊎ ⊤)
            {W} (lW : LgW L₀ W) b (r₀ : StH W a a₀) (u : Br r₀) → LgB b → LgB (slf σ₀ E₀ σ m lW b r₀ u)
Lg-readS σ Em lW b n0 l = l
Lg-readS σ Em lW b n1 l = l
Lg-readS σ Em lW b (x ⨾ y) l = Lg-readS σ Em lW (readS σ Em lW b x) y (Lg-readS σ Em lW b x l)
Lg-readS σ Em lW b (nl d) l = (λ n → readS-fst σ Em lW (readSp σ Em lW b d n) (d n)) , Lg-readSp σ Em lW b d l
Lg-readS σ Em lW b (ni r u) l = Lg-rdN σ Em lW b r u l
Lg-readS σ Em lW b (nc κ z u) l = Lg-readS σ Em lW b (u ≤rf lW) l
Lg-readS σ Em lW b (nw p x) l = Lg-readS σ Em (lgDn L₀ p lW) b x l
Lg-readSp σ Em lW b d l zero = l
Lg-readSp σ Em lW b d l (suc n) = Lg-readS σ Em lW (readSp σ Em lW b d n) (d n) (Lg-readSp σ Em lW b d l n)

Lg-rdN (ss σ₁) Em lW b (ss P) u l = Lg-rdP (ss σ₁) Em σ₁ (Em ∘E stepE) (inj₁ Em) lW b (ss P) u P l
Lg-rdN (sl σf) Em lW b (sl n P) u l = Lg-rdP (sl σf) Em (σf n) (Em ∘E supE n) (inj₂ tt) lW b (sl n P) u P l
Lg-rdN (sΩ cv′ σg) Em lW b (sL {c = e} bd P) u l = Lg-rdP (sΩ cv′ σg) Em (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b (sL bd P) u P l

Lg-rdP σ₀ E₀ σ Em m lW b r₀ u hself l = Lg-slf σ₀ E₀ σ m lW b r₀ u l
Lg-rdP σ₀ E₀ (ss σ₁) Em m lW b r₀ u (hsuc P) l = Lg-rdP σ₀ E₀ σ₁ (Em ∘E stepE) (inj₁ Em) lW b r₀ u P l
Lg-rdP σ₀ E₀ (sl σf) Em m lW b r₀ u (hlim n P) l = Lg-rdP σ₀ E₀ (σf n) (Em ∘E supE n) (inj₂ tt) lW b r₀ u P l
Lg-rdP σ₀ E₀ (sΩ cv′ σg) Em m lW b r₀ u (hLim {c = e} bd P) l = Lg-rdP σ₀ E₀ (σg e) (Em ∘E supE (inj₂ (cv′ e))) (inj₂ tt) lW b r₀ u P l

Lg-slf σ₀ E₀ σ (inj₁ Ep) lW b r₀ u l =
  (λ lw e e′ p → nbJ-mono (Ep ∘E stepE) fs (pr→ Ep p)) ,
  (λ {w} {c} lw e → Lg-nbJ (Ep ∘E stepE) fs l (λ y h lh → Lg-readS σ₀ E₀ lW h _ lh) (cv Ep c)
     (lgB⊲ (bd→ Ep e) (proj₁ (lgπ Ep lw)) (proj₂ (lgπ Ep lw))))
  where
  fs : ∀ y h {w} → h ⊲[ w ] readS σ₀ E₀ lW h (u ≤rf lW (inS r₀ (wrS σ y)))
  fs y h = readS-fst σ₀ E₀ lW h (u ≤rf lW (inS r₀ (wrS σ y)))
Lg-slf σ₀ E₀ σ (inj₂ _) lW b r₀ u l = Lg-readS σ₀ E₀ lW b (u ≤rf lW (inS r₀ n0)) l
```
