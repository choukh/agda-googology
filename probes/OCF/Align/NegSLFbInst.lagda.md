# `SL` 上带证据的回灌, 否定一路 (五): 对构造一路实例的检查

> 不含记号. 入口 [NegSLFb](NegSLFb.lagda.md). 只读导入构造一路的 [SLFbTm](SLFbTm.lagda.md), [SLFbKit](SLFbKit.lagda.md), [SLFbRd](SLFbRd.lagda.md) (20:08–20:13 版), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> 任务第 2 条要查三件事: 每站种类是否真的回灌; 深种类是否仍有损; 回灌是否只是一份共享的界. 结果 (都是定理):
>
> - **每站头种类有自己的精确升界, 不共享** (构造一路 `headFb`, `head-rs-top`); 升第 1 站的头不动第 3 站的分量 (`rs1-other`). 回灌**不是**一份共享的界: 站号在 $\mathbb N$ 上点更新.
> - **但第 $n\ge1$ 站的头读回的值只含第 0 层种类的 $\Omega$-结点.** 头种类 $(n,\mathrm{new})$ 的坐标是第 $k_n$ 层的值 `HB (Lv kₙ)` (第 $n\ge2$ 站的层号含函数, 这一层很大), 读回 `SLFbRd.rdQ` 产出的高度里每个 $\Omega$-结点都是同一个种类 `κa a` (`onlyA-rdQ`, `head-rd-onlyA`), 而这个种类的级是 `lz` (`akV-lz`, `head-ak-lz`: 对一切 $m$, 第 $m+1$ 站选的可读成 `A` 的种类的级是第 0 层). 起点满足时 (基世界的顶是 $0$, `SLFbTm.top-baseN`), 喂给头种类的值里没有级 $\ge1$ 的种类 (判断: 由这两条定理加 "折叠只把读回值写进头种类的界" 得出, 后者没有写成定理).
> - **同级的拷贝有损, 头的回灌不传给它.** 第 3 站的层里有一个种类 `cp1`, 级与坐标类型都和第 1 站的头相同 (`cp1-lvl`, `cp1-coord`, `SL` 里是不同的种类 `cp1≢head1`), 它没有回灌 (`cp1-lossy`), 升第 1 站的头不动它的界 (`cp1-not-moved`), 而头自己的界变成 $v$ (`head1-moved`). 这是 `NegStratTwDeep.no-wmatch-cp` 的情形在 `SN` 上的一个具体见证.
>
> **只说明什么.** 本篇不否定构造一路的闭项 `TF` (合法, 有 FGH), 不否定 `SNᵢ` 这条出口. 它划出 `TF` 的回灌**实际**喂进去的东西: 头种类有, 内容只含第 0 层的结点; 经坐标下标的深种类 (含头种类的同级拷贝) 没有. 值的高低没有定理 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSLFbInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (GenK; LgDn; top; _⨾_; n0; n1; nl; ni; nc; nw; ss)
open import OCF.Align.GenFoldTree using (module Tree)
import OCF.Align.KindLvIf as KI
open import OCF.Align.LFReTy
open import OCF.Align.SLFbIf using (AK; κa; fr; jN)
open import OCF.Align.FabLFReGen using (LvΩ)
open import OCF.Align.SLFbKit using (akV; akSt; akNew; akOld; akSup; mapS)
open import OCF.Align.SLFbTm using (kₙ; SN; tpN; GN; LdN; KH; KH₁; KHn; lvN; akV-suc; head-rs-top)
open import OCF.Align.NewTwrObs using (OnlyA; oz; os; ol; oΩ)
```

## §1 读回 `rdQ` 只产出一个种类的 $\Omega$-结点

与 `NewTwrObs.onlyA-rd₁` 逐行同形, 目标换成任一 $Q$ 与它的可读成 `A` 的种类 `κa ak`.

```agda
module RdOnlyQ (T : KS) (G : GenK T) (Ld : LgDn T) {Q : KS} (ak : AK Q) where
  open Tree T
  open import OCF.Align.GenFoldRd T G Ld using (lgW≤; module NbA)
  open NbA
  open import OCF.Align.SLFbRd T G Ld ak using (rdQ; rdpQ)

  OQ : HB Q → Set
  OQ = OnlyA {Q} (κa ak)

  onlyA-nbQ : ∀ {b : HB Q} {s : A → HB Q → HB Q} → OQ b → (∀ c h → OQ h → OQ (s c h)) → ∀ c → OQ (nbA b s c)
  onlyA-nbQ ob os′ azero = ob
  onlyA-nbQ ob os′ (asuc c) = os′ c _ (onlyA-nbQ ob os′ c)
  onlyA-nbQ ob os′ (alim f) = ol (λ n → onlyA-nbQ ob os′ (f n))

  onlyA-rdQ  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → OQ b → OQ (rdQ lW b x)
  onlyA-rdpQ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → OQ b → ∀ n → OQ (rdpQ lW b d n)
  onlyA-rdQ lW b n0 ob = ob
  onlyA-rdQ lW b n1 ob = os ob
  onlyA-rdQ lW b (x ⨾ y) ob = onlyA-rdQ lW (rdQ lW b x) y (onlyA-rdQ lW b x ob)
  onlyA-rdQ lW b (nl d) ob = ol (onlyA-rdpQ lW b d ob)
  onlyA-rdQ lW b (ni (ss hself) u) ob =
    oΩ (λ e → onlyA-nbQ ob (λ c h oh → onlyA-rdQ lW h (u ≤rf lW (toD₀ c)) oh) (fr ak e))
  onlyA-rdQ lW b (nc (inj₁ κ) z u) ob = onlyA-rdQ lW b (u ≤rf lW) ob
  onlyA-rdQ lW b (nc (inj₂ _) () u) ob
  onlyA-rdQ lW b (nw p x) ob = onlyA-rdQ (lgW≤ p lW) b x ob
  onlyA-rdpQ lW b d ob zero = ob
  onlyA-rdpQ lW b d ob (suc n) = onlyA-rdQ lW (rdpQ lW b d n) (d n) (onlyA-rdpQ lW b d ob n)
```

**在 `SN` 上: 头种类级层 $1$ 的读回.** `KH₁ n a` 的 `rd` 字面就是 `rdQ`.

```agda
head-rd-onlyA : ∀ n (a : AK (Lv (kₙ n))) {W} (lW : LgW (step SN) W) b x →
  OnlyA {Lv (kₙ n)} (κa a) b → OnlyA {Lv (kₙ n)} (κa a) (KI.rd (KH₁ n a) lW b x)
head-rd-onlyA n a lW b x ob = RdOnlyQ.onlyA-rdQ SN GN LdN a lW b x ob
```

## §2 选出的可读成 `A` 的种类的级是第 0 层

`lvlSt k`: `step (Lv k)` 的种类的级 (旧种类按 `lvl k`, 新种类是 $k$). 对 `akV`, `akSt` 的定义互递归.

```agda
lvlSt : (k : LH) → K (step (Lv k)) → LH
lvlSt k (inj₁ κ) = lvl k κ
lvlSt k (inj₂ _) = k

lvl-ls : ∀ x κ → lvl (ls x) κ ≡ lvlSt x κ
lvl-ls x (inj₁ κ) = refl
lvl-ls x (inj₂ _) = refl

lvl-Ω : ∀ k g κ → lvl (lΩ k g) (inj₁ tt , κ) ≡ lvlSt k κ
lvl-Ω k g (inj₁ κ) = refl
lvl-Ω k g (inj₂ _) = refl

OnS : ∀ {X : Set} → (X → Set) → X ⊎ ⊤ → Set
OnS P (inj₁ x) = P x
OnS P (inj₂ _) = ⊤

onS-map : ∀ {X : Set} {P Q : X → Set} → (∀ x → P x → Q x) → ∀ s → OnS P s → OnS Q s
onS-map h (inj₁ x) p = h x p
onS-map h (inj₂ _) p = tt

mapP : ∀ {X Y : Set} (f : X → Y) {P : X → Set} {Q : Y → Set} → (∀ x → P x → Q (f x)) → ∀ s → OnS P s → OnS Q (mapS f s)
mapP f h (inj₁ x) p = h x p
mapP f h (inj₂ _) p = tt

akV-lz : ∀ k → OnS (λ a → lvl k (κa a) ≡ lz) (akV k)
akSt-lz : ∀ k → OnS (λ a → lvlSt k (κa a) ≡ lz) (akSt k)
akV-lz lz = tt
akV-lz (ls x) = onS-map (λ a p → trans (lvl-ls x (κa a)) p) (akSt x) (akSt-lz x)
akV-lz (ll f) = mapP (akSup {F = λ n → Lv (f n)} 0) (λ a p → p) (akV (f 0)) (akV-lz (f 0))
akV-lz (lΩ k g) = mapP (akSup {F = LvΩ k g} (inj₁ tt)) (λ a p → trans (lvl-Ω k g (κa a)) p) (akSt k) (akSt-lz k)
akSt-lz lz = refl
akSt-lz (ls x) = mapP akOld (λ a p → p) (akV (ls x)) (akV-lz (ls x))
akSt-lz (ll f) = mapP akOld (λ a p → p) (akV (ll f)) (akV-lz (ll f))
akSt-lz (lΩ k g) = mapP akOld (λ a p → p) (akV (lΩ k g)) (akV-lz (lΩ k g))

-- 第 m+1 站: 头种类的 KLv 就是 KH₁ 用一个级为 lz 的种类
head-ak-lz : ∀ m → Σ (AK (Lv (kₙ (suc m)))) (λ a →
  (KHn (suc m) ≡ KH₁ (suc m) a) × (lvl (kₙ (suc m)) (κa a) ≡ lz))
head-ak-lz m = proj₁ (akV-suc m) , cong (KH (suc m)) (proj₂ (akV-suc m)) ,
  subst (OnS (λ a → lvl (kₙ (suc m)) (κa a) ≡ lz)) (proj₂ (akV-suc m)) (akV-lz (kₙ (suc m)))
```

## §3 同级的拷贝: 第 3 站层里第 1 站头的拷贝

第 3 站的层号 `kₙ 3 = lΩ lz g₃`, 坐标 $1$ 处的分支层号是 `lΩ (ls lz) _`, 它的左分量 `step (Lv (ls lz))` 的新种类级是 `ls lz = kₙ 1`.

```agda
cp1 : K SN
cp1 = 3 , inj₁ (inj₂ (hs hz) , inj₁ tt , inj₂ tt)

head1 : K SN
head1 = 1 , inj₂ tt

cp1-lvl : rbl (jN {kₙ} cp1) ≡ kₙ 1
cp1-lvl = refl

head1-lvl : rbl (jN {kₙ} head1) ≡ kₙ 1
head1-lvl = refl

cp1-coord : E SN cp1 ≡ E SN head1
cp1-coord = refl

cp1≢head1 : ¬ (jN {kₙ} cp1 ≡ jN {kₙ} head1)
cp1≢head1 ()

cp1-lossy : lvN cp1 ≡ inj₂ tt
cp1-lossy = refl

cp1-not-moved : ∀ w v → top tpN cp1 (KI.rs (KHn 1) w v) ≡ top tpN cp1 w
cp1-not-moved w v = refl

head1-moved : ∀ w v → top tpN head1 (KI.rs (KHn 1) w v) ≡ v
head1-moved w v = head-rs-top 1 w v

-- 升第 1 站的头不动第 3 站的分量 (站号在 ℕ 上点更新)
rs1-other : ∀ w v → KI.rs (KHn 1) w v 3 ≡ w 3
rs1-other w v = refl
```

## §4 结论 (按档)

- **[定理]** **`onlyA-rdQ`** (对一切 `T`, `G`, `Ld`, `Q`, `ak`), **`head-rd-onlyA`**; **`akV-lz`**, `akSt-lz` (`OnS`, `onS-map`, `mapP`), **`head-ak-lz`** (对一切 $m$, 第 $m+1$ 站头种类的 `KLv` 是 `KH₁` 配一个级为 `lz` 的种类).
- **[定理]** `cp1-lvl`, `head1-lvl`, `cp1-coord`, `cp1≢head1`, **`cp1-lossy`**, **`cp1-not-moved`**, `head1-moved`, `rs1-other`.
- **[判断]** 起点为 $0$ 时, 折叠喂给头种类的值只含第 0 层种类的结点 (要把 "折叠只把读回值写进界" 写成对 `KindLvRun` 的定理才算定理; 未写). 经坐标下标的深种类中, 头种类的同级拷贝不止 `cp1` 一个 (每个以后的站都有; 只验了一个). 值的高低没有定理.
