# 主线数据类型上的 View (一): 对一切层的骨架

> 不含记号. 入口 [MainView](MainView.lagda.md). 主线的数据树是 [HtFeedTree](HtFeedTree.lagda.md) 的 `D L = D₊ (StH · · L) (Vs L) (NZ L)`, 层 $L$ 是一棵高度. 这里**对一切层一条定义**: 参数是任意的 `D₊ Kd Vv Zz` (所以覆盖一切 $L$), 一个目标签名 `Sig` ([BrwViewDef](BrwViewDef.lagda.md)), 一个读法 `Sm q b y` ("$b$ 接着走 $y$", $y$ 沿 $q$ 抬到下标的世界), 九条方程 (和的五个构造子, 值与读法, 零, $\mathbb N$-极限, 第一位置), 合法性 `Lgl` 的七条结构律. 在这些之上:
>
> - `WithSeg.vw`, `WithSeg.view`: 和的五个构造子 (`n0`, `n1`, `⨾`, `nl`, `nw`) 的读法对一切层相同 (零/后继/$\mathbb N$-极限, 部分是前缀与部分和); 两种 $\Omega$-节点 (`ni`, `nκ`) 各是一个**段** (`SegI`, `SegK`), 作参数. 层与层之间只差这两个段.
> - `Dec.wf`: 部分良基, 也对一切层一条定义. 参数是值上的一个良基关系 (秩) 与它在后继、$\mathbb N$-极限上的两条, 加上两个段各自的下降.
>
> 方程写成 $\equiv$, 在第 0 层与第 1 层的实例里都是 `refl` (定义相等), 所以骨架在实例上计算成与 [BrwViewZero](BrwViewZero.lagda.md), [BrwViewOne](BrwViewOne.lagda.md) 同样的项 (第 0 层的 FGH 一致要用到这一点, 见 [MainViewZero](MainViewZero.lagda.md)). 只有 $\mathbb N$-极限的值一条是 $\approx$ (部分和与 `pt` 逐点相等, 不用 `Funext`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainViewGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; D₊; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwWfDef using (Obj; Part; p-s; p-l; p-Ω; _◁_; BrwViewᵂ; measure)
```

## §1 部分和

```agda
module _ {Kd : A → H → Set} {Vv : ∀ {W k} → Kd W k → A → Set} {Zz : Set} where
  ps : ∀ {W} → (ℕ → D₊ Kd Vv Zz W) → ℕ → D₊ Kd Vv Zz W
  ps d zero = n0
  ps d (suc n) = ps d n ⨾ d n
```

## §2 骨架的参数

读法 `Sm {i} q b y`: 下标 $i$ (它的世界是 `wd i`), 底 $b$, 加数 $y$ 在世界 $W_0$ 里, 沿 $q:W_0\lhd$ `wd i` 抬上来. `val x` 是对象的值. 方程: 和的五个构造子各一条, 值与读法的两条 (`e-val`: 前缀接上抬升的 $y$ 的值就是从前缀的值接着读 $y$; `e-top`), 零的值, $\mathbb N$-极限的值 (`e-nl`), 第一位置 (`fst`, 目标树自己的合法性里那一条).

```agda
module Skel {Nd : A → H → Set} {Vv : ∀ {W k} → Nd W k → A → Set} {Zz : Set}
  (Sg : Sig) (open Sig Sg)
  (wd   : Ix → A)
  (val  : ∀ {i} → D₊ Nd Vv Zz (wd i) → B i)
  (Lgl  : ∀ {W} → D₊ Nd Vv Zz W → Set)
  (Sm   : ∀ {i W₀} → W₀ ⊲ wd i → B i → D₊ Nd Vv Zz W₀ → B i)
  (≈-rf : ∀ {i} (a : B i) → a ≈ a)
  (e-n0 : ∀ {i W₀} (q : W₀ ⊲ wd i) b → Sm q b n0 ≡ b)
  (e-n1 : ∀ {i W₀} (q : W₀ ⊲ wd i) b → Sm q b n1 ≡ bs b)
  (e-⨾  : ∀ {i W₀} (q : W₀ ⊲ wd i) b y z → Sm q b (y ⨾ z) ≡ Sm q (Sm q b y) z)
  (e-nw : ∀ {i W₁ W₀} (r : W₁ ⊲ W₀) (q : W₀ ⊲ wd i) b y → Sm q b (nw r y) ≡ Sm (⊲-tr r q) b y)
  (e-val : ∀ {i} (x : D₊ Nd Vv Zz (wd i)) {W₀} (q : W₀ ⊲ wd i) y → val (x ⨾ nw q y) ≡ Sm q (val x) y)
  (e-top : ∀ {i} (x : D₊ Nd Vv Zz (wd i)) → val x ≡ Sm C.self (val (n0 {W = wd i})) x)
  (e-0  : ∀ {i} → val (n0 {W = wd i}) ≈ bz)
  (e-nl : ∀ {i} (x : D₊ Nd Vv Zz (wd i)) {W₀} (q : W₀ ⊲ wd i) d → Sm q (val x) (nl d) ≈ bl (λ n → val (x ⨾ nw q (ps d n))))
  (fst  : ∀ {i W₀} (q : W₀ ⊲ wd i) b y → Stp b (Sm q b y))
  (L-n0 : ∀ {W} → Lgl (n0 {W = W}))
  (L-⨾  : ∀ {W} {x y : D₊ Nd Vv Zz W} → Lgl x → Lgl y → Lgl (x ⨾ y))
  (L-⨾₁ : ∀ {W} {x y : D₊ Nd Vv Zz W} → Lgl (x ⨾ y) → Lgl x)
  (L-⨾₂ : ∀ {W} {x y : D₊ Nd Vv Zz W} → Lgl (x ⨾ y) → Lgl y)
  (L-nl : ∀ {W} {d : ℕ → D₊ Nd Vv Zz W} → Lgl (nl d) → ∀ n → Lgl (d n))
  (L-nw : ∀ {W₀ W} {p : W₀ ⊲ W} {y : D₊ Nd Vv Zz W₀} → Lgl (nw p y) → Lgl y)
  (L-nwI : ∀ {W₀ W} {p : W₀ ⊲ W} {y : D₊ Nd Vv Zz W₀} → Lgl y → Lgl (nw p y))
  where

  Dt : A → Set
  Dt = D₊ Nd Vv Zz

  X : Ix → Set
  X i = Dt (wd i)

  Lgx : ∀ {i} → X i → Set
  Lgx x = Lgl x

  V : (i : Ix) → B i → Set
  V = View Sg X val Lgx

  Pt : ∀ {i v} → V i v → Obj Sg X val Lgx → Set
  Pt = Part Sg X val Lgx

  L-ps : ∀ {W} (d : ℕ → Dt W) → (∀ n → Lgl (d n)) → ∀ n → Lgl (ps d n)
  L-ps d h zero = L-n0
  L-ps d h (suc n) = L-⨾ (L-ps d h n) (h n)
```

## §3 两个段

`SegI`: 前缀 $x$ (带它的 View) 之后接一个 `ni` 节点 (沿 $q$ 抬升), 给出整体的 View. `SegK` 同, 对 `nκ`. **层与层之间只差这两个类型的居民.**

```agda
  SegI : Set
  SegI = ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀ k} (q : W₀ ⊲ wd i) (r : Nd W₀ k) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vv r W′ → Dt W′) →
         Lgl (ni r u) → V i (Sm q (val x) (ni r u))

  SegK : Set
  SegK = ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀} (q : W₀ ⊲ wd i) (zz : Zz) (u : ∀ {c} → W₀ ⊲ c → Lg c → Dt c) →
         Lgl (nκ zz u) → V i (Sm q (val x) (nκ zz u))
```

## §4 读法, 对一切层

方程的名字单独写出, 下降的证明 (§5) 要引用同一个项.

```agda
  E⨾ : ∀ {i} (x : X i) {W₀} (q : W₀ ⊲ wd i) (y₁ y₂ : Dt W₀) → Sm q (val (x ⨾ nw q y₁)) y₂ ≡ Sm q (val x) (y₁ ⨾ y₂)
  E⨾ x q y₁ y₂ = trans (cong (λ b → Sm q b y₂) (e-val x q y₁)) (sym (e-⨾ q (val x) y₁ y₂))

  Eps : ∀ {i} (x : X i) {W₀} (q : W₀ ⊲ wd i) (d : ℕ → Dt W₀) n →
        val (x ⨾ nw q (ps d (suc n))) ≡ Sm q (Sm q (val x) (ps d n)) (d n)
  Eps x q d n = trans (e-val x q (ps d n ⨾ d n)) (e-⨾ q (val x) (ps d n) (d n))

  module WithSeg (sgi : SegI) (sgk : SegK) where
    vw : ∀ {i} (x : X i) → Lgl x → V i (val x) → ∀ {W₀} (q : W₀ ⊲ wd i) (y : Dt W₀) → Lgl y → V i (Sm q (val x) y)
    vw {i} x hx vx q n0 hy = subst (V i) (sym (e-n0 q (val x))) vx
    vw {i} x hx vx q n1 hy = vs x hx (subst (λ v → v ≈ bs (val x)) (sym (e-n1 q (val x))) (≈-rf (bs (val x))))
    vw {i} x hx vx q (y₁ ⨾ y₂) hy =
      subst (V i) (E⨾ x q y₁ y₂)
        (vw (x ⨾ nw q y₁) (L-⨾ hx (L-nwI (L-⨾₁ hy))) (subst (V i) (sym (e-val x q y₁)) (vw x hx vx q y₁ (L-⨾₁ hy))) q y₂ (L-⨾₂ hy))
    vw {i} x hx vx q (nl d) hy =
      vl (λ n → x ⨾ nw q (ps d n)) (λ n → L-⨾ hx (L-nwI (L-ps d (L-nl hy) n)))
         (λ n → subst₂ Stp (sym (e-val x q (ps d n))) (sym (Eps x q d n)) (fst q (Sm q (val x) (ps d n)) (d n)))
         (e-nl x q d)
    vw {i} x hx vx q (nw r y) hy = subst (V i) (sym (e-nw r q (val x) y)) (vw x hx vx (⊲-tr r q) y (L-nw hy))
    vw x hx vx q (ni r u) hy = sgi x hx vx q r u hy
    vw x hx vx q (nκ zz u) hy = sgk x hx vx q zz u hy

    view : BrwView Sg X val Lgx
    view = record { view = λ {i} x lx → subst (V i) (sym (e-top x)) (vw n0 L-n0 (vz e-0) C.self x lx) }
```

## §5 部分的良基, 对一切层

秩 `rk` 是值上的度量, 关系 `_<ᵣ_` 良基. 要的: 后继的秩高于底 (`R-s`), $\mathbb N$-极限的秩高于每个部分 (`R-l`), 两个段的下降 (`D-i`, `D-κ`, 可以用前缀部分的下降). 证明与 `vw` 同形归纳.

```agda
    Pt-subst : ∀ {i v v′} (e : v ≡ v′) (w : V i v) {o} → Pt (subst (V i) e w) o → Pt w o
    Pt-subst refl w p = p

    module Dec (T : Set) (_<ᵣ_ : T → T → Set) (wfᵣ : WellFounded _<ᵣ_) (rk : ∀ {i} → B i → T)
      (R-s : ∀ {i} (b : B i) → rk b <ᵣ rk (bs b))
      (R-l : ∀ {i} (x : X i) {W₀} (q : W₀ ⊲ wd i) (d : ℕ → Dt W₀) n → rk (val (x ⨾ nw q (ps d n))) <ᵣ rk (Sm q (val x) (nl d)))
      (D-i : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀ k} (q : W₀ ⊲ wd i) (r : Nd W₀ k) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vv r W′ → Dt W′) (hy : Lgl (ni r u)) →
             (∀ {o} → Pt vx o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (val x)) →
             ∀ {o} → Pt (sgi x hx vx q r u hy) o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (Sm q (val x) (ni r u)))
      (D-κ : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀} (q : W₀ ⊲ wd i) (zz : Zz) (u : ∀ {c} → W₀ ⊲ c → Lg c → Dt c) (hy : Lgl (nκ zz u)) →
             (∀ {o} → Pt vx o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (val x)) →
             ∀ {o} → Pt (sgk x hx vx q zz u hy) o → rk (val (proj₁ (proj₂ o))) <ᵣ rk (Sm q (val x) (nκ zz u)))
      where

      rko : Obj Sg X val Lgx → T
      rko o = rk (val (proj₁ (proj₂ o)))

      ↑< : ∀ {i} {t : T} {b b′ : B i} → b ≡ b′ → t <ᵣ rk b → t <ᵣ rk b′
      ↑< e h = subst (λ v → _ <ᵣ rk v) e h

      dec : ∀ {i} (x : X i) (hx : Lgl x) (vx : V i (val x)) {W₀} (q : W₀ ⊲ wd i) (y : Dt W₀) (hy : Lgl y) →
            (∀ {o} → Pt vx o → rko o <ᵣ rk (val x)) →
            ∀ {o} → Pt (vw x hx vx q y hy) o → rko o <ᵣ rk (Sm q (val x) y)
      dec x hx vx q n0 hy H p = ↑< (sym (e-n0 q (val x))) (H (Pt-subst (sym (e-n0 q (val x))) vx p))
      dec x hx vx q n1 hy H p-s = ↑< (sym (e-n1 q (val x))) (R-s (val x))
      dec x hx vx q (y₁ ⨾ y₂) hy H p =
        ↑< (E⨾ x q y₁ y₂)
           (dec (x ⨾ nw q y₁) (L-⨾ hx (L-nwI (L-⨾₁ hy))) v₁′ q y₂ (L-⨾₂ hy)
                (λ p′ → ↑< (sym (e-val x q y₁)) (dec x hx vx q y₁ (L-⨾₁ hy) H (Pt-subst (sym (e-val x q y₁)) v₁ p′)))
                (Pt-subst (E⨾ x q y₁ y₂) _ p))
        where
        v₁ = vw x hx vx q y₁ (L-⨾₁ hy)
        v₁′ = subst (V _) (sym (e-val x q y₁)) v₁
      dec x hx vx q (nl d) hy H (p-l n) = R-l x q d n
      dec x hx vx q (nw r y) hy H p =
        ↑< (sym (e-nw r q (val x) y)) (dec x hx vx (⊲-tr r q) y (L-nw hy) H (Pt-subst (sym (e-nw r q (val x) y)) _ p))
      dec x hx vx q (ni r u) hy H p = D-i x hx vx q r u hy H p
      dec x hx vx q (nκ zz u) hy H p = D-κ x hx vx q zz u hy H p

      _◁ᴳ_ : Obj Sg X val Lgx → Obj Sg X val Lgx → Set
      _◁ᴳ_ = _◁_ Sg X val Lgx view

      dec-top : ∀ {o o′} → o′ ◁ᴳ o → rko o′ <ᵣ rko o
      dec-top {i , x , lx} p =
        ↑< (sym (e-top x)) (dec n0 L-n0 (vz e-0) C.self x lx (λ ()) (Pt-subst (sym (e-top x)) _ p))

      wf : WellFounded _◁ᴳ_
      wf = measure _◁ᴳ_ _<ᵣ_ rko wfᵣ dec-top

      viewᵂ : BrwViewᵂ Sg X val Lgx
      viewᵂ = record { bv = view ; wf = wf }
```

**读法.** 骨架里没有层号: 它对 `D₊ Nd Vv Zz` 的一切参数成立, 主线的每一层 `D L` 都是这个形状. 实例要给的只是: 读法 `Sm` (第 0 层是 `sum`, 第 1 层是 `LayerTrOne.S` 经 `π`), 方程 (实例里都是 `refl`, 除 `e-nl`), 以及两个段. 第 0 层没有节点, 两个段是空的 (`NZ hz = ⊥`, `StH W k hz` 空), 所以第 0 层的 View 与良基无条件.
