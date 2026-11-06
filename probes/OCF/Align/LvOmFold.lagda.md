# Ω-极限坐标上的读回包 (四): 一级回灌以 Ω-极限层号为读回目标, 最小实例 `ΩA`

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 依赖 [LvOmLev](LvOmLev.lagda.md), [LvOmRd](LvOmRd.lagda.md); 只读导入 `HtTowerCont.Ωtop`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **一级回灌 `F1 a la c`.** 坐标 $c$ (任意 `H₀`, 可含 $\Omega$-结点), 外层世界 $a$ (合法). 一个槽, 类型 `HB (Lv a c)`. 折叠 `fold v Λ` 把 `step (Lv a c)` 的高度折成第 `Ly c` 层的树, 只在 $a$ 之上的世界给出 (`Out = (W : Wd₂) → a ⊲ proj₁ W → D (Ly c) W`): 旧种类经 `trK (pk c)` 翻译; 新种类的结点是世界链上的 ℕ-极限, 链的每一步把**折叠自己输出的读回** (`lay`, 读在世界 $(a,0)$ 上, 读回目标正是层号 $c$ 的层结构) 加到槽上. 形状定理 `fold-Ω`, `ch-s`, `lay-is` 都是 `refl`; 链合法且只增 (`ch-lg`, `ch-≤`).
>
> 与 `LvRdFold.GF` 的差别 (都是 R1 逼出的): 输出只在 $a\lhd W_A$ 的世界上给 (外层世界 $a\ne0$ 时, 对一切世界给就要 `no-unifΩ` 否定的证据, 见 `LvOmNeg`); 槽类型是 `Lv a c` 而不是接口的码槽 `Pc k` (接口 `LvRdIf.Pc` 只到外层界 $\omega+1$). 增量取读回本身, 不经 `LvRdFold.δF` 的 "底 1 读回 $\Omega_{L\boxplus h}$" (那一步要 `Lv a c` 到 `Ht` 的下降, 一般坐标上没有写).
>
> **最小实例.** $\mathrm{ΩA}=\mathrm{h\Omega}\,(x\mapsto\ulcorner x\urcorner)$: `A` 的元素原样当作高度的 $\Omega$-结点 (`HtTowerCont.Ωtop S₀` 那一种的 `H₀` 版; 读法 $\Omega_1$ 当作层号, 判断). 合法 (`Lg-ΩA`). 外层世界 $\omega$ (`ωA`, 合法). 闭项 `HΩ : HB (Lv ωA ΩA)`: 级顶 `Ωtop (Lv ωA ΩA)` 经一级回灌折叠, 在 $(\omega,0)$ 上读回; 合法 (`Lg-HΩ`), 无参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (H₀; Ht; Wd₂; LgW₂; D; n0; n1; _⨾_; nl)
open import OCF.Align.LvOmLev
open import OCF.Align.LvOmRd
```

## §1 一级回灌

```agda
module F1 (a : A) (la : Lg a) (c : H₀) where
  open Rd a

  Out : Set
  Out = (W : Wd₂) → a ⊲ proj₁ W → D (Ly c) W

  W⋆ : Wd₂
  W⋆ = a , hz

  lW⋆ : LgW₂ W⋆
  lW⋆ = la , tt

  -- 读回: 输出在 (a, 0) 上读成层号 c 的层结构的高度
  lay : Out → HB (Lv c)
  lay o = rdc (pk c) W⋆ (C.self , hself) lW⋆ C.self hz (o W⋆ C.self)

  Lg-lay : ∀ o → LgB (lay o)
  Lg-lay o = lgc (pk c) W⋆ (C.self , hself) lW⋆ C.self hz (o W⋆ C.self) tt

  ch : (HB (Lv c) → Out) → HB (Lv c) → ℕ → HB (Lv c)
  ch Fo v zero = v
  ch Fo v (suc k) = ch Fo v k ⊞ lay (Fo (ch Fo v k))

  fold : HB (Lv c) → HB (step (Lv c)) → Out
  fold v hz W i = n0
  fold v (hs x) W i = fold v x W i ⨾ n1
  fold v (hl f) W i = nl (λ k → fold v (f k) W i)
  fold v (hΩ (inj₁ κ) g) W i = trK (pk c) κ (λ _ → hself) (λ e W′ i′ → fold v (g e) W′ i′) W i
  fold v (hΩ (inj₂ tt) g) W i =
    nl (λ k → fold (ch (λ u → fold u (g u)) v k) (g (ch (λ u → fold u (g u)) v k)) W i)

  chain : HB (Lv c) → (HB (Lv c) → HB (step (Lv c))) → ℕ → HB (Lv c)
  chain v g = ch (λ u → fold u (g u)) v

  -- 形状定理
  fold-Ω : ∀ v g W i → fold v (hΩ (inj₂ tt) g) W i ≡ nl (λ k → fold (chain v g k) (g (chain v g k)) W i)
  fold-Ω v g W i = refl

  ch-s : ∀ v g k → chain v g (suc k) ≡ chain v g k ⊞ lay (fold (chain v g k) (g (chain v g k)))
  ch-s v g k = refl

  lay-is : ∀ o → lay o ≡ rdc (pk c) W⋆ (C.self , hself) lW⋆ C.self hz (o W⋆ C.self)
  lay-is o = refl

  fold-old : ∀ v κ g W i → fold v (hΩ (inj₁ κ) g) W i ≡ trK (pk c) κ (λ _ → hself) (λ e W′ i′ → fold v (g e) W′ i′) W i
  fold-old v κ g W i = refl

  ch-lg : ∀ v g → LgB v → ∀ k → LgB (chain v g k)
  ch-lg v g lv zero = lv
  ch-lg v g lv (suc k) = Lg-⊞ (chain v g k) _ (ch-lg v g lv k) (Lg-lay (fold (chain v g k) (g (chain v g k))))

  ch-≤ : ∀ v g k {w} → chain v g k ⊲[ w ] chain v g (suc k)
  ch-≤ v g k = ⊞-fst (chain v g k) _

  -- 级顶经一级回灌的读回
  top : HB (Lv c)
  top = lay (fold hz (Ωtop (Lv c)))

  Lg-top : LgB top
  Lg-top = Lg-lay (fold hz (Ωtop (Lv c)))
```

## §2 最小实例: 层号 ΩA, 外层世界 ω

```agda
hA₀ : A → H₀
hA₀ azero = hz
hA₀ (asuc x) = hs (hA₀ x)
hA₀ (alim f) = hl (λ n → hA₀ (f n))

hA₀-mono : ∀ {x y : A} {w : A} → x ⊲ y → hA₀ x ⊲[ w ] hA₀ y
hA₀-mono C.self = hself
hA₀-mono (C.suc p) = hsuc (hA₀-mono p)
hA₀-mono (C.lim n p) = hlim n (hA₀-mono p)

lg-hA₀ : ∀ x → Lg x → LgB (hA₀ x)
lg-hA₀ azero l = tt
lg-hA₀ (asuc x) l = lg-hA₀ x l
lg-hA₀ (alim f) (st , l) = (λ n → hA₀-mono (st n)) , (λ n → lg-hA₀ (f n) (l n))

ΩA : H₀
ΩA = hΩ tt hA₀

Lg-ΩA : LgB ΩA
Lg-ΩA = (λ lw e e′ pr → hA₀-mono pr) , (λ x lx → lg-hA₀ x lx)

finA : ℕ → A
finA zero = azero
finA (suc n) = asuc (finA n)

ωA : A
ωA = alim finA

lg-finA : ∀ n → Lg (finA n)
lg-finA zero = tt
lg-finA (suc n) = lg-finA n

Lg-ωA : Lg ωA
Lg-ωA = (λ n → C.suc C.self) , lg-finA

-- 读回层是 Ω-极限
Ly-ΩA : Ly ΩA ≡ hΩ (inj₁ tt) (λ x → Ly (hA₀ x))
Ly-ΩA = refl

module IΩ = F1 ωA Lg-ωA ΩA

HΩ : HB (LvM.Lv ωA ΩA)
HΩ = IΩ.top

Lg-HΩ : LgB HΩ
Lg-HΩ = IΩ.Lg-top
```
