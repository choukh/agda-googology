# 分层互递归塔, 否定一路 (三): 对构造一路实例 `StratTwTw` 的检查

> 不含记号. 入口 [NegStratTw](NegStratTw.lagda.md). 只读导入构造一路的 [StratTwTw](StratTwTw.lagda.md) (19:20 版), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 问题 (任务原话): "是否每站头种类真的按级回灌, 是否仍只有有限个种类被回灌, 对角的结点是否被回灌". 结论 (定理):
>
> 1. **每站头种类按自己的级回灌** (`own-ok` 即构造一路的 `ownU`; `KT-rd`: 读回是沿同形的 `readS (sim s)`, 不是常数, `refl`). 对照 KindLv 的 `only-κ₁`: 那里只有一个.
> 2. **按级回灌的种类恰好是: 底种类 $(0,\mathrm{tt})$ 与一切头种类** (`fed-exactly`); **两两不同, 无穷多** (`hd-inj-U`, 由 [NegStratTwBlind](NegStratTwBlind.lagda.md) 的 `hd-inj`).
> 3. **分量 $\ge2$ 的深种类既没有级回灌, 也没有 A-回灌** (`deep-lossy`, `deep-noA`, `refl`): 从第 1 站起级 $X_{s+1}$ 的头是 $\Omega$-结点 (`X-head`), `Lev (X (s+1))` 是以坐标为下标的并, `genLev` 在那里给 `genSupNo` (一切有损). 分量 1 的深种类里只有底拷贝有 A-回灌 (`deep1-A`).
> 4. **对角的头结点被回灌, 深结点不** (`Y-head`, `refl`): $Y_{s+1}$ 的头是种类 `hd s` 的 $\Omega$-结点. $Y_{s+1}$ 里种类不是头种类、不是 $(0,\mathrm{tt})$ 的结点一律有损 (由 2, 3).
> 5. **起始世界里头种类的界是 $0$** (`start-hd`, `refl`).
>
> **只否定什么.** 只说 `StratTwTw` 这一实例的形状; 不说 `TS` 的值 (没有 `ord` 的比较), 不否定分层路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegStratTwInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (fbA; tpK; top; w₀)
open import OCF.Align.KindLvIf using (KLv; rd)
open import OCF.Align.StratTwTw using (P; X; C; U; Y; hd; StU; GU; Λ; lvU; KT; ownU; MP; sim; QF; st; LdU)
import OCF.Align.StratTwRd as SRd
open import OCF.Align.NegStratTwBlind using (hd-inj)
```

## §1 头结点

```agda
X-head : ∀ s → Σ (HB (Lev (X s)) → HB (P (suc s))) (λ g → X (suc s) ≡ hΩ (inj₂ tt , inj₂ tt) g)
X-head s = _ , refl

Y-head : ∀ s → Σ (HB (Lev (X s)) → HB U) (λ g → Y (suc s) ≡ hΩ (hd s) g)
Y-head s = _ , refl
```

## §2 哪些种类有级回灌

```agda
fed-exactly : ∀ κ (L : KLv U (tpK GU) Λ κ) → lvU κ ≡ inj₁ L → (κ ≡ (0 , tt)) ⊎ Σ ℕ (λ s → κ ≡ hd s)
fed-exactly (zero , tt) L e = inj₁ refl
fed-exactly (suc s , inj₂ tt) L e = inj₂ (s , refl)
fed-exactly (suc s , inj₁ κ) L ()

deep-lossy : ∀ s (κ : K (Lev (X s))) → lvU (suc s , inj₁ κ) ≡ inj₂ tt
deep-lossy s κ = refl

hd-inj-U : ∀ s k → ¬ (hd s ≡ hd (suc k Data.Nat.+ s))
hd-inj-U = hd-inj StU {tp = tpK GU} {lv = lvU} ownU (w₀ GU)
```

## §3 深种类也没有 A-回灌 (分量 $\ge 2$)

```agda
deep-noA : ∀ s (κ : K (Lev (X (suc s)))) → fbA GU (suc (suc s) , inj₁ κ) ≡ inj₂ tt
deep-noA s κ = refl
```

分量 1 ($X_0=1$, `Lev 1 = step S₀`): 底拷贝 `inj₁ tt` 有 A-回灌 (`fbS₀` 经 `liftS`, `liftSℕ`), 新种类 (坐标 `H₀`) 没有.

```agda
deep1-A : Σ _ (λ F → fbA GU (1 , inj₁ (inj₁ tt)) ≡ inj₁ F)
deep1-A = _ , refl

deep1-H : fbA GU (1 , inj₁ (inj₂ tt)) ≡ inj₂ tt
deep1-H = refl
```

## §4 头种类的读回读数据; 起始世界

```agda
open SRd U LdU using (module SR)

KT-rd : ∀ s {W} (lW : LgW (step U) W) b x → rd (KT s) lW b x ≡ SR.readS (MP s) (sim s) lW b x
KT-rd s lW b x = refl

start-hd : ∀ s → top (tpK GU) (hd s) (w₀ GU) ≡ hz
start-hd s = refl
```

## §5 结论 (按档)

- **[定理]** `X-head`, `Y-head`, **`fed-exactly`**, **`deep-lossy`**, **`deep-noA`**, `deep1-A`, `deep1-H`, **`hd-inj-U`**, `KT-rd`, `start-hd`.
- **[判断]** 相对 KindLv (`only-κ₁`), 回灌从一个种类扩到每站的头种类 (无穷多, 两两不同), 这一点接口 (`OwnHd`) 与实例都做到了. 深种类 (级 $X_s$ 里面的种类, 坐标是更低级的高度, 以坐标为下标) 全部有损; 对角 $Y_{s+1}$ 的头结点被回灌, 头以下经求值 `evK` 来的结点里凡是深种类的都有损. 把头种类的点更新推广到深种类撞分离子 ([NegStratTwDeep](NegStratTwDeep.lagda.md) `updD-sep`). 值没有定理.
