# 相干的世界 (四): `Lev` 里的拷贝不相干

> 不含记号. 入口 [CohW](CohW.lagda.md). `U⋆` ([CohWL](CohWL.lagda.md)) 让**链上**的拷贝相干 (`rcohL→`, `yes-wmatch`). 但 `L′ (k+1)` 还有 `false` 分量 `Lev (Ωtop (L′ k)) = sup (HB (L′ k)) (c ↦ Lev (up c))`: 对第 $k$ 级的每个高度 $c$, 一个**新造的**种类结构 `Lev (up c)`, 世界是 `sup` 的独立分量. 这些种类结构里又有低级的种类, 是链上种类的拷贝.
>
> 例子: `step S₀` 的新种类 (坐标 `H₀`) 在 `U⋆` 里至少出现两次:
>
> - `κ0⋆ = (1, (true, new))`: 链上的, `step (L′ 0) = step S₀`;
> - `κL = (2, (false, (1, new)))`: `L′ 2` 的 `Lev` 部分, 坐标 $c=1$ 的分量 `Lev (up 1) = Lev 1 = step S₀` (`same-S`, `refl`).
>
> 两个种类的坐标类型相同 (`same-E`), 种类结构相同, 界却在世界的两个互不相干的位置: 前者是第 0 份扩张数据的 $\beta_0$, 后者在第 1 份扩张数据的 `Lev` 世界里. **`no-cross→`, `no-cross←`**: 在合法的 `U⋆` 世界里, 一个的界推不出另一个的界 (两个方向). 推论 **`no-route`**: 对任何种类结构 $S'$ 的任何种类 $\kappa'$, 任何坐标映射与世界映射, 不能同时 "从 `κ0⋆` 的界读进 $\kappa'$" 与 "从 $\kappa'$ 读出 `κL` 的界"; 这是 `HtTowerNStage.no-wmatch` 的形状, 搬到 `U⋆` 的 `Lev` 部分.
>
> 底种类 (坐标 `A`) 同样有两份: 链上的 `κA0 = (0, tt)` 与 `Lev` 拷贝 `κAL` (**`no-crossA→`, `no-crossA←`**, §4). 拷贝确实出现在对角之下: 合法世界 `wE` 里最外是 `κL` 的合法层是 `Λ⋆` 的第一位置 (**`κL-layer`**, §5).
>
> **范围.** 只说这两对种类 (反方向 `no-route←` 同). 不说读回必须把链上的种类读成 `Lev` 里的拷贝, 那是判断 (见入口的第一个障碍). 不否定 `U⋆` 的链相干 (`rcohL→` 是定理); 不否定 "`Lev` 部分也用扩张生成的世界" 这条路线.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; dWLev)
open import OCF.Align.CohWTy
open import OCF.Align.CohWL
open import OCF.Align.CohWTower using (θ⋆; Λ⋆; Lg-Λ⋆)
```

## §1 两个拷贝

```agda
κL : K U⋆
κL = 2 , (false , (hs hz , inj₂ tt))

same-S : Lev {step (L′ 1)} (up (hs hz)) ≡ step S₀
same-S = refl

same-E : E U⋆ κ0⋆ ≡ E U⋆ κL
same-E = refl
```

## §2 两个合法世界

`lgdW`: `HtTowerNStage.dWLev` (每一级取最小的分量) 是合法世界. `dW1`: 同样的形状, 新种类的界取 $1$.

```agda
lgdW : ∀ {S} (x : HB S) → LgW (Lev x) (dWLev x)
lgdW hz = tt
lgdW (hs x) = lgdW x , tt
lgdW (hl f) = λ n → lgdW (f n)
lgdW (hΩ κ g) = λ c → lgdW (g c)

dW1 : ∀ {S} (x : HB S) → Wd (Lev x)
dW1 hz = azero
dW1 (hs x) = dW1 x , hs hz
dW1 (hl f) = λ n → dW1 (f n)
dW1 (hΩ κ g) = λ c → dW1 (g c)

lgdW1 : ∀ {S} (x : HB S) → LgW (Lev x) (dW1 x)
lgdW1 hz = tt
lgdW1 (hs x) = lgdW1 x , tt
lgdW1 (hl f) = λ n → lgdW1 (f n)
lgdW1 (hΩ κ g) = λ c → lgdW1 (g c)
```

`wA`: 链上的界 $\beta_0 = 1$, `Lev` 拷贝的界是 $0$. `wB`: 链上的界都是 $0$, `Lev` 拷贝的界是 $1$.

```agda
βA : ∀ k → HB (L′ k)
βA zero = hs hz
βA (suc k) = hz

wA : Wd U⋆
wA = azero , (λ k → βA k , dWLev (Ωtop (L′ k)))

lgA : LgW U⋆ wA
lgA zero = tt
lgA (suc k) = λ { true → (lgA k , lgβ k) ; false → lgdW (Ωtop (L′ k)) }
  where
  lgβ : ∀ k → LgB (βA k)
  lgβ zero = tt
  lgβ (suc k) = tt

wB : Wd U⋆
wB = azero , (λ k → hz , dW1 (Ωtop (L′ k)))

lgB : LgW U⋆ wB
lgB zero = tt
lgB (suc k) = λ { true → (lgB k , tt) ; false → lgdW1 (Ωtop (L′ k)) }
```

## §3 否定

```agda
no-cross→ : ¬ (∀ {c w} → LgW U⋆ w → Bd U⋆ κ0⋆ c w → Bd U⋆ κL c w)
no-cross→ h with h {hs hz} {wA} lgA hself
... | ()

no-cross← : ¬ (∀ {c w} → LgW U⋆ w → Bd U⋆ κL c w → Bd U⋆ κ0⋆ c w)
no-cross← h with h {hs hz} {wB} lgB hself
... | ()
```

两个前提各自可满足 (同一个坐标 $1$, 各在自己的世界里):

```agda
satA : Bd U⋆ κ0⋆ (hs hz) wA
satA = hself

satB : Bd U⋆ κL (hs hz) wB
satB = hself
```

**推论: 经任何种类结构都不能读通.** 读回把 `U⋆` 的世界投影到某个种类结构 $S'$, 把坐标搬进 $S'$ 的种类 $\kappa'$; 若一头保 `κ0⋆` 的界, 另一头保 `κL` 的界, 合起来就是 `no-cross→` 否定的蕴涵.

```agda
no-route : ∀ (S′ : KS) (κ′ : K S′) (t : HB S₀ → E S′ κ′) (wm′ : Wd U⋆ → Wd S′) →
  (∀ {c w} → LgW U⋆ w → Bd U⋆ κ0⋆ c w → Bd S′ κ′ (t c) (wm′ w)) →
  (∀ {c w} → LgW U⋆ w → Bd S′ κ′ (t c) (wm′ w) → Bd U⋆ κL c w) → ⊥
no-route S′ κ′ t wm′ h1 h0 = no-cross→ (λ lw e → h0 lw (h1 lw e))

no-route← : ∀ (S′ : KS) (κ′ : K S′) (t : HB S₀ → E S′ κ′) (wm′ : Wd U⋆ → Wd S′) →
  (∀ {c w} → LgW U⋆ w → Bd U⋆ κL c w → Bd S′ κ′ (t c) (wm′ w)) →
  (∀ {c w} → LgW U⋆ w → Bd S′ κ′ (t c) (wm′ w) → Bd U⋆ κ0⋆ c w) → ⊥
no-route← S′ κ′ t wm′ h1 h0 = no-cross← (λ lw e → h0 lw (h1 lw e))
```

## §4 底的拷贝也不相干

坐标是 `H₀` 的高度时, 它里面的 $\Omega$-节点是底种类 (坐标 `A`) 的, 在**某个 `A` 世界**里有界. 链上的底种类 `κA0 = (0, tt)` 的 `A` 世界是 `U⋆` 世界的第一个分量; `Lev` 拷贝里的底种类 `κAL = (2, (false, (1, old)))` 的 `A` 世界在第 1 份扩张数据的 `Lev` 世界里. 同样互不相干. 这一条说的是: 哪怕读回层是第 1 层 (输出只含底种类的节点, 同 `HtTowerFRead.rd`), 读出的 `H₀` 高度作 `κL` 的坐标时, 它的节点要在**另一个** `A` 世界里有界.

```agda
κA0 κAL : K U⋆
κA0 = 0 , tt
κAL = 2 , (false , (hs hz , inj₁ tt))

dW2 : ∀ {S} (x : HB S) → Wd (Lev x)
dW2 hz = asuc azero
dW2 (hs x) = dW2 x , hz
dW2 (hl f) = λ n → dW2 (f n)
dW2 (hΩ κ g) = λ c → dW2 (g c)

lgdW2 : ∀ {S} (x : HB S) → LgW (Lev x) (dW2 x)
lgdW2 hz = tt
lgdW2 (hs x) = lgdW2 x , tt
lgdW2 (hl f) = λ n → lgdW2 (f n)
lgdW2 (hΩ κ g) = λ c → lgdW2 (g c)

-- 链上的 A 世界是 1, 拷贝的是 0
wC : Wd U⋆
wC = asuc azero , (λ k → hz , dWLev (Ωtop (L′ k)))

lgC : LgW U⋆ wC
lgC zero = tt
lgC (suc k) = λ { true → (lgC k , tt) ; false → lgdW (Ωtop (L′ k)) }

-- 链上的 A 世界是 0, 拷贝的是 1
wD : Wd U⋆
wD = azero , (λ k → hz , dW2 (Ωtop (L′ k)))

lgD : LgW U⋆ wD
lgD zero = tt
lgD (suc k) = λ { true → (lgD k , tt) ; false → lgdW2 (Ωtop (L′ k)) }

no-crossA→ : ¬ (∀ {c w} → LgW U⋆ w → Bd U⋆ κA0 c w → Bd U⋆ κAL c w)
no-crossA→ h with h {asuc azero} {wC} lgC C.self
... | ()

no-crossA← : ¬ (∀ {c w} → LgW U⋆ w → Bd U⋆ κAL c w → Bd U⋆ κA0 c w)
no-crossA← h with h {asuc azero} {wD} lgD C.self
... | ()
```

## §5 `Λ⋆` 之下确有 `Lev` 拷贝的层

`no-cross` 有意义, 要 `Lev` 拷贝的种类真的出现在对角之下. `c₂`: `L′ 2` 里最外是 `κL` 的节点的高度 (分支取常值 $0$, 合法). 世界 `wE` 的第 2 份扩张数据的界取 `c₂`, 合法. 在 `wE` 里, 最外是 `κL` 的层 `hΩ κL (_ ↦ θ⋆ 2)` 是 `Λ⋆` 的第一位置. 所以 `Λ⋆` 上的折叠要有 `κL` 的闭包 (判断: 照 `HtTowerFTree.Ωd`, 层的每个 $\Omega$-节点给一个闭包).

```agda
c₂ : HB (L′ 2)
c₂ = hΩ (false , (hs hz , inj₂ tt)) (λ _ → hz)

Lg-c₂ : LgB c₂
Lg-c₂ = (λ lw e e′ p → hself) , (λ c lc → tt)

βE : ∀ k → HB (L′ k)
βE zero = hz
βE (suc zero) = hz
βE (suc (suc zero)) = c₂
βE (suc (suc (suc k))) = hz

wE : Wd U⋆
wE = azero , (λ k → βE k , dWLev (Ωtop (L′ k)))

lgE : LgW U⋆ wE
lgE zero = tt
lgE (suc k) = λ { true → (lgE k , lgβ k) ; false → lgdW (Ωtop (L′ k)) }
  where
  lgβ : ∀ k → LgB (βE k)
  lgβ zero = tt
  lgβ (suc zero) = tt
  lgβ (suc (suc zero)) = Lg-c₂
  lgβ (suc (suc (suc k))) = tt

κL-layer : hΩ κL (λ _ → θ⋆ 2) ⊲[ wE ] Λ⋆
κL-layer = hlim 3 (hLim {c = c₂} hself hself)

Lg-κL-layer : LgB {U⋆} (hΩ κL (λ _ → θ⋆ 2))
Lg-κL-layer = lgB⊲ κL-layer lgE Lg-Λ⋆
```
