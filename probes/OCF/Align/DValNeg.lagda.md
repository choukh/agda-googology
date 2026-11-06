# 差树上的值关系 (五): 判据为什么必须有, `nκ` 为什么不在里面

> 不含记号. 入口 [DVal](DVal.lagda.md). **编译过的否定.** 场景: 世界 $1$, 目标第 0 层 ($\tau_0$ = `inj₁ (suc self)`), 起点状态 `F.Y₀` (全零), 动作 `A⁺`: 每一步输出一个 `n1` (满足 `DValSound.HA₁`, 所以在 `snd` 的范围里).
>
> 1. **`¬assoc`**: 折叠对重新加括号不单调. $(0⨾1)⨾x_b$ 输出 $\ge2$, $0⨾(1⨾x_b)$ 输出 $\le1$, 其中 $x_b$ 是 [L1ValShape](L1ValShape.lagda.md) 的读坐标形状的 `ni`. 原因: 两种加括号让 $x_b$ 起步时状态的第 0 层差**值相同, 字面不同** ($0⨾(0⨾1)$ 对 $(0⨾0)⨾1$), 链的第一个链点在 `n1` 处的坐标一个是坏形状一个不是. 所以 `DValTree` 的结合律必须带 `Rf z` 的前提, 不能无条件.
>    - **`xb-not-Rf`**: $x_b$ 不自比. 所以判据 `Rf` 是真的限制, 不是一切树都满足. `ub-not-Mono`: 它的分支不 `Mono`.
> 2. **`¬κ-refl`**: 任何关系, 只要对 `⨾` 同余, 能比第 0 层值相同的无节点前缀 ($1$ 对 $(\lim_n 0)⨾1$), 并且**每个 `nκ` 都自比** (同一世界、同一路径逐分支比的最弱形式), 就不能让折叠单调. 反例 $u$ 在字面的层 $1$ 上给 `n1`, 在值也是 $1$ 的层 $\lim_n 1$ 上给 `n0`: 前缀不同, 回灌读的层 `sum W z` 字面不同, 一边走到 $1$, 一边走到 $\lim_n 1$, 后者以后全部停滞 (`L1ValBase.κ-stall`). `DValTree` 的关系满足前两条 (`v1ᵈ`), 所以它**不能**加上无条件的 `nκ` 自比规则; `nκ` 的分支必须按层的**值**对齐比较.
>
> 否定的范围: 只否定所述的那一类关系 (前提都可满足: 两条反例都是具体的项, 定理里的前提由 `⊑ᵈ` 实例化). 不否定: 带判据 (分支对层的值单调且对齐方式合适) 的 `nκ` 规则; 别的目标层.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DValNeg where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.L1ValBase using (Z; has1; low; zup; chain-stall; κ-stall; Rκ; SFL; drp-Z)
open import OCF.Align.L1ValShape using (ub; xb; bad)
open import OCF.Align.DValTree
import OCF.Align.DValSound as S
```

## §1 场景

```agda
A⁺ : F.Ig (cnt one) one
A⁺ _ _ _ _ = F.df (λ τ lt → n1) n0

kW : azero ⊲ one
kW = C.suc C.self

out⁺ : D one one → D azero one
out⁺ x = F.yc (F.Run (F.accCn one) x C.self tt C.self A⁺ n0 F.Y₀) (inj₁ kW) tt

val⁺ : D one one → A
val⁺ x = sum azero (out⁺ x)

module S₁ = S {one} tt C.self

HA⁺ : S₁.HA₁ A⁺
HA⁺ w w′ c c′ Y Y′ cb r = s≤ cb

-- snd 在这个场景里
mono⁺ : ∀ {x x′ : D one one} → x ⊑ᵈ x′ → val⁺ x ≤ val⁺ x′
mono⁺ h = S₁.snd h A⁺ HA⁺ C.self C.self n0 n0 azero azero F.Y₀ F.Y₀ z≤ z≤

no21 : ¬ (asuc (asuc azero) ≤ asuc azero)
no21 (s≤ ())

-- 和的第二段
rt : ∀ {W} → D azero W → D azero W
rt (_ ⨾ y) = y
rt _ = n0
```

## §2 结合律要判据

```agda
L R : D one one
L = (n0 ⨾ n1) ⨾ xb
R = n0 ⨾ (n1 ⨾ xb)

-- 左边: 链点 0⨾(0⨾1), n1 处坐标是坏形状
big : has1 (rt (out⁺ L)) ≡ true
big = refl

-- 右边: 链点 (0⨾0)⨾1, n1 处坐标不是坏形状, 第 0 段为零, 以后停滞
A²R : F.Ig (cnt azero) one
A²R = F.Ai (F.accCn one) (ss C.self) ub C.self kW C.self A⁺ ((n0 ⨾ nw C.self n0) ⨾ nw C.self n1)

YR : F.St one
YR = (F.Y₀ F.⊕ F.zeroD) F.⊕ A⁺ C.self tt (n0 ⨾ nw C.self n0) (F.Y₀ F.⊕ F.zeroD)

δR : ℕ → D azero one
δR n = proj₁ (proj₂ (F.Chn (F.accCn azero) kW tt tt A²R YR n))

seg0 : Z (F.yc (F.Run (F.accCn azero) (δR 0) C.self tt kW A²R n0 YR) (inj₁ kW) tt)
seg0 = _

d1 : Z (δR 1)
d1 = _

zs : ∀ n → Z (δR (suc n))
zs zero = d1
zs (suc n) = proj₂ (chain-stall (F.accCn azero) kW tt tt A²R YR (suc n) (zs n))

PzR : D azero one
PzR = nl (λ n → F.yc (F.Run (F.accCn azero) (δR n) C.self tt kW A²R (proj₁ (F.Chn (F.accCn azero) kW tt tt A²R YR n))
                             (proj₂ (proj₂ (F.Chn (F.accCn azero) kW tt tt A²R YR n)))) (inj₁ kW) tt)

zR : Z PzR
zR zero = seg0
zR (suc n) = proj₁ (chain-stall (F.accCn azero) kW tt tt A²R YR (suc n) (zs n)) (inj₁ kW) tt

-- 右边的输出就是 0 ⨾ (1 ⨾ PzR)
outR : out⁺ R ≡ n0 ⨾ (n1 ⨾ PzR)
outR = refl

¬assoc : ¬ (val⁺ L ≤ val⁺ R)
¬assoc le = no21 (≤-trans lo (≤-trans le up))
  where
  lo : asuc (asuc azero) ≤ val⁺ L
  lo = low (asuc azero) (rt (out⁺ L)) big
  up : val⁺ R ≤ asuc azero
  up = zup (asuc azero) (asuc azero) PzR zR (≤-refl _)

xb-not-Rf : ¬ Rf xb
xb-not-Rf h = ¬assoc (mono⁺ (asʳ h (⨾⊑ (⨾⊑ n0⊑ n1⊑) h)))

ub-not-Mono : ¬ Mono ub
ub-not-Mono m = xb-not-Rf (rf-ni m)
```

## §3 `nκ` 不能无条件自比

```agda
isOne : A → Bool
isOne (asuc azero) = true
isOne _ = false

pk : ∀ {W} → Bool → D one W
pk true = n1
pk false = n0

uκ : ∀ {c} → one ⊲ c → Lg c → D one c
uκ {c} p l = pk (isOne c)

c0 : ∀ {W} → ℕ → D one W
c0 _ = n0

Xκ X′κ : D one one
Xκ = n1 ⨾ nκ tt uκ
X′κ = (nl c0 ⨾ n1) ⨾ nκ tt uκ

-- 左边: 第一格走到字面的层 1
bigκ : has1 (rt (out⁺ Xκ)) ≡ true
bigκ = refl

-- 右边: 层是 (lim 1)+1, 第一格只走到 lim 1, 分支为零
Y′ : F.St one
Y′ = F.Y₀ F.⊕ F.Run (F.accCn one) (nl c0 ⨾ n1) C.self tt C.self A⁺ n0 F.Y₀

sfl-pt : ∀ n → SFL (pt (asuc azero) (λ _ → n0 {W = one}) n) (OCF.Align.SumOneTree.Lg-pt (asuc azero) (λ _ → n0 {W = one}) n tt)
sfl-pt zero = tt
sfl-pt (suc n) = sfl-pt n

Rκ0 : Rκ (F.accCn one) uκ C.self tt C.self A⁺ (n0 ⨾ nw C.self (nl c0 ⨾ n1)) Y′ 0
Rκ0 = (λ τ lt → _) , ((λ n → tt) , sfl-pt)

rκ : ∀ n → Rκ (F.accCn one) uκ C.self tt C.self A⁺ (n0 ⨾ nw C.self (nl c0 ⨾ n1)) Y′ n
rκ zero = Rκ0
rκ (suc n) = κ-stall (F.accCn one) uκ C.self tt C.self A⁺ _ Y′ n (rκ n)

Pκ : D azero one
Pκ = nl (λ n → drp (F.yc (F.κΔ (F.accCn one) uκ C.self A⁺ (F.κc (F.accCn one) uκ C.self tt C.self A⁺ (n0 ⨾ nw C.self (nl c0 ⨾ n1)) Y′ n))
                         (inj₁ (z⊲ (F.v (F.κc (F.accCn one) uκ C.self tt C.self A⁺ (n0 ⨾ nw C.self (nl c0 ⨾ n1)) Y′ n)))) tt))
  where open OCF.Align.SumOneTree using (drp)

zκ : Z Pκ
zκ n = drp-Z _ (proj₁ (rκ n) (inj₁ (z⊲ _)) tt)

outκ : out⁺ X′κ ≡ (nl (λ _ → n0) ⨾ n1) ⨾ Pκ
outκ = refl

no1 : ∀ n → ¬ (asuc azero ≤ pt azero (λ _ → n0 {W = one}) n)
no1 zero ()
no1 (suc n) h = no1 n h

no2 : ¬ (asuc (asuc azero) ≤ asuc (alim (pt azero (λ _ → n0 {W = one}))))
no2 (s≤ (≤l n h)) = no1 n h

sepκ : ¬ (val⁺ Xκ ≤ val⁺ X′κ)
sepκ le = no2 (≤-trans (low (asuc azero) (rt (out⁺ Xκ)) bigκ) (≤-trans le (zup _ _ Pκ zκ (≤-refl _))))

-- 抽象的否定: 同余 + 无节点前缀按值 + nκ 自比 ⇒ 折叠不单调
¬κ-refl : (_⊑_ : D one one → D one one → Set) →
          (∀ {x y x′ y′} → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)) →
          (n1 ⊑ (nl c0 ⨾ n1)) →
          (∀ (u : ∀ {c} → one ⊲ c → Lg c → D one c) → nκ tt u ⊑ nκ tt u) →
          ¬ (∀ {x x′} → x ⊑ x′ → val⁺ x ≤ val⁺ x′)
¬κ-refl _⊑_ cg v1 κr H = sepκ (H (cg v1 (κr uκ)))

-- ⊑ᵈ 满足前两条
v1ᵈ : _⊑ᵈ_ {one} {one} n1 (nl c0 ⨾ n1)
v1ᵈ = trˡ (u0ʳ n1⊑) (⨾⊑ n0⊑ n1⊑)
```
