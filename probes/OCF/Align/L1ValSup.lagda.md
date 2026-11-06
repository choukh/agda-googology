# 第 1 层差树的值语义 (三): 上确界读法与链的停滞

> 不含记号. 入口 [L1Val](L1Val.lagda.md). **编译过的否定.** 两棵自然的第 1 层差树:
>
> - $x_1=\sum_z 1$ (`ni` 分支恒为 `n1`, 即 $\Omega_1$ 的主体),
> - $x_2=\sum_z z$ (`CvLayerInst.xs`, 分支是坐标抬上来).
>
> 两者的分支都对坐标的值单调 (`Mono`, `mono₁`, `mono₂`), $\mathrm{toB}\,x_1\preccurlyeq\mathrm{toB}\,x_2$ (`toB-le`), 而折叠 (同 [L1ValBase](L1ValBase.lagda.md) §4 的场景) 在 $x_1$ 上输出 $\ge1$, 在 $x_2$ 上输出 $0$ (`fold-sep`).
>
> **原因是停滞.** 目标第 0 层低于节点层, 折叠走链 (`RKi` rise, `Chn`): 第一个链点是状态的差 $\delta_0$, 每一段沿 $\delta_n$ 走, 每个位置在坐标 $w$ 处跑分支 $u(w)$. $x_2$ 在值为 $0$ 的坐标上分支是 $0$, 所以第一段输出 $0$, 下一个链点没有 `n1`, 之后全部停滞 (`L1ValBase.chain-stall`, 对一切输入). `toB` 的值是分支部分和的上确界, 只看 "最终多大", 不看 "从链点出发第一步给不给东西".
>
> **否定的是什么.** "折叠对第 1 层输入的 `toB` 值单调" 在分支对坐标值单调的输入上也不成立 (`¬mono-on-Mono`). 所以 `Mono` (现有的 `Kn-mono`, `KL-mono` 那种判据) 不够; 第 1 层的值语义对 `ni` 不能用上确界 (`i≼`) 比, 要逐分支比, 或者再加一个判据排除停滞. 这是 `Value.ψ⁰-not-cong` 在差树第 1 层上的同类, 这里两棵树都不是人为的.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.L1ValSup where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; cnt; Dif)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (dif; toA; sum₀; round₁)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; toB)
open import OCF.Align.LayerTrOmega using (Iv)
open import OCF.Align.CvLayerInst using (↑; xs)
open import OCF.Align.L1ValBase
open import OCF.Align.LayerTrOne using (S-fst; ok-yes)
open import OCF.Align.CvFoldSub using (≼-suc)
open import OCF.Align.CvFoldInst using (Kn)
open import OCF.Align.CvHighInst using (br)
```

## §1 两棵树

```agda
x₁ x₂ : D one one
x₁ = ni (ss C.self) (λ _ _ _ → n1)
x₂ = xs
```

## §2 抬上来的坐标: 值就是和

`S q l b (↑ z)` 夹在 $b$ 加上 $z$ 的和的两侧 (底与和的嵌入可比时).

```agda
up-low  : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (z : D azero W₀) a (b : B₁ W) → emb {W} a ≼ b → emb {W} (sum a z) ≼ S q l b (↑ z)
up-lowp : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (d : ℕ → D azero W₀) a (b : B₁ W) → emb {W} a ≼ b →
          ∀ n → emb {W} (pt a d n) ≼ Sp q l b (λ m → ↑ (d m)) n
up-low q l n0 a b h = h
up-low q l n1 a b h = s≼s h
up-low q l (x ⨾ y) a b h = up-low q l y (sum a x) (S q l b (↑ x)) (up-low q l x a b h)
up-low q l (nl d) a b h = l≼ (λ n → ≼l n (up-lowp q l d a b h n))
up-low q l (nw p x) a b h = up-low (⊲-tr p q) l x a b h
up-low q l (ni () u) a b h
up-low q l (nκ () u) a b h
up-lowp q l d a b h zero = h
up-lowp q l d a b h (suc n) = up-low q l (d n) (pt a d n) _ (up-lowp q l d a b h n)

up-high  : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (z : D azero W₀) a (b : B₁ W) → b ≼ emb {W} a → S q l b (↑ z) ≼ emb {W} (sum a z)
up-highp : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (d : ℕ → D azero W₀) a (b : B₁ W) → b ≼ emb {W} a →
           ∀ n → Sp q l b (λ m → ↑ (d m)) n ≼ emb {W} (pt a d n)
up-high q l n0 a b h = h
up-high q l n1 a b h = s≼s h
up-high q l (x ⨾ y) a b h = up-high q l y (sum a x) (S q l b (↑ x)) (up-high q l x a b h)
up-high q l (nl d) a b h = l≼ (λ n → ≼l n (up-highp q l d a b h n))
up-high q l (nw p x) a b h = up-high (⊲-tr p q) l x a b h
up-high q l (ni () u) a b h
up-high q l (nκ () u) a b h
up-highp q l d a b h zero = h
up-highp q l d a b h (suc n) = up-high q l (d n) (pt a d n) _ (up-highp q l d a b h n)
```

## §3 两棵树的分支都对坐标值单调

```agda
mono₁ : Mono {one} (λ _ _ _ → n1)
mono₁ p l z z′ h = ≼-refl _

sum-le : ∀ {W W′} (z : D azero W) (z′ : D azero W′) → proj₁ (toA z) ≤ proj₁ (toA z′) → sum azero z ≤ sum azero z′
sum-le z z′ h = ≤-trans (proj₁ (sum₀ z)) (≤-trans h (proj₂ (sum₀ z′)))

mono₂ : Mono {one} (λ _ _ w → ↑ w)
mono₂ p l z z′ h =
  ≼-trans (up-high C.self l z azero bz z≼) (≼-trans (emb-mono (sum-le z z′ h)) (up-low C.self l z′ azero bz z≼))
```

## §4 $\mathrm{toB}\,x_1\preccurlyeq\mathrm{toB}\,x_2$

$x_1$ 在坐标 $y$ 上的分支是 $\sum_{w<y}1\approx y$ (`LayerTrOmega.Iv`). $x_2$ 在坐标 $y+1$ 上的分支的最后一格是 $u(\mathrm{dif}\,y)=\uparrow(\mathrm{dif}\,y)$, 它 $\succcurlyeq y$ (`up-low`).

```agda
dif≤ : ∀ {W} y (ly : Lg y) → sum azero (dif {W} y (z⊲ y) ly) ≤ y
dif≤ {W} y ly = ≤-trans (proj₁ (sum₀ (dif {W} y (z⊲ y) ly))) (proj₁ (round₁ {W} y ly))

≤dif : ∀ {W} y (ly : Lg y) → y ≤ sum azero (dif {W} y (z⊲ y) ly)
≤dif {W} y ly = ≤-trans (proj₂ (round₁ {W} y ly)) (proj₂ (sum₀ (dif {W} y (z⊲ y) ly)))

toB-le : toB tt x₁ ≼ toB tt x₂
toB-le = i≼ (λ {W′} p l y ly →
  ≼i p l (asuc y) ly
    (≼-trans (proj₁ (Iv (dif y (z⊲ y) ly) C.self n0 (bw p bz) azero (w≼ z≼ , z≼)))
    (≼-trans (emb-mono {W′} {W′} (dif≤ {W′} y ly))
    (≼-trans (emb-mono {W′} {W′} (≤dif {W′} y ly))
             (up-low C.self l (dif y (z⊲ y) ly) azero _ z≼)))))
```

## §5 折叠: $x_1$ 给东西, $x_2$ 停滞

```agda
big : has1 (out x₁) ≡ true
big = refl

-- 链的参数, 照 RunNi / RKi rise 写
kW : azero ⊲ one
kW = C.suc C.self

A² : F.Ig (cnt azero) one
A² = F.Ai (F.accCn one) (ss C.self) (λ _ _ w → ↑ w) C.self kW C.self StepA₁ n0

δ₂ : ℕ → D azero one
δ₂ = δ (F.accCn azero) kW tt (lg⊲ kW tt) A² Ys

-- 第 0 段与第 1 个链点: 由检查器归约
seg0 : ZD (seg (F.accCn azero) kW tt (lg⊲ kW tt) A² Ys 0)
seg0 τ lt = _

d1 : Z (δ₂ 1)
d1 = _

zs : ∀ n → Z (δ₂ (suc n))
zs zero = d1
zs (suc n) = proj₂ (chain-stall (F.accCn azero) kW tt (lg⊲ kW tt) A² Ys (suc n) (zs n))

small : Z (out x₂)
small zero = seg0 (inj₁ (z⊲ one)) tt
small (suc n) = proj₁ (chain-stall (F.accCn azero) kW tt (lg⊲ kW tt) A² Ys (suc n) (zs n)) (inj₁ (z⊲ one)) tt
```

## §6 否定

```agda
fold-sep : ¬ (val x₁ ≤ val x₂)
fold-sep = sep (out x₁) (out x₂) big small

¬mono-on-Mono : ¬ (∀ (u u′ : ∀ {W′} → one ⊲ W′ → Lg W′ → D azero W′ → D one W′) → Mono u → Mono u′ →
                   toB tt (ni (ss C.self) u) ≼ toB tt (ni (ss C.self) u′) → val (ni (ss C.self) u) ≤ val (ni (ss C.self) u′))
¬mono-on-Mono H = fold-sep (H (λ _ _ _ → n1) (λ _ _ w → ↑ w) mono₁ mono₂ toB-le)
```

## §7 判据: 不停滞

`Pos u`: `ni` 的分支在每个坐标上都 $\succcurlyeq1$. 链的第一步给东西当且仅当链点上的分支给东西, 所以这是排除停滞最直接的判据 (判断: 它不一定够). $x_2$ 不满足 (`x₂-not-pos`, 坐标 `n0` 处). 折叠在 $\psi_0(\Omega_{\Omega+1})$ 计算里真正产出的读坐标节点 `CvFoldInst.Kn` 满足 (`Kn-pos`, 对一切状态): 它的分支是 `Step` 的输出, 字面以 $\cdot\omega$ 包着 `n1` 开头.

```agda
Pos : ∀ {W} → (∀ {W′} → W ⊲ W′ → Lg W′ → D azero W′ → D one W′) → Set
Pos {W} u = ∀ {W′} (p : W ⊲ W′) (l : Lg W′) (z : D azero W′) → bs (bz {W′}) ≼ S C.self l bz (u p l z)

x₂-not-pos : ¬ Pos {one} (λ _ _ w → ↑ w)
x₂-not-pos H = no-suc {b = bz {one}} tt (H C.self tt n0)

⊲→≼ : ∀ {V V′ fl} {a : B₁ V} {b : B₁ V′} → a ⊲⟨ fl ⟩ b → a ≼ b
⊲→≼ self = ≼-refl _
⊲→≼ (suc p) = ≼-suc (⊲→≼ p)
⊲→≼ (lim n p) = ≼l n (⊲→≼ p)
⊲→≼ (wR p) = ≼w (⊲→≼ p)
⊲→≼ (wL p) = w≼ (⊲→≼ p)
⊲→≼ (ini l p) = ≼i C.self l azero tt (⊲→≼ p)
⊲→≼ (inκ l p) = ≼κ C.self l (⊲→≼ p)

-- 分支形如 ·ω 包着以 n1 开头的东西
pos-ω : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (x y : D one W₀) → bs b ≼ S q l b (nl (λ _ → (n1 ⨾ x) ⨾ y))
pos-ω q l b x y =
  ≼l 1 (⊲→≼ (⊲ᴮ-tr (S-fst yes q l (bs b) x (ok-yes x)) (S-fst yes q l (S q l (bs b) x) y (ok-yes y))))

Kn-pos : ∀ w Y → Pos {one} (λ p l z → br (Kn w Y) p l z)
Kn-pos w Y p l z = pos-ω C.self l bz (Dif one (z⊲ one) C.self tt) _
```
