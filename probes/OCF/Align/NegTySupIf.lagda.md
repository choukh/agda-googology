# 带类型折叠到 sup 层, 否定一路 (四): 接口的盲区 — `dec` 没有律

> 不含记号. 入口 [NegTySup](NegTySup.lagda.md). 对着接口 [TySupIf](TySupIf.lagda.md) ("接口定稿 2026-11-05 21:37 (首次编译通过)") 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 接口的 `dec` 带公共上界 (好), 但它的结果 `Dc` (留 / 同层 / 在上) 与种类的层号 `lv X κ` 之间**没有律**: `keep` 不要求层号低于目标, `same` 不要求层号等于目标, `above i` 不要求 $i$ 就是层号; 各个读回 (`fr`, `to`, `toE`) 与地板 `top` 也没有律. 本篇把这一点写成定理.
>
> **结果.**
>
> 1. **`towerIf` (构造, 前提实例).** Fab3Typed 的塔 `T n` 是接口的一个实例: 层号是 ℕ, `_⊏_` 是 `Below` (字面的 "在下面"), 种类的层号 `lvT`, 地板 `Ω n`, `dec` 由 ℕ 上的三歧 (`cmpN`) 给出, 留下的种类由位置证据 `νT` 找到, 读回逐构造子是恒等. **`ok-tower` (定理)**: 它的 `dec` 正确 (`Ok`: 留 ⇒ 层号在目标下面; 同层 ⇒ 层号就是目标; 在上 ⇒ $i$ 就是层号).
> 2. **`constIf` (构造), `¬ok-const`, `noKeep-const` (定理, 盲).** 把 `towerIf` 的 `dec` 换成 "一律同层, 回灌取常值 `toE X κ 0`", 其余字段不动, 仍是接口的实例; 它的 `dec` 不正确 (第 2 层的 $\Omega_2$ 种类对目标 $0$ 报 "同层"), 从不留任何种类, 回灌不是恒等. 换法对**一切**实例可做 (`constDec`): `same (λ _ → toE X κ hz)` 总是 `Dc` 的一个居民. 所以接口不区分 "按层号正确地决定" 与 "什么都坍缩成常值链".
> 3. **`trivIf` (构造, 盲).** 层号只有一个、没有种类的实例. 接口不要求有任何种类, 不要求地板是结点.
>
> **只否定什么.** 只否定推断 "接口 (`TySupIf`) 保证 sup 层按层号正确地留/坍缩, 或保证回灌是恒等, 或保证高层种类被保留". 这些是**实例**的性质, 要对实例单独证 (例如 `ok-tower`). **不否定**: 接口本身, 构造一路的折叠与证书 (`TySupFold.Φ`, `Sh-Φ` 对一切实例成立, 本篇不碰它们的正确性; 它们的盲区见 [NegTySupMono](NegTySupMono.lagda.md)); 给接口**增补** `Ok` 一类的律 (接口只增不改, 可以加).
>
> **对纲领与目标.** 正确性 (`Ok`) 是树侧可以写出的判据: 只用层号与种类的位置, 不看记号. 本篇建议把它作为增补字段, 并在实例上证明.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTySupIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab3Typed using (T; Ω)
open import OCF.Align.TySupIf
```

## §1 正确性: 一个接口外的判据

```agda
module _ (R : TySupIf) where
  open TySupIf R

  -- 对给定的层号 j 陈述 (j 就是种类的层号时即 Ok)
  OkAt : ∀ {X t κ} → C → Dc L _⊏_ _⊑_ X t κ → Set
  OkAt {t = t} j (keep _ _) = j ⊏ t
  OkAt {t = t} j (same _) = j ≡ t
  OkAt j (above i _ _ _) = i ≡ j

  Ok : ∀ X t κ → Dc L _⊏_ _⊑_ X t κ → Set
  Ok X t κ d = OkAt (lv X κ) d

  Correct : Set
  Correct = ∀ X t q l κ → Ok X t κ (dec X t q l κ)

  -- 对一切实例: "一律同层, 回灌取常值" 总是一个决定
  constDec : ∀ X t → t ⊑ X → LgC X → (κ : K (L X)) → Dc L _⊏_ _⊑_ X t κ
  constDec X t q l κ = same (λ _ → toE X κ hz)

  constOf : TySupIf
  constOf = record
    { C = C ; _⊑_ = _⊑_ ; _⊏_ = _⊏_ ; LgC = LgC ; ⊏→⊑ = ⊏→⊑ ; lgC↓ = lgC↓ ; wf = wf ; L = L
    ; lv = lv ; pos = pos ; toE = toE ; top = top ; z = z ; z⊑ = z⊑ ; noK = noK ; dec = constDec }

  IsKeep : ∀ {X t κ} → Dc L _⊏_ _⊑_ X t κ → Set
  IsKeep (keep _ _) = ⊤
  IsKeep (same _) = ⊥
  IsKeep (above _ _ _ _) = ⊥

  noKeep-const : ∀ X t q l κ → ¬ IsKeep (constDec X t q l κ)
  noKeep-const X t q l κ ()
```

## §2 塔的实例

`Below j n`: $j$ 字面地在 $n$ 下面 ($n = j+1+\dots$). 种类的层号 `lvT`, 位置 `posT`, 坐标 `toET` 都对种类结构递归, 到底一步类型字面对上 (恒等).

```agda
data Below : ℕ → ℕ → Set where
  here  : ∀ {n} → Below n (suc n)
  there : ∀ {j n} → Below j n → Below j (suc n)

accB : ∀ n → AccR Below n
downB : ∀ {i n} → Below i n → AccR Below i
accB n = acc (λ i p → downB p)
downB {n = suc n} here = accB n
downB (there p) = downB p

LeB : ℕ → ℕ → Set
LeB i X = (i ≡ X) ⊎ Below i X

zB : ∀ n → Below 0 (suc n)
zB zero = here
zB (suc n) = there (zB n)

z⊑B : ∀ X → LeB 0 X
z⊑B zero = inj₁ refl
z⊑B (suc n) = inj₂ (zB n)

liftB : ∀ {j t} → Below j t → Below (suc j) (suc t)
liftB here = here
liftB (there p) = there (liftB p)

cmpN : ∀ j t → Below j t ⊎ ((j ≡ t) ⊎ Below t j)
cmpN zero zero = inj₂ (inj₁ refl)
cmpN zero (suc t) = inj₁ (zB t)
cmpN (suc j) zero = inj₂ (inj₂ (zB j))
cmpN (suc j) (suc t) with cmpN j t
... | inj₁ p = inj₁ (liftB p)
... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong suc e))
... | inj₂ (inj₂ p) = inj₂ (inj₂ (liftB p))

lvT : ∀ n → K (T n) → ℕ
lvT (suc n) (inj₁ κ) = lvT n κ
lvT (suc n) (inj₂ _) = n

posT : ∀ n κ → Below (lvT n κ) n
posT (suc n) (inj₁ κ) = there (posT n κ)
posT (suc n) (inj₂ _) = here

toET : ∀ n κ → HB (T (lvT n κ)) → E (T n) κ
toET (suc n) (inj₁ κ) = toET n κ
toET (suc n) (inj₂ _) = λ h → h

νT : ∀ {j} n → Below j n → K (T n)
νT (suc n) here = inj₂ tt
νT (suc n) (there p) = inj₁ (νT n p)

fromE : ∀ {j} n (p : Below j n) → E (T n) (νT n p) → HB (T j)
fromE (suc n) here = λ h → h
fromE (suc n) (there p) = fromE n p

noKT : K (T 0) → ⊥
noKT ()

goT : ∀ X t κ → Below (lvT X κ) t ⊎ ((lvT X κ ≡ t) ⊎ Below t (lvT X κ)) → Dc (λ n → T n) Below LeB X t κ
goT X t κ (inj₁ p) = keep (νT t p) (λ c → toET X κ (fromE t p c))
goT X t κ (inj₂ (inj₁ e)) = same (λ h → toET X κ (subst (λ m → HB (T m)) (sym e) h))
goT X t κ (inj₂ (inj₂ p)) = above (lvT X κ) (posT X κ) (inj₂ p) (toET X κ)

decT : ∀ X t → LeB t X → ⊤ → (κ : K (T X)) → Dc (λ n → T n) Below LeB X t κ
decT X t q l κ = goT X t κ (cmpN (lvT X κ) t)

towerIf : TySupIf
towerIf = record
  { C = ℕ ; _⊑_ = LeB ; _⊏_ = Below ; LgC = λ _ → ⊤ ; ⊏→⊑ = inj₂ ; lgC↓ = λ _ _ → tt ; wf = accB
  ; L = T ; lv = lvT ; pos = posT ; toE = toET ; top = Ω ; z = 0 ; z⊑ = z⊑B ; noK = noKT ; dec = decT }

ok-go : ∀ X t κ r → Ok towerIf X t κ (goT X t κ r)
ok-go X t κ (inj₁ p) = p
ok-go X t κ (inj₂ (inj₁ e)) = e
ok-go X t κ (inj₂ (inj₂ p)) = refl

ok-tower : Correct towerIf
ok-tower X t q l κ = ok-go X t κ (cmpN (lvT X κ) t)
```

**回灌在塔上是恒等 (定理, `refl`).** 第 2 层的新种类 ($\Omega_2$, 层号 1) 对目标 1: `same`, 读回就是恒等.

```agda
feed-tower : decT 2 1 (inj₂ here) tt (inj₂ tt) ≡ same (λ h → h)
feed-tower = refl
```

## §3 常值决定: 同样的字段, 错误的决定

```agda
constIf : TySupIf
constIf = constOf towerIf

¬ok-const : ¬ Correct constIf
¬ok-const ok with ok 2 0 (inj₂ (zB 1)) tt (inj₂ tt)
... | ()

-- 除 dec 外字段相同 (逐字段 refl)
same-L : TySupIf.L constIf ≡ TySupIf.L towerIf
same-L = refl

same-top : TySupIf.top constIf ≡ TySupIf.top towerIf
same-top = refl

same-lv : TySupIf.lv constIf ≡ TySupIf.lv towerIf
same-lv = refl
```

## §4 平凡实例: 没有种类

```agda
trivIf : TySupIf
trivIf = record
  { C = ⊤ ; _⊑_ = λ _ _ → ⊤ ; _⊏_ = λ _ _ → ⊥ ; LgC = λ _ → ⊤ ; ⊏→⊑ = λ () ; lgC↓ = λ () ; wf = λ _ → acc (λ _ ())
  ; L = λ _ → S⊥ ; lv = λ _ () ; pos = λ _ () ; toE = λ _ () ; top = λ _ → hz ; z = tt ; z⊑ = λ _ → tt
  ; noK = λ () ; dec = λ _ _ _ _ () }
```

## 结论 (按档)

- **[定理]** `OkAt`, `Ok`, `Correct`, `constDec`, `constOf`, `noKeep-const` (对一切实例); `towerIf` (塔的实例), `ok-tower`, `feed-tower`; `constIf`, `¬ok-const`, `same-L`, `same-top`, `same-lv`; `trivIf`.
- **[判断]** 建议增补的律: `Correct` (或它的一部分), 以及 `same` 的读回在 `lv X κ ≡ t` 上是恒等 (塔上 `feed-tower`). 加了以后 `constOf` 不再是实例; 这是否给构造一路的实例带来难处 (例如 `HB S⊥` 层号上的 `same` 要 `bdec` 的相等证据) 未查.
