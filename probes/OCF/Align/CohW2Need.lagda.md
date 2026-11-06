# 单一并上的折叠要什么 (一): 按层号读界、只升一层

> 不含记号. 入口 [CohW2](CohW2.lagda.md). 接 [CohWUpd](CohWUpd.lagda.md) 的条件定理, 把它收紧到折叠真正要用的接口上, 并把用到的层号限制在 `Λ` 之下真的出现的层号.
>
> **折叠要的世界操作 (判断, 读自 `HtTowerFFold`).** 闭包 (`RunM`) 回灌时: 从当前世界在闭包那一层的界出发 ($x_0=\mathrm{rd}(\text{界}, z_1)$, 要**读**界), 把**这一层**的界接长 (界 $\mapsto$ 界 $\boxplus\,\delta$), 在升高的世界里跑分支, 再把低于读回层的树搬回原来的世界 (`drp`, `drp₁`, 要**低于这一层的层号的界不变**). 写成接口:
>
> - `World`: 世界类型 `Wd`, 按层号读界 `β y : Wd → H⁰ (Lv y)` (这是 `CohWGl.glob` 的形状: 界只看层号), 一个各层界都是 $0$ 的世界 `w₀`.
> - `RaiseAt Wo ℓ`: 只升层 $\ell$: `raise x w`, 律 `r-at`: 层 $\ell$ 的界变成 `β ℓ w ⊞⁰ x`; 律 `r-sub`: 层 $\ell$ 的**子层号** ($y\prec\ell$, 结构上的子项) 的界不变. **不要求**别的层号不变 (比 `CohWUpd.Upd` 弱).
>
> **定理.**
>
> - **`raiseFin`** (可满足): `GW` 上, 每个有限层号 `fin n` 都有 `RaiseAt`, 构造性的, 不用判定.
> - **`raise-Lc→WLPO`**: 记 `Lc c` 为 `Λ` 之下坐标 $c$ 处出现的层号 (见 [CohW2Lim](CohW2Lim.lagda.md): 合法世界里, 最外是层号 `Lc c` 的新种类的层是 `Λ` 的第一位置). 若对一切可数坐标 $c$ 都有 `RaiseAt Wo (Lc c)`, 且对 `ℕ → LH` 的函数有外延 (`FE`, 作为前提, 不是公设), 则 **WLPO**. 证明只用到 $c$ 取一族合法的极限坐标 `l⁰ (hα α)`. 不用 `FE` 时得到的是 `raise-Lc→wdec`: 对每个 $\alpha$, 要么 $\alpha$ 恒假, 要么某两个层号不相等.
> - `raise-nat`: 坐标有限时 (`Lc (nat n) ≡ fin (n+1)`) `RaiseAt` 存在. 所以分界就在**极限坐标**.
>
> **范围.** 只对按层号读界的世界 (`World` 的 `β`), 只对 "读界 + 只升一层 + 子层号不变" 这个接口. 不说别的世界形状 (按位置存界: 有 `CohWNeg.no-cross`; 界只作关系、不能读: 没有试), 不说 `HtFeed` 族之外的折叠, 不说逐层折叠再取 ℕ-对角的路线. `FE` 在 `--safe --without-K` 里证不出, 也否证不了; 有外延的构造性模型 (实现性) 里 WLPO 不成立, 所以在那些模型里接口在一切 `Lc c` 上都不存在 (纸面, 元定理, 不是编译的).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延 (`FE` 只作前提).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohW2Need where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊞_)
open import OCF.Align.CohWGl using (LH; lz; ls; ll; lΩ; Lv; H⁰; z⁰; s⁰; l⁰; Ω⁰; GW; cv; ιS; ofHB)
```

## §1 子层号, 良基

`y ≺ ℓ`: $y$ 是 $\ell$ 的结构上的真子项 (经 `ls`, `ll` 的第 $n$ 项, `lΩ` 的 $k$ 或第 $d$ 支). 良基, 所以没有 $\ell\prec\ell$.

```agda
infix 4 _≺_
data _≺_ : LH → LH → Set where
  ≺s₀ : ∀ {x} → x ≺ ls x
  ≺s  : ∀ {x y} → x ≺ y → x ≺ ls y
  ≺l₀ : ∀ {f} n → f n ≺ ll f
  ≺l  : ∀ {x f} n → x ≺ f n → x ≺ ll f
  ≺k₀ : ∀ {k g} → k ≺ lΩ k g
  ≺k  : ∀ {x k g} → x ≺ k → x ≺ lΩ k g
  ≺g₀ : ∀ {k g} d → g d ≺ lΩ k g
  ≺g  : ∀ {x k g} d → x ≺ g d → x ≺ lΩ k g

data Acc (x : LH) : Set where
  acc : (∀ {y} → y ≺ x → Acc y) → Acc x

down : ∀ {x y} → Acc x → y ≺ x → Acc y
down (acc r) p = r p

wf : ∀ x → Acc x
wf lz = acc (λ ())
wf (ls x) = acc (λ { ≺s₀ → wf x ; (≺s p) → down (wf x) p })
wf (ll f) = acc (λ { (≺l₀ n) → wf (f n) ; (≺l n p) → down (wf (f n)) p })
wf (lΩ k g) = acc (λ { ≺k₀ → wf k ; (≺k p) → down (wf k) p ; (≺g₀ d) → wf (g d) ; (≺g d p) → down (wf (g d)) p })

irr : ∀ {x} → Acc x → ¬ (x ≺ x)
irr (acc r) p = irr (r p) p

≺→≢ : ∀ {y x} → y ≺ x → ¬ (y ≡ x)
≺→≢ {y} {x} p e = irr (wf x) (subst (λ z → z ≺ x) e p)
```

## §2 世界的接口

```agda
infixl 6 _⊞⁰_
_⊞⁰_ : ∀ {S} → H⁰ S → H⁰ S → H⁰ S
a ⊞⁰ z⁰ = a
a ⊞⁰ s⁰ b = s⁰ (a ⊞⁰ b)
a ⊞⁰ l⁰ f = l⁰ (λ n → a ⊞⁰ f n)
a ⊞⁰ Ω⁰ κ g = Ω⁰ κ (λ c → a ⊞⁰ g c)

record World : Set₁ where
  field
    Wd : Set
    β  : (y : LH) → Wd → H⁰ (Lv y)
    w₀ : Wd
    β₀ : ∀ y → β y w₀ ≡ z⁰
open World public

record RaiseAt (Wo : World) (ℓ : LH) : Set where
  field
    raise : H⁰ (Lv ℓ) → Wd Wo → Wd Wo
    r-at  : ∀ x w → β Wo ℓ (raise x w) ≡ (β Wo ℓ w ⊞⁰ x)
    r-sub : ∀ {y} → y ≺ ℓ → ∀ x w → β Wo y (raise x w) ≡ β Wo y w
open RaiseAt public
```

`GW` (`CohWGl` 的世界) 是一个实例: 读界就是取分量.

```agda
GWo : World
GWo = record { Wd = GW ; β = λ y w → w y ; w₀ = λ _ → z⁰ ; β₀ = λ y → refl }
```

## §3 有限层号上可以升 (前提可满足)

`sel n y P b d`: 对 $y$ 的结构递归, $y$ 恰是 `fin n` 时取 $b$, 否则取 $d$. 有限层号只由 `lz`, `ls` 构成, 头部可以逐层比, 不用判定任意层号的相等.

```agda
fin : ℕ → LH
fin zero = lz
fin (suc n) = ls (fin n)

sel : (n : ℕ) (y : LH) (P : LH → Set) → P (fin n) → P y → P y
sel zero lz P b d = b
sel zero (ls y) P b d = d
sel zero (ll f) P b d = d
sel zero (lΩ k g) P b d = d
sel (suc n) lz P b d = d
sel (suc n) (ls y) P b d = sel n y (λ z → P (ls z)) b d
sel (suc n) (ll f) P b d = d
sel (suc n) (lΩ k g) P b d = d

sel-at : ∀ n P b d → sel n (fin n) P b d ≡ b
sel-at zero P b d = refl
sel-at (suc n) P b d = sel-at n (λ z → P (ls z)) b d

sel-off : ∀ n y P b d → ¬ (fin n ≡ y) → sel n y P b d ≡ d
sel-off zero lz P b d ne = ⊥-elim (ne refl)
sel-off zero (ls y) P b d ne = refl
sel-off zero (ll f) P b d ne = refl
sel-off zero (lΩ k g) P b d ne = refl
sel-off (suc n) lz P b d ne = refl
sel-off (suc n) (ls y) P b d ne = sel-off n y (λ z → P (ls z)) b d (λ e → ne (cong ls e))
sel-off (suc n) (ll f) P b d ne = refl
sel-off (suc n) (lΩ k g) P b d ne = refl

raiseFin : ∀ n → RaiseAt GWo (fin n)
raiseFin n = record
  { raise = λ x w y → sel n y (λ z → H⁰ (Lv z)) (w (fin n) ⊞⁰ x) (w y)
  ; r-at = λ x w → sel-at n (λ z → H⁰ (Lv z)) (w (fin n) ⊞⁰ x) (w (fin n))
  ; r-sub = λ {y} p x w → sel-off n y (λ z → H⁰ (Lv z)) (w (fin n) ⊞⁰ x) (w y) (λ e → ≺→≢ p (sym e)) }
```

## §4 `Λ` 之下的层号

`Lc c`: `Λ` 的第 3 项 `tw 3` 在坐标 $c$ 处的分支是 $\hat\Omega(1\boxplus c)$; 在坐标 $c+1$ 处它最外是层号 `Lc c = ofHB (1 ⊞ c)` 的新种类 ([CohW2Lim](CohW2Lim.lagda.md) 的 `lim-layer`). 下面的等式都是定义相等: `Lc` 把后继读成 `ls`, 把 ℕ-极限读成 `ll`.

```agda
Lc : H⁰ (Lv lz) → LH
Lc c = ofHB (hs hz ⊞ ιS lz (cv lz c))

Lc-z : Lc z⁰ ≡ ls lz
Lc-z = refl

Lc-s : ∀ c → Lc (s⁰ c) ≡ ls (Lc c)
Lc-s c = refl

Lc-l : ∀ h → Lc (l⁰ h) ≡ ll (λ n → Lc (h n))
Lc-l h = refl

nat : ℕ → H⁰ (Lv lz)
nat zero = z⁰
nat (suc n) = s⁰ (nat n)

Lc-nat : ∀ n → Lc (nat n) ≡ fin (suc n)
Lc-nat zero = refl
Lc-nat (suc n) = cong ls (Lc-nat n)

-- 坐标有限时可以升
raise-nat : ∀ n → RaiseAt GWo (Lc (nat n))
raise-nat n = subst (RaiseAt GWo) (sym (Lc-nat n)) (raiseFin (suc n))
```

**一族合法的极限坐标.** $\omega$ 是 `l⁰ nat`. 对 $\alpha:\mathbb N\to\mathrm{Bool}$, `sw α n` 是 "前 $n$ 项里有真"; `hα α n` 在没见到真时是 $n$, 见到真以后是 $\omega+1+n$. 一路严格上升 (合法性在 `CohW2Lim`). $y_0 = $ `Lc ω` $=\mathrm{ll}(n\mapsto \mathrm{Lc}\,n)$.

```agda
ω⁰ : H⁰ (Lv lz)
ω⁰ = l⁰ nat

sn : ∀ {S} → ℕ → H⁰ S → H⁰ S
sn zero a = a
sn (suc n) a = s⁰ (sn n a)

sw : (ℕ → Bool) → ℕ → Bool
sw α zero = α zero
sw α (suc n) = sw α n ∨ α (suc n)

pickH : Bool → ℕ → H⁰ (Lv lz)
pickH true n = sn n (s⁰ ω⁰)
pickH false n = nat n

hα : (ℕ → Bool) → ℕ → H⁰ (Lv lz)
hα α n = pickH (sw α n) n

y₀ : LH
y₀ = Lc ω⁰

ℓα : (ℕ → Bool) → LH
ℓα α = Lc (l⁰ (hα α))
```

`α` 恒假时 `hα α` 逐点是 `nat`; `α n` 为真时 $y_0$ 是 `Lc (hα α n)` 的子层号, 从而是 `ℓα α` 的子层号.

```agda
∨-true : ∀ b → (b ∨ true) ≡ true
∨-true true = refl
∨-true false = refl

sw-true : ∀ α n → α n ≡ true → sw α n ≡ true
sw-true α zero e = e
sw-true α (suc n) e = trans (cong (λ b → sw α n ∨ b) e) (∨-true (sw α n))

sw-false : ∀ α → (∀ n → α n ≡ false) → ∀ n → sw α n ≡ false
sw-false α h zero = h zero
sw-false α h (suc n) = cong₂ _∨_ (sw-false α h n) (h (suc n))

≺-sn : ∀ n → y₀ ≺ Lc (sn n (s⁰ ω⁰))
≺-sn zero = ≺s₀
≺-sn (suc n) = ≺s (≺-sn n)

y₀≺ℓα : ∀ α n → α n ≡ true → y₀ ≺ ℓα α
y₀≺ℓα α n e = ≺l n (subst (λ b → y₀ ≺ Lc (pickH b n)) (sym (sw-true α n e)) (≺-sn n))

pt : ∀ α → (∀ n → α n ≡ false) → ∀ n → Lc (hα α n) ≡ Lc (nat n)
pt α h n = cong (λ b → Lc (pickH b n)) (sw-false α h n)
```

## §5 定理

`isZ`: 头部是不是 $0$ (可判定). 升一层之后读 $y_0$ 层的界, 看头部.

- 头部是 $0$: 若 $\alpha$ 恒假, 由 `FE`, `ℓα α ≡ y₀`, 而 `r-at` 说 `ℓα α` 层的界是 `0 ⊞ 1`, 头部不是 $0$, 矛盾. 所以 $\alpha$ 不恒假.
- 头部不是 $0$: 若某个 $\alpha\,n$ 为真, $y_0\prec$ `ℓα α`, `r-sub` 说 $y_0$ 层的界不变, 还是 $0$, 矛盾. `α n` 可判定, 所以 $\alpha$ 恒假.

```agda
isZ : ∀ {S} → H⁰ S → Bool
isZ z⁰ = true
isZ (s⁰ a) = false
isZ (l⁰ f) = false
isZ (Ω⁰ κ g) = false

t≢f : true ≡ false → ⊥
t≢f ()

FE : Set
FE = ∀ (f g : ℕ → LH) → (∀ n → f n ≡ g n) → f ≡ g

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

module _ (Wo : World) (R : ∀ c → RaiseAt Wo (Lc c)) (α : ℕ → Bool) where
  private
    Rα : RaiseAt Wo (ℓα α)
    Rα = R (l⁰ (hα α))
    W₁ : Wd Wo
    W₁ = raise Rα (s⁰ z⁰) (w₀ Wo)

  -- 被升的那一层, 头部不是 0
  at-nz : isZ (β Wo (ℓα α) W₁) ≡ false
  at-nz = cong isZ (r-at Rα (s⁰ z⁰) (w₀ Wo))

  -- 每个 α n 为真都给出 y₀ 层的界是 0
  sub-z : ∀ n → α n ≡ true → isZ (β Wo y₀ W₁) ≡ true
  sub-z n e = cong isZ (trans (r-sub Rα (y₀≺ℓα α n e) (s⁰ z⁰) (w₀ Wo)) (β₀ Wo y₀))

  all-false : isZ (β Wo y₀ W₁) ≡ false → ∀ n → α n ≡ false
  all-false e n with α n | sub-z n
  ... | true  | s = ⊥-elim (t≢f (trans (sym (s refl)) e))
  ... | false | s = refl

  -- 不用 FE: 要么 α 恒假, 要么 ℓα α 与 y₀ 不相等
  raise-Lc→wdec : (∀ n → α n ≡ false) ⊎ ¬ (ℓα α ≡ y₀)
  raise-Lc→wdec = go (isZ (β Wo y₀ W₁)) refl
    where
    go : (b : Bool) → isZ (β Wo y₀ W₁) ≡ b → (∀ n → α n ≡ false) ⊎ ¬ (ℓα α ≡ y₀)
    go false e = inj₁ (all-false e)
    go true e = inj₂ (λ p → t≢f (trans (sym e) (subst (λ z → isZ (β Wo z W₁) ≡ false) p at-nz)))

raise-Lc→WLPO : FE → (Wo : World) → (∀ c → RaiseAt Wo (Lc c)) → WLPO
raise-Lc→WLPO fe Wo R α with raise-Lc→wdec Wo R α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (cong ll (fe (λ n → Lc (hα α n)) (λ n → Lc (nat n)) (pt α h))))
```
