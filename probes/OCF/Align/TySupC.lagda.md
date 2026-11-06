# 带类型折叠的 sup 层: 可数层号的实例

> 不含记号. 入口 [TySup](TySup.lagda.md), 接口 [TySupIf](TySupIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 层号取第 0 层的值 `HB S⊥` (只有 $0$, 后继, ℕ-极限的树). 种类结构 `L x = Lv (ofC x)`: [LFReTy](LFReTy.lagda.md) 的 `Lv` 限制在不含 `lΩ` 的层号上, 即 $0\mapsto$ `S⊥`, 后继 $\mapsto$ `step`, ℕ-极限 $\mapsto$ `sup ℕ`. 字面第一位置 `t ⊑ X` 是 `t ⊲[ tt ] X`, 严格 `i ⊏ X` 是 `hs i ⊲[ tt ] X` (第 $i$ 层的新种类在 $X$ 里的位置), 层号的合法是 `LgB`.
>
> **决定** (§3) 用 `cmpB {S⊥}`, 公共上界就是 $X$: 比较 `hs i` (种类的位置) 与 $t$ (目标), 都是 $X$ 的字面第一位置, $X$ 合法. 结果 `hs i ⊲ t` 给 "留": 沿这条路径把种类嵌进 `L t` (`along`, 后继走 `inj₁`, ℕ-极限走分量 $n$, 到头是新种类 `inj₂ tt`); `t ⊲ hs i` 的路径若是 `hself` 也是留, 若是 `hsuc hself` 是同层, 其余是在上. 坐标的转换都对路径或种类结构递归, 每一步类型字面对上, 不要运输.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TySupC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; Lv)
open import OCF.Align.TySupIf
```

## §1 层号, 种类结构, 位置

```agda
Cd : Set
Cd = HB S⊥

ofC : Cd → LH
ofC hz = lz
ofC (hs x) = ls (ofC x)
ofC (hl f) = ll (λ n → ofC (f n))
ofC (hΩ () _)

LC : Cd → KS
LC x = Lv (ofC x)

_⊑ᶜ_ : Cd → Cd → Set
t ⊑ᶜ X = t ⊲[ tt ] X

_⊏ᶜ_ : Cd → Cd → Set
i ⊏ᶜ X = hs i ⊲[ tt ] X

-- 种类的层号, 位置, 坐标
lvC : ∀ X → K (LC X) → Cd
lvC hz ()
lvC (hs x) (inj₁ κ) = lvC x κ
lvC (hs x) (inj₂ _) = x
lvC (hl f) (n , κ) = lvC (f n) κ
lvC (hΩ () _) _

posC : ∀ X κ → lvC X κ ⊏ᶜ X
posC hz ()
posC (hs x) (inj₁ κ) = hsuc (posC x κ)
posC (hs x) (inj₂ _) = hself
posC (hl f) (n , κ) = hlim n (posC (f n) κ)
posC (hΩ () _) _

toC : ∀ X κ → HB (LC (lvC X κ)) → E (LC X) κ
toC hz ()
toC (hs x) (inj₁ κ) c = toC x κ c
toC (hs x) (inj₂ _) c = c
toC (hl f) (n , κ) c = toC (f n) κ c
toC (hΩ () _) _
```

## §2 良基, 地板

`hs i ⊲ X` 只能沿 $X$ 的后继与 ℕ-极限走到某个 `hs i` 处, 所以 $i$ 是 $X$ 的真子项; 可达性对 $X$ 结构归纳.

```agda
wfC : ∀ X → AccR _⊏ᶜ_ X
goC : ∀ X i → i ⊏ᶜ X → AccR _⊏ᶜ_ i
wfC X = acc (goC X)
goC hz i ()
goC (hs x) .x hself = wfC x
goC (hs x) i (hsuc p) = goC x i p
goC (hl f) i (hlim n p) = goC (f n) i p
goC (hΩ () _) i _

⊏→⊑ᶜ : ∀ {i X} → i ⊏ᶜ X → i ⊑ᶜ X
⊏→⊑ᶜ p = ⊲ᴮ-tr (hsuc hself) p

lgC↓ᶜ : ∀ {i X} → i ⊏ᶜ X → LgB X → LgB i
lgC↓ᶜ p l = lgB⊲ p tt l
```

`topC X`: 第 $X$ 层的地板 (读法 $\Omega_X$). 后继层是新种类的结点 $\sup_c c$ (同 Fab3Typed 的 `Ω`), ℕ-极限逐分量取.

```agda
topC : ∀ X → HB (LC X)
topC hz = hz
topC (hs x) = hΩ (inj₂ tt) up
topC (hl f) = hl (λ n → ι n (topC (f n)))
topC (hΩ () _)
```

## §3 决定

`along q`: 沿路径 `q : hs i ⊲ t` 把第 $i$ 层的新种类嵌进 `L t`; `frA q` 读回坐标.

```agda
along : ∀ {i t} → i ⊏ᶜ t → K (LC t)
along hself = inj₂ tt
along (hsuc q) = inj₁ (along q)
along (hlim n q) = n , along q
along (hLim {κ = ()} _ _)

frA : ∀ {i t} (q : i ⊏ᶜ t) → E (LC t) (along q) → HB (LC i)
frA hself c = c
frA (hsuc q) c = frA q c
frA (hlim n q) c = frA q c
frA (hLim {κ = ()} _ _) _

pick : ∀ {X t i} {κ : K (LC X)} → (HB (LC i) → E (LC X) κ) → i ⊏ᶜ X →
       (t ⊲[ tt ] hs i) ⊎ (hs i ⊲[ tt ] t) → Dc LC _⊏ᶜ_ _⊑ᶜ_ X t κ
pick to pi (inj₂ q) = keep (along q) (λ c → to (frA q c))
pick to pi (inj₁ hself) = keep (inj₂ tt) to
pick to pi (inj₁ (hsuc hself)) = same to
pick to pi (inj₁ (hsuc (hsuc q))) = above _ pi (hsuc q) to
pick to pi (inj₁ (hsuc (hlim n q))) = above _ pi (hlim n q) to
pick to pi (inj₁ (hsuc (hLim {κ = ()} _ _)))

decC : ∀ X t → t ⊑ᶜ X → LgB X → (κ : K (LC X)) → Dc LC _⊏ᶜ_ _⊑ᶜ_ X t κ
decC X t pt lX κ = pick (toC X κ) (posC X κ) (cmpB (posC X κ) pt tt lX)
```

## §4 实例

```agda
noKC : K (LC hz) → ⊥
noKC ()

ICd : TySupIf
ICd = record
  { C = Cd ; _⊑_ = _⊑ᶜ_ ; _⊏_ = _⊏ᶜ_ ; LgC = LgB
  ; ⊏→⊑ = ⊏→⊑ᶜ ; lgC↓ = lgC↓ᶜ ; wf = wfC
  ; L = LC ; lv = lvC ; pos = posC ; toE = toC ; top = topC
  ; z = hz ; z⊑ = λ X → z⊲ᴮ X ; noK = noKC ; dec = decC }
```
