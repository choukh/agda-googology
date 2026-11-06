# LeanFb (三): 按级读回

> 不含记号. 入口 [LeanFb](LeanFb.lagda.md), 接口 [LeanFbIf](LeanFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 一份级层上的数据读成某个种类结构 $X$ 的高度增量 (接口 `LvRd`). 两种:
>
> - **级 0** (`R0`): 级层 $0$, 读回是 `sum` (第 0 层数据读成 `HB S⊥`). 用于级为 `lz` 的一切种类 (第 0 站的头与它的一切拷贝), 它们的坐标就是 `HB S⊥`.
> - **级 1 式** (`RX a`): 级层 $1$, 读回 `rdX` 与 [LeanTTree](LeanTTree.lagda.md) §5 的 `rd₁` 逐行同形, 只是目标换成任一 $X$ 与它的一个坐标可读成 `HB S⊥` 的种类 `a` (`AK0 X`; `rd₁` 的目标固定为折叠的 `T`, 用不上): 过第 0 层的结点读成种类 `a` 的 $\Omega$-结点, 分支对坐标连续 (`nbA`). 对级为 `ls lz` 的种类 (第 1 站的头与它的一切拷贝, 坐标 `HB (step S⊥)`), $X$ = `step S⊥`, `a` 是它的新种类: 级层与坐标的级都是 $1$ (**自己的级**). 对第 $n\ge2$ 站的头, $X$ = `Lv (st n)`, `a` 由 `find0` 在层号里找 (级 `lz` 的种类), 级层是 $1$, **不是**这些头自己的级.
>
> **为什么第 $n\ge2$ 站的头没有自己的级层 [判断].** 按级读回要级层的子层与坐标种类结构的种类一一对应 (原 `KindLvRd` 对 `Lev c` 与层 `hs (up c)` 是字面对应). 第 $n\ge2$ 站的头坐标是 `HB (Lv (st n))`, `st n` 是 `SL` 的高度 `tw n` 的层号; 折叠的层在 `HB (step SLs)` 里, 它的 $\Omega$-结点是站的种类. 要把 `Lv (st n)` 的种类一一放进层, 要么让层号是 `SLs` 的高度的读法 (`st (n+1)` 依赖 `SLs` 本身, 要分层, 即 `StratTw` 的路), 要么在 `SL` 上折叠 (世界以层号为下标, 否定一路的 `wdec1`). 本轮未走; 也没有否定定理, 记为未走通.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt
open Tree SLs
open NbA
```

## §1 坐标可读成 `HB S⊥` 的种类

```agda
record AK0 (X : KS) : Set where
  field
    aK      : K X
    fr      : E X aK → HB S⊥
    fr-lg   : ∀ {w e} → LgW X w → Bd X aK e w → LgB (fr e)
    fr-mono : ∀ {w e e′} → LgW X w → Bd X aK e w → Bd X aK e′ w → Pr X aK w e e′ → ∀ {v} → fr e ⊲[ v ] fr e′
open AK0 public

newAK : AK0 (step S⊥)
newAK = record { aK = inj₂ tt ; fr = λ e → e ; fr-lg = λ lw e → lgB⊲ e (proj₁ lw) (proj₂ lw)
               ; fr-mono = λ _ _ _ p → ⊲ᴮ↑ (λ ()) p }

oldAK : ∀ {S} → AK0 S → AK0 (step S)
oldAK a = record { aK = inj₁ (aK a) ; fr = fr a ; fr-lg = λ lw e → fr-lg a (proj₁ lw) e
                 ; fr-mono = λ lw e e′ p → fr-mono a (proj₁ lw) e e′ p }

supAK : ∀ {I : Set} {F : I → KS} (i : I) → AK0 (F i) → AK0 (sup I F)
supAK i a = record { aK = i , aK a ; fr = fr a ; fr-lg = λ lw e → fr-lg a (lw i) e
                   ; fr-mono = λ lw e e′ p → fr-mono a (lw i) e e′ p }

-- 在层号里找一个级为 lz 的种类
find0  : (k : LH) → AK0 (Lv k) ⊎ ⊤
findSt : (x : LH) → AK0 (step (Lv x)) ⊎ ⊤
findSt lz = inj₁ newAK
findSt (ls x) = map₁ oldAK (find0 (ls x))
findSt (ll f) = map₁ oldAK (find0 (ll f))
findSt (lΩ k g) = map₁ oldAK (find0 (lΩ k g))
find0 lz = inj₂ tt
find0 (ls x) = findSt x
find0 (ll f) = map₁ (supAK {ℕ} {λ n → Lv (f n)} 0) (find0 (f 0))
find0 (lΩ k g) = map₁ (supAK {⊤ ⊎ HB (Lv k)} {[ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′} (inj₁ tt)) (findSt k)
```

## §2 第 1 层的数据读进 $X$

```agda
module RdX {X : KS} (a : AK0 X) where
  rdX  : ∀ {W} → LgW L₀ W → HB X → D (hs hz) W → HB X
  rdpX : ∀ {W} → LgW L₀ W → HB X → (ℕ → D (hs hz) W) → ℕ → HB X
  rdX lW b n0 = b
  rdX lW b n1 = hs b
  rdX lW b (x ⨾ y) = rdX lW (rdX lW b x) y
  rdX lW b (nl d) = hl (rdpX lW b d)
  rdX lW b (ni (ss hself) u) = hΩ (aK a) (λ e → nbA b (λ c h → rdX lW h (u ≤rf lW (toD₀ c))) (fr a e))
  rdX lW b (nc (inj₁ κ) z u) = rdX lW b (u ≤rf lW)
  rdX lW b (nc (inj₂ _) () u)
  rdX lW b (nw p x) = rdX (lgDn L₀ p lW) b x
  rdpX lW b d zero = b
  rdpX lW b d (suc n) = rdX lW (rdpX lW b d n) (d n)

  rdX-fst : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) {w} → b ⊲[ w ] rdX lW b x
  rdX-fst lW b n0 = hself
  rdX-fst lW b n1 = hsuc hself
  rdX-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rdX-fst lW b x) (rdX-fst lW (rdX lW b x) y)
  rdX-fst lW b (nl d) = hlim 0 hself
  rdX-fst lW b (ni (ss hself) u) {w} =
    hLim {X} {κ = aK a} {c = bot X (aK a)} (botBd X (aK a) w)
      (nbA-fst b _ (λ c h → rdX-fst lW h (u ≤rf lW (toD₀ c))) (fr a (bot X (aK a))))
  rdX-fst lW b (nc (inj₁ κ) z u) = rdX-fst lW b (u ≤rf lW)
  rdX-fst lW b (nc (inj₂ _) () u)
  rdX-fst lW b (nw p x) = rdX-fst (lgDn L₀ p lW) b x

  Lg-rdX  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → LgB b → LgB (rdX lW b x)
  Lg-rdpX : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → LgB b → ∀ n → LgB (rdpX lW b d n)
  Lg-rdX lW b n0 l = l
  Lg-rdX lW b n1 l = l
  Lg-rdX lW b (x ⨾ y) l = Lg-rdX lW (rdX lW b x) y (Lg-rdX lW b x l)
  Lg-rdX lW b (nl d) l = (λ n → rdX-fst lW (rdpX lW b d n) (d n)) , Lg-rdpX lW b d l
  Lg-rdX lW b (ni (ss hself) u) l =
    (λ lw e e′ p → nbA-mono b _ fs (fr-mono a lw e e′ p {w₀ S⊥})) ,
    (λ {c = e₀} lw e → Lg-nbA b _ fs l (λ c h lh → Lg-rdX lW h (u ≤rf lW (toD₀ c)) lh) (fr a e₀) (fr-lg a lw e))
    where
    fs : ∀ c h {w} → h ⊲[ w ] rdX lW h (u ≤rf lW (toD₀ c))
    fs c h = rdX-fst lW h (u ≤rf lW (toD₀ c))
  Lg-rdX lW b (nc (inj₁ κ) z u) l = Lg-rdX lW b (u ≤rf lW) l
  Lg-rdX lW b (nc (inj₂ _) () u) l
  Lg-rdX lW b (nw p x) l = Lg-rdX (lgDn L₀ p lW) b x l
  Lg-rdpX lW b d l zero = l
  Lg-rdpX lW b d l (suc n) = Lg-rdX lW (rdpX lW b d n) (d n) (Lg-rdpX lW b d l n)
open RdX public
```

## §3 接口实例

```agda
R0 : LvRd SLs ΛF S⊥
R0 = record { ℓ = hz ; ℓ⊲ = z⊲ᴮ ΛF ; δ = λ lW x → sum hz x ; δLg = λ lW x → Lg-sum hz x tt ; δ-n1 = λ lW → refl }

RX : ∀ {X} → AK0 X → LvRd SLs ΛF X
RX a = record { ℓ = hs hz ; ℓ⊲ = oneF ; δ = λ lW x → rdX a lW hz x ; δLg = λ lW x → Lg-rdX a lW hz x tt ; δ-n1 = λ lW → refl }
```

**读回产出 $\Omega$-结点 (定理).** 过第 0 层的结点读成种类 `a` 的 $\Omega$-结点 (不是可数的增量; 对照 `Fab2SLs.rdC-form`).

```agda
rdX-node : ∀ {X} (a : AK0 X) {W} (lW : LgW L₀ W) b
  (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → Vs (hs hz) {W} (ss hself) W′ → D (hs hz) W′) →
  rdX a lW b (ni (ss hself) u) ≡ hΩ (aK a) (λ e → nbA b (λ c h → rdX a lW h (u ≤rf lW (toD₀ c))) (fr a e))
rdX-node a lW b u = refl
```
