# 种类结构的对应 (二): 第 2 层读回成 `HB S₁` 的高度

> 不含记号. 入口 [HtTowerN](HtTowerN.lagda.md). 两种种类的折叠 ([HtTowerFFold](HtTowerFFold.lagda.md)) 在第 2 层目标上的输出 `D₂ = D (hs (hs hz))`, 接在高度 $b$ 后面读成 `Ht = HB S₁` 的高度 (`rd₂`), 与 [HtTowerFRead](HtTowerFRead.lagda.md) 的 `rd` (第 1 层读成 `H₀`) 同形, 多两种节点:
>
> - 过第 0 层的节点与旧种类的闭包 `nκ`: 读成旧种类 `κA` 上对 `A` 坐标递归的分支 (`nbAᵗ`); 坐标 $c$ 喂 `toD c`.
> - **过第 1 层的节点**: 读成**新种类** `κH` 上对 `H₀` 坐标递归的分支 (`HtTowerCont.nbᴮ`, 连续是定义性的, 合法由 `cont→Lg`); 坐标 $x$ 喂 **`toD₁ x`** (高度读成第 1 层的树: 旧种类的 $\Omega$-极限读成 `nκ`).
> - **新种类的闭包 `nμ`**: 也读成新种类的分支; 坐标 $x$ 上世界的高度界升到 $\mathrm{rd}(w_1,\mathrm{toD}_1\,x)$ (经第 1 层读回, 所以对任意 $x$ 都合法, 不要 $x$ 合法).
>
> `Lg-rd₂`: 底合法则读出合法, 无别的前提. `rd₂-fst`: 底是读出的第一位置, 在一切世界.
>
> **选择 (值不忠实, 判断):** `toD₁` 把 $\mathrm{h\Omega}\,h$ 读成闭包 (和), 不是上确界; 同 `HtOutRead.toD` 在极限坐标处的选择.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerNRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFRead using (D₁; toD; rd; rd-fst; Lg-rd; wκ; lwκ; pwκ)
```

## §1 高度读成第 1 层的树

```agda
toD₁ : ∀ {W} → H₀ → D₁ W
toD₁ hz = n0
toD₁ (hs x) = toD₁ x ⨾ n1
toD₁ (hl f) = nl (λ n → toD₁ (f n))
toD₁ (hΩ tt h) = nκ tt (λ {c} _ _ → toD₁ (h c))
```

## §2 旧种类上对 `A` 坐标递归的分支

```agda
nbAᵗ : Ht → (A → Ht → Ht) → A → Ht
nbAᵗ b s azero = b
nbAᵗ b s (asuc c) = s c (nbAᵗ b s c)
nbAᵗ b s (alim f) = hl (λ n → nbAᵗ b s (f n))

module _ {b : Ht} {s : A → Ht → Ht} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
  nbAᵗ-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbAᵗ b s c ⊲[ w ] nbAᵗ b s c′
  nbAᵗ-mono C.self = hself
  nbAᵗ-mono (C.suc p) = ⊲ᴮ-tr (nbAᵗ-mono p) (fs _ _)
  nbAᵗ-mono (C.lim n p) = hlim n (nbAᵗ-mono p)

  Lg-nbAᵗ : LgB b → (∀ c h → LgB h → LgB (s c h)) → LgB {S₁} (hΩ κA (nbAᵗ b s))
  Lg-nbAᵗ lb ls = (λ lw e e′ p → nbAᵗ-mono p) , lg
    where
    lg : ∀ c → Lg c → LgB (nbAᵗ b s c)
    lg azero _ = lb
    lg (asuc c) l = ls c _ (lg c l)
    lg (alim f) (st , l) = (λ n → nbAᵗ-mono (st n)) , (λ n → lg (f n) (l n))
```

## §3 第 2 层的树读成高度

`nμ` 的坐标 $x$ 上的世界: `A` 分量不变, 高度界取 $\mathrm{rd}(w_1,\mathrm{toD}_1\,x)$.

```agda
D₂ : Wd₂ → Set
D₂ = D (hs (hs hz))

xμ : ∀ {W} → LgW₂ W → H₀ → H₀
xμ {W} lW x = rd lW (proj₂ W) (toD₁ {W} x)

lxμ : ∀ {W} (lW : LgW₂ W) x → LgB (xμ lW x)
lxμ {W} lW x = Lg-rd lW (proj₂ W) (toD₁ x) (proj₂ lW)

≤μ : ∀ {W} (lW : LgW₂ W) x → W ≤ (proj₁ W , xμ lW x)
≤μ {W} lW x = C.self , rd-fst lW (proj₂ W) (toD₁ x)

rd₂  : ∀ {W} → LgW₂ W → Ht → D₂ W → Ht
rdp₂ : ∀ {W} → LgW₂ W → Ht → (ℕ → D₂ W) → ℕ → Ht
rd₂ lW b n0 = b
rd₂ lW b n1 = hs b
rd₂ lW b (x ⨾ y) = rd₂ lW (rd₂ lW b x) y
rd₂ lW b (nl d) = hl (rdp₂ lW b d)
rd₂ lW b (ni (ss hself) u) = hΩ κH (nbᴮ b (λ x h → rd₂ lW h (u ≤rf lW (toD₁ x))))
rd₂ lW b (ni (ss (hsuc hself)) u) = hΩ κA (nbAᵗ b (λ c h → rd₂ lW h (u ≤rf lW (toD c))))
rd₂ {W} lW b (nκ _ u) =
  hΩ κA (nbAᵗ b (λ c h → rd₂ (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))))
rd₂ {W} lW b (nμ _ u) =
  hΩ κH (nbᴮ b (λ x h → rd₂ (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x))))
rd₂ lW b (nw p x) = rd₂ (lgW≤ p lW) b x
rdp₂ lW b d zero = b
rdp₂ lW b d (suc n) = rd₂ lW (rdp₂ lW b d n) (d n)

rd₂-fst : ∀ {W} (lW : LgW₂ W) b (x : D₂ W) {w} → b ⊲[ w ] rd₂ lW b x
rd₂-fst lW b n0 = hself
rd₂-fst lW b n1 = hsuc hself
rd₂-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₂-fst lW b x) (rd₂-fst lW (rd₂ lW b x) y)
rd₂-fst lW b (nl d) = hlim 0 hself
rd₂-fst lW b (ni (ss hself) u) {w} = hLim {S₁} {κ = κH} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (ni (ss (hsuc hself)) u) {w} = hLim {S₁} {κ = κA} {c = azero} (z⊲ (proj₁ w)) hself
rd₂-fst lW b (nκ _ u) {w} = hLim {S₁} {κ = κA} {c = azero} (z⊲ (proj₁ w)) hself
rd₂-fst lW b (nμ _ u) {w} = hLim {S₁} {κ = κH} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₂-fst lW b (nw p x) = rd₂-fst (lgW≤ p lW) b x

Lg-rd₂  : ∀ {W} (lW : LgW₂ W) b (x : D₂ W) → LgB b → LgB (rd₂ lW b x)
Lg-rdp₂ : ∀ {W} (lW : LgW₂ W) b (d : ℕ → D₂ W) → LgB b → ∀ n → LgB (rdp₂ lW b d n)
Lg-rd₂ lW b n0 l = l
Lg-rd₂ lW b n1 l = l
Lg-rd₂ lW b (x ⨾ y) l = Lg-rd₂ lW (rd₂ lW b x) y (Lg-rd₂ lW b x l)
Lg-rd₂ lW b (nl d) l = (λ n → rd₂-fst lW (rdp₂ lW b d n) (d n)) , Lg-rdp₂ lW b d l
Lg-rd₂ lW b (ni (ss hself) u) l =
  cont→Lg (nb-contB l (λ x h → rd₂-fst lW h (u ≤rf lW (toD₁ x))) (λ x h lh → Lg-rd₂ lW h (u ≤rf lW (toD₁ x)) lh))
Lg-rd₂ lW b (ni (ss (hsuc hself)) u) l =
  Lg-nbAᵗ (λ c h → rd₂-fst lW h (u ≤rf lW (toD c))) l (λ c h lh → Lg-rd₂ lW h (u ≤rf lW (toD c)) lh)
Lg-rd₂ {W} lW b (nκ _ u) l =
  Lg-nbAᵗ (λ c h → rd₂-fst (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
          (λ c h lh → Lg-rd₂ (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
Lg-rd₂ {W} lW b (nμ _ u) l =
  cont→Lg (nb-contB l (λ x h → rd₂-fst (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)))
                      (λ x h lh → Lg-rd₂ (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)) lh))
Lg-rd₂ lW b (nw p x) l = Lg-rd₂ (lgW≤ p lW) b x l
Lg-rdp₂ lW b d l zero = l
Lg-rdp₂ lW b d l (suc n) = Lg-rd₂ lW (rdp₂ lW b d n) (d n) (Lg-rdp₂ lW b d l n)
```
